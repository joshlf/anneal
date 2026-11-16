-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ITree
import Anneal.Rustc.V2026_06_01.TraceCheck

namespace Anneal.Mir.ITreeApproxRunnerTests

open Trusted.Effect
open Trusted.ITree
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.ITree
open Anneal.Rustc.V2026_06_01.TraceCheck

/-!
# Suffix-Free `CofixA` Approximant Walkers & Fast `TraceCheck` Suite (`[adv ep1-A0]`)

Kernel regression, non-vacuity canary, and heartbeat-scaling benchmark suite for
`Anneal.ITree` Section 7 (`CofixA` walkers) and `Anneal.Rustc.V2026_06_01.TraceCheck`:
1. `#guard_msgs (whitespace := lax) in #print axioms` guards on all principal
   `Anneal.ITree` and `Anneal.Rustc.V2026_06_01.TraceCheck` bridge and soundness
   theorems, verifying zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`.
2. Positive `by rfl` kernel confirmation and `ReachesRet` / `TauStar` adequacy proofs
   across loop depths $k \in \{4, 8, 16, 32\}$ for `approxCofix`, `bindApprox`,
   `iterApprox`, `interpApprox`, and `interpStateApprox` (including nested
   `interpState` over `interp` over `iter`) under tight `maxHeartbeats` bounds.
3. Multi-iteration MIR loop `CapturedMir` fixtures with `SwitchInt` branches and
   external `MirCallE` oracle calls tested at $k \in \{4, 8, 16, 32\}$ across
   `checkRawByteTraceFullBounded*`, `checkRawByteTraceObsErasedBounded*`,
   `checkRawByteTraceFullApprox`, `checkRawByteTraceObsErasedApprox`, and
   `diagnoseRawByteTrace*Bounded`.
4. Negative non-vacuity canary theorems proving that wrong outcomes, wrong branch
   tags, wrong external call arguments, unexpected trailing events, impure pointer
   external calls, and insufficient fuel are soundly rejected (`= false` and
   exact `TraceReplayDiag` mismatch `by rfl`).
-/

/-! ## 1. Axiom-Hygiene Guards (`#print axioms`) -/

/-- info: 'Anneal.ITree.trunc_ofITree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trunc_ofITree

/-- info: 'Anneal.ITree.ofITree_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_inj

/-- info: 'Anneal.ITree.ofITree_cofix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_cofix

/-- info: 'Anneal.ITree.bindApprox_congr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bindApprox_congr

/-- info: 'Anneal.ITree.ofITree_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_bind

/-- info: 'Anneal.ITree.ofITree_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_map

/-- info: 'Anneal.ITree.iterApprox_congr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iterApprox_congr

/-- info: 'Anneal.ITree.ofITree_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_iter

/-- info: 'Anneal.ITree.interpApprox_ofITree_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interpApprox_ofITree_le

/-- info: 'Anneal.ITree.ofITree_interp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_interp

/-- info: 'Anneal.ITree.interpStateApprox_ofITree_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interpStateApprox_ofITree_le

/-- info: 'Anneal.ITree.ofITree_interpState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_interpState

/-- info: 'Anneal.ITree.ReachesRetApprox.toReachesRet' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReachesRetApprox.toReachesRet

/-- info: 'Anneal.ITree.ReachesRet.exists_ofITree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ReachesRet.exists_ofITree

/-- info: 'Anneal.ITree.reachesRet_iff_exists_ofITree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms reachesRet_iff_exists_ofITree

/-- info: 'Anneal.ITree.evalTauApprox_sound_tauStar' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_sound_tauStar

/-- info: 'Anneal.ITree.evalTauApprox_sound_reachesRet' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_sound_reachesRet

/-- info: 'Anneal.ITree.tauStar_ret_iff_exists_evalTauApprox' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms tauStar_ret_iff_exists_evalTauApprox

/-- info: 'Anneal.ITree.checkTauRetApprox_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkTauRetApprox_sound

/-- info: 'Anneal.ITree.checkTraceApprox_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.reconstructFullMirTraceFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstructFullMirTraceFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullMirTraceFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullMirTraceFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.reconstructFullMirTraceFast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstructFullMirTraceFast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullMirTraceFast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullMirTraceFast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullObservedTraceBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.reconstructObsErasedMirTraceFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstructObsErasedMirTraceFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedMirTraceFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedMirTraceFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.reconstructObsErasedMirTraceFast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstructObsErasedMirTraceFast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedMirTraceFast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedMirTraceFast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedObservedTraceBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedObservedTraceBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedObservedTraceWithCalleesBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedObservedTraceWithCalleesBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_mirTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_mirTree

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_mirStatefulTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_mirStatefulTree

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_mirStatefulTreeWithCallees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_mirStatefulTreeWithCallees

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_silenceMirObs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_silenceMirObs

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_interp_silenceMirObs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_interp_silenceMirObs

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_mirObsErasedStatefulTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_mirObsErasedStatefulTree

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.ofITree_mirObsErasedStatefulTreeWithCallees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofITree_mirObsErasedStatefulTreeWithCallees

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirStatefulApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirStatefulApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirObsErasedStatefulApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirObsErasedStatefulApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesFullBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBounded_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedBounded_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullBounded_fast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullBounded_fast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded_fast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBounded_fast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedApprox_sound

/-! ## 2. Nested `interpState` over `interp` over `iter` (`CofixA` Walkers vs `.observe`) -/

/-- Effect with an observation tag request (`tagStep`) and an accumulator request (`incBy`). -/
inductive CounterReq : Type where
  | tagStep (step : Nat)
  | incBy (delta : Nat)
  deriving DecidableEq, Repr

@[reducible]
def CounterE : Effect.{0} where
  I := CounterReq
  O
    | .tagStep _ => PUnit
    | .incBy _ => Nat

instance : FaultEffect CounterE where
  isFault _ := False

/-- State effect whose `addGet delta` adds `delta` to state and returns the updated state. -/
inductive StateReq : Type where
  | addGet (delta : Nat)
  deriving DecidableEq, Repr

@[reducible]
def StateE : Effect.{0} where
  I := StateReq
  O | .addGet _ => Nat

instance : FaultEffect StateE where
  isFault _ := False

@[reducible]
def triggerApprox {E : Effect.{u}} (i : E.I) : (m : Nat) → CofixA E (E.O i) m
  | 0 => .zero
  | m' + 1 => .vis i (fun o => CofixA.retApprox o m')

@[simp]
theorem ofITree_trigger_all {E : Effect.{u}} (n : Nat) (i : E.I) :
    ofITree n (ITree.trigger i) = triggerApprox i n := by
  cases n with
  | zero => rfl
  | succ m => exact ofITree_trigger m i

/--
Coinductive `ITree.iter` loop body running `limit` iterations:
on iteration `i < limit`, emits `tagStep i`, then `incBy (i + 1)`, and continues
with `(i + 1, lastObs)`. At `i ≥ limit`, returns `.inr lastObs`.
-/
def counterIterBody (limit : Nat) (st : Nat × Nat) : ITree CounterE ((Nat × Nat) ⊕ Nat) :=
  if Nat.ble limit st.1 then
    ITree.ret (Sum.inr st.2)
  else
    ITree.trigger (E := CounterE) (.tagStep st.1) >>= fun _ =>
      ITree.trigger (E := CounterE) (.incBy (st.1 + 1)) >>= fun nextAcc =>
        ITree.ret (Sum.inl (st.1 + 1, nextAcc))

/-- Direct `CofixA` approximant of `counterIterBody limit`. -/
@[reducible]
def counterIterBodyApprox (limit : Nat) (st : Nat × Nat) (m : Nat) :
    CofixA CounterE ((Nat × Nat) ⊕ Nat) m :=
  if Nat.ble limit st.1 then
    CofixA.retApprox (Sum.inr st.2) m
  else
    bindApprox (triggerApprox (E := CounterE) (.tagStep st.1) m) fun _ m₁ =>
      bindApprox (triggerApprox (E := CounterE) (.incBy (st.1 + 1)) m₁) fun nextAcc m₂ =>
        CofixA.retApprox (Sum.inl (st.1 + 1, nextAcc)) m₂

theorem ofITree_counterIterBody (limit : Nat) (st : Nat × Nat) (m : Nat) :
    ofITree m (counterIterBody limit st) = counterIterBodyApprox limit st m := by
  unfold counterIterBody counterIterBodyApprox
  cases Nat.ble limit st.1 with
  | true =>
    simp only [↓reduceIte]
    exact ofITree_ret_all m (Sum.inr st.2)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ofITree_bind, ofITree_trigger_all]
    refine bindApprox_congr _ fun _ m₁ => ?_
    rw [ofITree_bind, ofITree_trigger_all]
    exact bindApprox_congr _ fun nextAcc m₂ =>
      ofITree_ret_all m₂ (Sum.inl (st.1 + 1, nextAcc))

/-- Stateless handler from `CounterE` to `StateE`: erases `tagStep` into `.ret ()`
and translates `incBy delta` into `ITree.trigger (.addGet delta)`. -/
def counterToStateHandler : (i : CounterE.I) → ITree StateE (CounterE.O i)
  | .tagStep _ => .ret PUnit.unit
  | .incBy delta => ITree.trigger (E := StateE) (.addGet delta)

/-- Direct `CofixA` approximant of `counterToStateHandler`. -/
@[reducible]
def counterToStateHandlerApprox :
    (i : CounterE.I) → (m : Nat) → CofixA StateE (CounterE.O i) m
  | .tagStep _, m => CofixA.retApprox PUnit.unit m
  | .incBy _, 0 => .zero
  | .incBy delta, m' + 1 => .vis (.addGet delta) (fun ans => CofixA.retApprox ans m')

theorem ofITree_counterToStateHandler (i : CounterE.I) (m : Nat) :
    ofITree m (counterToStateHandler i) = counterToStateHandlerApprox i m := by
  cases i with
  | tagStep step =>
    cases m <;> rfl
  | incBy delta =>
    cases m with
    | zero => rfl
    | succ m' =>
      dsimp [counterToStateHandler, counterToStateHandlerApprox]
      exact ofITree_trigger (E := StateE) m' (.addGet delta)

/-- Stateful handler for `StateE` into `EmptyE` with `Nat` state. -/
def stateHandler : (i : StateE.I) → Nat → ITree EmptyE (StateE.O i × Nat)
  | .addGet delta, s => .ret (s + delta, s + delta)

/-- Direct `CofixA` approximant of `stateHandler`. -/
@[reducible]
def stateHandlerApprox :
    (i : StateE.I) → Nat → (m : Nat) → CofixA EmptyE (StateE.O i × Nat) m
  | .addGet delta, s, m => CofixA.retApprox (s + delta, s + delta) m

theorem ofITree_stateHandler (i : StateE.I) (s : Nat) (m : Nat) :
    ofITree m (stateHandler i s) = stateHandlerApprox i s m := by
  cases i with
  | addGet _ =>
    cases m <;> rfl

/-- Full coinductive nested pipeline: `interpState` over `interp` over `iter`. -/
def nestedPipelineITree (limit initState : Nat) : ITree EmptyE (Nat × Nat) :=
  ITree.interpState stateHandler
    (ITree.interp counterToStateHandler
      (ITree.iter (counterIterBody limit) (0, 0)))
    initState

/-- Suffix-free `CofixA` nested pipeline: `interpStateApprox` over `interpApprox` over `iterApprox`. -/
@[reducible]
def nestedPipelineApprox (limit initState fuel : Nat) : CofixA EmptyE (Nat × Nat) fuel :=
  interpStateApprox stateHandlerApprox fuel
    (interpApprox counterToStateHandlerApprox fuel
      (iterApprox (counterIterBodyApprox limit) fuel (0, 0)))
    initState

/-- Exact equational bridge between `ofITree fuel (nestedPipelineITree limit initState)`
and `nestedPipelineApprox limit initState fuel`. -/
theorem ofITree_nestedPipeline (limit initState fuel : Nat) :
    ofITree fuel (nestedPipelineITree limit initState) =
      nestedPipelineApprox limit initState fuel := by
  unfold nestedPipelineITree nestedPipelineApprox
  rw [ofITree_interpState]
  have h_state :
      interpStateApprox (fun i st m => ofITree m (stateHandler i st)) fuel
        (ofITree fuel (ITree.interp counterToStateHandler (ITree.iter (counterIterBody limit) (0, 0))))
        initState =
      interpStateApprox stateHandlerApprox fuel
        (ofITree fuel (ITree.interp counterToStateHandler (ITree.iter (counterIterBody limit) (0, 0))))
        initState :=
    (interpStateApprox_congr ofITree_stateHandler fuel).1 _ initState
  rw [h_state, ofITree_interp]
  congr 1
  have h_interp :
      interpApprox (fun i m => ofITree m (counterToStateHandler i)) fuel
        (ofITree fuel (ITree.iter (counterIterBody limit) (0, 0))) =
      interpApprox counterToStateHandlerApprox fuel
        (ofITree fuel (ITree.iter (counterIterBody limit) (0, 0))) :=
    (interpApprox_congr ofITree_counterToStateHandler fuel).1 _
  rw [h_interp, ofITree_iter]
  congr 1
  exact iterApprox_congr (ofITree_counterIterBody limit) fuel (0, 0)

/-- Bridge theorem lifting `evalTauApprox (nestedPipelineApprox limit initState fuel) = some r`
directly to `ReachesRet (nestedPipelineITree limit initState) [] r` and `TauStar`. -/
theorem nestedPipelineApprox_sound
    {limit initState fuel : Nat} {r : Nat × Nat}
    (h : evalTauApprox (nestedPipelineApprox limit initState fuel) = some r) :
    ReachesRet (nestedPipelineITree limit initState) [] r ∧
    ∃ u, TauStar (nestedPipelineITree limit initState) u ∧ u.observe = .ret r := by
  rw [← ofITree_nestedPipeline] at h
  exact ⟨evalTauApprox_sound_reachesRet h, evalTauApprox_sound_tauStar h⟩

/--
Reference `.observe`-based fuel evaluator on `ITree EmptyE R` for side-by-side
heartbeat comparison against `evalTauApprox ∘ nestedPipelineApprox`.
Notice that each step invokes `t.observe`, which unfolds `CoInd.unfold` across all
3 nested layers (`interpState`, `interp`, `iter`) and re-wraps continuation trees
with `ITreeF.map`.
-/
def evalTauObserve {R : Type} : Nat → ITree EmptyE R → Option R
  | 0, _ => none
  | fuel + 1, t =>
    match t.observe with
    | .ret r => some r
    | .tau t' => evalTauObserve fuel t'
    | .vis i _ => nomatch i

/-!
### Kernel `by rfl` Confirmation & Scaling Across Loop Depths $k \in \{4, 8, 16, 32\}$

Each iteration of `counterIterBody` performs two `CounterE` requests (`tagStep`
and `incBy`) plus one `iter` back-edge `.tau`, consuming exactly `5` output `.tau`
steps per iteration under `interpState ∘ interp ∘ iter` plus `1` terminal `.ret`
(`5 * k + 1` steps total).

Measured kernel reduction scaling (`evalTauApprox (nestedPipelineApprox k 100 (5 * k + 2))`):
- `k = 4` (`fuel = 22`): succeeds well within `maxHeartbeats 15000` (`(110, 110)`).
- `k = 8` (`fuel = 42`): succeeds well within `maxHeartbeats 15000` (`(136, 136)`).
- `k = 16` (`fuel = 82`): succeeds well within `maxHeartbeats 15000` (`(236, 236)`).
- `k = 32` (`fuel = 162`): succeeds well within `maxHeartbeats 20000` (`(628, 628)`).
By contrast, `evalTauObserve` on `nestedPipelineITree` cannot even reduce a single
step by `rfl` in the kernel without rewriting via `ITree.observe_cofix` axioms
because `CoInd.unfold` is a non-computable quotient lift (`Quot.liftOn`)!
-/

set_option maxHeartbeats 15000 in
theorem nestedPipeline_k4_rfl :
    evalTauApprox (nestedPipelineApprox 4 100 22) = some (110, 110) :=
  rfl

set_option maxHeartbeats 15000 in
theorem nestedPipeline_k8_rfl :
    evalTauApprox (nestedPipelineApprox 8 100 42) = some (136, 136) :=
  rfl

set_option maxHeartbeats 15000 in
theorem nestedPipeline_k16_rfl :
    evalTauApprox (nestedPipelineApprox 16 100 82) = some (236, 236) :=
  rfl

set_option maxHeartbeats 20000 in
theorem nestedPipeline_k32_rfl :
    evalTauApprox (nestedPipelineApprox 32 100 162) = some (628, 628) :=
  rfl

/-- Exact boundary fuel check: `4 * k + 1` is the minimum depth for `k` iterations
(`17` succeeds for `k = 4`, while `16` returns `none`). -/
theorem nestedPipeline_k4_exact_fuel_boundary :
    evalTauApprox (nestedPipelineApprox 4 100 17) = some (110, 110) ∧
    evalTauApprox (nestedPipelineApprox 4 100 16) = none :=
  ⟨rfl, rfl⟩

/-- End-to-end `ReachesRet` and `TauStar` adequacy theorems at $k = 4, 8, 16, 32$. -/
theorem nestedPipeline_k4_reachesRet :
    ReachesRet (nestedPipelineITree 4 100) [] (110, 110) ∧
    ∃ u, TauStar (nestedPipelineITree 4 100) u ∧ u.observe = .ret (110, 110) :=
  nestedPipelineApprox_sound nestedPipeline_k4_rfl

theorem nestedPipeline_k8_reachesRet :
    ReachesRet (nestedPipelineITree 8 100) [] (136, 136) ∧
    ∃ u, TauStar (nestedPipelineITree 8 100) u ∧ u.observe = .ret (136, 136) :=
  nestedPipelineApprox_sound nestedPipeline_k8_rfl

theorem nestedPipeline_k16_reachesRet :
    ReachesRet (nestedPipelineITree 16 100) [] (236, 236) ∧
    ∃ u, TauStar (nestedPipelineITree 16 100) u ∧ u.observe = .ret (236, 236) :=
  nestedPipelineApprox_sound nestedPipeline_k16_rfl

theorem nestedPipeline_k32_reachesRet :
    ReachesRet (nestedPipelineITree 32 100) [] (628, 628) ∧
    ∃ u, TauStar (nestedPipelineITree 32 100) u ∧ u.observe = .ret (628, 628) :=
  nestedPipelineApprox_sound nestedPipeline_k32_rfl

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.nestedPipeline_k32_reachesRet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nestedPipeline_k32_reachesRet

/-! ## 3. Multi-Iteration MIR Loop `CapturedMir` Fixture with Branches & External `MirCallE` Calls -/

def approxU32Ty0 : Ty := { kind := .uint .u32, layoutIdx := 0 }
def approxBoolTy1 : Ty := { kind := .bool, layoutIdx := 1 }
def approxMutRefU32Ty2 : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 }

def approxU32LayoutEntry : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def approxBoolLayoutEntry : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def approxMutRefU32LayoutEntry : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) { start := 1, end_ := 18446744073709551615 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [0]
}

def approxFnDefZstLayoutEntry : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .arbitrary [] []
  variants := .single 0
  isUninhabited := false
}

def approxTestLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [approxU32LayoutEntry, approxBoolLayoutEntry, approxMutRefU32LayoutEntry, approxFnDefZstLayoutEntry]
}

def approxTestFnAbi : FnAbi := {
  args := [{ layout := approxU32LayoutEntry, mode := .direct }]
  ret := { layout := approxU32LayoutEntry, mode := .direct }
  conv := .rust
  canUnwind := true
}

def approxMkDecl (mutability : Mutability) (ty : Ty) : LocalDecl :=
  { mutability, ty, debugName := none }

def approxMkStmt (kind : StatementKind) : Statement :=
  { kind, span := "ITreeApproxRunnerTests.lean" }

def approxMkTerm (kind : TerminatorKind) : Terminator :=
  { kind, span := "ITreeApproxRunnerTests.lean" }

def approxU32ConstOperand (n : Nat) : Operand :=
  .constant { ty := approxU32Ty0, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

/-- External oracle callee signature `fn ffi_step_oracle(iter: u32) -> u32`. -/
def ffiStepOracleSig : CapturedMir := {
  defPath := "approx_test::ffi_step_oracle"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [approxMkDecl .mut approxU32Ty0, approxMkDecl .not approxU32Ty0]
  basicBlocks := []
  fnAbi := approxTestFnAbi
  layouts := approxTestLayouts
  allocations := []
}

/-- External impure callee signature `fn ffi_impure_mut(p: &mut u32) -> u32`
used by negative non-vacuity canaries to verify `.impureExtCallPtrArg` rejection. -/
def ffiImpureMutSig : CapturedMir := {
  defPath := "approx_test::ffi_impure_mut"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [approxMkDecl .mut approxU32Ty0, approxMkDecl .not approxMutRefU32Ty2]
  basicBlocks := []
  fnAbi := approxTestFnAbi
  layouts := approxTestLayouts
  allocations := []
}

/--
Multi-iteration MIR loop `fn loop_accum_oracle(n: u32) -> u32`:
```rust
let mut i: u32 = 0;
let mut acc: u32 = 0;
while i < n {
    let step_val = ffi_step_oracle(i);
    acc = acc + step_val;
    i = i + 1;
}
return acc;
```
Locals:
- `_0 : u32` (return value)
- `_1 : u32` (`n`, parameter)
- `_2 : u32` (`i`, loop counter)
- `_3 : u32` (`acc`, accumulator)
- `_4 : bool` (`cond = i < n`)
- `_5 : u32` (`step_val = ffi_step_oracle(i)`)
Basic blocks:
- `bb0`: `_2 = 0; _3 = 0; goto bb1`
- `bb1`: `_4 = Lt(copy _2, copy _1); switchInt(move _4) [0 -> bb4, otherwise -> bb2]`
  (emits `.event 0` when exiting at `i == n` (`_4 == 0`), `.event 1` when continuing at `i < n`)
- `bb2`: `call ffi_step_oracle(copy _2) -> (_5, bb3)`
- `bb3`: `_3 = Add(copy _3, copy _5); _2 = Add(copy _2, const 1u32); goto bb1`
- `bb4`: `_0 = copy _3; return`
-/
def mirLoopWithOracleCall : CapturedMir := {
  defPath := "approx_test::loop_accum_oracle"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls :=
    [ approxMkDecl .mut approxU32Ty0
    , approxMkDecl .not approxU32Ty0
    , approxMkDecl .mut approxU32Ty0
    , approxMkDecl .mut approxU32Ty0
    , approxMkDecl .mut approxBoolTy1
    , approxMkDecl .mut approxU32Ty0 ]
  basicBlocks :=
    [ { statements :=
          [ approxMkStmt (.storageLive 2)
          , approxMkStmt (.storageLive 3)
          , approxMkStmt (.storageLive 4)
          , approxMkStmt (.storageLive 5)
          , approxMkStmt (.assign ⟨2, []⟩ (.use (approxU32ConstOperand 0)))
          , approxMkStmt (.assign ⟨3, []⟩ (.use (approxU32ConstOperand 0))) ]
        terminator := approxMkTerm (.goto 1)
        isCleanup := false }
    , { statements :=
          [ approxMkStmt (.assign ⟨4, []⟩
              (.binaryOp .lt (.copy ⟨2, []⟩) (.copy ⟨1, []⟩))) ]
        terminator :=
          approxMkTerm (.switchInt (.move ⟨4, []⟩) { branches := [(0, 4)], otherwise := 2 })
        isCleanup := false }
    , { statements := []
        terminator :=
          approxMkTerm (.call
            (.constant
              { ty := { kind := .fnDef "approx_test::ffi_step_oracle" [], layoutIdx := 3 }
                val := .zeroSized })
            [.copy ⟨2, []⟩]
            ⟨5, []⟩
            (.some 3)
            .continue_)
        isCleanup := false }
    , { statements :=
          [ approxMkStmt (.assign ⟨3, []⟩
              (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)))
          , approxMkStmt (.assign ⟨2, []⟩
              (.binaryOp .add (.copy ⟨2, []⟩) (approxU32ConstOperand 1))) ]
        terminator := approxMkTerm (.goto 1)
        isCleanup := false }
    , { statements :=
          [ approxMkStmt (.assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))) ]
        terminator := approxMkTerm .return_
        isCleanup := false } ]
  fnAbi := approxTestFnAbi
  layouts := approxTestLayouts
  allocations := []
}

/-- Encode a small `Nat` (`< 65536`) as 4-byte little-endian `u32` bytes. -/
@[reducible]
def encodeU32LeBytes (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n % 256)
  , UInt8.ofNat ((n / 256) % 256)
  , 0
  , 0 ]

/-- Oracle value returned by `ffi_step_oracle(i)` on iteration `i`: `2 * i + 3`. -/
@[reducible]
def oracleStepVal (i : Nat) : Nat :=
  2 * i + 3

/-- Expected terminal accumulator after `k` iterations: $\sum_{i=0}^{k-1} (2i + 3) = k^2 + 2k$. -/
@[reducible]
def expectedLoopAccum (k : Nat) : Nat :=
  k * k + 2 * k

/-- Build the full (`checkBranches = true`) `RawObservedEvent` list for `k` loop iterations
starting at `i = startIdx`: each iteration emits `.branch 1` (`switchInt` otherwise arm)
followed by `.extCall "approx_test::ffi_step_oracle" [encodeU32LeBytes i] (encodeU32LeBytes (2*i + 3))`,
and loop exit emits `.branch 0`. -/
@[reducible]
def mkLoopFullRawEventsAux : Nat → Nat → List RawObservedEvent
  | 0, _ => [.branch 0]
  | rem + 1, i =>
    .branch 1 ::
    .extCall "approx_test::ffi_step_oracle"
      [encodeU32LeBytes i]
      (encodeU32LeBytes (oracleStepVal i)) ::
    mkLoopFullRawEventsAux rem (i + 1)

/-- Build the branch-erased (`checkBranches = false`) `RawObservedEvent` list for `k`
loop iterations starting at `i = startIdx`. -/
@[reducible]
def mkLoopObsErasedRawEventsAux : Nat → Nat → List RawObservedEvent
  | 0, _ => []
  | rem + 1, i =>
    .extCall "approx_test::ffi_step_oracle"
      [encodeU32LeBytes i]
      (encodeU32LeBytes (oracleStepVal i)) ::
    mkLoopObsErasedRawEventsAux rem (i + 1)

@[reducible]
def mkLoopFullRawTrace (k : Nat) : RawByteTrace := {
  rawArgs := [encodeU32LeBytes k]
  events := mkLoopFullRawEventsAux k 0
  outcome := .normal (encodeU32LeBytes (expectedLoopAccum k))
}

@[reducible]
def mkLoopObsErasedRawTrace (k : Nat) : RawByteTrace := {
  rawArgs := [encodeU32LeBytes k]
  events := mkLoopObsErasedRawEventsAux k 0
  outcome := .normal (encodeU32LeBytes (expectedLoopAccum k))
}

/-!
### Kernel `by rfl` Confirmation & Soundness Across Loop Depths $k \in \{4, 8, 16, 32\}$

Each iteration of `mirLoopWithOracleCall` executes:
- `bb1`: 1 statement + 1 `switchInt` branch (`.vis (.emit (.event 1))` + `.tau` continuation) = 3 steps
- `bb2`: 1 `call` terminator (`.vis (.call ...)` + `.tau` continuation) = 2 steps
- `bb3`: 2 statements + 1 `goto` = 3 steps
Total per iteration = `8` steps, plus `bb0` (`3` steps), final `bb1` exit (`3` steps), and
`bb4` return (`2` steps) = `8 * k + 8` steps (`8 * k + 9` for `CofixA` `mirObsErasedStatefulApprox`
where each silenced `MirObsE` adds 1 `.tau` step, so `9 * k + 10` fuel suffices).
-/

@[reducible]
def emptyShadowProvenanceTable : ShadowProvenanceTable := []

set_option maxHeartbeats 25000 in
theorem mirLoop_k4_full_and_obsErased_rfl :
    checkRawByteTraceFullBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceObsErasedBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true ∧
    checkRawByteTraceFullApprox 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceObsErasedApprox 39 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true ∧
    (diagnoseRawByteTraceFullBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4)).isOk = true ∧
    (diagnoseRawByteTraceObsErasedBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4)).isOk = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 25000 in
theorem mirLoop_k8_full_and_obsErased_rfl :
    checkRawByteTraceFullBounded 59 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 8) = true ∧
    checkRawByteTraceObsErasedBounded 59 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 8) = true ∧
    checkRawByteTraceFullApprox 59 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 8) = true ∧
    checkRawByteTraceObsErasedApprox 67 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 8) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 50000 in
theorem mirLoop_k16_full_and_obsErased_rfl :
    checkRawByteTraceFullBounded 107 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 16) = true ∧
    checkRawByteTraceObsErasedBounded 107 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 16) = true ∧
    checkRawByteTraceFullApprox 107 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 16) = true ∧
    checkRawByteTraceObsErasedApprox 123 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 16) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 120000 in
theorem mirLoop_k32_full_and_obsErased_rfl :
    checkRawByteTraceFullBounded 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = true ∧
    checkRawByteTraceObsErasedBounded 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = true ∧
    checkRawByteTraceFullApprox 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = true ∧
    checkRawByteTraceObsErasedApprox 235 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- End-to-end `ReachesRet` soundness at $k = 32$ for both `checkRawByteTraceFullBounded`
and `checkRawByteTraceObsErasedBounded` (and `checkRawByteTraceObsErasedApprox`). -/
theorem mirLoop_k32_full_reachesRet :
    ∃ obsTrace tr out,
      decodeRawByteTrace mirLoopWithOracleCall [ffiStepOracleSig]
        emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree mirLoopWithOracleCall obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceFullBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 32)
    mirLoop_k32_full_and_obsErased_rfl.1

theorem mirLoop_k32_obsErased_reachesRet :
    ∃ obsTrace tr out,
      decodeRawByteTrace mirLoopWithOracleCall [ffiStepOracleSig]
        emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree mirLoopWithOracleCall obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceObsErasedBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32)
    mirLoop_k32_full_and_obsErased_rfl.2.1

theorem mirLoop_k32_obsErasedApprox_reachesRet :
    ∃ obsTrace tr out,
      decodeRawByteTrace mirLoopWithOracleCall [ffiStepOracleSig]
        emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree mirLoopWithOracleCall obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceObsErasedApprox_sound 235 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32)
    mirLoop_k32_full_and_obsErased_rfl.2.2.2

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.mirLoop_k32_obsErasedApprox_reachesRet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirLoop_k32_obsErasedApprox_reachesRet

/-! ## 4. Negative Non-Vacuity Canaries (`= false` & Exact `TraceReplayDiag` `by rfl`) -/

/-- Canary 1: Wrong terminal outcome (`25` instead of `expectedLoopAccum 4 = 24`) is
rejected (`= false`) and diagnosed as `.outcomeMismatch`. -/
theorem canary_wrong_outcome_rejected :
    let badTrace : RawByteTrace :=
      { mkLoopFullRawTrace 4 with outcome := .normal (encodeU32LeBytes 25) }
    checkRawByteTraceFullBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    checkRawByteTraceFullApprox 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceFullBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace =
      .outcomeMismatch
        (.normal (Value.scalar ⟨24, 4⟩, emptyMemory))
        (.normal (Value.scalar ⟨25, 4⟩)) :=
  ⟨rfl, rfl, rfl⟩

/-- Canary 2: Wrong branch tag in full trace mode (`.branch 0` instead of `.branch 1` on
iteration 0) is rejected (`= false`) and diagnosed as `.branchTagMismatch 1 0 1`. -/
theorem canary_wrong_branch_tag_rejected :
    let badTrace : RawByteTrace :=
      { mkLoopFullRawTrace 4 with
        events := .branch 0 :: (mkLoopFullRawEventsAux 4 0).drop 1 }
    checkRawByteTraceFullBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    checkRawByteTraceFullApprox 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceFullBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = .branchTagMismatch 1 0 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Canary 3: Wrong external call argument (`i = 99` instead of `0` on the first call)
is rejected (`= false`) and diagnosed as `.callArgMismatch`. -/
theorem canary_wrong_extCall_arg_rejected :
    let badTrace : RawByteTrace :=
      { mkLoopObsErasedRawTrace 4 with
        events :=
          .extCall "approx_test::ffi_step_oracle"
            [encodeU32LeBytes 99]
            (encodeU32LeBytes (oracleStepVal 0)) ::
          (mkLoopObsErasedRawEventsAux 4 0).drop 1 }
    checkRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    checkRawByteTraceObsErasedApprox 46 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace =
      .callArgMismatch "approx_test::ffi_step_oracle" 2 :=
  ⟨rfl, rfl, rfl⟩

/-- Canary 4: Wrong external call target `defPath` is rejected (`= false`) and diagnosed
as `.unexpectedExtCall`. -/
theorem canary_wrong_extCall_target_rejected :
    let otherSig : CapturedMir := { ffiStepOracleSig with defPath := "approx_test::other_callee" }
    let badTrace : RawByteTrace :=
      { mkLoopObsErasedRawTrace 4 with
        events :=
          .extCall "approx_test::other_callee"
            [encodeU32LeBytes 0]
            (encodeU32LeBytes (oracleStepVal 0)) ::
          (mkLoopObsErasedRawEventsAux 4 0).drop 1 }
    checkRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig, otherSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig, otherSig]
      emptyShadowProvenanceTable badTrace =
      .unexpectedExtCall "approx_test::ffi_step_oracle" 2 :=
  ⟨rfl, rfl⟩

/-- Canary 5: Unexpected trailing event after loop completion is rejected (`= false`)
and diagnosed as `.unconsumedEventsRemaining 1`. -/
theorem canary_unexpected_trailing_events_rejected :
    let badTrace : RawByteTrace :=
      { mkLoopObsErasedRawTrace 4 with
        events := mkLoopObsErasedRawEventsAux 4 0 ++ [.branch 0] }
    checkRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    checkRawByteTraceObsErasedApprox 46 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable badTrace = .unconsumedEventsRemaining 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Canary 6: External call with an impure `&mut u32` pointer parameter is rejected
(`= false`) at raw decode and diagnosed as `.impureExtCallPtrArg` (and runtime
`MirCallReq` with `Value.ptr` is rejected by both `checkFullMirTraceFast` and `checkMirTraceApprox`). -/
theorem canary_impure_ptr_extCall_rejected :
    let badRawTrace : RawByteTrace :=
      { rawArgs := [encodeU32LeBytes 1]
        events := [.extCall "approx_test::ffi_impure_mut" [[1, 0, 0, 0, 0, 0, 0, 0]] [0, 0, 0, 0]]
        outcome := .normal (encodeU32LeBytes 0) }
    let impureReq : MirCallReq :=
      { defPath := "approx_test::ffi_impure_mut"
        args := [Value.ptr { allocId := 1, offsetBytes := 0 } 8]
        memory := emptyMemory }
    let impureApprox : CofixA MirEffect MirOutcome 2 :=
      .vis (.inr (.inr (.call impureReq)))
        (fun _ => .ret (.normal (Value.scalar ⟨0, 4⟩, emptyMemory)))
    checkRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiImpureMutSig]
      emptyShadowProvenanceTable badRawTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiImpureMutSig]
      emptyShadowProvenanceTable badRawTrace =
      .impureExtCallPtrArg "approx_test::ffi_impure_mut" 0 0 ∧
    checkMirTraceApprox impureApprox
      [.extCall "approx_test::ffi_impure_mut"
        [Value.ptr { allocId := 1, offsetBytes := 0 } 8]
        (Value.scalar ⟨0, 4⟩)]
      (.normal (Value.scalar ⟨0, 4⟩)) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Canary 7: Insufficient fuel (`fuel = 34` when `k = 4` requires `35` steps) is
soundly rejected (`= false`) and diagnosed as `.outOfFuel`, while `fuel = 35` succeeds (`= true`). -/
theorem canary_insufficient_fuel_rejected :
    checkRawByteTraceFullBounded 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = false ∧
    checkRawByteTraceFullBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceObsErasedBounded 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = false ∧
    checkRawByteTraceObsErasedBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true ∧
    (diagnoseRawByteTraceFullBounded 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4)).tagName = "out_of_fuel" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Mir.ITreeApproxRunnerTests
