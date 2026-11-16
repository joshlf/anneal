-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
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
# Suffix-Free `CofixA` Approximant Walkers & `TraceCheck` Suite

Kernel regression, non-vacuity canary, and heartbeat-scaling benchmark suite for
`Anneal.ITree` Section 7 (`CofixA` walkers) and `Anneal.Rustc.V2026_06_01.TraceCheck`:
1. `#guard_msgs (whitespace := lax) in #print axioms` guards on the principal
   bridge, adequacy, and soundness theorems (zero `sorryAx`, zero `Classical.choice`,
   zero `Lean.ofReduceBool`).
2. `#audit_closure` guards walking the definitional closure of every walker and
   trace checker: no `ITree.observe` / `CoInd.unfold` anywhere, and no `Eq.rec`
   / `Eq.ndrec` / `Eq.mpr` / `cast` / `Nat.noConfusion` index transports in the
   `CofixA` walkers (with `ofITree` as a positive control that does reach them).
3. Measured heartbeat benchmarks for nested `interpStateApprox ∘ interpApprox ∘
   iterApprox` at loop depths `k ∈ {4, 8, 16, 32}` (`by rfl` and kernel-only
   `decide +kernel`), side by side with the `ITree.observe`-based evaluator on the
   corresponding coinductive `ITree` (`by rfl` at `k ∈ {1, 2, 3}`, kernel at
   `k ∈ {1, 2, 4, 8}`) and a `(kernel) deterministic timeout` canary for
   `.observe` at `k = 8` under the budget that the walker meets at `k = 32`.
4. A multi-iteration MIR loop (`SwitchInt` branches + external `MirCallE` oracle
   calls) checked at `k ∈ {4, 8, 16, 32}` in the exact theorem shape
   `cargo-anneal` emits (`checkRawByteTrace*Bounded_sound ... rfl`), kernel-only
   (`decide +kernel`), through the `checkRawByteTrace*Approx` `CofixA` route, and
   through `diagnoseRawByteTrace*Bounded`, all at the exact minimal fuel; the
   consistency theorem is also derived from the diagnostic `"ok"` tag with no
   second evaluation, and kernel-only soundness succeeds at `k = 64`, where the
   generated `rfl` application exceeds the default `maxRecDepth`.
5. Negative non-vacuity canaries: wrong outcome, wrong branch tag, wrong call
   argument, wrong call target, trailing events, impure pointer calls,
   insufficient fuel (exact boundaries for every checker), and the
   call-site-operand purity policy that a state-free `CofixA` walker can only
   enforce over the policy-guarded approximant `mirExecGuardedApprox`.

All heartbeat figures are `maxHeartbeats` units (1000 internal heartbeats) for the
whole declaration (elaboration plus kernel check), measured with
`IO.getNumHeartbeats` around synchronous elaboration (`Elab.async false`); every
guard below is set at most about 1.5x the measured figure, except that the
near-free derived certificates (`mirLoop_k32_*_from_diag_tag`, measured at `18`
heartbeats for the full one) use small absolute floors.
-/

/-! ## 1. Axiom-Hygiene Guards (`#print axioms`) -/

/-- info: 'Anneal.ITree.trunc_ofITree' depends on axioms: [Quot.sound] -/
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

/-- info: 'Anneal.ITree.ReachesRetApprox.ofITree_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReachesRetApprox.ofITree_mono

/-- info: 'Anneal.ITree.evalTauApprox_ofITree_mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_ofITree_mono

/-- info: 'Anneal.ITree.checkTraceApprox_complete' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_complete

/-- info: 'Anneal.ITree.checkTraceApprox_ofITree_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_ofITree_iff

/-- info: 'Anneal.ITree.checkTraceApprox_ofITree_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_ofITree_mono

/-- info: 'Anneal.ITree.checkTraceApprox_approxCofix_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_approxCofix_sound

/-- info: 'Anneal.ITree.checkTraceApprox_iterApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_iterApprox_sound

/-- info: 'Anneal.ITree.checkTraceApprox_interpApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_interpApprox_sound

/-- info: 'Anneal.ITree.checkTraceApprox_interpStateApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkTraceApprox_interpStateApprox_sound

/-- info: 'Anneal.ITree.evalTauApprox_approxCofix_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_approxCofix_sound

/-- info: 'Anneal.ITree.evalTauApprox_iterApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_iterApprox_sound

/-- info: 'Anneal.ITree.evalTauApprox_interpApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_interpApprox_sound

/-- info: 'Anneal.ITree.evalTauApprox_interpStateApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalTauApprox_interpStateApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_eq_fast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullObservedTraceBounded_eq_fast

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedObservedTraceBounded_eq_fast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedObservedTraceBounded_eq_fast

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_guarded_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_guarded_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirObsErasedTraceApprox_guarded_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirObsErasedTraceApprox_guarded_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_interpSilence_guarded_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_interpSilence_guarded_imp

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullBoundedFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullBoundedFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBoundedFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBoundedFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullBoundedFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesFullBoundedFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBoundedFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedBoundedFast_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullBounded_fast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesFullBounded_fast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBounded_fast_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedBounded_fast_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullApprox_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullApprox_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullApprox_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesFullApprox_eq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedApprox_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedApprox_imp

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedApprox_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedApprox_imp

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesFullApprox_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedApprox_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedApprox_sound

/-- info: 'Anneal.ITree.checkTauRetApprox_complete' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkTauRetApprox_complete

/-- info: 'Anneal.ITree.checkTauRetApprox_ofITree_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkTauRetApprox_ofITree_iff

/-- info: 'Anneal.ITree.checkTauRetApprox_ofITree_mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms checkTauRetApprox_ofITree_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullMirTraceFast_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullMirTraceFast_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedMirTraceFast_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedMirTraceFast_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkObsErasedMirTraceFast_imp_interpSilence_guarded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkObsErasedMirTraceFast_imp_interpSilence_guarded

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_trunc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_trunc

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_ofITree_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_ofITree_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox_interpSilence_guarded_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMirTraceApprox_interpSilence_guarded_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullBounded_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullBounded_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBounded_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullApprox_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceFullApprox_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedApprox_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedApprox_mono

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded_imp_approx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBounded_imp_approx

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBounded_imp_approx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedBounded_imp_approx

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.exists_checkRawByteTraceObsErasedApprox_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_checkRawByteTraceObsErasedApprox_iff

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.stringEq_eq_beq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms stringEq_eq_beq

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseCallObservedEvent_toOption' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseCallObservedEvent_toOption

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseMirExecBounded_isOk_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseMirExecBounded_isOk_full

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseMirExecBounded_isOk_obsErased' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseMirExecBounded_isOk_obsErased

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseDecodeFnArgs_toOption' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseDecodeFnArgs_toOption

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseDecodeRawEventsAux_toOption' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseDecodeRawEventsAux_toOption

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceFullBounded_isOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceFullBounded_isOk

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceObsErasedBounded_isOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceObsErasedBounded_isOk

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceWithCalleesFullBounded_isOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceWithCalleesFullBounded_isOk

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceWithCalleesObsErasedBounded_isOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceWithCalleesObsErasedBounded_isOk

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.TraceReplayDiag.isOk_of_tagName_eq_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TraceReplayDiag.isOk_of_tagName_eq_ok

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceFullBounded_tag_ok_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceFullBounded_tag_ok_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceObsErasedBounded_tag_ok_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagnoseRawByteTraceObsErasedBounded_tag_ok_sound

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkFullMirTraceFast_imp_obsErased' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkFullMirTraceFast_imp_obsErased

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.decodeRawObservedEvents_eraseRawBranchEvents' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeRawObservedEvents_eraseRawBranchEvents

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.decodeRawByteTrace_eraseRawBranchEvents' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeRawByteTrace_eraseRawBranchEvents

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded_of_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceObsErasedBounded_of_full

/-- info: 'Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBounded_of_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkRawByteTraceWithCalleesObsErasedBounded_of_full

/-! ## 2. Definitional-Closure Audit (`#audit_closure`)

Kernel `rfl` / `decide` confirmation unfolds every definition reachable from a
walker. The audit below walks that closure (including the root symbol itself,
definition bodies, compiled matchers, and structural-recursion auxiliaries;
theorem proofs and opaque constants are not entered) and reports every forbidden
constant it reaches:
- `walker` profile: `ITree.observe`, `CoInd.unfold` (the `childApprox` /
  `head_eq ▸` tower rebuilt at every `.observe`), quotient/choice/cheat
  constants (`Quot.lift`, `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`), and
  index-transport / `noConfusion` eliminators `Eq.rec`, `Eq.ndrec`, `Eq.mpr`,
  `Eq.mp`, `cast`, `HEq.rec`, `HEq.ndrec`, `Nat.noConfusion`,
  `Nat.noConfusionType`, `CofixA.noConfusion`, `ITreeF.noConfusion`;
- `checker` profile: `ITree.observe`, `CoInd.unfold`, `ITree.cofix`, `CoInd.fold`,
  `Quot.lift`, `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`
  (no coinductive `ITree` is ever built or observed by the replay checkers).
`ofITree` (which observes by design) and the generic `checkTraceApprox` (which
transports answers along a decided request equality) are positive controls that
prove the audit is not vacuous. `elimMirVis` eliminates `MirEffect.I` using
`Sum.casesOn` / `FailReq.casesOn` / `ObsReq.casesOn` / `MirObs.casesOn` /
`CallReq.casesOn` before introducing the continuation `k` and passes the strict
`walker` profile (`checkMirTraceApprox` / `checkMirObsErasedTraceApprox` reach
`Eq.ndrec` only through `Char` / `UInt32` equality inside `stringEq`).
-/

open Lean Elab Command in
/--
`#audit_closure (walker|checker) root` reports which constants of the chosen
forbidden profile occur in the transitive definitional closure of `root`.
-/
elab "#audit_closure " prof:ident root:ident : command => do
  let env ← getEnv
  let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let forbidden : Array Name :=
    if prof.getId == `walker then
      #[``Trusted.ITree.ITree.observe, ``Trusted.CoInd.CoInd.unfold,
        ``Quot.lift, ``Classical.choice, ``sorryAx, ``Lean.ofReduceBool,
        ``Eq.rec, ``Eq.ndrec, ``Eq.mpr, ``Eq.mp, ``cast, ``HEq.rec, ``HEq.ndrec,
        ``Nat.noConfusion, ``Nat.noConfusionType,
        ``Anneal.ITree.CofixA.noConfusion, ``Trusted.ITree.ITreeF.noConfusion]
    else
      #[``Trusted.ITree.ITree.observe, ``Trusted.CoInd.CoInd.unfold,
        ``Trusted.ITree.ITree.cofix, ``Trusted.CoInd.CoInd.fold,
        ``Quot.lift, ``Classical.choice, ``sorryAx, ``Lean.ofReduceBool]
  let mut visited : NameSet := NameSet.empty.insert rootName
  let mut stack : Array Name := #[rootName]
  let mut hits : NameSet :=
    if forbidden.contains rootName then NameSet.empty.insert rootName else {}
  for _ in [0:1000000] do
    match stack.back? with
    | none => break
    | some n =>
      stack := stack.pop
      match env.find? n with
      | some (.defnInfo v) =>
        for c in v.value.getUsedConstants do
          if forbidden.contains c then
            hits := hits.insert c
          if !visited.contains c then
            visited := visited.insert c
            stack := stack.push c
      | _ => pure ()
  let hitList := (hits.toList.map toString).toArray.qsort (· < ·)
  if hitList.isEmpty then
    logInfo m!"{rootName}: clean"
  else
    logInfo m!"{rootName}: reaches {hitList.toList}"

/-- info: Anneal.ITree.approxCofix: clean -/
#guard_msgs in #audit_closure walker approxCofix
/-- info: Anneal.ITree.CofixA.map: clean -/
#guard_msgs in #audit_closure walker CofixA.map
/-- info: Anneal.ITree.CofixA.trunc: clean -/
#guard_msgs in #audit_closure walker CofixA.trunc
/-- info: Anneal.ITree.approxStep: clean -/
#guard_msgs in #audit_closure walker approxStep
/-- info: Anneal.ITree.bindApprox: clean -/
#guard_msgs in #audit_closure walker bindApprox
/-- info: Anneal.ITree.iterApprox: clean -/
#guard_msgs in #audit_closure walker iterApprox
/-- info: Anneal.ITree.interpApprox: clean -/
#guard_msgs in #audit_closure walker interpApprox
/-- info: Anneal.ITree.interpHandlerApprox: clean -/
#guard_msgs in #audit_closure walker interpHandlerApprox
/-- info: Anneal.ITree.interpStateApprox: clean -/
#guard_msgs in #audit_closure walker interpStateApprox
/-- info: Anneal.ITree.interpStateHandlerApprox: clean -/
#guard_msgs in #audit_closure walker interpStateHandlerApprox
/-- info: Anneal.ITree.evalTauApprox: clean -/
#guard_msgs in #audit_closure walker evalTauApprox
/-- info: Anneal.ITree.checkTauRetApprox: clean -/
#guard_msgs in #audit_closure walker checkTauRetApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.silenceMirObsApprox: clean -/
#guard_msgs in #audit_closure walker silenceMirObsApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.elimMirVis: clean -/
#guard_msgs in #audit_closure walker elimMirVis

/-- info: Anneal.ITree.ofITree: reaches [Eq.rec, Trusted.CoInd.CoInd.unfold, Trusted.ITree.ITree.observe] -/
#guard_msgs (whitespace := lax) in #audit_closure walker ofITree
/-- info: Anneal.ITree.checkTraceApprox: reaches [Eq.ndrec, Eq.rec] -/
#guard_msgs (whitespace := lax) in #audit_closure walker checkTraceApprox

/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.guardMirCallNode: clean -/
#guard_msgs in #audit_closure checker guardMirCallNode
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.stepMirStateGuarded: clean -/
#guard_msgs in #audit_closure checker stepMirStateGuarded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.mirExecGuardedApprox: clean -/
#guard_msgs in #audit_closure checker mirExecGuardedApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkMirTraceApprox: clean -/
#guard_msgs in #audit_closure checker checkMirTraceApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkMirObsErasedTraceApprox: clean -/
#guard_msgs in #audit_closure checker checkMirObsErasedTraceApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullBounded: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceFullBounded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedBounded: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceObsErasedBounded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullBounded: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceWithCalleesFullBounded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedBounded: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceWithCalleesObsErasedBounded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceFullApprox: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceFullApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceObsErasedApprox: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceObsErasedApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesFullApprox: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceWithCalleesFullApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.checkRawByteTraceWithCalleesObsErasedApprox: clean -/
#guard_msgs in #audit_closure checker checkRawByteTraceWithCalleesObsErasedApprox
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceFullBounded: clean -/
#guard_msgs in #audit_closure checker diagnoseRawByteTraceFullBounded
/-- info: Anneal.Rustc.V2026_06_01.TraceCheck.diagnoseRawByteTraceObsErasedBounded: clean -/
#guard_msgs in #audit_closure checker diagnoseRawByteTraceObsErasedBounded
/-- info: Trusted.VerificationResult.mirStatefulTree: reaches [Trusted.ITree.ITree.cofix] -/
#guard_msgs in #audit_closure checker mirStatefulTree

/-! ## 3. Nested `interpState` over `interp` over `iter` (`CofixA` Walkers vs `.observe`) -/

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

/-- Reference `.observe`-based fuel evaluator on `ITree EmptyE R` for side-by-side
heartbeat comparison against `evalTauApprox ∘ nestedPipelineApprox`. Every step
calls `t.observe` (`CoInd.unfold`), which on `nestedPipelineITree` re-evaluates
the `childApprox` / `head_eq ▸` towers of all three nested coalgebras
(`interpState`, `interp`, `iter`) and re-wraps continuations with `ITreeF.map`. -/
def evalTauObserve {R : Type} : Nat → ITree EmptyE R → Option R
  | 0, _ => none
  | fuel + 1, t =>
    match t.observe with
    | .ret r => some r
    | .tau t' => evalTauObserve fuel t'
    | .vis i _ => nomatch i

/-!
### Measured Kernel Scaling: `CofixA` Walkers versus `ITree.observe`

Each loop iteration of `counterIterBody` contributes exactly `4` output `.tau`s
under `interpState ∘ interp ∘ iter`: `tagStep` (handler `.ret` → `.tau`), `incBy`
(`interp` emits `.vis (.addGet _)`, which `interpState` answers with a `.tau`,
followed by `interp`'s handler-return `.tau`), and the `iter` back-edge `.tau`;
the run ends with one `.ret`. The minimal fuel is therefore `4 * k + 1`
(`nestedPipeline_exact_fuel_boundary`).

Measured heartbeats (whole declaration):

| `k` | fuel | walker `by rfl` | walker `decide +kernel` | `.observe` `by rfl` | `.observe` `decide +kernel` |
|----:|-----:|----------------:|------------------------:|--------------------:|----------------------------:|
|   1 |    5 |               – |                      54 |                 408 |                         122 |
|   2 |    9 |               – |                      67 |                1731 |                         404 |
|   3 |   13 |               – |                      80 |                5612 |                        1083 |
|   4 |   17 |             244 |                      98 |                   – |                        2364 |
|   8 |   33 |             432 |                     149 |                   – |                       17252 |
|  16 |   65 |             809 |                     252 |                   – |                           – |
|  32 |  129 |            1563 |                     458 |                   – |                           – |

For reference, the same walkers written with index-unifying `match`es on
`CofixA` (whose compiled matchers transport indices with `Eq.ndrec`) measured
`164 / 270 / 481 / 904` (kernel) at `k = 4 / 8 / 16 / 32`.

The walker is linear in `k` (about `13` kernel and `47` `by rfl` heartbeats per
iteration), while the `.observe` evaluator grows roughly cubically (`7.3x` from
`k = 4` to `k = 8` in the kernel, `3.2x` from `k = 2` to `k = 3` under `by rfl`,
the `O(k^3)` nested-`childApprox` blowup): `.observe` `by rfl` at `k = 3` already
costs 3.6x what the walker needs at `k = 32`, kernel-only `.observe` at `k = 4`
costs 5x the walker's `k = 32`, and at `k = 8` it times out under the walker's
`k = 32` kernel budget (`nestedPipelineObserve_k8_exceeds_walker_k32_budget`).
`by rfl` costs a constant factor over the kernel because `Meta.isDefEq`
evaluates the term before the kernel re-checks it.
-/

set_option maxHeartbeats 320 in
theorem nestedPipeline_k4_rfl :
    evalTauApprox (nestedPipelineApprox 4 100 17) = some (110, 110) := by
  rfl

set_option maxHeartbeats 570 in
theorem nestedPipeline_k8_rfl :
    evalTauApprox (nestedPipelineApprox 8 100 33) = some (136, 136) := by
  rfl

set_option maxHeartbeats 1060 in
theorem nestedPipeline_k16_rfl :
    evalTauApprox (nestedPipelineApprox 16 100 65) = some (236, 236) := by
  rfl

set_option maxHeartbeats 2050 in
theorem nestedPipeline_k32_rfl :
    evalTauApprox (nestedPipelineApprox 32 100 129) = some (628, 628) := by
  rfl

set_option maxHeartbeats 150 in
theorem nestedPipeline_k4_kernel :
    evalTauApprox (nestedPipelineApprox 4 100 17) = some (110, 110) := by
  decide +kernel

set_option maxHeartbeats 200 in
theorem nestedPipeline_k8_kernel :
    evalTauApprox (nestedPipelineApprox 8 100 33) = some (136, 136) := by
  decide +kernel

set_option maxHeartbeats 350 in
theorem nestedPipeline_k16_kernel :
    evalTauApprox (nestedPipelineApprox 16 100 65) = some (236, 236) := by
  decide +kernel

set_option maxHeartbeats 600 in
theorem nestedPipeline_k32_kernel :
    evalTauApprox (nestedPipelineApprox 32 100 129) = some (628, 628) := by
  decide +kernel

set_option maxHeartbeats 170 in
theorem nestedPipelineObserve_k1_kernel :
    evalTauObserve 5 (nestedPipelineITree 1 100) = some (101, 101) := by
  decide +kernel

set_option maxHeartbeats 550 in
theorem nestedPipelineObserve_k2_kernel :
    evalTauObserve 9 (nestedPipelineITree 2 100) = some (103, 103) := by
  decide +kernel

set_option maxHeartbeats 3100 in
theorem nestedPipelineObserve_k4_kernel :
    evalTauObserve 17 (nestedPipelineITree 4 100) = some (110, 110) := by
  decide +kernel

set_option maxHeartbeats 22500 in
theorem nestedPipelineObserve_k8_kernel :
    evalTauObserve 33 (nestedPipelineITree 8 100) = some (136, 136) := by
  decide +kernel

set_option maxHeartbeats 540 in
theorem nestedPipelineObserve_k1_rfl :
    evalTauObserve 5 (nestedPipelineITree 1 100) = some (101, 101) := by
  rfl

set_option maxHeartbeats 2260 in
theorem nestedPipelineObserve_k2_rfl :
    evalTauObserve 9 (nestedPipelineITree 2 100) = some (103, 103) := by
  rfl

set_option maxHeartbeats 7300 in
theorem nestedPipelineObserve_k3_rfl :
    evalTauObserve 13 (nestedPipelineITree 3 100) = some (106, 106) := by
  rfl

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
set_option maxHeartbeats 600 in
theorem nestedPipelineObserve_k8_exceeds_walker_k32_budget :
    evalTauObserve 33 (nestedPipelineITree 8 100) = some (136, 136) := by
  decide +kernel

/-- Exact minimal fuel `4 * k + 1` at `k = 4` and `k = 32`. -/
theorem nestedPipeline_exact_fuel_boundary :
    evalTauApprox (nestedPipelineApprox 4 100 17) = some (110, 110) ∧
    evalTauApprox (nestedPipelineApprox 4 100 16) = none ∧
    evalTauApprox (nestedPipelineApprox 32 100 129) = some (628, 628) ∧
    evalTauApprox (nestedPipelineApprox 32 100 128) = none := by
  decide +kernel

/-- End-to-end `ReachesRet` and `TauStar` adequacy theorems at $k = 4, 8, 16, 32$. -/
theorem nestedPipeline_k4_reachesRet :
    ReachesRet (nestedPipelineITree 4 100) [] (110, 110) ∧
    ∃ u, TauStar (nestedPipelineITree 4 100) u ∧ u.observe = .ret (110, 110) :=
  nestedPipelineApprox_sound nestedPipeline_k4_kernel

theorem nestedPipeline_k8_reachesRet :
    ReachesRet (nestedPipelineITree 8 100) [] (136, 136) ∧
    ∃ u, TauStar (nestedPipelineITree 8 100) u ∧ u.observe = .ret (136, 136) :=
  nestedPipelineApprox_sound nestedPipeline_k8_kernel

theorem nestedPipeline_k16_reachesRet :
    ReachesRet (nestedPipelineITree 16 100) [] (236, 236) ∧
    ∃ u, TauStar (nestedPipelineITree 16 100) u ∧ u.observe = .ret (236, 236) :=
  nestedPipelineApprox_sound nestedPipeline_k16_kernel

theorem nestedPipeline_k32_reachesRet :
    ReachesRet (nestedPipelineITree 32 100) [] (628, 628) ∧
    ∃ u, TauStar (nestedPipelineITree 32 100) u ∧ u.observe = .ret (628, 628) :=
  nestedPipelineApprox_sound nestedPipeline_k32_kernel

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.nestedPipeline_k32_reachesRet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nestedPipeline_k32_reachesRet

/-! ### Walker-Level `checkTraceApprox` Soundness on the `iter` Layer -/

instance (i : CounterE.I) : Decidable (FaultEffect.isFault (E := CounterE) i) :=
  instDecidableFalse

/-- The visible `CounterE` trace of two `counterIterBody` iterations (oracle answers
`1` and `7`), checked by `checkTraceApprox` on the `iterApprox` walker at its exact
depth `3 * 2 + 1 = 7`, lifted to `ReachesRet` on the coinductive `ITree.iter` by
`checkTraceApprox_iterApprox_sound`. -/
theorem counterIter_k2_trace_reachesRet :
    ∃ r, (r == 7) = true ∧
      ReachesRet (ITree.iter (counterIterBody 2) (0, 0))
        [⟨.tagStep 0, PUnit.unit⟩, ⟨.incBy 1, (1 : Nat)⟩,
         ⟨.tagStep 1, PUnit.unit⟩, ⟨.incBy 2, (7 : Nat)⟩] r :=
  checkTraceApprox_iterApprox_sound (counterIterBody 2) (counterIterBodyApprox 2)
    (fun i m => (ofITree_counterIterBody 2 i m).symm) (0, 0) (n := 7)
    (p := fun r => r == 7) (by decide +kernel)

/-- The same trace is rejected one depth short of `7`, and with a wrong final answer. -/
theorem counterIter_k2_trace_boundary :
    checkTraceApprox (iterApprox (counterIterBodyApprox 2) 6 (0, 0))
        [⟨.tagStep 0, PUnit.unit⟩, ⟨.incBy 1, (1 : Nat)⟩,
         ⟨.tagStep 1, PUnit.unit⟩, ⟨.incBy 2, (7 : Nat)⟩] (fun r => r == 7) = false ∧
    checkTraceApprox (iterApprox (counterIterBodyApprox 2) 7 (0, 0))
        [⟨.tagStep 0, PUnit.unit⟩, ⟨.incBy 1, (1 : Nat)⟩,
         ⟨.tagStep 1, PUnit.unit⟩, ⟨.incBy 2, (7 : Nat)⟩] (fun r => r == 8) = false := by
  decide +kernel

/-! ## 4. Multi-Iteration MIR Loop `CapturedMir` Fixture with Branches & External `MirCallE` Calls -/

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
### Exact Minimal Fuel & Measured Heartbeats Across Loop Depths $k \in \{4, 8, 16, 32\}$

`bb0` executes `6` statements and a `goto` (`7` steps). Each loop iteration then
executes `bb1` (`1` statement + `switchInt`, `2` steps), `bb2` (the `call`
terminator: `1` step, a `.vis (.call ...)` node whose continuation resumes at
`bb3`), and `bb3` (`2` statements + `goto`, `3` steps), i.e. `6` steps, and the
exit executes `bb1` (`2` steps) and `bb4` (`1` statement + `return`, `2` steps).
The minimal fuel of `checkRawByteTrace{Full,ObsErased}Bounded`,
`checkRawByteTraceFullApprox`, and `diagnoseRawByteTrace*Bounded` is therefore
`6 * k + 11`. The `interpApprox silenceMirObsApprox` route
(`checkRawByteTraceObsErasedApprox`) needs one extra output depth per external
call (the handler-return `.tau` of `silenceMirObs`'s `ITree.trigger`): `7 * k + 11`.
Every minimum is pinned by `= false` boundary canaries one unit below.

Measured heartbeats (whole declaration). The `generated` columns are the exact
shape `cargo-anneal` emits per trace, a `checkRawByteTrace*Bounded_sound ... rfl`
application proving the `ReachesRet` consistency statement
(`mirLoop_k*_{full,obsErased}_generated`); the `kernel` columns discharge the same
hypothesis `by decide +kernel` (`*_generated_kernel`); the `*Approx` columns run the
policy-exact `CofixA` route kernel-only:

| `k` | fuel (`6k+11`) | full generated | full kernel | obsErased generated | obsErased kernel | `FullApprox` kernel | `ObsErasedApprox` kernel |
|----:|---------------:|---------------:|------------:|--------------------:|-----------------:|--------------------:|-------------------------:|
|   4 |             35 |           4695 |        1630 |                4670 |             1623 |                1646 |                     1670 |
|   8 |             59 |           5875 |        2026 |                5830 |             2014 |                2054 |                     2096 |
|  16 |            107 |           8248 |        2828 |                8161 |             2806 |                2878 |                     2956 |
|  32 |            203 |          13044 |        4465 |               12881 |             4423 |                4561 |                     4709 |

Discharging the generated hypothesis kernel-only is 2.9x cheaper, adds no axioms
(no `Lean.ofReduceBool`), and does not need the elaborator's `maxRecDepth`: at
`k = 64` the generated `rfl` application exceeds the default `maxRecDepth`
(`mirLoop_k64_full_generated_exceeds_maxRecDepth`; generated chunks raise it to
`100000`) while `decide +kernel` succeeds in `7871`
(`mirLoop_k64_full_generated_kernel`). A standalone `theorem ... := rfl` on the
checker is the most expensive form (`22654` at `k = 32`). The checker definitions
themselves are not the bottleneck (`decodeRawByteTrace` is about 13% and
`stepMirState` most of the rest).

Every generated chunk also emits a `diagnoseRawByteTrace*Bounded ... tagName = "ok"`
theorem (`13066` at `k = 32`, `mirLoop_k32_diag_tag_rfl`), which repeats the whole
evaluation. `diagnoseRawByteTraceFullBounded_isOk` proves that the diagnosis accepts
exactly when `checkRawByteTraceFullBounded` does, so the consistency theorem follows
from the already-confirmed tag in `18` heartbeats
(`mirLoop_k32_full_from_diag_tag`) instead of a second `13044`-heartbeat evaluation.
Likewise `checkRawByteTraceObsErasedBounded_of_full` derives the branch-erased
certificate for the same recording with its `.branch` events removed
(`eraseRawBranchEvents`, `mirLoop_k32_obsErased_from_diag_tag`) instead of a third
`12881`-heartbeat evaluation, so one evaluation per recording suffices for all
three theorems a generated chunk emits.
-/

@[reducible]
def emptyShadowProvenanceTable : ShadowProvenanceTable := []

/-- The `ReachesRet` consistency statement `cargo-anneal` emits for the full
(`checkBranches = true`) loop trace at depth `k`. -/
abbrev LoopFullConsistent (k : Nat) : Prop :=
  ∃ obsTrace tr out,
    decodeRawByteTrace mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace k) = some obsTrace ∧
    MatchesObservedEvents obsTrace.events tr ∧
    MatchesObservedOutcome obsTrace.outcome out ∧
    ReachesRet
      (mirStatefulTree mirLoopWithOracleCall obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees })
      tr out

/-- The `ReachesRet` consistency statement `cargo-anneal` emits for the
branch-erased (`checkBranches = false`) loop trace at depth `k`. -/
abbrev LoopObsErasedConsistent (k : Nat) : Prop :=
  ∃ obsTrace tr out,
    decodeRawByteTrace mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace k) = some obsTrace ∧
    MatchesObservedEvents obsTrace.events tr ∧
    MatchesObservedOutcome obsTrace.outcome out ∧
    ReachesRet
      (mirObsErasedStatefulTree mirLoopWithOracleCall obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees })
      tr out

set_option maxHeartbeats 6100 in
theorem mirLoop_k4_full_generated : LoopFullConsistent 4 :=
  checkRawByteTraceFullBounded_sound 35 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 4) rfl

set_option maxHeartbeats 2120 in
theorem mirLoop_k4_full_generated_kernel : LoopFullConsistent 4 :=
  checkRawByteTraceFullBounded_sound 35 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 4) (by decide +kernel)

set_option maxHeartbeats 6080 in
theorem mirLoop_k4_obsErased_generated : LoopObsErasedConsistent 4 :=
  checkRawByteTraceObsErasedBounded_sound 35 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) rfl

set_option maxHeartbeats 2110 in
theorem mirLoop_k4_obsErased_generated_kernel : LoopObsErasedConsistent 4 :=
  checkRawByteTraceObsErasedBounded_sound 35 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) (by decide +kernel)

set_option maxHeartbeats 7640 in
theorem mirLoop_k8_full_generated : LoopFullConsistent 8 :=
  checkRawByteTraceFullBounded_sound 59 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 8) rfl

set_option maxHeartbeats 2640 in
theorem mirLoop_k8_full_generated_kernel : LoopFullConsistent 8 :=
  checkRawByteTraceFullBounded_sound 59 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 8) (by decide +kernel)

set_option maxHeartbeats 7580 in
theorem mirLoop_k8_obsErased_generated : LoopObsErasedConsistent 8 :=
  checkRawByteTraceObsErasedBounded_sound 59 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 8) rfl

set_option maxHeartbeats 2620 in
theorem mirLoop_k8_obsErased_generated_kernel : LoopObsErasedConsistent 8 :=
  checkRawByteTraceObsErasedBounded_sound 59 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 8) (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 10720 in
theorem mirLoop_k16_full_generated : LoopFullConsistent 16 :=
  checkRawByteTraceFullBounded_sound 107 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 16) rfl

set_option maxHeartbeats 3680 in
theorem mirLoop_k16_full_generated_kernel : LoopFullConsistent 16 :=
  checkRawByteTraceFullBounded_sound 107 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 16) (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 10610 in
theorem mirLoop_k16_obsErased_generated : LoopObsErasedConsistent 16 :=
  checkRawByteTraceObsErasedBounded_sound 107 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 16) rfl

set_option maxHeartbeats 3650 in
theorem mirLoop_k16_obsErased_generated_kernel : LoopObsErasedConsistent 16 :=
  checkRawByteTraceObsErasedBounded_sound 107 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 16) (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16960 in
theorem mirLoop_k32_full_generated : LoopFullConsistent 32 :=
  checkRawByteTraceFullBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 32) rfl

set_option maxHeartbeats 5810 in
theorem mirLoop_k32_full_generated_kernel : LoopFullConsistent 32 :=
  checkRawByteTraceFullBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 32) (by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16750 in
theorem mirLoop_k32_obsErased_generated : LoopObsErasedConsistent 32 :=
  checkRawByteTraceObsErasedBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) rfl

set_option maxHeartbeats 5750 in
theorem mirLoop_k32_obsErased_generated_kernel : LoopObsErasedConsistent 32 :=
  checkRawByteTraceObsErasedBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) (by decide +kernel)

set_option maxHeartbeats 2200 in
theorem mirLoop_k4_fullApprox_kernel :
    checkRawByteTraceFullApprox 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true := by
  decide +kernel

set_option maxHeartbeats 2750 in
theorem mirLoop_k8_fullApprox_kernel :
    checkRawByteTraceFullApprox 59 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 8) = true := by
  decide +kernel

set_option maxHeartbeats 3900 in
theorem mirLoop_k16_fullApprox_kernel :
    checkRawByteTraceFullApprox 107 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 16) = true := by
  decide +kernel

set_option maxHeartbeats 6200 in
theorem mirLoop_k32_fullApprox_kernel :
    checkRawByteTraceFullApprox 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = true := by
  decide +kernel

set_option maxHeartbeats 2250 in
theorem mirLoop_k4_obsErasedApprox_kernel :
    checkRawByteTraceObsErasedApprox 39 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true := by
  decide +kernel

set_option maxHeartbeats 2800 in
theorem mirLoop_k8_obsErasedApprox_kernel :
    checkRawByteTraceObsErasedApprox 67 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 8) = true := by
  decide +kernel

set_option maxHeartbeats 4000 in
theorem mirLoop_k16_obsErasedApprox_kernel :
    checkRawByteTraceObsErasedApprox 123 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 16) = true := by
  decide +kernel

set_option maxHeartbeats 6400 in
theorem mirLoop_k32_obsErasedApprox_kernel :
    checkRawByteTraceObsErasedApprox 235 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = true := by
  decide +kernel

set_option maxHeartbeats 7700 in
theorem mirLoop_k4_diag_rfl :
    (diagnoseRawByteTraceFullBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4)).isOk = true ∧
    (diagnoseRawByteTraceObsErasedBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4)).isOk = true :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 17000 in
theorem mirLoop_k32_diag_tag_rfl :
    (diagnoseRawByteTraceFullBounded 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32)).tagName = "ok" := by
  rfl

set_option maxHeartbeats 4100 in
/-- `WithCallees` and tail-recursive `*Fast` entry points at `k = 4` (no inlined
callees, so the same minimal fuel applies). -/
theorem mirLoop_k4_withCallees_and_fast_kernel :
    checkRawByteTraceWithCalleesFullBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesObsErasedBounded 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesFullApprox 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesObsErasedApprox 39 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true ∧
    checkRawByteTraceFullBoundedFast 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = true ∧
    checkRawByteTraceObsErasedBoundedFast 35 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true := by
  decide +kernel

/-- Concrete body for `fn ffi_step_oracle(iter: u32) -> u32 { 2 * iter + 3 }`:
when placed in `RawByteTrace.inlinedCallees`, each loop call steps transparently
through `Memory.callStack` via `.tau` transitions (`4` extra steps per iteration:
`storageLive 2`, `_2 = Mul(copy _1, 2)`, `_0 = Add(copy _2, 3)`, `return`), so
the minimal fuel for `k` iterations becomes `10 * k + 11` (`51` at `k = 4`) and
no external `MirCallE` events are emitted. -/
def ffiStepOracleInlinedBody : CapturedMir := {
  defPath := "approx_test::ffi_step_oracle"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls :=
    [ approxMkDecl .mut approxU32Ty0
    , approxMkDecl .not approxU32Ty0
    , approxMkDecl .mut approxU32Ty0 ]
  basicBlocks :=
    [ { statements :=
          [ approxMkStmt (.storageLive 2)
          , approxMkStmt (.assign ⟨2, []⟩
              (.binaryOp .mul (.copy ⟨1, []⟩) (approxU32ConstOperand 2)))
          , approxMkStmt (.assign ⟨0, []⟩
              (.binaryOp .add (.copy ⟨2, []⟩) (approxU32ConstOperand 3))) ]
        terminator := approxMkTerm .return_
        isCleanup := false } ]
  fnAbi := approxTestFnAbi
  layouts := approxTestLayouts
  allocations := []
}

@[reducible]
def mkLoopInlinedFullRawEvents : Nat → List RawObservedEvent
  | 0 => [.branch 0]
  | rem + 1 => .branch 1 :: mkLoopInlinedFullRawEvents rem

@[reducible]
def mkLoopInlinedFullRawTrace (k : Nat) : RawByteTrace := {
  rawArgs := [encodeU32LeBytes k]
  inlinedCallees := [ffiStepOracleInlinedBody]
  events := mkLoopInlinedFullRawEvents k
  outcome := .normal (encodeU32LeBytes (expectedLoopAccum k))
}

@[reducible]
def mkLoopInlinedObsErasedRawTrace (k : Nat) : RawByteTrace := {
  rawArgs := [encodeU32LeBytes k]
  inlinedCallees := [ffiStepOracleInlinedBody]
  events := []
  outcome := .normal (encodeU32LeBytes (expectedLoopAccum k))
}

set_option maxHeartbeats 2200 in
/-- Multi-frame inlined-callee verification at `k = 4`: with `ffiStepOracleInlinedBody`
in `inlinedCallees`, all `WithCallees` checkers (`*Bounded`, `*BoundedFast`, and
`*Approx`) accept at exact minimal fuel `10 * 4 + 11 = 51` and reject at `50`. -/
theorem mirLoop_k4_inlinedCallees_kernel :
    checkRawByteTraceWithCalleesFullBounded 51 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedFullRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesFullBounded 50 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedFullRawTrace 4) = false ∧
    checkRawByteTraceWithCalleesObsErasedBounded 51 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesObsErasedBounded 50 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4) = false ∧
    checkRawByteTraceWithCalleesFullApprox 51 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedFullRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesFullApprox 50 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedFullRawTrace 4) = false ∧
    checkRawByteTraceWithCalleesObsErasedApprox 51 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4) = true ∧
    checkRawByteTraceWithCalleesObsErasedApprox 50 mirLoopWithOracleCall []
      emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4) = false := by
  decide +kernel

theorem mirLoop_k4_inlinedCallees_obsErasedApprox_reachesRet :
    ∃ obsTrace tr out,
      decodeRawByteTrace mirLoopWithOracleCall []
        emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4) = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          mirLoopWithOracleCall obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out :=
  checkRawByteTraceWithCalleesObsErasedApprox_sound 51 mirLoopWithOracleCall []
    emptyShadowProvenanceTable (mkLoopInlinedObsErasedRawTrace 4)
    mirLoop_k4_inlinedCallees_kernel.2.2.2.2.2.2.1

set_option maxHeartbeats 12000 in
/-- Exact minimal-fuel boundaries (`6 * k + 10` and `7 * k + 10` rejected) for every
checker at `k = 4` and `k = 32`. -/
theorem mirLoop_exact_fuel_boundaries :
    checkRawByteTraceFullBounded 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = false ∧
    checkRawByteTraceObsErasedBounded 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = false ∧
    checkRawByteTraceFullApprox 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = false ∧
    checkRawByteTraceObsErasedApprox 38 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = false ∧
    checkRawByteTraceFullBounded 202 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = false ∧
    checkRawByteTraceObsErasedBounded 202 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = false ∧
    checkRawByteTraceFullApprox 202 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = false ∧
    checkRawByteTraceObsErasedApprox 234 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) = false := by
  decide +kernel

/-- End-to-end `ReachesRet` soundness at $k = 32$ for the `CofixA` route
`checkRawByteTraceObsErasedApprox` (the `*Bounded` routes are the
`mirLoop_k*_{full,obsErased}_generated` theorems above). -/
theorem mirLoop_k32_obsErasedApprox_reachesRet : LoopObsErasedConsistent 32 :=
  checkRawByteTraceObsErasedApprox_sound 235 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) mirLoop_k32_obsErasedApprox_kernel

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.mirLoop_k32_obsErasedApprox_reachesRet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirLoop_k32_obsErasedApprox_reachesRet

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.mirLoop_k32_full_generated_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirLoop_k32_full_generated_kernel

set_option maxHeartbeats 40 in
/-- The full consistency statement at `k = 32`, derived from the `"ok"` diagnostic
tag theorem that `cargo-anneal` already emits for every trace
(`mirLoop_k32_diag_tag_rfl`) through `diagnoseRawByteTraceFullBounded_tag_ok_sound`,
with no second evaluation of the MIR execution. -/
theorem mirLoop_k32_full_from_diag_tag : LoopFullConsistent 32 :=
  diagnoseRawByteTraceFullBounded_tag_ok_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 32) mirLoop_k32_diag_tag_rfl

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.mirLoop_k32_full_from_diag_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirLoop_k32_full_from_diag_tag

/-- The recorded branch-erased loop events are exactly the full events with their
`.branch` observations removed. -/
theorem mkLoopObsErasedRawEventsAux_eq_erase :
    ∀ (k i : Nat),
      mkLoopObsErasedRawEventsAux k i = eraseRawBranchEvents (mkLoopFullRawEventsAux k i)
  | 0, _ => rfl
  | k + 1, i => by
    simp only [mkLoopObsErasedRawEventsAux, eraseRawBranchEvents]
    rw [mkLoopObsErasedRawEventsAux_eq_erase k (i + 1)]

theorem mkLoopObsErasedRawTrace_eq_erase (k : Nat) :
    mkLoopObsErasedRawTrace k =
      { mkLoopFullRawTrace k with events := eraseRawBranchEvents (mkLoopFullRawTrace k).events } := by
  simp only [mkLoopObsErasedRawTrace, mkLoopObsErasedRawEventsAux_eq_erase]

set_option maxHeartbeats 300 in
/-- The branch-erased consistency statement at `k = 32`, derived from the full
acceptance carried by the already-confirmed diagnostic tag
(`checkRawByteTraceObsErasedBounded_of_full` over `eraseRawBranchEvents`), with no
further evaluation of the MIR execution. -/
theorem mirLoop_k32_obsErased_from_diag_tag : LoopObsErasedConsistent 32 := by
  have h_full : checkRawByteTraceFullBounded 203 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 32) = true := by
    rw [← diagnoseRawByteTraceFullBounded_isOk]
    exact TraceReplayDiag.isOk_of_tagName_eq_ok mirLoop_k32_diag_tag_rfl
  have h := checkRawByteTraceObsErasedBounded_of_full 203 mirLoopWithOracleCall
    [ffiStepOracleSig] emptyShadowProvenanceTable (mkLoopFullRawTrace 32) h_full
  rw [← mkLoopObsErasedRawTrace_eq_erase] at h
  exact checkRawByteTraceObsErasedBounded_sound 203 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 32) h

/-- info: 'Anneal.Mir.ITreeApproxRunnerTests.mirLoop_k32_obsErased_from_diag_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mirLoop_k32_obsErased_from_diag_tag

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option maxHeartbeats 15000 in
theorem mirLoop_k64_full_generated_exceeds_maxRecDepth : LoopFullConsistent 64 :=
  checkRawByteTraceFullBounded_sound 395 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 64) rfl

set_option maxHeartbeats 10240 in
theorem mirLoop_k64_full_generated_kernel : LoopFullConsistent 64 :=
  checkRawByteTraceFullBounded_sound 395 mirLoopWithOracleCall [ffiStepOracleSig]
    emptyShadowProvenanceTable (mkLoopFullRawTrace 64) (by decide +kernel)

/-! ## 5. Negative Non-Vacuity Canaries (`= false` & Exact `TraceReplayDiag` `by rfl`) -/

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
    checkRawByteTraceObsErasedApprox 46 mirLoopWithOracleCall [ffiStepOracleSig, otherSig]
      emptyShadowProvenanceTable badTrace = false ∧
    diagnoseRawByteTraceObsErasedBounded 40 mirLoopWithOracleCall [ffiStepOracleSig, otherSig]
      emptyShadowProvenanceTable badTrace =
      .unexpectedExtCall "approx_test::ffi_step_oracle" 2 :=
  ⟨rfl, rfl, rfl⟩

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
(`= false`) at raw decode and diagnosed as `.impureExtCallPtrArg`; a hand-built
approximant whose `MirCallReq` passes an untracked (borrow-less) `Value.ptr` is
rejected by both state-free walkers `checkMirTraceApprox` and
`checkMirObsErasedTraceApprox`. -/
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
      (.normal (Value.scalar ⟨0, 4⟩)) = false ∧
    checkMirObsErasedTraceApprox impureApprox
      [.extCall "approx_test::ffi_impure_mut"
        [Value.ptr { allocId := 1, offsetBytes := 0 } 8]
        (Value.scalar ⟨0, 4⟩)]
      (.normal (Value.scalar ⟨0, 4⟩)) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary 7: Insufficient fuel (`fuel = 34` when `k = 4` requires `6 * 4 + 11 = 35`
steps, and `38` for the `interpApprox` route that requires `7 * 4 + 11 = 39`) is
soundly rejected (`= false`) and diagnosed as `.outOfFuel`, while the exact
minimum succeeds (`= true`). -/
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
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4)).tagName = "out_of_fuel" ∧
    checkRawByteTraceFullApprox 34 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopFullRawTrace 4) = false ∧
    checkRawByteTraceObsErasedApprox 38 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = false ∧
    checkRawByteTraceObsErasedApprox 39 mirLoopWithOracleCall [ffiStepOracleSig]
      emptyShadowProvenanceTable (mkLoopObsErasedRawTrace 4) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Canary 8: Call-Site Operand Purity Policy Under State-Free `CofixA` Walkers

`fn peek_raw(p: *const u32) -> u32 { ffi_peek(p) }` passes a raw pointer whose
runtime tag is registered `.frozen`, so the runtime argument check
`findCallReqImpurePtrArgIdx?` accepts it, while the call-site operand-type check
`findBlockCallImpurePtrArgIdx?` (part of `findActiveCallImpurePtrArgIdx?`) rejects
it. A `CofixA` node forgets the `MirExecState`, so `checkMirTraceApprox` over the
plain approximant `mirExecApprox` accepts this trace (soundly with respect to
`ReachesRet`, but violating the memory-pure external-callee policy enforced by
`checkFullMirTraceFast` and `diagnoseMirExecBounded`); over the policy-guarded
approximant `mirExecGuardedApprox` it is rejected exactly like the coalgebra-direct
checkers (`checkMirTraceApprox_guarded_eq`).
-/

def policyU32Ty0 : Ty := { kind := .uint .u32, layoutIdx := 0 }
def policyRawConstU32Ty1 : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 1 }

def policyRawPtrLayoutEntry : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 8 }
  backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 18446744073709551615 })
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def policyLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [approxU32LayoutEntry, policyRawPtrLayoutEntry, approxFnDefZstLayoutEntry]
}

/-- `fn peek_raw(p: *const u32) -> u32 { ffi_peek(p) }`. -/
def rawPeekBody : CapturedMir := {
  defPath := "policy_test::peek_raw"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [approxMkDecl .mut policyU32Ty0, approxMkDecl .not policyRawConstU32Ty1]
  basicBlocks :=
    [ { statements := []
        terminator :=
          approxMkTerm (.call
            (.constant
              { ty := { kind := .fnDef "policy_test::ffi_peek" [], layoutIdx := 2 }
                val := .zeroSized })
            [.copy ⟨1, []⟩]
            ⟨0, []⟩
            (.some 1)
            .continue_)
        isCleanup := false }
    , { statements := []
        terminator := approxMkTerm .return_
        isCleanup := false } ]
  fnAbi := {
    args := [{ layout := policyRawPtrLayoutEntry, mode := .direct }]
    ret := { layout := approxU32LayoutEntry, mode := .direct }
    conv := .rust
    canUnwind := true }
  layouts := policyLayouts
  allocations := []
}

def frozenRawPtr : Value := Value.ptr { allocId := 7, offsetBytes := 0 } 8

def frozenRawPtrMem : Memory :=
  { borrows := [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .frozen }] }

def rawPeekState : MirExecState :=
  .running (initMachineStateWithMemory rawPeekBody [frozenRawPtr] frozenRawPtrMem)

def rawPeekEvents : List ObservedEvent :=
  [.extCall "policy_test::ffi_peek" [frozenRawPtr] (Value.scalar ⟨42, 4⟩)]

theorem canary_callsite_raw_ptr_policy :
    findCallReqImpurePtrArgIdx?
        { defPath := "policy_test::ffi_peek", args := [frozenRawPtr], memory := frozenRawPtrMem } =
      none ∧
    checkMirTraceApprox (mirExecApprox rawPeekBody 4 rawPeekState)
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = true ∧
    checkMirTraceApprox (mirExecGuardedApprox rawPeekBody 4 rawPeekState)
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = false ∧
    checkMirObsErasedTraceApprox (mirExecGuardedApprox rawPeekBody 4 rawPeekState)
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = false ∧
    checkMirTraceApprox
        (interpApprox silenceMirObsApprox 4 (mirExecGuardedApprox rawPeekBody 4 rawPeekState))
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = false ∧
    checkFullMirTraceFast 4 rawPeekBody rawPeekState
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = false ∧
    checkObsErasedMirTraceFast 4 rawPeekBody rawPeekState
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩)) = false ∧
    (diagnoseMirExecBounded 4 true rawPeekBody rawPeekState
      rawPeekEvents (.normal (Value.scalar ⟨42, 4⟩))).tagName = "impure_ext_call_ptr_arg" := by
  decide +kernel

end Anneal.Mir.ITreeApproxRunnerTests
