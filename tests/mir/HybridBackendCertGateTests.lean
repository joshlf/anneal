-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Anneal.Hybrid
import Anneal.Hybrid.Canaries
import Anneal.Backend
import Anneal.Backend.Canaries
import Anneal.CanonicalDiode.Canaries
import Anneal.SpecRealizability
import Anneal.HybridCertBridgesV2026

/-!
# End-to-End Hybrid Certificate-Gate & Backend Test Suite

Exercises all four certificate-checked subsystems unified under
`Anneal.Hybrid` and `Anneal.HybridCertBridgesV2026`:

1. **`Anneal.LinearArithIndexed` (`natCutIdxGate`, `intCutIdxGate`):**
   concrete `BoolCertCut.seal _ _ rfl` discharges covering row reuse and
   Chvatal-Gomory `.divCut` parity cuts, `firstAccepted` / `natCutPortfolio` /
   `intCutPortfolio` / dual-backend selection, oversized/forged rejections,
   and total `gateVerdict` (`withFallback`) verdicts.
2. **`Anneal.FarkasMirCert` (`farkasMirGate`):**
   concrete `BoolCertCut.seal _ _ rfl` discharges across `uintAddNoOverflow`,
   `uintSubNoUnderflowCertified`, `uintMulConstNoOverflow`, `sliceBounds`,
   `alignedStride`, `arrayToSliceCast`, and `natEntailmentAdequacy` (all four
   `FarkasMirCert` constructors), plus `farkasMirPortfolio`, `gateVerdict`,
   forged/oversized/mismatched rejections, and the `natCutIdxGate` ->
   `evalScalarBinOp` bridge.
3. **`Anneal.CanonicalDiode` (`canonicalDiodeChunkGate` + `foldStreamPrefix`):**
   concrete `BoolCertCut` and streaming checks over
   `Anneal.CanonicalDiode.Canaries.diode` and a strict-parser diode proving
   canonical emission on valid streams, immediate halt with zero emission of
   malformed or tampered chunks at the head AND mid-stream, rejection of
   non-canonical/wrong-AST/replayed producer outputs, and the exact
   `filterAll` characterization for adversarial producers. The same
   `foldStreamPrefix` also runs `farkasMirGate` and `natCutIdxGate` as
   prefix-safe obligation streams (`obligationChunkGate`).
4. **`Anneal.Backend` + `Anneal.Mir.OverflowTrapRefinement`:**
   end-to-end `blockOptGate` `BoolCertCut` + `stepMirState` `u64` checked-to-
   unchecked add/sub refinement via `farkasMirGate`, `natCutIdxGate`, and
   `CtxFact`, certificate transport from ANY accepted `blockOptGate` witness
   to `stepMirState` at every `u64`-ranged environment, faithfulness of the
   outcome bridge, plus negative counterexamples (forged certs, `.symm` on
   `.refines`, `.refines` under `.freeze`, `.fuzz`/`.sorryStub` candidates
   for which no certificate is ever accepted, unsound overflow/underflow
   guard elision, `.diverged` distinctness, and `-C panic=abort` vs
   `-C panic=unwind` separation).
5. **Episode 1 Handoff Compatibility Pins:**
   exact `rfl` equalities between all four `Anneal.Hybrid` and
   `Anneal.SpecRealizability` realizability predicates, plus `#guard_msgs`
   negative elaboration checks confirming zero field defaults on
   `Anneal.Hybrid.EffectMask` and `Anneal.Hybrid.FnContract.effects`.
6. **Exhaustive Axiom & `._unsafe_rec` Audit (`run_cmd` + `#print axioms`):**
   sweeps every constant across all 9 new theory modules plus this test
   module, pins each module's exact declaration counts and axiom set, the
   exact `Quot.sound` users,
   and the exact axiom set of every capstone, and looks up the `._unsafe_rec`
   companion of every reachable `Anneal.*` constant (none in the 10 audited
   modules; the pre-existing base ones are pinned by name).
-/

namespace Anneal.Mir.HybridBackendCertGateTests

open Anneal.LinearArith
open Anneal.AiPcc
open Anneal.UnsafeObligations
open Anneal.FarkasMirCert
open Anneal.CanonicalDiode
open Anneal.CanonicalDiode.Canaries
open Anneal.Backend
open Anneal.Backend.Canaries
open Anneal.Mir.OverflowTrapRefinement
open Anneal.HybridCertBridgesV2026
open Trusted.Refinement
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `LinearArithIndexed` (`natCutIdxGate` / `intCutIdxGate`) -/

/-- Row-reuse `NatCutGoal`: `x0 ≤ 10`, `x1 ≤ 20`, `x2 ≤ 5` implies
`2 * x0 + 2 * x1 + x2 ≤ 65`, reusing the derived `x0 + x1 ≤ 30` row twice. -/
def natRowReuseGoal : NatCutGoal :=
  { hyps :=
      [ ⟨.var 0, .cst 10⟩,
        ⟨.var 1, .cst 20⟩,
        ⟨.var 2, .cst 5⟩ ]
    concl :=
      ⟨.add (.add (.mulC 2 (.var 0)) (.mulC 2 (.var 1))) (.var 2), .cst 65⟩ }

/-- Derived row 3 (`x0 + x1 ≤ 30`) is referenced twice in step 4. -/
def natRowReuseCert : List CutStep :=
  [ .hyp 0,            -- 0: x0 ≤ 10
    .hyp 1,            -- 1: x1 ≤ 20
    .hyp 2,            -- 2: x2 ≤ 5
    .comb 0 1 1 1,     -- 3: x0 + x1 ≤ 30 (reused below)
    .comb 3 1 3 1,     -- 4: 2*x0 + 2*x1 ≤ 60
    .comb 4 1 2 1,     -- 5: 2*x0 + 2*x1 + x2 ≤ 65
    .hyp 6,            -- 6: 66 ≤ 2*x0 + 2*x1 + x2 (negated concl)
    .comb 5 1 6 1 ]    -- 7: 0 ≤ -1

/-- Concrete `rfl` `BoolCertCut` discharges on `natCutIdxGate` (row reuse,
Chvatal-Gomory parity `.divCut`, and stride parity) and `intCutIdxGate`. -/
theorem test_linearArithIndexed_boolCertCut_discharges
    (x0 x1 x2 : Nat) (h0 : x0 ≤ 10) (h1 : x1 ≤ 20) (h2 : x2 ≤ 5) :
    2 * x0 + 2 * x1 + x2 ≤ 65 ∧
    parityCutReqGoal.denote ∧
    parityStrideGoal.denote ∧
    intSubNegMulGoal.denote := by
  have hReuse : natRowReuseGoal.denote :=
    natCutIdxGate_cut_sound 8 natRowReuseGoal natRowReuseCert
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hParity : parityCutReqGoal.denote :=
    Anneal.Hybrid.certGateCut_sound (natCutIdxGate 8) True.intro
      (Anneal.Framework.StepWp.BoolCertCut.seal
        (Anneal.Hybrid.gateCheckBounded (natCutIdxGate 8))
        (parityCutReqGoal, (), parityCutReqCert) rfl)
  have hStride : parityStrideGoal.denote :=
    natCutIdxGate_cut_sound 8 parityStrideGoal parityStrideCert
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hIntDen : intSubNegMulGoal.denote :=
    intCutIdxGate_cut_sound 8 intSubNegMulGoal intSubNegMulCert
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  exact ⟨hReuse [x0, x1, x2] h0 h1 h2, hParity, hStride, hIntDen⟩

/-- Signed integer row-reuse goal discharged via `intCutIdxGate` `BoolCertCut`.
-/
def intRowReuseGoal : IntCutGoal :=
  { hyps :=
      [ ⟨.var 0, .cst ⟨true, 3⟩⟩,
        ⟨.var 1, .cst ⟨false, 2⟩⟩ ]
    concl :=
      ⟨.add (.mulC ⟨false, 2⟩ (.var 0)) (.mulC ⟨false, 2⟩ (.var 1)),
       .cst ⟨true, 2⟩⟩ }

def intRowReuseCert : List CutStep :=
  [ .hyp 0,         -- 0: x0 ≤ -3
    .hyp 1,         -- 1: x1 ≤ 2
    .comb 0 1 1 1,  -- 2: x0 + x1 ≤ -1 (reused twice)
    .comb 2 1 2 1,  -- 3: 2*x0 + 2*x1 ≤ -2
    .hyp 2,         -- 4: -1 ≤ 2*x0 + 2*x1 (negated concl)
    .comb 3 1 4 1 ] -- 5: 0 ≤ -1

theorem test_intCutIdxGate_rowReuse_boolCertCut :
    intRowReuseGoal.denote :=
  intCutIdxGate_cut_sound 8 intRowReuseGoal intRowReuseCert
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- `firstAccepted`, `natCutPortfolio`, `intCutPortfolio`, dual-backend gate,
and oversized / forged certificate rejections for `LinearArithIndexed`. -/
theorem test_linearArithIndexed_portfolio_and_rejections :
    -- Oversized witness rejected in O(1)
    Anneal.Hybrid.evalGate (E := Unit) (natCutIdxGate 4) natRowReuseGoal
      (.candidate () natRowReuseCert) = .error (.witnessOversized 8 4) ∧
    Anneal.Hybrid.evalGate (E := Unit) (intCutIdxGate 3) intRowReuseGoal
      (.candidate () intRowReuseCert) = .error (.witnessOversized 6 3) ∧
    -- Forged witness rejected by checker
    Anneal.Hybrid.evalGate (E := Unit) (natCutIdxGate 8) parityCutReqGoal
      (.candidate () [.hyp 0, .hyp 1, .comb 0 1 1 1]) =
      .error .rejectedByChecker ∧
    Anneal.Hybrid.evalGate (E := Unit) (intCutIdxGate 8) intRowReuseGoal
      (.candidate () [.hyp 0]) = .error .rejectedByChecker ∧
    -- `firstAccepted` skips oversized, trapped, forged, and accepts valid
    Anneal.Hybrid.firstAccepted (E := Unit) (natCutIdxGate 8) natRowReuseGoal
      [ .candidate () (natRowReuseCert ++ [.hyp 0]),
        .trapped,
        .candidate () [.hyp 0],
        .candidate () natRowReuseCert ] = .ok () ∧
    -- `natCutPortfolio` falls back from failed indexed list to list-backed cert
    natCutPortfolio (E := Unit) 8 parityCutReqGoal
      [ .candidate () [.hyp 0], .trapped ]
      [ .candidate () parityCutReqCert ] = .ok () ∧
    -- `intCutPortfolio` succeeds on primary indexed cert
    intCutPortfolio (E := Unit) 8 intSubNegMulGoal
      [ .prodErr (), .candidate () intSubNegMulCert ] [] = .ok () ∧
    -- `natCutDualGate` accepts interleaved `.indexed` and `.list` candidates
    Anneal.Hybrid.firstAccepted (E := Unit) (natCutDualGate 8) parityCutReqGoal
      [ .candidate () (.indexed, [.hyp 0]),
        .candidate () (.list, parityCutReqCert) ] = .ok () ∧
    natRowReuseGoal.denote ∧
    parityCutReqGoal.denote ∧
    intSubNegMulGoal.denote :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   Anneal.Hybrid.firstAccepted_sound (E := Unit) (natCutIdxGate 8)
     natRowReuseGoal
     [ .candidate () (natRowReuseCert ++ [.hyp 0]),
       .trapped,
       .candidate () [.hyp 0],
       .candidate () natRowReuseCert ] () True.intro rfl,
   natCutPortfolio_sound (E := Unit) 8 parityCutReqGoal
     [ .candidate () [.hyp 0], .trapped ]
     [ .candidate () parityCutReqCert ] rfl,
   intCutPortfolio_sound (E := Unit) 8 intSubNegMulGoal
     [ .prodErr (), .candidate () intSubNegMulCert ] [] rfl⟩

/-- `natCutDualGate` / `intCutDualGate` `BoolCertCut` discharges under BOTH
witness tags, tag-for-tag agreement with the single-checker gates, and the
failure direction of `natCutPortfolio_ok_iff_exists` /
`intCutPortfolio_ok_iff_exists`. -/
theorem test_linearArithIndexed_dualGate_and_portfolio_iff :
    parityCutReqGoal.denote ∧
    intSubNegMulGoal.denote ∧
    Anneal.Hybrid.evalGate (E := Unit) (natCutDualGate 8) parityCutReqGoal
        (.candidate () (.indexed, parityCutReqCert)) =
      Anneal.Hybrid.evalGate (natCutIdxGate 8) parityCutReqGoal
        (.candidate () parityCutReqCert) ∧
    Anneal.Hybrid.evalGate (E := Unit) (intCutDualGate 8) intSubNegMulGoal
        (.candidate () (.list, intSubNegMulCert)) =
      Anneal.Hybrid.evalGate (Anneal.Hybrid.intCutGate 8) intSubNegMulGoal
        (.candidate () intSubNegMulCert) ∧
    -- Empty portfolios never succeed
    ¬ (natCutPortfolio (E := Unit) 8 parityCutReqGoal [] [] = .ok ()) ∧
    ¬ (intCutPortfolio (E := Unit) 8 intSubNegMulGoal [] [] = .ok ()) ∧
    -- Oversized / forged / trapped / failed producers on both sides: the
    -- portfolio reports the last fallback producer's rejection
    natCutPortfolio (E := Unit) 4 natRowReuseGoal
      [.candidate () natRowReuseCert, .trapped]
      [.candidate () [.hyp 0], .prodErr ()] =
      .error (.producerFailed ()) := by
  have hNat : parityCutReqGoal.denote :=
    natCutDualGate_cut_sound 8 parityCutReqGoal (.indexed, parityCutReqCert)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hInt : intSubNegMulGoal.denote :=
    intCutDualGate_cut_sound 8 intSubNegMulGoal (.list, intSubNegMulCert)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  refine ⟨hNat, hInt,
    (natCutDualGate_agrees 8 parityCutReqGoal parityCutReqCert).1,
    (intCutDualGate_agrees 8 intSubNegMulGoal intSubNegMulCert).2,
    ?_, ?_, rfl⟩
  · intro hOk
    cases (natCutPortfolio_ok_iff_exists 8 parityCutReqGoal [] []).1 hOk with
    | inl h => have ⟨_, hMem, _⟩ := h; cases hMem
    | inr h => have ⟨_, hMem, _⟩ := h; cases hMem
  · intro hOk
    cases (intCutPortfolio_ok_iff_exists 8 intSubNegMulGoal [] []).1 hOk with
    | inl h => have ⟨_, hMem, _⟩ := h; cases hMem
    | inr h => have ⟨_, hMem, _⟩ := h; cases hMem

/-! ## 2. `FarkasMirCert` (`farkasMirGate`) -/

def mirAddGoal : FarkasMirGoal :=
  .uintAddNoOverflow .u64
    [⟨.var 0, .cst 1000000⟩, ⟨.var 1, .cst 250000⟩]
    (.var 0) (.mulC 4 (.var 1))

def mirAddCert : FarkasMirCert :=
  .single [.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 4, .comb 3 1 2 1]

def mirSubCertGoal : FarkasMirGoal :=
  .uintSubNoUnderflowCertified .u64
    [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
    (.var 0) (.var 1)

def mirSubCert : FarkasMirCert :=
  .pair [.hyp 0, .hyp 4, .comb 0 1 1 1] [.hyp 1, .hyp 4, .comb 0 1 1 1]

def mirMulGoal : FarkasMirGoal :=
  .uintMulConstNoOverflow .u8 [⟨.var 0, .cst 10⟩] 8 (.var 0)

def mirMulCert : FarkasMirCert :=
  .single [.hyp 0, .hyp 2, .comb 0 8 1 1]

def mirSliceGoal : FarkasMirGoal :=
  .sliceBounds
    [⟨.var 0, .cst 4⟩, ⟨.var 1, .cst 8⟩, ⟨.cst 12, .var 2⟩]
    (.var 0) (.var 1) (.var 2)

def mirSliceCert : FarkasMirCert :=
  .single [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 2, .comb 2 1 3 1,
           .hyp 6, .comb 4 1 5 1]

def mirAlignGoal : FarkasMirGoal :=
  .alignedStride
    [⟨.mulC 8 (.var 1), .var 0⟩, ⟨.var 0, .mulC 8 (.var 1)⟩]
    8 (.var 0) (.var 1)

def mirAlignCert : FarkasMirCert :=
  .pair [.hyp 0, .hyp 4, .comb 0 1 1 1] [.hyp 1, .hyp 4, .comb 0 1 1 1]

def mirArrayCastGoal : FarkasMirGoal :=
  .arrayToSliceCast
    [⟨.mulC 8 (.var 1), .var 0⟩, ⟨.var 0, .mulC 8 (.var 1)⟩,
     ⟨.var 0, .cst 16⟩, ⟨.var 2, .cst 4⟩, ⟨.cst 48, .var 3⟩]
    8 8 (.var 0) (.var 1) (.var 2) (.var 3)

def mirArrayCastCert : FarkasMirCert :=
  .triple
    [.hyp 0, .hyp 9, .comb 0 1 1 1]
    [.hyp 1, .hyp 9, .comb 0 1 1 1]
    [.hyp 2, .hyp 3, .comb 0 1 1 8, .hyp 4, .comb 2 1 3 1,
     .hyp 9, .comb 4 1 5 1]

def mirEdgeGoal : FarkasMirGoal :=
  .natEntailmentAdequacy [⟨.var 0, .cst 5⟩] [⟨.var 0, .cst 10⟩] [0]
    (.strict [6])

def mirEdgeCert : FarkasMirCert :=
  .edge [[.hyp 0, .hyp 2, .comb 0 1 1 1]]

/-- Concrete `rfl` `BoolCertCut` discharges across `FarkasMirGoal` variants
(covering `.single`, `.pair`, `.triple`, and `.edge` certificates) plus
`farkasMirCertSize` counts. -/
theorem test_farkasMirGate_boolCertCut_variants :
    farkasMirCertSize mirAddCert = 5 ∧
    farkasMirCertSize mirSubCert = 6 ∧
    farkasMirCertSize mirArrayCastCert = 13 ∧
    farkasMirCertSize mirEdgeCert = 3 ∧
    mirAddGoal.denote ∧
    mirSubCertGoal.denote ∧
    mirMulGoal.denote ∧
    mirSliceGoal.denote ∧
    mirAlignGoal.denote ∧
    mirArrayCastGoal.denote ∧
    mirEdgeGoal.denote :=
  ⟨rfl, rfl, rfl, rfl,
   farkasMirGate_cut_sound 16 mirAddGoal mirAddCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirSubCertGoal mirSubCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirMulGoal mirMulCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirSliceGoal mirSliceCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirAlignGoal mirAlignCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirArrayCastGoal mirArrayCastCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl),
   farkasMirGate_cut_sound 16 mirEdgeGoal mirEdgeCert
     (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)⟩

/-- `farkasMirPortfolio`, oversized / forged / mismatched rejections, and the
`natCutIdxGate` -> `evalScalarBinOp` arithmetic bridge. -/
theorem test_farkasMirGate_portfolio_rejections_and_idx_bridge
    (a b : Nat) (locals : List LocalSlot) (mem : Memory)
    (ha : a ≤ 1000000) (hb : b ≤ 250000) :
    -- Oversized rejection on `.triple` (size 13 > 10)
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirGate 10) mirArrayCastGoal
      (.candidate () mirArrayCastCert) = .error (.witnessOversized 13 10) ∧
    -- Empty-edge bomb: `farkasMirCertSize = 0`, bounded by
    -- `farkasMirCertWeight`
    farkasMirCertSize (.edge [[], [], [], [], []]) = 0 ∧
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirBoundedEdgeGate 2) mirEdgeGoal
      (.candidate () (.edge [[], [], [], [], []])) =
      .error (.witnessOversized 5 2) ∧
    mirEdgeGoal.denote ∧
    -- Payload-shape mismatch rejection (`.pair` for `.uintAddNoOverflow`)
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirGate 16) mirAddGoal
      (.candidate () (.pair [.hyp 0] [.hyp 1])) = .error .rejectedByChecker ∧
    -- Forged `.single` cert rejection
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirGate 16) mirAddGoal
      (.candidate () (.single [.hyp 0])) = .error .rejectedByChecker ∧
    -- `firstAccepted` portfolio skips bad/oversized/trapped certs
    farkasMirPortfolio (E := Unit) 16 mirSubCertGoal
      [ .candidate () (.single [.hyp 0]),
        .trapped,
        .candidate () mirSubCert ] = .ok () ∧
    -- An all-oversized portfolio reports the producer's rejection
    farkasMirPortfolio (E := Unit) 2 mirAddGoal
      [.candidate () mirAddCert] = .error (.witnessOversized 5 2) ∧
    -- Indexed-to-MIR bridge: `natCutIdxGate` discharges `evalScalarBinOp`
    evalScalarBinOp .addUnchecked
      ⟨a, uintBytes .u64⟩ ⟨4 * b, uintBytes .u64⟩ locals mem false =
      .ok (.scalar ⟨a + 4 * b, uintBytes .u64⟩) locals mem ∧
    evalScalarBinOp .addWithOverflow
      ⟨a, uintBytes .u64⟩ ⟨4 * b, uintBytes .u64⟩ locals mem false =
      .ok (.aggregate 0
        [.scalar ⟨a + 4 * b, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem := by
  have hIdxAdd :=
    natCutIdxGate_discharges_uint_add_no_overflow 8 .u64
      [⟨.var 0, .cst 1000000⟩, ⟨.var 1, .cst 250000⟩]
      (.var 0) (.mulC 4 (.var 1))
      [.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 4, .comb 3 1 2 1]
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [a, b] locals mem ha hb
  have hEdgeBound :=
    farkasMirBoundedEdgeGate_cut_sound 8 mirEdgeGoal mirEdgeCert
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hBomb := neg_farkasMir_empty_edge_bomb_bounded mirEdgeGoal
  exact ⟨rfl, hBomb.1, hBomb.2.2, hEdgeBound, rfl, rfl, rfl, rfl,
    hIdxAdd.2.2.1, hIdxAdd.2.2.2⟩

/-- Indexed-to-MIR subtraction bridge: `natCutIdxGate` directly discharges
`evalScalarBinOp .subUnchecked` and `.subWithOverflow`. -/
theorem test_natCutIdxGate_sub_evalScalarBinOp
    (c d : Nat) (locals : List LocalSlot) (mem : Memory)
    (hc : c ≤ 1000) (hcd : d + 4 ≤ c) :
    evalScalarBinOp .subUnchecked
      ⟨c, uintBytes .u64⟩ ⟨d, uintBytes .u64⟩ locals mem false =
      .ok (.scalar ⟨c - d, uintBytes .u64⟩) locals mem ∧
    evalScalarBinOp .subWithOverflow
      ⟨c, uintBytes .u64⟩ ⟨d, uintBytes .u64⟩ locals mem false =
      .ok (.aggregate 0
        [.scalar ⟨c - d, uintBytes .u64⟩, .scalar ⟨0, 1⟩]) locals mem := by
  have hIdxSub :=
    natCutIdxGate_discharges_uint_sub_no_underflow_certified 8 .u64
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
      (.var 0) (.var 1)
      [.hyp 0, .hyp 4, .comb 0 1 1 1]
      [.hyp 1, .hyp 4, .comb 0 1 1 1]
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [c, d] locals mem hcd hc
  exact ⟨hIdxSub.2.2.2.1, hIdxSub.2.2.2.2⟩

/-- General `.edge` weight bounds, beyond the one 5-entry instance: for 64
empty step lists the exact `CutStep` count is `0` and the weight is `64`; the
bounded-edge gate rejects them before the checker runs; and whatever the
bounded-edge gate accepts, `farkasMirGate` accepts. -/
theorem test_farkasMir_edge_weight_bounds (goal : FarkasMirGoal) :
    farkasMirCertSize (.edge (List.replicate 64 [])) = 0 ∧
    farkasMirCertWeight (.edge (List.replicate 64 [])) = 64 ∧
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirBoundedEdgeGate 63) goal
      (.candidate () (.edge (List.replicate 64 []))) =
      .error (.witnessOversized
        (farkasMirCertWeight (.edge (List.replicate 64 []))) 63) ∧
    Anneal.Hybrid.gateCheckBounded (farkasMirGate 4)
      (mirEdgeGoal, (), mirEdgeCert) = true ∧
    -- One entry of three steps weighs 4: accepted at cap 4, refused at cap 3
    -- by the bounded-edge gate, while `farkasMirGate 3` still accepts it
    Anneal.Hybrid.gateCheckBounded (farkasMirBoundedEdgeGate 3)
      (mirEdgeGoal, (), mirEdgeCert) = false ∧
    Anneal.Hybrid.gateCheckBounded (farkasMirGate 3)
      (mirEdgeGoal, (), mirEdgeCert) = true ∧
    -- Strictness lifted to `evalGate` and total `gateVerdict`
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirGate 4) mirEdgeGoal
      (.candidate () mirEdgeCert) = .ok () ∧
    gateVerdict (E := Unit) (farkasMirGate 4) mirEdgeGoal
      [ .candidate false (.edge []), .candidate true mirEdgeCert ] = true ∧
    -- Total `gateVerdict` over dual-backend (`natCutDualGate` /
    -- `intCutDualGate`)
    parityCutReqGoal.denote ∧
    intSubNegMulGoal.denote :=
  ⟨(farkasMirCert_empty_edge_size_and_weight 64).1,
   (farkasMirCert_empty_edge_size_and_weight 64).2,
   farkasMirBoundedEdgeGate_rejects_long_edge 63 goal
     (List.replicate 64 []) (Nat.le_of_ble_eq_true rfl),
   farkasMirBoundedEdgeGate_accept_imp_farkasMirGate 4 mirEdgeGoal
     mirEdgeCert rfl,
   rfl, rfl,
   farkasMirBoundedEdgeGate_eval_ok_imp_farkasMirGate 4 mirEdgeGoal
     (.candidate () mirEdgeCert) rfl,
   farkasMirBoundedEdgeGate_verdict_imp_farkasMirGate 4 mirEdgeGoal
     [ .candidate false (.edge []), .candidate true mirEdgeCert ] rfl,
   natCutDualGate_verdict_sound (E := Unit) 8 parityCutReqGoal
     [ .candidate false (.indexed, []),
       .candidate true (.list, parityCutReqCert) ] rfl,
   intCutDualGate_verdict_sound (E := Unit) 8 intSubNegMulGoal
     [ .candidate false (.list, []),
       .candidate true (.indexed, intSubNegMulCert) ] rfl⟩

/-- Total sabotage-resistant `Bool` verdicts (`gateVerdict`, i.e.
`withFallback` over `firstAccepted` on `verdictGate`): a `true` claim needs a
gate-accepted witness, forged/oversized `true` claims fall back to `false`,
and an uncertified `false` claim is rejected so it cannot sabotage a valid
later producer in the portfolio. -/
theorem test_gateVerdict_withFallback_total_and_sound :
    -- Valid `true` claim after a forged claim and a trap
    gateVerdict (E := Unit) (natCutIdxGate 8) natRowReuseGoal
      [ .candidate true [.hyp 0], .trapped,
        .candidate true natRowReuseCert ] = true ∧
    -- Forged-only `true` claims: fallback `false`
    gateVerdict (E := Unit) (natCutIdxGate 8) natRowReuseGoal
      [ .candidate true [.hyp 0], .prodErr () ] = false ∧
    -- Oversized valid certificate: fallback `false`
    gateVerdict (E := Unit) (natCutIdxGate 4) natRowReuseGoal
      [ .candidate true natRowReuseCert ] = false ∧
    -- No producers at all: fallback `false`
    gateVerdict (E := Unit) (intCutIdxGate 8) intRowReuseGoal [] = false ∧
    -- Sabotage resistance: uncertified `false` does NOT mask a valid later cert
    gateVerdict (E := Unit) (intCutIdxGate 8) intRowReuseGoal
      [ .candidate false [], .candidate true intRowReuseCert ] = true ∧
    -- Uncertified `false` alone falls back to `false` (never accepted)
    gateVerdict (E := Unit) (intCutIdxGate 8) intRowReuseGoal
      [ .candidate false [] ] = false ∧
    (∀ b, Anneal.Hybrid.evalGate (E := Unit) (verdictGate (intCutIdxGate 8))
      intRowReuseGoal (.candidate false []) ≠ .ok b) ∧
    -- `farkasMirGate`: valid, oversized, and payload-mismatched `true` claims
    gateVerdict (E := Unit) (farkasMirGate 16) mirAddGoal
      [ .candidate true mirAddCert ] = true ∧
    gateVerdict (E := Unit) (farkasMirGate 2) mirAddGoal
      [ .candidate true mirAddCert ] = false ∧
    gateVerdict (E := Unit) (farkasMirGate 16) mirAddGoal
      [ .candidate true (.pair [.hyp 0] [.hyp 1]) ] = false ∧
    -- Exact characterization: `gateVerdict = true` iff an accepted cert exists
    (∃ r : Anneal.Hybrid.RawOutcome Unit Bool (List CutStep),
      r ∈ [ .candidate false [], .candidate true intRowReuseCert ] ∧
      ∃ w, r = .candidate true w ∧
        Anneal.Hybrid.gateCheckBounded (intCutIdxGate 8)
          (intRowReuseGoal, (), w) = true) ∧
    -- A `true` verdict is accepted exactly when the underlying gate accepts
    Anneal.Hybrid.evalGate (E := Unit) (verdictGate (natCutIdxGate 8))
      natRowReuseGoal (.candidate true natRowReuseCert) = .ok true ∧
    natRowReuseGoal.denote ∧
    intRowReuseGoal.denote ∧
    mirAddGoal.denote := by
  have hAllRej :
      gateVerdict (E := Unit) (natCutIdxGate 8) natRowReuseGoal
        [ .candidate true [.hyp 0], .prodErr () ] = false := by
    refine gateVerdict_eq_false_of_all_rejected _ _ _ (fun r hMem b hEv => ?_)
    cases hMem with
    | head => cases hEv
    | tail _ hTl =>
      cases hTl with
      | head => cases hEv
      | tail _ hNil => cases hNil
  have hExInt :=
    (gateVerdict_eq_true_iff_exists (E := Unit) (intCutIdxGate 8)
      intRowReuseGoal
      [ .candidate false [], .candidate true intRowReuseCert ]).1 rfl
  exact ⟨rfl, hAllRej, rfl, rfl, rfl, rfl,
    verdictGate_false_never_ok (intCutIdxGate 8) intRowReuseGoal [],
    rfl, rfl, rfl, hExInt,
    (verdictGate_true_ok_iff (natCutIdxGate 8) natRowReuseGoal
      natRowReuseCert).2 rfl,
    gateVerdict_sound (E := Unit) (natCutIdxGate 8) natRowReuseGoal
      [ .candidate true [.hyp 0], .trapped,
        .candidate true natRowReuseCert ] rfl,
    gateVerdict_sound (E := Unit) (intCutIdxGate 8) intRowReuseGoal
      [ .candidate false [], .candidate true intRowReuseCert ] rfl,
    gateVerdict_sound (E := Unit) (farkasMirGate 16) mirAddGoal
      [ .candidate true mirAddCert ] rfl⟩

/-! ## 3. `CanonicalDiode` (`canonicalDiodeChunkGate` + `foldStreamPrefix`) -/

/-- Strict-parser diode rejecting non-canonical trailing bits (`raw2`). -/
def strictFrameDiode : CanonicalDiode (List (List Bool)) (List Bool) where
  parse := frameStream.dec
  canon := frameStream

/-- `canonicalDiodeChunkGate` on `Anneal.CanonicalDiode.Canaries.diode`. -/
def lenientDiodeGate :=
  canonicalDiodeChunkGate diode frameStream_lawful boolListBeq boolListBeq_eq

/-- `canonicalDiodeChunkGate` instantiated on `strictFrameDiode`. -/
def strictDiodeGate :=
  canonicalDiodeChunkGate strictFrameDiode frameStream_lawful
    boolListBeq boolListBeq_eq

/-- Concrete `BoolCertCut` discharges and valid stream emission matching
`CanonicalDiode.filterAll` on `Anneal.CanonicalDiode.Canaries.diode`. -/
theorem test_canonicalDiode_boolCertCut_and_valid_stream :
    IsCanonicalImage diode raw1 ∧
    IsCanonicalImage diode raw3 ∧
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage diode)
      lenientDiodeGate (faithfulDiodeProducer diode ()) () [raw1, raw2, raw3] =
      ([raw1, raw1, raw3], none) ∧
    (∀ c, c ∈ (Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := IsCanonicalImage diode)
        lenientDiodeGate (faithfulDiodeProducer diode ()) ()
        [raw1, raw2, raw3]).1 →
      IsCanonicalImage diode c) := by
  have hCut1 : IsCanonicalImage diode raw1 :=
    canonicalDiodeChunkGate_cut_sound diode frameStream_lawful
      boolListBeq boolListBeq_eq raw2 raw1
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hCut3 : IsCanonicalImage diode raw3 :=
    canonicalDiodeChunkGate_cut_sound diode frameStream_lawful
      boolListBeq boolListBeq_eq raw3 raw3
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hStream :=
    canonicalDiode_stream_faithful_eq_filterAll diode frameStream_lawful
      boolListBeq boolListBeq_eq boolListBeq_refl ()
      [raw1, raw2, raw3] [raw1, raw1, raw3] rfl
  have hValid :=
    canonicalDiode_stream_all_emitted_canonical diode frameStream_lawful
      boolListBeq boolListBeq_eq (faithfulDiodeProducer diode ())
      [raw1, raw2, raw3]
  exact ⟨hCut1, hCut3, hStream, hValid⟩

/-- Negative streaming tests: malformed input
(`strictFrameDiode.filter raw2 = none`), tampered non-canonical output
(`raw2`), and wrong-AST output (`raw3` for `raw2`) halt `foldStreamPrefix`
immediately and are never emitted. -/
theorem test_canonicalDiode_malformed_and_tampered_rejections :
    -- Strict diode: valid prefix `[raw1]` emitted, halts at malformed `raw2`
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage strictFrameDiode)
      strictDiodeGate (faithfulDiodeProducer strictFrameDiode ()) ()
      [raw1, raw2, raw3] = ([raw1], some (.producerFailed ())) ∧
    -- Adversarial producer emitting `raw1` when `strictFrameDiode.filter raw2`
    -- is `none`
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage strictFrameDiode)
      strictDiodeGate (fun _ _ => .candidate (E := Unit) ((), raw1) ()) ()
      [raw2, raw1] = ([], some .rejectedByChecker) ∧
    -- Tampered producer echoing non-canonical `raw2` on lenient `diode`
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage diode)
      lenientDiodeGate (fun _ u => .candidate (E := Unit) ((), u) ()) ()
      [raw1, raw2, raw3] = ([raw1], some .rejectedByChecker) ∧
    -- Tampered producer substituting wrong-AST canonical `raw3` for `raw2`
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage diode)
      lenientDiodeGate (fun _ _ => .candidate (E := Unit) ((), raw3) ()) ()
      [raw2, raw1] = ([], some .rejectedByChecker) ∧
    -- Non-canonical `raw2` is NOT in `IsCanonicalImage diode`
    ¬ IsCanonicalImage diode raw2 := by
  have hNotCanon : ¬ IsCanonicalImage diode raw2 := by
    rintro ⟨a, _, hDec⟩
    have hNone : diode.canon.dec raw2 = none := rfl
    rw [hNone] at hDec
    nomatch hDec
  have hStrictNone :=
    canonicalDiode_stream_halts_on_filter_none strictFrameDiode
      frameStream_lawful boolListBeq boolListBeq_eq
      (fun _ _ => .candidate (E := Unit) ((), raw1) ()) raw2 raw1 [raw1] rfl rfl
  have hWrongAst :
      Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := IsCanonicalImage diode)
        lenientDiodeGate (fun _ _ => .candidate (E := Unit) ((), raw3) ()) ()
        [raw2, raw1] = ([], some .rejectedByChecker) := by
    refine canonicalDiode_stream_halts_on_tampered diode frameStream_lawful
      boolListBeq boolListBeq_eq
      (fun _ _ => .candidate (E := Unit) ((), raw3) ()) raw2 raw3 [raw1] ?_ rfl
    intro hEq
    have hF : diode.filter raw2 = some raw1 := rfl
    rw [hF] at hEq
    injection hEq with h13
    have hNe : raw1 ≠ raw3 := by decide
    exact hNe h13
  exact ⟨rfl, hStrictNone, rfl, hWrongAst, hNotCanon⟩

/-- Adversarial producer that answers every input chunk with the canonical
chunk `raw1` (a replay of an earlier valid output). -/
def replayRaw1Producer :
    Unit → List Bool → Anneal.Hybrid.RawOutcome Unit (Unit × List Bool) Unit :=
  fun _ _ => .candidate ((), raw1) ()

/-- Mid-stream and whole-stream guarantees against an ADVERSARIAL producer.
The replayed chunk `raw1` is canonical, so it passes `IsCanonicalImage`; it is
accepted for inputs `raw1` and `raw2` (both filter to `raw1`) and rejected for
`raw3`, where the stream halts with exactly the accepted prefix. The emitted
chunks are `filterAll` of the consumed input prefix. -/
theorem test_canonicalDiode_midstream_halt_and_prefix_characterization :
    IsCanonicalImage diode raw1 ∧
    -- Halt at position 2 with the accepted prefix kept and `raw1` not
    -- appended a third time
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := IsCanonicalImage diode)
      lenientDiodeGate replayRaw1Producer ()
      ([raw1, raw2] ++ raw3 :: [raw1, raw1]) =
      ([raw1, raw1], some .rejectedByChecker) ∧
    -- Exact characterization: emitted = `filterAll` of the consumed prefix,
    -- and the first unconsumed chunk is the one the gate rejected
    (∃ consumed rest : List (List Bool),
      [raw1, raw2, raw3, raw1, raw1] = consumed ++ rest ∧
      diode.filterAll consumed = some [raw1, raw1] ∧
      ∃ u rest', rest = u :: rest' ∧
        Anneal.Hybrid.evalGate lenientDiodeGate ((), u)
          (replayRaw1Producer () u) = .error .rejectedByChecker) ∧
    -- Any accepted gate result is the filter image of ITS input
    diode.filter raw2 = some raw1 := by
  have hCanon : IsCanonicalImage diode raw1 :=
    canonicalDiodeChunkGate_cut_sound diode frameStream_lawful
      boolListBeq boolListBeq_eq raw1 raw1
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
  have hMid :=
    canonicalDiode_stream_halts_on_tampered_midstream diode frameStream_lawful
      boolListBeq boolListBeq_eq replayRaw1Producer
      [raw1, raw2] [raw1, raw1] raw3 raw1 [raw1, raw1] rfl
      (fun hEq => by
        have hF : diode.filter raw3 = some raw3 := rfl
        rw [hF] at hEq
        injection hEq with h31
        have hNe : raw3 ≠ raw1 := by decide
        exact hNe h31)
      rfl
  have ⟨consumed, rest, hSplit, hAll, _, hSome⟩ :=
    canonicalDiode_stream_prefix_eq_filterAll diode frameStream_lawful
      boolListBeq boolListBeq_eq replayRaw1Producer
      [raw1, raw2, raw3, raw1, raw1]
  have hOkFilter :=
    canonicalDiodeChunkGate_ok_filter diode frameStream_lawful
      boolListBeq boolListBeq_eq raw2 (replayRaw1Producer () raw2)
      ((), raw1) rfl
  exact ⟨hCanon, hMid,
    ⟨consumed, rest, hSplit, hAll, hSome .rejectedByChecker rfl⟩, hOkFilter⟩

/-! ## 3b. Obligation and Transform Streams (`foldStreamPrefix` over Pillars
1, 2, and 4) -/

/-- Overflow obligations of one function, by guard id. -/
def mirObligation : Nat → FarkasMirGoal
  | 0 => mirAddGoal
  | 1 => mirSubCertGoal
  | 2 => mirMulGoal
  | _ => mirSliceGoal

/-- Certificate table: guard `3` and beyond have no certificate. -/
def mirObligationCert : Nat → Option FarkasMirCert
  | 0 => some mirAddCert
  | 1 => some mirSubCert
  | 2 => some mirMulCert
  | _ => none

/-- Forged table: guard `1` is handed guard `0`'s certificate, which is valid
for guard `0` and wrong for guard `1`. -/
def mirObligationForgedCert : Nat → Option FarkasMirCert
  | 1 => some mirAddCert
  | i => mirObligationCert i

/-- `farkasMirGate` re-indexed by guard id and lifted to a stream gate. -/
noncomputable def mirObligationGate :=
  obligationChunkGate (gateComap mirObligation (farkasMirGate 16)) Nat.beq
    (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)

/-- `LinearArithIndexed` obligations by id, all with certificates. -/
def natObligation : Nat → NatCutGoal
  | 0 => natRowReuseGoal
  | 1 => parityCutReqGoal
  | _ => parityStrideGoal

def natObligationCert : Nat → Option (List CutStep)
  | 0 => some natRowReuseCert
  | 1 => some parityCutReqCert
  | _ => some parityStrideCert

/-- `natCutIdxGate` re-indexed by obligation id and lifted to a stream gate.
-/
noncomputable def natObligationGate (maxSteps : Nat) :=
  obligationChunkGate (gateComap natObligation (natCutIdxGate maxSteps))
    Nat.beq (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)

/-- Prefix-safe obligation streams over `farkasMirGate` and `natCutIdxGate`:
certified obligations are emitted in order; the first one without an accepted
certificate (missing, forged, oversized, or a valid certificate for a
DIFFERENT obligation) halts the stream; every emitted obligation holds. -/
theorem test_obligation_stream_prefix_safe :
    -- All three certified guards are emitted, in order, with no error
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (mirObligation i).denote)
      mirObligationGate (tableProducer mirObligationCert ()) () [0, 1, 2] =
      ([0, 1, 2], none) ∧
    -- The first guard without a certificate halts the stream; guard `2`,
    -- which does have one, is not emitted after it
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (mirObligation i).denote)
      mirObligationGate (tableProducer mirObligationCert ()) ()
      [0, 1, 3, 2] = ([0, 1], some (.producerFailed ())) ∧
    -- A certificate that is valid for another guard is rejected
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (mirObligation i).denote)
      mirObligationGate (tableProducer mirObligationForgedCert ()) ()
      [0, 1, 2] = ([0], some .rejectedByChecker) ∧
    -- Substitution: answering every guard with guard `0` and its valid
    -- certificate is accepted for guard `0` only
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (mirObligation i).denote)
      mirObligationGate
      (fun _ _ => .candidate (E := Unit) ((), 0) mirAddCert) ()
      [0, 1, 2] = ([0], some .rejectedByChecker) ∧
    -- The emitted obligations are a prefix of the input, and the stream
    -- stopped at the first unemitted one
    (∃ rest : List Nat, [0, 1, 3, 2] = [0, 1] ++ rest ∧
      ∃ u rest', rest = u :: rest' ∧
        Anneal.Hybrid.evalGate mirObligationGate ((), u)
          (tableProducer mirObligationCert () () u) =
          .error (.producerFailed ())) ∧
    -- `natCutIdxGate` stream: complete at cap 8; at cap 5 the 5-step
    -- certificate passes and the 8-step one is halted by the size bound
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (natObligation i).denote)
      (natObligationGate 8) (tableProducer natObligationCert ()) ()
      [0, 1, 2] = ([0, 1, 2], none) ∧
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (natObligation i).denote)
      (natObligationGate 5) (tableProducer natObligationCert ()) ()
      [1, 0, 2] = ([1], some (.witnessOversized 8 5)) ∧
    -- Every emitted obligation holds
    mirAddGoal.denote ∧ mirSubCertGoal.denote ∧ mirMulGoal.denote := by
  have hComplete :=
    obligationStream_complete (E := Unit)
      (gateComap mirObligation (farkasMirGate 16)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      Anneal.InitLemmas.nat_beq_refl mirObligationCert () [0, 1, 2]
      (fun x hMem => by
        cases hMem with
        | head => exact ⟨_, rfl, rfl⟩
        | tail _ h1 =>
          cases h1 with
          | head => exact ⟨_, rfl, rfl⟩
          | tail _ h2 =>
            cases h2 with
            | head => exact ⟨_, rfl, rfl⟩
            | tail _ h3 => cases h3)
  have hHold :=
    obligationStream_all_emitted_hold (E := Unit)
      (gateComap mirObligation (farkasMirGate 16)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      (tableProducer mirObligationCert ()) [0, 1, 2]
  rw [hComplete] at hHold
  have ⟨rest, hSplit, _, hSome⟩ :=
    obligationStream_emitted_prefix (E := Unit)
      (gateComap mirObligation (farkasMirGate 16)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      (tableProducer mirObligationCert ()) [0, 1, 3, 2]
  exact ⟨hComplete, rfl, rfl, rfl, ⟨rest, hSplit, hSome _ rfl⟩, rfl, rfl,
    hHold 0 (List.Mem.head _),
    hHold 1 (List.Mem.tail _ (List.Mem.head _)),
    hHold 2 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- Pillar 4 (`blockOptGate`) block stream under `foldStreamPrefix` via
`transformChunkGate` + `gateComapY`: blocks `0..2` carry `.proven` facts and
valid certificates; block `3` has only a `.fuzz` candidate. -/
def backendStreamSrc : Nat → SourceBlockUnit
  | 0 => u64CheckedAddSrc
  | 1 => u64CheckedSubSrc
  | 2 => paddingSrc
  | _ => u64CheckedAddSrcAt .fuzz

def backendStreamTable : Nat → Option (CompiledBlockUnit × List DagStep)
  | 0 =>
    some (u64UncheckedAddOpt, [.refl 0, .biRule (.promoteAddNuw 0) [0, 1] 2 3])
  | 1 => some (u64UncheckedSubOpt, u64CheckedSubToUncheckedSteps)
  | 2 => some (paddingOpt, paddingSteps)
  | _ => some (u64UncheckedAddOpt, u64CheckedAddToUncheckedSteps)

noncomputable def backendStreamGate :=
  transformChunkGate (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
    (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)

/-- Prefix-safe Pillar 4 (`blockOptGate`) stream under `foldStreamPrefix`:
valid blocks `[0, 1, 2]` complete with every emitted pair proven to refine its
source block; a `.fuzz`-only block `3` halts mid-stream without emitting block
`3` or any trailing block; and an adversarial producer trying to replay block
`0`'s valid certificate for block `1` halts immediately at block `1`. -/
theorem test_backend_transform_stream_prefix_safe :
    -- Complete valid stream `[0, 1, 2]`
    (Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate (transformTableProducer backendStreamTable ()) ()
      [0, 1, 2]).2 = none ∧
    ((Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate (transformTableProducer backendStreamTable ()) ()
      [0, 1, 2]).1.map Prod.fst) = [0, 1, 2] ∧
    -- `.fuzz` block `3` halts mid-stream with `.rejectedByChecker`
    (Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate (transformTableProducer backendStreamTable ()) ()
      [0, 1, 3, 2]).2 = some .rejectedByChecker ∧
    ((Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate (transformTableProducer backendStreamTable ()) ()
      [0, 1, 3, 2]).1.map Prod.fst) = [0, 1] ∧
    -- Adversarial replay of block `0` for every block halts at block `1`
    ((Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate
      (fun _ _ => .candidate (E := Unit) ((), (0, u64UncheckedAddOpt))
        [.refl 0, .biRule (.promoteAddNuw 0) [0, 1] 2 3])
      () [0, 1, 2]).1.map Prod.fst) = [0] ∧
    -- Every emitted pair in `[0, 1, 2]` satisfies `SemRefinesUnder`
    SemRefinesUnder (SourceEntryPre u64CheckedAddSrc)
      (evalSourceBlockUnit u64CheckedAddSrc)
      (evalCompiledBlockUnit u64UncheckedAddOpt) ∧
    SemRefinesUnder (SourceEntryPre paddingSrc)
      (evalSourceBlockUnit paddingSrc)
      (evalCompiledBlockUnit paddingOpt) := by
  have hComp :=
    transformStream_complete (E := Unit)
      (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      Anneal.InitLemmas.nat_beq_refl backendStreamTable () [0, 1, 2]
      (fun x hMem => by
        cases hMem with
        | head => exact ⟨_, _, rfl, rfl⟩
        | tail _ h1 =>
          cases h1 with
          | head => exact ⟨_, _, rfl, rfl⟩
          | tail _ h2 =>
            cases h2 with
            | head => exact ⟨_, _, rfl, rfl⟩
            | tail _ h3 => cases h3)
  have hValid :=
    transformStream_all_emitted_valid (E := Unit)
      (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      (transformTableProducer backendStreamTable ()) [0, 1, 2]
  have hRes :
      (Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := fun p : Nat × CompiledBlockUnit =>
          SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
            (evalSourceBlockUnit (backendStreamSrc p.1))
            (evalCompiledBlockUnit p.2))
        backendStreamGate (transformTableProducer backendStreamTable ()) ()
        [0, 1, 2]).1 =
        [ (0, u64UncheckedAddOpt),
          (1, u64UncheckedSubOpt),
          (2, paddingOpt) ] := rfl
  dsimp only [backendStreamGate] at hRes
  rw [hRes] at hValid
  exact ⟨hComp.1, hComp.2, rfl, rfl, rfl,
    hValid (0, u64UncheckedAddOpt) (List.Mem.head _),
    hValid (2, paddingOpt)
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- Expected compiled block per id for `backendStreamTable`. -/
def backendStreamOut : Nat → CompiledBlockUnit
  | 0 => u64UncheckedAddOpt
  | 1 => u64UncheckedSubOpt
  | 2 => paddingOpt
  | _ => u64UncheckedAddOpt

/-- The halted `blockOptGate` stream `[0, 1, 3, 2]` emits only accepted table
entries, its emitted keys are the prefix `[0, 1]` halted at `.fuzz` block `3`,
the complete stream `[0, 1, 2]` matches `transformStream_complete_exact` on
BOTH keys and outputs, and `obligationChunkGate` over
`farkasMirBoundedEdgeGate` halts an empty-edge bomb mid-stream as
`.witnessOversized`. -/
theorem test_backend_transform_stream_entries_and_prefix :
    -- Full-list exact completeness (keys AND outputs)
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun p : Nat × CompiledBlockUnit =>
        SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
          (evalSourceBlockUnit (backendStreamSrc p.1))
          (evalCompiledBlockUnit p.2))
      backendStreamGate (transformTableProducer backendStreamTable ()) ()
      [0, 1, 2] =
      ([ (0, u64UncheckedAddOpt),
         (1, u64UncheckedSubOpt),
         (2, paddingOpt) ], none) ∧
    (∀ p : Nat × CompiledBlockUnit,
      p ∈ (Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
        (ValidChunk := fun p : Nat × CompiledBlockUnit =>
          SemRefinesUnder (SourceEntryPre (backendStreamSrc p.1))
            (evalSourceBlockUnit (backendStreamSrc p.1))
            (evalCompiledBlockUnit p.2))
        backendStreamGate (transformTableProducer backendStreamTable ()) ()
        [0, 1, 3, 2]).1 →
      ∃ w, backendStreamTable p.1 = some (p.2, w) ∧
        Anneal.Hybrid.gateCheckBounded
          (gateComapY backendStreamSrc (blockOptGate 4)) (p.1, p.2, w) =
          true) ∧
    (∃ rest : List Nat, [0, 1, 3, 2] = [0, 1] ++ rest ∧
      ∃ u rest', rest = u :: rest' ∧
        Anneal.Hybrid.evalGate backendStreamGate ((), u)
          (transformTableProducer backendStreamTable () () u) =
          .error .rejectedByChecker) ∧
    -- Bounded-edge obligation stream halts mid-stream on an empty-edge bomb
    Anneal.Hybrid.foldStreamPrefix (AccInv := fun _ => True)
      (ValidChunk := fun i => (mirObligation i).denote)
      (obligationChunkGate
        (gateComap mirObligation (farkasMirBoundedEdgeGate 8)) Nat.beq
        (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h))
      (tableProducer
        (fun i => match i with
          | 0 => some mirAddCert
          | 1 => some (.edge (List.replicate 9 []))
          | _ => some mirMulCert) ()) () [0, 1, 2] =
      ([0], some (.witnessOversized 9 8)) := by
  have hExact :=
    transformStream_complete_exact (E := Unit)
      (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      Anneal.InitLemmas.nat_beq_refl backendStreamTable backendStreamOut ()
      [0, 1, 2]
      (fun x hMem => by
        cases hMem with
        | head => exact ⟨_, rfl, rfl⟩
        | tail _ h1 =>
          cases h1 with
          | head => exact ⟨_, rfl, rfl⟩
          | tail _ h2 =>
            cases h2 with
            | head => exact ⟨_, rfl, rfl⟩
            | tail _ h3 => cases h3)
  have hEntries :=
    transformStream_table_entries (E := Unit)
      (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      backendStreamTable () [0, 1, 3, 2]
  have ⟨rest, hSplit, _, hSome⟩ :=
    transformStream_emitted_prefix (E := Unit)
      (gateComapY backendStreamSrc (blockOptGate 4)) Nat.beq
      (fun _ _ h => Anneal.InitLemmas.nat_eq_of_beq h)
      (transformTableProducer backendStreamTable ()) [0, 1, 3, 2]
  exact ⟨hExact, hEntries, ⟨rest, hSplit, hSome _ rfl⟩, rfl⟩

/-! ## 4. `Anneal.Backend` + `OverflowTrapRefinement` End-to-End & Negatives -/

/-- End-to-end `u64` addition and subtraction checked-to-unchecked refinement
via BOTH `farkasMirGate` and `natCutIdxGate` `BoolCertCut`s, uniting `CtxFact`,
`blockOptGate`, `stepMirState`, and `ITree.toPartial`. -/
theorem test_backend_overflowTrap_e2e_add_sub
    (a b : Nat) (ha : a ≤ 1000) (hb : b ≤ 2000)
    (c d : Nat) (hc : c ≤ 1000) (hcd : d + 4 ≤ c) :
    -- `u64` add via `farkasMirGate` + `blockOptGate` + `stepMirState`
    SourceEntryPre u64CheckedAddSrc (env2 a b) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 a b)).toPartial ∧
    -- `u64` sub via `natCutIdxGate` + `blockOptGate` + `stepMirState`
    SourceEntryPre u64CheckedSubSrc (env2 c d) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 c d)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 c d))) ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 c d)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 c d))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 c d)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 c d)).toPartial := by
  have hAdd :=
    u64_add_farkasMirGate_to_stepMirState_bridge 8
      [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 2000⟩] (.var 0) (.var 1)
      (.single [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1])
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [a, b] ha hb
  have hSub :=
    u64_sub_natCutIdxGate_to_stepMirState_bridge 8
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
      (.var 0) (.var 1)
      [.hyp 0, .hyp 4, .comb 0 1 1 1]
      [.hyp 1, .hyp 4, .comb 0 1 1 1]
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [c, d] hcd hc
  exact ⟨hAdd.1, hAdd.2.2.1, hAdd.2.2.2.1, hAdd.2.2.2.2,
         hSub.1, hSub.2.2.1, hSub.2.2.2.1, hSub.2.2.2.2⟩

/-- Also verify `blockOptGate_cut_preserves_mirRefines` on `paddingSrc` /
`paddingOpt` from `Anneal.Backend.Canaries` and `u64_add_natCutIdxGate` +
`u64_sub_farkasMirGate` directions. -/
theorem test_backend_blockOptGate_mirRefines_and_alt_bridges
    (env : Nat → Nat) (hPad : SourceEntryPre paddingSrc env)
    (a b : Nat) (ha : a ≤ 1000) (hb : b ≤ 2000)
    (c d : Nat) (hc : c ≤ 1000) (hcd : d + 4 ≤ c) :
    MirOutcomeRefines
      (evalBlockMirClass paddingSrc.guards paddingSrc.arena
        paddingSrc.srcRetId env)
      (evalBlockMirClass paddingOpt.guardsOut paddingOpt.arenaOut
        paddingOpt.retId env) ∧
    MirExactOutcomeRefines
      (evalBlockMirExactClass paddingSrc.guards paddingSrc.arena
        paddingSrc.srcRetId env)
      (evalBlockMirExactClass paddingOpt.guardsOut paddingOpt.arenaOut
        paddingOpt.retId env) ∧
    SourceEntryPre u64CheckedAddSrc (env2 a b) ∧
    SourceEntryPre u64CheckedSubSrc (env2 c d) := by
  have hPadMir :=
    blockOptGate_cut_preserves_mirRefines 4 paddingSrc paddingOpt paddingSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl) env hPad
  have hAddIdx :=
    u64_add_natCutIdxGate_to_stepMirState_bridge 8
      [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 2000⟩] (.var 0) (.var 1)
      [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [a, b] ha hb
  have hSubFarkas :=
    u64_sub_farkasMirGate_to_stepMirState_bridge 8
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
      (.var 0) (.var 1)
      mirSubCert
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [c, d] hcd hc
  exact ⟨hPadMir.1, hPadMir.2.1, hAddIdx.1, hSubFarkas.1⟩

/-- Negative counterexamples across `Anneal.Backend` and
`OverflowTrapRefinement`: forged `blockOptGate` cert, inverted `.symm` on
`.refines`, `.refines` under `.freeze`, `.fuzz`/`.sorryStub` candidates,
unsound overflow/underflow guard elision, `.diverged` distinctness, and
`-C panic=abort` vs `-C panic=unwind` strategy separation. -/
theorem test_backend_and_trap_negative_counterexamples :
    -- Forged `blockOptGate` witness rejected
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2) u64CheckedAddSrc
      (.candidate u64UncheckedAddOpt [.refl 0]) = .error .rejectedByChecker ∧
    -- Inverted `.symm` on `.refines` rejected + `.poison` witness
    verifyDagGoal freezeTestArena []
      [.dirRule .landZero [0, 1] 4 1, .symm 0] 1 4 .refines = false ∧
    (¬ ∀ x : PoisonOr Nat,
      refinesPoison (.val 0) (evalSsaOp (fun _ => 0) .land [x, .val 0])) ∧
    -- `.refines` under `.freeze` rejected
    verifyDagGoal freezeTestArena []
      [.dirRule .landZero [0, 1] 4 1, .cong 7 8 [0]] 7 8 .refines = false ∧
    (LetBody.addWrap .boundVar (.freeze 7 .boundVar)).isFreezeFree = false ∧
    -- `.fuzz` and `.sorryStub` candidates rejected by `blockOptGate`
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 4) paddingFuzzOnlySrc
      (.candidate paddingOpt paddingSteps) = .error .rejectedByChecker ∧
    -- Unsound overflow/underflow guard elision refuted
    ¬ SemRefines (evalSourceBlockUnit u64CheckedAddSrc)
        (evalCompiledBlockUnit u64WrappingAddOpt) ∧
    ¬ SemRefines (evalSourceBlockUnit u64CheckedSubSrc)
        (evalCompiledBlockUnit u64WrappingSubOpt) ∧
    -- Strategy separation (`abort` ≠ `unwind`)
    ¬ MirExactOutcomeRefines (.trap .abort : MirExactOutcomeClass Value)
        (.trap .panic) ∧
    -- `.diverged` never collapses into `.ret`, `.trap`, or `.ub`
    execOutcomeToMirClass? .diverged = none ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? .diverged)
        (execOutcomeToMirClass? .faultUB) :=
  ⟨rfl,
   neg1_symmOnDirRefine_rejected,
   neg2_symmOnDirRefine_unsound_witness,
   neg3_dirRefineUnderFreeze_rejected,
   neg4_dirRefineInLetFreeze_rejected,
   neg5_fuzzAndSorryCandidatesRejectedByGate,
   neg_u64_add_undischarged_guard_elision_unsound.2.2.2.1,
   neg_u64_sub_undischarged_guard_elision_unsound.2.2.2.1,
   neg_aborted_strategy_separation.2.2.1,
   (execOutcomeToMirClass?_diverged_distinct 0).1,
   (execOutcomeToMirClass?_diverged_distinct 0).2.2.2.2.2.2.2.2.1⟩

/-- A second, non-canonical certificate for the `addNoOverflow` elision: a
redundant leading `.refl` step before the `promoteAddNuw` rewrite. -/
def u64AddAltSteps : List DagStep :=
  [.refl 0, .biRule (.promoteAddNuw 0) [0, 1] 2 3]

/-- Certificate transport: the real `stepMirState` refinement is derived from
ANY accepted `blockOptGate` `BoolCertCut` (here a non-canonical certificate),
for add and sub and for the unchecked and wrapping targets, including the
fully chained two-gate capstones (`farkasMirGate` + `blockOptGate`). -/
theorem test_backend_cert_transport_to_stepMirState
    (a b : Nat) (ha : a ≤ 1000) (hb : b ≤ 2000)
    (c d : Nat) (hc : c ≤ 1000) (hcd : d + 4 ≤ c) :
    -- Both gates chained, non-canonical `blockOptGate` certificate
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    -- Wrapping target: full equivalence under the discharged fact
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    -- Subtraction, both gates chained (`farkasMirGate` + `blockOptGate`)
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 c d)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 c d))) ∧
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 c d)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u64 .sub) 2
          (uintArgs2 .u64 c d))) ∧
    -- Both `natCutIdxGate` + `blockOptGate` two-gate capstones
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 a b))) ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 c d)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 c d))) ∧
    -- Bidirectional `ITree.toPartial` equivalence from all 4 two-gate capstones
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 c d)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 c d)).toPartial := by
  have hBig : 2000 < modPow2 (uintWidth .u64) := by decide
  have haLt : a < modPow2 (uintWidth .u64) :=
    Nat.lt_of_le_of_lt ha (Nat.lt_trans (by decide) hBig)
  have hbLt : b < modPow2 (uintWidth .u64) := Nat.lt_of_le_of_lt hb hBig
  have hcLt : c < modPow2 (uintWidth .u64) :=
    Nat.lt_of_le_of_lt hc (Nat.lt_trans (by decide) hBig)
  have hdLt : d < modPow2 (uintWidth .u64) :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right d 4) hcd) hcLt
  have hAddEntry : SourceEntryPre u64CheckedAddSrc (env2 a b) :=
    (sourceEntryPre_u64CheckedAdd_iff a b haLt hbLt).2
      (Nat.lt_of_le_of_lt (Nat.add_le_add ha hb) (by decide))
  have hSubEntry : SourceEntryPre u64CheckedSubSrc (env2 c d) :=
    (sourceEntryPre_u64CheckedSub_iff c d hcLt hdLt).2
      (Nat.le_trans (Nat.le_add_right d 4) hcd)
  have hAdd :=
    u64_add_farkas_and_blockOpt_cuts_to_stepMirState 8 2
      [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 2000⟩] (.var 0) (.var 1)
      (.single [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1])
      u64AddAltSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [a, b] ha hb
  have hAddWrap :=
    u64_add_blockOptGate_cut_to_stepMirState_wrapping 2
      u64CheckedAddToWrappingSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      a b haLt hbLt hAddEntry
  have hSub :=
    u64_sub_farkas_and_blockOpt_cuts_to_stepMirState 8 2
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
      (.var 0) (.var 1) mirSubCert u64CheckedSubToUncheckedSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [c, d] hcd hc
  have hSubWrap :=
    u64_sub_blockOptGate_cut_to_stepMirState_wrapping 2
      u64CheckedSubToWrappingSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      c d hcLt hdLt hSubEntry
  have hAddIdx :=
    u64_add_natCutIdx_and_blockOpt_cuts_to_stepMirState 8 2
      [⟨.var 0, .cst 1000⟩, ⟨.var 1, .cst 2000⟩] (.var 0) (.var 1)
      [.hyp 0, .hyp 1, .comb 0 1 1 1, .hyp 4, .comb 2 1 3 1]
      u64AddAltSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [a, b] ha hb
  have hSubIdx :=
    u64_sub_natCutIdx_and_blockOpt_cuts_to_stepMirState 8 2
      [⟨.add (.var 1) (.cst 4), .var 0⟩, ⟨.var 0, .cst 1000⟩]
      (.var 0) (.var 1)
      [.hyp 0, .hyp 4, .comb 0 1 1 1]
      [.hyp 1, .hyp 4, .comb 0 1 1 1]
      u64CheckedSubToUncheckedSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      [c, d] hcd hc
  exact ⟨hAdd.1, hAdd.2.1, hAddWrap.1, hSub.1, hSubWrap.2, hAddIdx.1, hSubIdx.1,
    hAdd.2.2.2, hSubIdx.2.2.2⟩

/-- Genuinely asymmetric `.ub ⊑ .ret` certificate transport through
`blockOptGate` to `stepMirState` and `ITree.toPartial`, plus the relational
source-UB case of `semRefinesUnder_preserves_mirOptRefines_asymmetric`. -/
theorem test_backend_asymmetric_ub_transport
    (a b : Nat) (ha : a < modPow2 (uintWidth .u64))
    (hb : b < modPow2 (uintWidth .u64)) :
    MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .add) 2 (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 a b)).toPartial ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .add) 2
            (uintArgs2 .u64 u64Max 1))) ∧
    (∃ outSrc, evalSourceBlockUnit u64UncheckedAddSrc (env2 u64Max 1) outSrc ∧
      MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
        (execOutcomeToMirClass? (.returned 0 ()))) ∧
    -- Symmetric subtraction asymmetric `.ub ⊑ .ret` transport (`dropSubNuw`)
    MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2 (uintArgs2 .u64 a b)))
      (classifyMirExecStateExact
        (runMirCall (mkWrappingArithBody .u64 .sub) 2 (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkWrappingArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 a b)).toPartial ∧
    ¬ MirExactOutcomeRefines
        (classifyMirExecStateExact
          (runMirCall (mkWrappingArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1)))
        (classifyMirExecStateExact
          (runMirCall (mkUncheckedArithBody .u64 .sub) 2
            (uintArgs2 .u64 0 1))) := by
  have hTr := u64_addNuw_to_addWrap_asymmetric_ub_transport a b ha hb
  have hSubTr := u64_subNuw_to_subWrap_asymmetric_ub_transport a b ha hb
  have hCut :
      Anneal.Framework.StepWp.BoolCertCut
        (Anneal.Hybrid.gateCheckBounded (blockOptGate 2))
        (u64UncheckedAddSrc, u64WrappingAddOpt,
          [.dirRule .dropAddNuw [0, 1] 3 2]) :=
    Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl
  have hSem := Anneal.Hybrid.certGateCut_sound (blockOptGate 2) True.intro hCut
  have hSrcUb : evalSourceBlockUnit u64UncheckedAddSrc
      (env2 u64Max 1) .faultUB := by
    dsimp only [evalSourceBlockUnit]
    rw [evalBlockWithGuards_iff_det]
    rfl
  have hTgtRet : evalCompiledBlockUnit u64WrappingAddOpt
      (env2 u64Max 1) (.returned 0 ()) := by
    dsimp only [evalCompiledBlockUnit]
    rw [evalBlockWithGuards_iff_det]
    rfl
  have hAsym :=
    semRefinesUnder_preserves_mirOptRefines_asymmetric hSem
      (fun _ _ h => nomatch h) (Or.inl hSrcUb) hTgtRet
  have ⟨outSrc, hS, hR, _⟩ := hAsym
  exact ⟨hTr.1, hTr.2.2.1, hTr.2.2.2, ⟨outSrc, hS, hR⟩,
    hSubTr.1, hSubTr.2.2.1, hSubTr.2.2.2⟩

/-- The outcome bridge is faithful exactly on `u64`-ranged outcomes: it is
injective there, refinement between bridged outcomes means "the spec is UB
or the outcomes are equal", and outside the range `0` and `2^64` collide. -/
theorem test_backend_outcome_bridge_faithful :
    ¬ MirOptExactOutcomeRefines (execOutcomeToMirExactClass? (.aborted ()))
        (execOutcomeToMirExactClass? (.returned 0 ())) ∧
    ¬ MirOptExactOutcomeRefines (execOutcomeToMirExactClass? (.returned 1 ()))
        (execOutcomeToMirExactClass? .diverged) ∧
    MirOptExactOutcomeRefines (execOutcomeToMirExactClass? .faultUB)
      (execOutcomeToMirExactClass? .diverged) ∧
    (∀ v : Nat, v < modPow2 (uintWidth .u64) →
      execOutcomeToMirExactClass? (.returned v ()) =
        execOutcomeToMirExactClass? (.returned 7 ()) → v = 7) ∧
    (∀ v : Nat, v < modPow2 (uintWidth .u64) →
      execOutcomeToMirClass? (.returned v ()) =
        execOutcomeToMirClass? (.returned 7 ()) → v = 7) ∧
    ¬ MirOptOutcomeRefines (execOutcomeToMirClass? (.aborted ()))
        (execOutcomeToMirClass? (.returned 0 ())) ∧
    execOutcomeToMirExactClass? (.returned 0 ()) =
      execOutcomeToMirExactClass? (.returned u64Mod ()) := by
  have h0 : 0 < modPow2 (uintWidth .u64) := by decide
  have h1 : 1 < modPow2 (uintWidth .u64) := by decide
  have h7 : 7 < modPow2 (uintWidth .u64) := by decide
  refine ⟨fun hRef => ?_, fun hRef => ?_, ?_, fun v hv hEq => ?_,
    fun v hv hEq => ?_, fun hRef => ?_,
    neg_execOutcomeToMirExactClass?_not_injective_unranged.1⟩
  · cases (mirOptExactOutcomeRefines_exec_iff_on_u64
        (o₁ := .aborted ()) (o₂ := .returned 0 ()) True.intro h0).1 hRef with
    | inl h => nomatch h
    | inr h => nomatch h
  · cases (mirOptExactOutcomeRefines_exec_iff_on_u64
        (o₁ := .returned 1 ()) (o₂ := .diverged) h1 True.intro).1 hRef with
    | inl h => nomatch h
    | inr h => nomatch h
  · exact (mirOptExactOutcomeRefines_exec_iff_on_u64
      (o₁ := .faultUB) (o₂ := .diverged) True.intro True.intro).2 (Or.inl rfl)
  · have hOut := execOutcomeToMirExactClass?_injective_on_u64
      (o₁ := .returned v ()) (o₂ := .returned 7 ()) hv h7 hEq
    injection hOut
  · have hOut := execOutcomeToMirClass?_injective_on_u64
      (o₁ := .returned v ()) (o₂ := .returned 7 ()) hv h7 hEq
    injection hOut
  · cases (mirOptOutcomeRefines_exec_iff_on_u64
        (o₁ := .aborted ()) (o₂ := .returned 0 ()) True.intro h0).1 hRef with
    | inl h => nomatch h
    | inr h => nomatch h

/-- An environment that is NOT of the form `env2 a b`: variable `2` is `13`,
not `0`. -/
def affineEnv : Nat → Nat := fun i => 5 * i + 3

/-- An out-of-range environment whose `0` and `1` coordinates exceed `2^64`
(`wrappedEnv 0 = 2^64 + 3`, `wrappedEnv 1 = 2 * 2^64 + 8`). -/
def wrappedEnv : Nat → Nat := fun i => (i + 1) * u64Mod + 5 * i + 3

/-- Certificate transport at EVERY Backend environment (both `u64`-ranged
`affineEnv` AND out-of-range `wrappedEnv` with NO range hypotheses), for
non-canonical certificates and both unchecked and wrapping targets. -/
theorem test_backend_every_environment_transport :
    affineEnv 2 ≠ env2 (affineEnv 0) (affineEnv 1) 2 ∧
    u64Mod ≤ wrappedEnv 0 ∧
    SourceEntryPre u64CheckedAddSrc affineEnv ∧
    SourceEntryPre u64CheckedAddSrc wrappedEnv ∧
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
          (uintArgs2 .u64 3 8)))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .add) 2
          (uintArgs2 .u64 3 8))) ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 3 8)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 3 8)).toPartial ∧
    -- Out-of-range `wrappedEnv`: unchecked + wrapping `ITree.toPartial` equiv
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (wrappedEnv 0))
          (word64 (wrappedEnv 1)))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (wrappedEnv 0))
          (word64 (wrappedEnv 1)))).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u64 .add .terminate)
        (uintArgs2 .u64 (word64 (wrappedEnv 0))
          (word64 (wrappedEnv 1)))).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u64 .add)
        (uintArgs2 .u64 (word64 (wrappedEnv 0))
          (word64 (wrappedEnv 1)))).toPartial ∧
    -- Subtraction at swapped environments (in-range + out-of-range wrapping)
    MirOutcomeEquiv
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 8 3)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 8 3))) ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (wrappedEnv 1))
          (word64 (wrappedEnv 0)))).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (wrappedEnv 1))
          (word64 (wrappedEnv 0)))).toPartial := by
  have h3 : 3 < modPow2 (uintWidth .u64) := by decide
  have h8 : 8 < modPow2 (uintWidth .u64) := by decide
  have hAddEntry : SourceEntryPre u64CheckedAddSrc affineEnv :=
    (sourceEntryPre_u64CheckedAdd_env_iff affineEnv).2
      ((sourceEntryPre_u64CheckedAdd_iff 3 8 h3 h8).2 (by decide))
  have hWrapAddEntry : SourceEntryPre u64CheckedAddSrc wrappedEnv :=
    (sourceEntryPre_u64CheckedAdd_any_env_iff wrappedEnv).2
      ((sourceEntryPre_u64CheckedAdd_iff _ _ (by decide) (by decide)).2
        (by decide))
  have hAdd :=
    u64_add_blockOptGate_cut_to_stepMirState_env 2 u64AddAltSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      affineEnv h3 h8 hAddEntry
  have hWrapAdd :=
    u64_add_blockOptGate_cut_to_stepMirState_any_env 2 u64AddAltSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      wrappedEnv hWrapAddEntry
  have hWrapAddW :=
    u64_add_blockOptGate_cut_to_stepMirState_wrapping_any_env 2
      u64CheckedAddToWrappingSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      wrappedEnv hWrapAddEntry
  have hSubEntry :
      SourceEntryPre u64CheckedSubSrc (fun i => affineEnv (1 - i)) :=
    (sourceEntryPre_u64CheckedSub_env_iff _).2
      ((sourceEntryPre_u64CheckedSub_iff 8 3 h8 h3).2 (by decide))
  have hSub :=
    u64_sub_blockOptGate_cut_to_stepMirState_env 2
      u64CheckedSubToUncheckedSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (fun i => affineEnv (1 - i)) h8 h3 hSubEntry
  have hWrapSubEntry :
      SourceEntryPre u64CheckedSubSrc (fun i => wrappedEnv (1 - i)) :=
    (sourceEntryPre_u64CheckedSub_any_env_iff _).2
      ((sourceEntryPre_u64CheckedSub_iff _ _ (by decide) (by decide)).2
        (by decide))
  have hWrapSubW :=
    u64_sub_blockOptGate_cut_to_stepMirState_wrapping_any_env 2
      u64CheckedSubToWrappingSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (fun i => wrappedEnv (1 - i)) hWrapSubEntry
  exact ⟨by decide, by decide, hAddEntry, hWrapAddEntry, hAdd.1, hAdd.2.2.2,
    hWrapAdd.2.2.2, hWrapAddW.2.2.2, hSub.2.1, hWrapSubW.2.2.2⟩

/-- Checked-to-UNCHECKED subtraction at an out-of-range environment, with no
range hypothesis: the one unrestricted-environment transport theorem the test
above does not instantiate. -/
theorem test_backend_unchecked_sub_any_environment :
    MirExactOutcomeEquiv
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u64 .sub .terminate) 6
          (uintArgs2 .u64 (word64 (wrappedEnv 1))
            (word64 (wrappedEnv 0)))))
      (classifyMirExecStateExact
        (runMirCall (mkUncheckedArithBody .u64 .sub) 2
          (uintArgs2 .u64 (word64 (wrappedEnv 1))
            (word64 (wrappedEnv 0))))) ∧
    (mirCallTree (mkCheckedArithBody .u64 .sub .terminate)
        (uintArgs2 .u64 (word64 (wrappedEnv 1))
          (word64 (wrappedEnv 0)))).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u64 .sub)
        (uintArgs2 .u64 (word64 (wrappedEnv 1))
          (word64 (wrappedEnv 0)))).toPartial := by
  have hEntry :
      SourceEntryPre u64CheckedSubSrc (fun i => wrappedEnv (1 - i)) :=
    (sourceEntryPre_u64CheckedSub_any_env_iff _).2
      ((sourceEntryPre_u64CheckedSub_iff _ _ (by decide) (by decide)).2
        (by decide))
  have h :=
    u64_sub_blockOptGate_cut_to_stepMirState_any_env 2
      u64CheckedSubToUncheckedSteps
      (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)
      (fun i => wrappedEnv (1 - i)) hEntry
  exact ⟨h.1, h.2.2.2⟩

/-- Undischarged-fact negatives. The SAME elision certificate that
`blockOptGate` accepts for the `.proven` source is rejected once the fact is
only `.fuzz` or `.sorryStub`; no certificate of any size is ever accepted
there; and the `stepMirState` picture at the overflow / underflow witnesses
shows the abort that elision would have erased. -/
theorem test_backend_unproven_tier_elision_never_certified
    (maxStepsPerNode : Nat) (steps : List DagStep) :
    -- Differential: only the candidate's trust tier changes
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedAddSrcAt .proven)
      (.candidate u64UncheckedAddOpt u64CheckedAddToUncheckedSteps) =
      .ok u64UncheckedAddOpt ∧
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedAddSrcAt .fuzz)
      (.candidate u64UncheckedAddOpt u64CheckedAddToUncheckedSteps) =
      .error .rejectedByChecker ∧
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedAddSrcAt .sorryStub)
      (.candidate u64UncheckedAddOpt u64CheckedAddToUncheckedSteps) =
      .error .rejectedByChecker ∧
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedSubSrcAt .proven)
      (.candidate u64WrappingSubOpt u64CheckedSubToWrappingSteps) =
      .ok u64WrappingSubOpt ∧
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedSubSrcAt .fuzz)
      (.candidate u64WrappingSubOpt u64CheckedSubToWrappingSteps) =
      .error .rejectedByChecker ∧
    Anneal.Hybrid.evalGate (E := Unit) (blockOptGate 2)
      (u64CheckedSubSrcAt .sorryStub)
      (.candidate u64WrappingSubOpt u64CheckedSubToWrappingSteps) =
      .error .rejectedByChecker ∧
    -- No certificate of ANY size, for ANY step list
    Anneal.Hybrid.gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedAddSrcAt .fuzz, u64WrappingAddOpt, steps) = false ∧
    Anneal.Hybrid.gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedAddSrcAt .sorryStub, u64UncheckedAddOpt, steps) = false ∧
    Anneal.Hybrid.gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedSubSrcAt .sorryStub, u64WrappingSubOpt, steps) = false ∧
    Anneal.Hybrid.gateCheckBounded (blockOptGate maxStepsPerNode)
      (u64CheckedSubSrcAt .fuzz, u64UncheckedSubOpt, steps) = false ∧
    -- `stepMirState` at the witnesses: checked aborts, wrapping returns
    classifyMirExecStateExact
      (runMirCall (mkCheckedArithBody .u64 .add .terminate) 6
        (uintArgs2 .u64 u64Max 1)) = .trap .abort ∧
    classifyMirExecStateExact
      (runMirCall (mkWrappingArithBody .u64 .add) 2
        (uintArgs2 .u64 u64Max 1)) = .ret (execOutcomeToMirValue 0) ∧
    classifyMirExecStateExact
      (runMirCall (mkWrappingArithBody .u64 .sub) 2
        (uintArgs2 .u64 0 1)) = .ret (execOutcomeToMirValue u64Max) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
   (neg_u64_add_unproven_elision_never_certified .fuzz
     (fun h => nomatch h) maxStepsPerNode steps).1,
   (neg_u64_add_unproven_elision_never_certified .sorryStub
     (fun h => nomatch h) maxStepsPerNode steps).2,
   (neg_u64_sub_unproven_elision_never_certified .sorryStub
     (fun h => nomatch h) maxStepsPerNode steps).1,
   (neg_u64_sub_unproven_elision_never_certified .fuzz
     (fun h => nomatch h) maxStepsPerNode steps).2,
   neg_u64_add_overflow_stepMirState_matrix.1,
   neg_u64_add_overflow_stepMirState_matrix.2.1,
   neg_u64_sub_underflow_stepMirState_matrix.2.1⟩

/-- `SemRefinesUnder` preservation without any determinism assumption on the
source semantics, instantiated at the certified `u64` add elision: every
target outcome is a non-UB source-permitted outcome. -/
theorem test_backend_relational_preservation (a b : Nat)
    (ha : a < modPow2 (uintWidth .u64)) (hb : b < modPow2 (uintWidth .u64))
    (hEntry : SourceEntryPre u64CheckedAddSrc (env2 a b))
    (outTgt : ExecOutcome Nat Unit)
    (hTgt : evalCompiledBlockUnit u64UncheckedAddOpt (env2 a b) outTgt) :
    execOutcomeToMirClass? outTgt ≠ some .ub ∧
    ∃ outSrc, evalSourceBlockUnit u64CheckedAddSrc (env2 a b) outSrc ∧
      MirOptOutcomeRefines (execOutcomeToMirClass? outSrc)
        (execOutcomeToMirClass? outTgt) := by
  have hLt : a + b < modPow2 (uintWidth .u64) :=
    (sourceEntryPre_u64CheckedAdd_iff a b ha hb).1 hEntry
  have hNoUb :
      ¬ evalSourceBlockUnit u64CheckedAddSrc (env2 a b) .faultUB := by
    intro hUb
    have hCls := congrArg execOutcomeToMirExactClass?
      ((evalBlockWithGuards_iff_det _ _ _ _ _).1 hUb)
    have hOk := runMirCall_checked_add_ok .u64 .abort a b hLt
    dsimp only [PanicStrategy.toUnwindAction] at hOk
    rw [execOutcomeToMirExactClass?_evalBlockDet,
      u64CheckedAddSrc_corresponds_stepMirState a b ha hb, hOk] at hCls
    nomatch hCls
  have h :=
    semRefinesUnder_preserves_mirOptRefines_relational
      u64CheckedAdd_blockOptGate_to_unchecked hEntry hNoUb hTgt
  have ⟨outSrc, hSrc, hRef, _⟩ := h.2.2
  exact ⟨h.1, outSrc, hSrc, hRef⟩

/-! ## 5. Episode 1 Handoff Compatibility Checks -/

section Ep1Compat

universe u v w

theorem ep1_compat_postconditionDichotomy_rfl :
    @Anneal.Hybrid.PostconditionDichotomy.{u, v} =
      @Anneal.SpecRealizability.PostconditionDichotomy.{u, v} :=
  rfl

theorem ep1_compat_contractDeterministicOn_rfl :
    @Anneal.Hybrid.ContractDeterministicOn.{u, v, w} =
      @Anneal.SpecRealizability.ContractDeterministicOn.{u, v, w} :=
  rfl

theorem ep1_compat_contractDeterministic_rfl :
    @Anneal.Hybrid.ContractDeterministic.{u, v} =
      @Anneal.SpecRealizability.ContractDeterministic.{u, v} :=
  rfl

theorem ep1_compat_dichotomyModuloObservation_rfl :
    @Anneal.Hybrid.DichotomyModuloObservation.{u, v, w} =
      @Anneal.SpecRealizability.DichotomyModuloObservation.{u, v, w} :=
  rfl

end Ep1Compat

/-! Positive controls: with every non-defaulted field present both structures
elaborate, so each failure below is caused by the omitted field alone. -/

example : Anneal.Hybrid.EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

example : Anneal.Hybrid.FnContract Nat Nat Unit :=
  { effects := { terminates := true, noUnwind := true, noAbort := true } }

/--
error: Fields missing: `terminates`

Hint: Add missing fields:
  ,̲ ̲t̲e̲r̲m̲i̲n̲a̲t̲e̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.EffectMask :=
  { noUnwind := true, noAbort := true }

/--
error: Fields missing: `noUnwind`

Hint: Add missing fields:
  ,̲ ̲n̲o̲U̲n̲w̲i̲n̲d̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.EffectMask :=
  { terminates := true, noAbort := true }

/--
error: Fields missing: `noAbort`

Hint: Add missing fields:
  ,̲ ̲n̲o̲A̲b̲o̲r̲t̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.EffectMask :=
  { terminates := true, noUnwind := true }

/--
error: Fields missing: `effects`

Hint: Add missing fields:
  ,̲ ̲e̲f̲f̲e̲c̲t̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.FnContract Nat Nat Unit :=
  { safetyPre := fun _ => True, behaviorPre := fun _ => True }

/-! `effects` is the ONLY `FnContract` field without a default: with the three
postcondition fields supplied instead of the two preconditions, the report is
again exactly `effects`. A partial `EffectMask` nested in a `FnContract`
literal is rejected as well. -/

/--
error: Fields missing: `effects`

Hint: Add missing fields:
  ,̲ ̲e̲f̲f̲e̲c̲t̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.FnContract Nat Nat Unit :=
  { postReturn := fun _ _ _ => True, postUnwind := fun _ _ => True,
    postAbort := fun _ _ => True }

/--
error: Fields missing: `noAbort`

Hint: Add missing fields:
  ,̲ ̲n̲o̲A̲b̲o̲r̲t̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
example : Anneal.Hybrid.FnContract Nat Nat Unit :=
  { effects := { terminates := true, noUnwind := true } }

/-! ## 6. Exhaustive Programmatic Axiom & `._unsafe_rec` Sweep -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let unsafeRecSuffix : String := "_" ++ "unsafe_rec"
  let hasUnsafeRecName (n : Name) : Bool :=
    (n.toString.splitOn unsafeRecSuffix).length > 1
  let sameSet (xs ys : List Name) : Bool :=
    xs.all ys.contains && ys.all xs.contains
  let propextOnly : List Name := [``propext]
  let constructive : List Name := [``propext, ``Quot.sound]
  -- Audit ONE constant of any kind: no `unsafe_rec` companion in its name,
  -- type, or body; not `unsafe`, `partial`, an axiom, or an opaque; and every
  -- axiom it depends on is in `allowed`. Returns its kind (`1` theorem, `2`
  -- definition, `0` other) and its axioms.
  let auditConst (loc : String) (allowed : List Name) (c : Name)
      (ci : ConstantInfo) : CommandElabM (Nat × List Name) := do
    if hasUnsafeRecName c then
      throwError "audit: forbidden companion {c} in {loc}"
    for u in ci.type.getUsedConstants do
      if hasUnsafeRecName u then
        throwError "audit: type of {c} in {loc} uses {u}"
    if let some v := ci.value? then
      for u in v.getUsedConstants do
        if hasUnsafeRecName u then
          throwError "audit: body of {c} in {loc} uses {u}"
    if ci.isUnsafe || ci.isPartial then
      throwError "audit: unsafe or partial constant {c} in {loc}"
    let kind : Nat ← match ci with
      | .axiomInfo _ => throwError "audit: forbidden axiom {c} in {loc}"
      | .opaqueInfo _ => throwError "audit: forbidden opaque {c} in {loc}"
      | .thmInfo _ => pure 1
      | .defnInfo _ => pure 2
      | _ => pure 0
    let axs := (← liftCoreM <| Lean.collectAxioms c).toList
    for a in axs do
      if hasUnsafeRecName a then
        throwError "audit: {c} in {loc} references {a}"
      unless allowed.contains a do
        throwError "audit: {c} in {loc} uses axiom {a} (all={axs})"
    return (kind, axs)
  -- Audit EVERY constant of an imported module, pin its theorem and
  -- definition counts exactly, and pin the exact union of axioms the module
  -- uses. A count that is merely a floor goes stale as soon as declarations
  -- are added; an exact pin cannot drift in either direction.
  let auditModule (mod : Name)
      (allowed expected : List Name) (expThms expDefs expOther : Nat) :
      CommandElabM String := do
    let some idx := env.getModuleIdx? mod
      | throwError "audit: module {mod} is not imported"
    let mut nThm : Nat := 0
    let mut nDef : Nat := 0
    let mut nOther : Nat := 0
    let mut used : List Name := []
    for c in env.header.moduleData[idx]!.constNames do
      let some ci := env.find? c
        | throwError "audit: {c} of {mod} is not in the environment"
      let (kind, axs) ← auditConst mod.toString allowed c ci
      for a in axs do
        unless used.contains a do
          used := a :: used
      if kind == 1 then
        nThm := nThm + 1
      else if kind == 2 then
        nDef := nDef + 1
      else
        nOther := nOther + 1
    if nThm != expThms || nDef != expDefs || nOther != expOther then
      throwError
        "audit: {mod} count drift: thms={nThm}, defs={nDef}, aux={nOther}"
    unless sameSet used expected do
      throwError "audit: {mod} uses axioms {used}, expected {expected}"
    return s!"{mod}: {nThm} thms, {nDef} defs, {nOther} aux, axioms={used}"
  -- All counts (theorems, definitions, and auxiliaries) are exact pins.
  let r1 ← auditModule `Anneal.Hybrid propextOnly propextOnly 120 269 59
  let r2 ←
    auditModule `Anneal.Hybrid.Canaries propextOnly propextOnly 65 70 3
  let r3 ←
    auditModule `Anneal.Backend.Rules propextOnly propextOnly 95 316 47
  let r4 ←
    auditModule `Anneal.Backend.CtxFact propextOnly propextOnly 52 150 25
  let r5 ←
    auditModule `Anneal.Backend.CongruenceDagCtx propextOnly
      propextOnly 46 104 14
  let r6 ←
    auditModule `Anneal.Backend.PassRefines propextOnly propextOnly
      23 66 12
  let r7 ← auditModule `Anneal.Backend propextOnly [] 0 0 0
  let r8 ←
    auditModule `Anneal.Backend.Canaries propextOnly propextOnly 30 64 0
  let r9 ←
    auditModule `Anneal.HybridCertBridgesV2026 constructive constructive
      190 263 4
  -- Enforce an EXACT duplicate-free `Quot.sound` allowlist on
  -- `Anneal.HybridCertBridgesV2026`: every non-allowlisted constant must be
  -- `<= [propext]` (only exact allowlisted theorems and their direct
  -- compiler-generated `match_*` auxiliaries may use `Quot.sound`).
  let quotAllowed : List Name :=
    [ ``blockOptGate_cut_transports_to_mirCallTree_toPartial,
      ``blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv,
      ``u64_add_ctxFact_to_stepMirState_bridge,
      ``u64_sub_ctxFact_to_stepMirState_bridge,
      ``u64_add_farkasMirGate_to_stepMirState_bridge,
      ``u64_sub_farkasMirGate_to_stepMirState_bridge,
      ``u64_add_natCutIdxGate_to_stepMirState_bridge,
      ``u64_sub_natCutIdxGate_to_stepMirState_bridge,
      ``u64_add_farkas_and_blockOpt_cuts_to_stepMirState,
      ``u64_sub_farkas_and_blockOpt_cuts_to_stepMirState,
      ``u64_add_natCutIdx_and_blockOpt_cuts_to_stepMirState,
      ``u64_sub_natCutIdx_and_blockOpt_cuts_to_stepMirState,
      ``u64_addNuw_to_addWrap_asymmetric_ub_transport,
      ``u64_subNuw_to_subWrap_asymmetric_ub_transport,
      ``u64_add_blockOptGate_cut_to_stepMirState_env,
      ``u64_sub_blockOptGate_cut_to_stepMirState_env,
      ``u64_add_blockOptGate_cut_to_stepMirState_any_env,
      ``u64_add_blockOptGate_cut_to_stepMirState_wrapping_any_env,
      ``u64_sub_blockOptGate_cut_to_stepMirState_any_env,
      ``u64_sub_blockOptGate_cut_to_stepMirState_wrapping_any_env,
      ``neg_u64_add_undischarged_guard_elision_unsound,
      ``neg_u64_sub_undischarged_guard_elision_unsound ]
  let isMatchAuxOf (q c : Name) : Bool :=
    match c with
    | .str p s => p == q && s.startsWith "match_"
    | _ => false
  let mut seenAllow : List Name := []
  for q in quotAllowed do
    if seenAllow.contains q then
      throwError "audit: duplicate Quot.sound allowlist entry {q}"
    seenAllow := q :: seenAllow
  let some idxBr := env.getModuleIdx? `Anneal.HybridCertBridgesV2026
    | throwError "audit: Anneal.HybridCertBridgesV2026 not imported"
  let brConsts := env.header.moduleData[idxBr]!.constNames.toList
  let mut quotActual : List Name := []
  let mut quotMatchHelpers : Nat := 0
  for c in brConsts do
    let axs := (← liftCoreM <| Lean.collectAxioms c).toList
    if axs.contains ``Quot.sound then
      if quotAllowed.contains c then
        quotActual := c :: quotActual
      else if quotAllowed.any (fun q => isMatchAuxOf q c) then
        quotMatchHelpers := quotMatchHelpers + 1
      else
        throwError "audit: unexpected Quot.sound in {c} (axs={axs})"
  for q in quotAllowed do
    unless quotActual.contains q do
      throwError "audit: stale Quot.sound allowlist entry {q}"
  -- Transitive `unsafe_rec` audit. A companion `c._unsafe_rec` is a sibling of
  -- `c` and never one of its dependencies, so following `getUsedConstants`
  -- alone can never reach one. For every `Anneal.*` constant reachable from
  -- the 9 theory modules and this test module (plus every local constant in
  -- `env.constants.map₂`), the companion is looked up by name. The 10 audited
  -- modules must have none. The pre-existing base modules they build on do
  -- have some; that set is pinned exactly (duplicate-free), so a new
  -- well-founded dependency is reported instead of silently accepted.
  let theoryMods : List Name :=
    [ `Anneal.Hybrid, `Anneal.Hybrid.Canaries, `Anneal.Backend.Rules,
      `Anneal.Backend.CtxFact, `Anneal.Backend.CongruenceDagCtx,
      `Anneal.Backend.PassRefines, `Anneal.Backend, `Anneal.Backend.Canaries,
      `Anneal.HybridCertBridgesV2026 ]
  let mut work : List Name := []
  for m in theoryMods do
    let some idx := env.getModuleIdx? m
      | throwError "audit: module {m} is not imported"
    for c in env.header.moduleData[idx]!.constNames do
      work := c :: work
  for (c, _) in env.constants.map₂.toList do
    if env.contains (Name.str c unsafeRecSuffix) then
      throwError "audit: test constant {c} has a companion"
    work := c :: work
  let mut visited : NameSet := {}
  let mut annealTransitive : Nat := 0
  let mut baseCompanions : List Name := []
  while !work.isEmpty do
    match work with
    | [] => pure ()
    | n :: rest =>
      work := rest
      if visited.contains n then
        pure ()
      else
        visited := visited.insert n
        if hasUnsafeRecName n then
          throwError "audit: transitive forbidden companion {n}"
        if n.getRoot == `Anneal then
          annealTransitive := annealTransitive + 1
          if env.contains (Name.str n unsafeRecSuffix) then
            let owned : Bool :=
              match env.getModuleIdxFor? n with
              | none => true
              | some idx =>
                theoryMods.contains env.header.moduleNames[idx.toNat]!
            if owned then
              throwError "audit: audited constant {n} has a companion"
            baseCompanions := n :: baseCompanions
          if let some ci := env.find? n then
            for u in ci.type.getUsedConstants do
              if !visited.contains u then
                work := u :: work
            if let some v := ci.value? then
              for u in v.getUsedConstants do
                if !visited.contains u then
                  work := u :: work
  let expectedBaseCompanions : List Name :=
    [ ``Anneal.FarkasMirCert.checkNatSpecWitness,
      ``Anneal.FarkasMirCert.checkNatSpecFalsifies,
      ``Anneal.FarkasMirCert.checkIntSpecWitness,
      ``Anneal.FarkasMirCert.checkIntSpecFalsifies,
      ``Anneal.FarkasMirCert.evalNatLinExpr,
      ``Anneal.FarkasMirCert.evalIntLinExprSInt,
      ``Anneal.FarkasMirCert.listLookup?,
      ``Anneal.Mir.OverflowTrapRefinement.runMirSteps ]
  let mut seenBase : List Name := []
  for b in expectedBaseCompanions do
    if seenBase.contains b then
      throwError "audit: duplicate expectedBaseCompanions entry {b}"
    seenBase := b :: seenBase
  unless sameSet baseCompanions expectedBaseCompanions do
    throwError "audit: base constants with companions: {baseCompanions}"
  -- Sweep every constant defined so far in this test module, enforcing an
  -- exact duplicate-free `Quot.sound` allowlist on the test module as well.
  let testQuotAllowed : List Name :=
    [ ``test_backend_overflowTrap_e2e_add_sub,
      ``test_backend_blockOptGate_mirRefines_and_alt_bridges,
      ``test_backend_and_trap_negative_counterexamples,
      ``test_backend_cert_transport_to_stepMirState,
      ``test_backend_asymmetric_ub_transport,
      ``test_backend_every_environment_transport,
      ``test_backend_unchecked_sub_any_environment ]
  let mut seenTestQuot : List Name := []
  for tq in testQuotAllowed do
    if seenTestQuot.contains tq then
      throwError "audit: duplicate testQuotAllowed entry {tq}"
    seenTestQuot := tq :: seenTestQuot
  let mut testThms : Nat := 0
  let mut testDefs : Nat := 0
  let mut testOther : Nat := 0
  let mut testUsed : List Name := []
  let mut testQuotActual : List Name := []
  for (c, ci) in env.constants.map₂.toList do
    let (kind, axs) ← auditConst "the test module" constructive c ci
    if axs.contains ``Quot.sound then
      if testQuotAllowed.contains c then
        testQuotActual := c :: testQuotActual
      else if !testQuotAllowed.any (fun q => isMatchAuxOf q c) then
        throwError "audit: unexpected Quot.sound in test {c} (axs={axs})"
    for a in axs do
      unless testUsed.contains a do
        testUsed := a :: testUsed
    if kind == 1 then
      testThms := testThms + 1
    else if kind == 2 then
      testDefs := testDefs + 1
    else
      testOther := testOther + 1
  for tq in testQuotAllowed do
    unless testQuotActual.contains tq do
      throwError "audit: stale testQuotAllowed entry {tq}"
  if testThms != 29 || testDefs != 57 || testOther != 0 then
    throwError
      "audit: test drift: thms={testThms}, defs={testDefs}, aux={testOther}"
  let rT :=
    s!"test module: {testThms} thms, {testDefs} defs, {testOther} aux, " ++
    s!"axioms={testUsed}, quotAllowed={quotAllowed.length}+" ++
    s!"{quotMatchHelpers}m, testQuot={testQuotAllowed.length}, " ++
    s!"annealTransitive={annealTransitive}, " ++
    s!"baseCompanions={baseCompanions.length}"
  -- Pin the EXACT axiom set of every capstone, so a proof that starts to
  -- depend on a new axiom fails here even while it stays within the bound.
  let expectAxioms (expected : List Name) (cs : List Name) :
      CommandElabM Unit := do
    for c in cs do
      let axs := (← liftCoreM <| Lean.collectAxioms c).toList
      unless sameSet axs expected do
        throwError "audit: {c} uses axioms {axs}, expected {expected}"
  expectAxioms []
    [ ``verdictGate_false_never_ok,
      ``verdictGate_ok_eq_true,
      ``firstAccepted_ok_mem,
      ``farkasMirCertWeight_edge_length_le,
      ``farkasMirCert_empty_edge_size_and_weight,
      ``neg_execOutcomeToMirExactClass?_not_injective_unranged,
      ``gateVerdict_sound,
      ``gateVerdict_eq_true_iff_exists,
      ``farkasMirCertSize_le_weight,
      ``canonicalDiodeChunkGate_cut_sound,
      ``canonicalDiode_stream_all_emitted_canonical,
      ``canonicalDiode_stream_faithful_eq_filterAll,
      ``canonicalDiode_stream_halts_on_tampered_midstream,
      ``canonicalDiode_stream_prefix_eq_filterAll,
      ``obligationChunkGate_ok,
      ``obligationStream_all_emitted_hold,
      ``obligationStream_emitted_prefix,
      ``obligationStream_complete,
      ``transformChunkGate_ok,
      ``transformStream_all_emitted_valid,
      ``transformStream_emitted_prefix,
      ``transformStream_complete,
      ``transformStream_complete_exact,
      ``transformStream_table_entries ]
  expectAxioms propextOnly
    [ ``natCutIdxGate_cut_sound,
      ``intCutIdxGate_cut_sound,
      ``natCutDualGate_cut_sound,
      ``natCutDualGate_verdict_sound,
      ``intCutDualGate_verdict_sound,
      ``natCutPortfolio_sound,
      ``intCutPortfolio_sound,
      ``farkasMirGate_cut_sound,
      ``farkasMirBoundedEdgeGate_cut_sound,
      ``farkasMirBoundedEdgeGate_rejects_long_edge,
      ``farkasMirBoundedEdgeGate_accept_imp_farkasMirGate,
      ``farkasMirBoundedEdgeGate_eval_ok_imp_farkasMirGate,
      ``farkasMirBoundedEdgeGate_verdict_imp_farkasMirGate,
      ``neg_farkasMir_empty_edge_bomb_bounded,
      ``farkasMirPortfolio_sound,
      ``natCutIdxGate_discharges_uint_add_no_overflow,
      ``natCutIdxGate_discharges_uint_sub_no_underflow_certified,
      ``execOutcomeToMirExactClass?_injective_on_u64,
      ``mirOptExactOutcomeRefines_exec_iff_on_u64,
      ``execOutcomeToMirClass?_injective_on_u64,
      ``mirOptOutcomeRefines_exec_iff_on_u64,
      ``u64CheckedAddArena_evalArena_any_env,
      ``u64CheckedSubArena_evalArena_any_env,
      ``sourceEntryPre_u64CheckedAdd_any_env_iff,
      ``sourceEntryPre_u64CheckedSub_any_env_iff,
      ``semRefinesUnder_preserves_mirOptRefines,
      ``semRefinesUnder_preserves_mirOptRefines_relational,
      ``semRefinesUnder_preserves_mirOptRefines_asymmetric,
      ``blockOptGate_cut_preserves_mirRefines,
      ``blockOptGate_cut_transports_to_mirExecState,
      ``blockOptGate_cut_transports_to_mirExecState_equiv,
      ``u64_add_blockOptGate_cut_to_stepMirState,
      ``u64_add_blockOptGate_cut_to_stepMirState_wrapping,
      ``u64_sub_blockOptGate_cut_to_stepMirState,
      ``u64_sub_blockOptGate_cut_to_stepMirState_wrapping,
      ``neg_u64_add_unproven_elision_never_certified,
      ``neg_u64_sub_unproven_elision_never_certified,
      ``neg_u64_add_overflow_stepMirState_matrix,
      ``neg_u64_sub_underflow_stepMirState_matrix,
      ``neg_aborted_strategy_separation,
      ``abstractCost_boolCertCut_shrink,
      ``neg1_symmOnDirRefine_rejected,
      ``neg5_fuzzAndSorryCandidatesRejectedByGate,
      ``neg7_unconditionalGuardElision_unsound,
      ``neg10_reversedDropSubNuw_rejected ]
  -- `Quot.sound` enters only through `ITree.toPartial` statements (exact set)
  expectAxioms constructive quotAllowed
  let report :=
    "\n  ".intercalate [r1, r2, r3, r4, r5, r6, r7, r8, r9, rT]
  logInfo m!"ALL 10 MODULES AUDITED CLEAN:\n  {report}"

#print axioms natCutIdxGate_cut_sound
#print axioms intCutIdxGate_cut_sound
#print axioms natCutPortfolio_sound
#print axioms verdictGate_false_never_ok
#print axioms gateVerdict_sound
#print axioms gateVerdict_eq_true_iff_exists
#print axioms farkasMirGate_cut_sound
#print axioms farkasMirBoundedEdgeGate_cut_sound
#print axioms neg_farkasMir_empty_edge_bomb_bounded
#print axioms farkasMirBoundedEdgeGate_rejects_long_edge
#print axioms natCutIdxGate_discharges_uint_add_no_overflow
#print axioms natCutIdxGate_discharges_uint_sub_no_underflow_certified
#print axioms canonicalDiode_stream_all_emitted_canonical
#print axioms canonicalDiode_stream_faithful_eq_filterAll
#print axioms canonicalDiode_stream_prefix_eq_filterAll
#print axioms obligationStream_all_emitted_hold
#print axioms obligationStream_emitted_prefix
#print axioms obligationStream_complete
#print axioms transformChunkGate_ok
#print axioms transformStream_all_emitted_valid
#print axioms transformStream_emitted_prefix
#print axioms transformStream_complete
#print axioms transformStream_complete_exact
#print axioms transformStream_table_entries
#print axioms mirOptExactOutcomeRefines_exec_iff_on_u64
#print axioms semRefinesUnder_preserves_mirOptRefines_asymmetric
#print axioms blockOptGate_cut_preserves_mirRefines
#print axioms blockOptGate_cut_transports_to_mirExecState_equiv
#print axioms blockOptGate_cut_transports_to_mirCallTree_toPartial
#print axioms blockOptGate_cut_transports_to_mirCallTree_toPartial_equiv
#print axioms u64_add_farkas_and_blockOpt_cuts_to_stepMirState
#print axioms u64_sub_farkas_and_blockOpt_cuts_to_stepMirState
#print axioms u64_add_natCutIdx_and_blockOpt_cuts_to_stepMirState
#print axioms u64_sub_natCutIdx_and_blockOpt_cuts_to_stepMirState
#print axioms u64_addNuw_to_addWrap_asymmetric_ub_transport
#print axioms u64_subNuw_to_subWrap_asymmetric_ub_transport
#print axioms u64_add_blockOptGate_cut_to_stepMirState_env
#print axioms u64_sub_blockOptGate_cut_to_stepMirState_env
#print axioms u64_add_blockOptGate_cut_to_stepMirState_any_env
#print axioms u64_add_blockOptGate_cut_to_stepMirState_wrapping_any_env
#print axioms u64_sub_blockOptGate_cut_to_stepMirState_any_env
#print axioms u64_sub_blockOptGate_cut_to_stepMirState_wrapping_any_env
#print axioms u64_add_farkasMirGate_to_stepMirState_bridge
#print axioms u64_sub_natCutIdxGate_to_stepMirState_bridge
#print axioms neg_u64_add_undischarged_guard_elision_unsound
#print axioms neg_u64_add_unproven_elision_never_certified
#print axioms neg_aborted_strategy_separation
#print axioms abstractCost_boolCertCut_shrink
#print axioms test_linearArithIndexed_boolCertCut_discharges
#print axioms test_farkasMirGate_boolCertCut_variants
#print axioms test_natCutIdxGate_sub_evalScalarBinOp
#print axioms test_gateVerdict_withFallback_total_and_sound
#print axioms test_canonicalDiode_boolCertCut_and_valid_stream
#print axioms test_canonicalDiode_midstream_halt_and_prefix_characterization
#print axioms test_backend_overflowTrap_e2e_add_sub
#print axioms test_backend_cert_transport_to_stepMirState
#print axioms test_backend_asymmetric_ub_transport
#print axioms test_backend_every_environment_transport
#print axioms test_backend_unchecked_sub_any_environment
#print axioms test_obligation_stream_prefix_safe
#print axioms test_backend_transform_stream_prefix_safe
#print axioms test_backend_transform_stream_entries_and_prefix
#print axioms test_backend_outcome_bridge_faithful
#print axioms test_farkasMir_edge_weight_bounds
#print axioms test_backend_unproven_tier_elision_never_certified

end Anneal.Mir.HybridBackendCertGateTests
