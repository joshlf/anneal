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
   `intCutPortfolio` / dual-backend selection, and oversized/forged rejections.
2. **`Anneal.FarkasMirCert` (`farkasMirGate`):**
   concrete `BoolCertCut.seal _ _ rfl` discharges across `uintAddNoOverflow`,
   `uintSubNoUnderflowCertified`, `uintMulConstNoOverflow`, `sliceBounds`,
   `alignedStride`, `arrayToSliceCast`, and `natEntailmentAdequacy` (all four
   `FarkasMirCert` constructors), plus `farkasMirPortfolio`, `withFallback`,
   forged/oversized/mismatched rejections, and the `natCutIdxGate` ->
   `evalScalarBinOp` bridge.
3. **`Anneal.CanonicalDiode` (`canonicalDiodeChunkGate` + `foldStreamPrefix`):**
   concrete `BoolCertCut` and streaming checks over
   `Anneal.CanonicalDiode.Canaries.diode` and a strict-parser diode proving
   canonical emission on valid streams, immediate halt with zero emission of
   malformed or tampered chunks, and rejection of non-canonical/wrong-AST
   producer outputs.
4. **`Anneal.Backend` + `Anneal.Mir.OverflowTrapRefinement`:**
   end-to-end `blockOptGate` `BoolCertCut` + `stepMirState` `u64` checked-to-
   unchecked add/sub refinement via `farkasMirGate`, `natCutIdxGate`, and
   `CtxFact`, plus negative counterexamples (forged certs, `.symm` on
   `.refines`, `.refines` under `.freeze`, `.fuzz`/`.sorryStub` candidates,
   unsound overflow/underflow guard elision, `.diverged` distinctness, and
   `-C panic=abort` vs `-C panic=unwind` separation).
5. **Episode 1 Handoff Compatibility Pins:**
   exact `rfl` equalities between all four `Anneal.Hybrid` and
   `Anneal.SpecRealizability` realizability predicates, plus `#guard_msgs`
   negative elaboration checks confirming zero field defaults on
   `Anneal.Hybrid.EffectMask` and `Anneal.Hybrid.FnContract.effects`.
6. **Exhaustive Axiom & `._unsafe_rec` Audit (`run_cmd` + `#print axioms`):**
   sweeps every constant across all 9 new theory modules plus this test module.
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

/-- `farkasMirPortfolio`, `withFallback`, oversized / forged / mismatched
rejections, and the `natCutIdxGate` -> `evalScalarBinOp` arithmetic bridge. -/
theorem test_farkasMirGate_portfolio_rejections_and_idx_bridge
    (a b : Nat) (locals : List LocalSlot) (mem : Memory)
    (ha : a ≤ 1000000) (hb : b ≤ 250000) :
    -- Oversized rejection on `.triple` (size 13 > 10)
    Anneal.Hybrid.evalGate (E := Unit) (farkasMirGate 10) mirArrayCastGoal
      (.candidate () mirArrayCastCert) = .error (.witnessOversized 13 10) ∧
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
    -- `withFallback` yields fallback on total rejection
    Anneal.Hybrid.withFallback mirAddGoal
      (farkasMirPortfolio (E := Unit) 2 mirAddGoal
        [.candidate () mirAddCert])
      (fun _ => ()) = () ∧
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
  exact ⟨rfl, rfl, rfl, rfl, rfl, hIdxAdd.2.2.1, hIdxAdd.2.2.2⟩

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

/-- Negative streaming tests: malformed input (`strictFrameDiode.filter raw2 =
none`), tampered non-canonical output (`raw2`), and wrong-AST output (`raw3` for
`raw2`) halt `foldStreamPrefix` immediately and are never emitted. -/
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
    canonicalDiode_stream_halts_on_filter_none strictFrameDiode frameStream_lawful
      boolListBeq boolListBeq_eq
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
    (mirCallTree (mkUncheckedArithBody .u64 .add) (uintArgs2 .u64 a b)).toPartial ≤
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
    (mirCallTree (mkUncheckedArithBody .u64 .sub) (uintArgs2 .u64 c d)).toPartial ≤
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

/-! ## 6. Exhaustive Programmatic Axiom & `._unsafe_rec` Sweep -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let unsafeRecSuffix : String := "_" ++ "unsafe_rec"
  let hasUnsafeRecName (n : Name) : Bool :=
    (n.toString.splitOn unsafeRecSuffix).length > 1
  let checkNoUnsafeRecInInfo (mod : Name) (c : Name) (ci : ConstantInfo) :
      CommandElabM Unit := do
    if hasUnsafeRecName c then
      throwError "audit: forbidden companion {c} in {mod}"
    for u in ci.type.getUsedConstants do
      if hasUnsafeRecName u then
        throwError "audit: type of {c} in {mod} uses {u}"
    if let some v := ci.value? then
      for u in v.getUsedConstants do
        if hasUnsafeRecName u then
          throwError "audit: body of {c} in {mod} uses {u}"
  let isPropextOnly (a : Name) : Bool :=
    a == ``propext
  let isConstructive (a : Name) : Bool :=
    a == ``propext || a == ``Quot.sound
  let auditModule (mod : Name) (propextOnly : Bool)
      (minThms minDefs : Nat) : CommandElabM String := do
    let some idx := env.getModuleIdx? mod
      | throwError "audit: module {mod} is not imported"
    let mut nThm : Nat := 0
    let mut nDef : Nat := 0
    let mut nOther : Nat := 0
    let mut usedAxioms : List Name := []
    for c in env.header.moduleData[idx]!.constNames do
      match env.find? c with
      | some ci =>
        checkNoUnsafeRecInInfo mod c ci
        if ci.isUnsafe then
          throwError "audit: unsafe constant {c} in {mod}"
        match ci with
        | .axiomInfo _ =>
          throwError "audit: forbidden axiom {c} in {mod}"
        | .opaqueInfo _ =>
          throwError "audit: forbidden opaque {c} in {mod}"
        | .thmInfo _ =>
          let axs ← liftCoreM <| Lean.collectAxioms c
          for a in axs do
            if hasUnsafeRecName a then
              throwError "audit: {c} in {mod} references {a}"
            let ok := if propextOnly then isPropextOnly a else isConstructive a
            unless ok do
              throwError "audit: {c} in {mod} depends on disallowed axiom {a} (all={axs})"
            unless usedAxioms.contains a do
              usedAxioms := a :: usedAxioms
          nThm := nThm + 1
        | .defnInfo info =>
          if info.safety != .safe then
            throwError "audit: non-safe def {c} in {mod}"
          let axs ← liftCoreM <| Lean.collectAxioms c
          for a in axs do
            if hasUnsafeRecName a then
              throwError "audit: {c} in {mod} references {a}"
            let ok := if propextOnly then isPropextOnly a else isConstructive a
            unless ok do
              throwError "audit: {c} in {mod} depends on disallowed axiom {a} (all={axs})"
            unless usedAxioms.contains a do
              usedAxioms := a :: usedAxioms
          nDef := nDef + 1
        | _ =>
          nOther := nOther + 1
      | none => pure ()
    if nThm < minThms || nDef < minDefs then
      throwError "audit: vacuous floor in {mod}: thms={nThm} (<{minThms}), defs={nDef} (<{minDefs})"
    return s!"{mod}: {nThm} thms, {nDef} defs, {nOther} aux, axioms={usedAxioms}"
  let r1 ← auditModule `Anneal.Hybrid true 115 260
  let r2 ← auditModule `Anneal.Hybrid.Canaries true 60 65
  let r3 ← auditModule `Anneal.Backend.Rules true 90 310
  let r4 ← auditModule `Anneal.Backend.CtxFact true 50 145
  let r5 ← auditModule `Anneal.Backend.CongruenceDagCtx true 45 100
  let r6 ← auditModule `Anneal.Backend.PassRefines true 20 60
  let r7 ← auditModule `Anneal.Backend true 0 0
  let r8 ← auditModule `Anneal.Backend.Canaries true 30 60
  let r9 ← auditModule `Anneal.HybridCertBridgesV2026 false 80 120
  -- Sweep every constant defined in this test module
  let mut testThms : Nat := 0
  let mut testDefs : Nat := 0
  let mut testAxioms : List Name := []
  for (c, info) in env.constants.map₂.toList do
    checkNoUnsafeRecInInfo `HybridBackendCertGateTests c info
    if info.isUnsafe then
      throwError "audit: unsafe constant {c} in test module"
    match info with
    | .axiomInfo _ =>
      throwError "audit: forbidden axiom {c} in test module"
    | .opaqueInfo _ =>
      throwError "audit: forbidden opaque {c} in test module"
    | .thmInfo _ =>
      let axs ← liftCoreM <| Lean.collectAxioms c
      for a in axs do
        if hasUnsafeRecName a then
          throwError "audit: test theorem {c} references {a}"
        unless isConstructive a do
          throwError "audit: test theorem {c} depends on disallowed axiom {a} (all={axs})"
        unless testAxioms.contains a do
          testAxioms := a :: testAxioms
      testThms := testThms + 1
    | .defnInfo defn =>
      if defn.safety != .safe then
        throwError "audit: non-safe def {c} in test module"
      let axs ← liftCoreM <| Lean.collectAxioms c
      for a in axs do
        if hasUnsafeRecName a then
          throwError "audit: test def {c} references {a}"
        unless isConstructive a do
          throwError "audit: test def {c} depends on disallowed axiom {a} (all={axs})"
        unless testAxioms.contains a do
          testAxioms := a :: testAxioms
      testDefs := testDefs + 1
    | _ => pure ()
  if testThms < 12 || testDefs < 15 then
    throwError "audit: vacuous test floor: thms={testThms}, defs={testDefs}"
  logInfo m!"ALL 10 MODULES AUDITED CLEAN (0 Classical.choice, 0 sorryAx, 0 ofReduceBool, 0 unsafe_rec):
  {r1}
  {r2}
  {r3}
  {r4}
  {r5}
  {r6}
  {r7}
  {r8}
  {r9}
  test_module: {testThms} thms, {testDefs} defs, axioms={testAxioms}"

#print axioms Anneal.HybridCertBridgesV2026.natCutIdxGate_cut_sound
#print axioms Anneal.HybridCertBridgesV2026.intCutIdxGate_cut_sound
#print axioms Anneal.HybridCertBridgesV2026.natCutPortfolio_sound
#print axioms Anneal.HybridCertBridgesV2026.farkasMirGate_cut_sound
#print axioms Anneal.HybridCertBridgesV2026.natCutIdxGate_discharges_uint_add_no_overflow
#print axioms Anneal.HybridCertBridgesV2026.canonicalDiode_stream_all_emitted_canonical
#print axioms Anneal.HybridCertBridgesV2026.canonicalDiode_stream_faithful_eq_filterAll
#print axioms Anneal.HybridCertBridgesV2026.blockOptGate_cut_preserves_mirRefines
#print axioms Anneal.HybridCertBridgesV2026.u64_add_farkasMirGate_to_stepMirState_bridge
#print axioms Anneal.HybridCertBridgesV2026.u64_sub_natCutIdxGate_to_stepMirState_bridge
#print axioms Anneal.HybridCertBridgesV2026.neg_u64_add_undischarged_guard_elision_unsound
#print axioms Anneal.HybridCertBridgesV2026.neg_aborted_strategy_separation
#print axioms Anneal.Backend.Canaries.abstractCost_boolCertCut_shrink
#print axioms Anneal.Mir.HybridBackendCertGateTests.test_linearArithIndexed_boolCertCut_discharges
#print axioms Anneal.Mir.HybridBackendCertGateTests.test_farkasMirGate_boolCertCut_variants
#print axioms Anneal.Mir.HybridBackendCertGateTests.test_canonicalDiode_boolCertCut_and_valid_stream
#print axioms Anneal.Mir.HybridBackendCertGateTests.test_backend_overflowTrap_e2e_add_sub

end Anneal.Mir.HybridBackendCertGateTests
