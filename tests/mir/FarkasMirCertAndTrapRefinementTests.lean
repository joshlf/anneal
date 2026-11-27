-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Anneal.FarkasMirCert
import Anneal.Mir.OverflowTrapRefinement

/-!
# End-to-End Farkas MIR Bounds Certificate & Overflow-Trap Refinement Test Suite

Kernel-checked end-to-end tests covering:
1. Real `ci/farkas_cert_gen.py`-generated `CutStep` certificates replayed by `rfl` for:
   - `add_scaled` (`a + 4 * b < 2^64` and `2^32`) discharging both `Anneal.FarkasMirCert`
     and concrete `stepMirState` checked-to-unchecked elimination (`OverflowTrapRefinement`);
   - `u128` boundary addition (`a + b < 2^128`) checked-to-unchecked elimination;
   - `slice-range` (`ValidSliceRange` + `evalPtrOffset`), `slice-split` (`ValidSliceSplit`),
     and `non-overlapping-ptrs` (`NonOverlappingPtrs`);
   - `aligned-stride` with a genuine Chvatal-Gomory `CutStep.divCut` parity cut (`AlignedPtr`);
   - loop-bound `AiPcc` `WrappedInterval` and `MirAbsSlot.uint` refinement;
   - `uint-sub-no-underflow` (certified and range-hypothesized) + `stepMirState` checked-to-unchecked;
   - `uint-mul-const-no-overflow` + `stepMirState` checked-to-unchecked multiplication elimination.
2. Reflective Entailment-Graph adequacy non-vacuity, strictness, equivalence, multi-hop graph
   transitivity (`Nat` and `Int`), and negative fail-closed `= false` `rfl` checks.
3. Asymmetric overflow-trap refinement (`-C panic=abort` and `-C panic=unwind` `stepMirState`
   traces, unconditional `unchecked ⊑ checked`, `Trusted.Refinement.Partial` duality,
   `mirCallTree` / `WeakRef` bridges, and all 15 explicit negative soundness theorems).
4. Programmatic `run_cmd` soundness/hygiene audit over `Lean.collectAxioms` across all key
   declarations of `Anneal.FarkasMirCert`, `Anneal.Mir.OverflowTrapRefinement`, and this test
   module, plus `#print axioms` checks.
-/

namespace Anneal.Mir.FarkasMirCertAndTrapRefinementTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.ITree
open Anneal.LinearArith
open Anneal.AiPcc
open Anneal.UnsafeObligations
open Anneal.FarkasMirCert
open Anneal.Mir.OverflowTrapRefinement

/-! ## 1. End-to-End `ci/farkas_cert_gen.py`-Generated Certificates Replayed by `rfl` -/

/-! ### 1.1 `add_scaled` (`a + 4 * b < 2^64` and `2^32`) + Multi-Statement `stepMirState` Elimination -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-add-no-overflow --width 64 \
--     --hyp "a <= 1000000" --hyp "b <= 250000" --lhs-expr "a" --rhs-expr "4 * b" --json
private def addScaledHyps : List NatCutIneq :=
  [⟨.var 0, .cst 1000000⟩, ⟨.var 1, .cst 250000⟩]

private def addScaledCert : List CutStep :=
  [.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 4, .comb 3 1 2 1]

/-- End-to-end `u64` `add_scaled` (`a + 4 * b < 2^64`): discharges both `evalScalarBinOp`
overflow-freedom and multi-statement `stepMirState` checked-to-unchecked elimination under
both `-C panic=abort` and `-C panic=unwind` (constructively, zero `Classical.choice`). -/
theorem test_e2e_add_scaled_u64 (strat : PanicStrategy) (a b : Nat)
    (ha : a ≤ 1000000) (hb : b ≤ 250000) :
    a + 4 * b < modPow2 (uintWidth .u64) ∧
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody .u64 4 strat.toUnwindAction) 13 (uintArgs2 .u64 a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody .u64 4) 5 (uintArgs2 .u64 a b))) ∧
    (mirCallTree (mkUncheckedAddScaledBody .u64 4) (uintArgs2 .u64 a b)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody .u64 4 strat.toUnwindAction) (uintArgs2 .u64 a b)).toPartial := by
  have hF := farkas_discharges_u64_add_no_overflow
    addScaledHyps (.var 0) (.mulC 4 (.var 1)) addScaledCert rfl [a, b] [] canonInitMemory ha hb
  have hT := checked_add_scaled_refines_unchecked_of_farkas_cert
    .u64 4 strat addScaledHyps (.var 0) (.var 1) addScaledCert rfl rfl [a, b] ha hb
  exact ⟨hF.1, hT.2.1, hT.2.2⟩

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-add-no-overflow --width 32 \
--     --hyp "a <= 1000000" --hyp "b <= 250000" --lhs-expr "a" --rhs-expr "4 * b" --json
/-- End-to-end `u32` `add_scaled` (`a + 4 * b < 2^32`) checked-to-unchecked elimination. -/
theorem test_e2e_add_scaled_u32 (strat : PanicStrategy) (a b : Nat)
    (ha : a ≤ 1000000) (hb : b ≤ 250000) :
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody .u32 4 strat.toUnwindAction) 13 (uintArgs2 .u32 a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody .u32 4) 5 (uintArgs2 .u32 a b))) ∧
    (mirCallTree (mkUncheckedAddScaledBody .u32 4) (uintArgs2 .u32 a b)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody .u32 4 strat.toUnwindAction) (uintArgs2 .u32 a b)).toPartial := by
  have hT := checked_add_scaled_refines_unchecked_of_farkas_cert
    .u32 4 strat addScaledHyps (.var 0) (.var 1) addScaledCert rfl rfl [a, b] ha hb
  exact ⟨hT.2.1, hT.2.2⟩

/-! ### 1.2 `u128` Boundary Checked-to-Unchecked Addition Elimination -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-add-no-overflow --width 128 \
--     --hyp "a <= 340282366920938463463374607431768211356" --hyp "b <= 99" \
--     --lhs-expr "a" --rhs-expr "b" --json
private def u128BoundaryHyps : List NatCutIneq :=
  [⟨.var 0, .cst 340282366920938463463374607431768211356⟩, ⟨.var 1, .cst 99⟩]

private def u128BoundaryCert : List CutStep :=
  [.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 1, .comb 3 1 2 1]

/-- End-to-end `u128` boundary (`2^128 - 100 + 99 = 2^128 - 1 < 2^128`) checked-to-unchecked
addition elimination under both `-C panic=abort` and `-C panic=unwind`. -/
theorem test_e2e_u128_boundary_checked_add_elim (strat : PanicStrategy) (a b : Nat)
    (ha : a ≤ 340282366920938463463374607431768211356) (hb : b ≤ 99) :
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .add strat.toUnwindAction) 6 (uintArgs2 .u128 a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .add) 2 (uintArgs2 .u128 a b))) ∧
    (mirCallTree (mkUncheckedArithBody .u128 .add) (uintArgs2 .u128 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u128 .add strat.toUnwindAction) (uintArgs2 .u128 a b)).toPartial := by
  have hRev := checked_add_refines_unchecked_of_farkas_cert
    .u128 strat u128BoundaryHyps (.var 0) (.var 1) u128BoundaryCert rfl [a, b] ha hb
  have hEq := checked_add_equiv_unchecked_of_farkas_cert
    .u128 strat u128BoundaryHyps (.var 0) (.var 1) u128BoundaryCert rfl [a, b] ha hb
  exact ⟨hEq, hRev.2⟩

/-! ### 1.3 `slice-range`, `slice-split`, & `non-overlapping-ptrs` -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds slice-range \
--     --hyp "off <= 128" --hyp "len <= 64" --hyp "total >= 192" \
--     --offset-expr "off" --len-expr "len" --total-expr "total" --json
private def sliceRangeHyps : List NatCutIneq :=
  [⟨.var 0, .cst 128⟩, ⟨.var 1, .cst 64⟩, ⟨.cst 192, .var 2⟩]

private def sliceRangeCert : List CutStep :=
  [.hyp 0, .hyp 1, .hyp 2, .hyp 6, .comb 0 1 1 1, .comb 2 1 3 1, .comb 4 1 5 1]

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --domain nat --hyp "mid + right = total" --goal "mid + right <= total" --json
--   python3 -B ci/farkas_cert_gen.py --domain nat --hyp "mid + right = total" --goal "total <= mid + right" --json
private def sliceSplitHyps : List NatCutIneq :=
  [⟨.add (.var 0) (.var 1), .var 2⟩, ⟨.var 2, .add (.var 0) (.var 1)⟩]

private def sliceSplitCertLe : List CutStep :=
  [.hyp 0, .hyp 5, .comb 0 1 1 1]

private def sliceSplitCertGe : List CutStep :=
  [.hyp 1, .hyp 5, .comb 0 1 1 1]

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds non-overlapping-ptrs \
--     --hyp "src_off + count <= 256" --hyp "dst_off >= 256" \
--     --src-offset-expr "src_off" --dst-offset-expr "dst_off" --count-expr "count" \
--     --direction src-before-dst --json
private def nonOverlapHyps : List NatCutIneq :=
  [⟨.add (.var 0) (.var 2), .cst 256⟩, ⟨.cst 256, .var 1⟩]

private def nonOverlapCert : List CutStep :=
  [.hyp 0, .hyp 1, .hyp 5, .comb 0 1 1 1, .comb 3 1 2 1]

/-- End-to-end `ValidSliceRange`, `evalPtrOffset`, `ValidSliceSplit`, and
`NonOverlappingPtrs` discharged from `ci/farkas_cert_gen.py` certificates. -/
theorem test_e2e_slice_split_and_non_overlapping
    (rp src dst : RawPtrVal) (elemSize len total mid right count : Nat)
    (hOff : rp.offset ≤ 128) (hLen : len ≤ 64) (hTot : 192 ≤ total)
    (hSplit1 : mid + right ≤ total) (hSplit2 : total ≤ mid + right)
    (hSrc : src.offset + count ≤ 256) (hDst : 256 ≤ dst.offset) :
    ValidSliceRange rp len total ∧
    evalPtrOffset rp len total = some { rp with offset := rp.offset + len } ∧
    ValidSliceSplit rp elemSize total mid right ∧
    evalPtrOffset rp (mid * elemSize) (rp.offset + total * elemSize) =
      some (sliceSplitRightPtr rp elemSize mid) ∧
    NonOverlappingPtrs src dst count := by
  have hRange := farkas_discharges_slice_bounds
    sliceRangeHyps (.var 0) (.var 1) (.var 2) sliceRangeCert rfl
    [rp.offset, len, total] rp rfl hOff hLen hTot
  have hSplit := farkas_discharges_slice_split
    sliceSplitHyps (.var 0) (.var 1) (.var 2) sliceSplitCertLe sliceSplitCertGe
    rfl rfl [mid, right, total] rp elemSize hSplit1 hSplit2
  have hNonOv := farkas_discharges_non_overlapping_ptrs
    nonOverlapHyps (.var 0) (.var 1) (.var 2) .srcBeforeDst nonOverlapCert rfl
    [src.offset, dst.offset, count] src dst rfl rfl hSrc hDst
  exact ⟨hRange.1, hRange.2, hSplit.1, hSplit.2, hNonOv⟩

/-! ### 1.4 `aligned-stride` with Genuine Chvatal-Gomory `CutStep.divCut` -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds aligned-stride --align 8 \
--     --hyp "2 * z <= 1" --hyp "8 * q <= off + 2 * z" --hyp "off <= 8 * q + 2 * z" \
--     --offset-expr "off" --quot-expr "q" --json
private def alignedStrideHyps : List NatCutIneq :=
  [ ⟨.mulC 2 (.var 2), .cst 1⟩
  , ⟨.mulC 8 (.var 1), .add (.var 0) (.mulC 2 (.var 2))⟩
  , ⟨.var 0, .add (.mulC 8 (.var 1)) (.mulC 2 (.var 2))⟩ ]

private def alignedStrideCertLe : List CutStep :=
  [.hyp 1, .hyp 6, .hyp 0, .divCut 2 2, .comb 0 1 1 1, .comb 4 1 3 2]

private def alignedStrideCertGe : List CutStep :=
  [.hyp 2, .hyp 6, .hyp 0, .divCut 2 2, .comb 0 1 1 1, .comb 4 1 3 2]

/-- End-to-end `AlignedPtr rp 8` discharged via `ci/farkas_cert_gen.py`'s `CutStep.divCut 2`
parity/stride cut certificate (not derivable by rational Farkas combinations alone). -/
theorem test_e2e_aligned_stride_divcut (rp : RawPtrVal) (q z : Nat)
    (hz : 2 * z ≤ 1) (h1 : 8 * q ≤ rp.offset + 2 * z) (h2 : rp.offset ≤ 8 * q + 2 * z) :
    AlignedPtr rp 8 :=
  farkas_discharges_aligned_stride
    alignedStrideHyps 8 (.var 0) (.var 1) alignedStrideCertLe alignedStrideCertGe
    rfl rfl rfl [rp.offset, q, z] rp rfl hz h1 h2

/-! ### 1.5 Loop-Bound `AiPcc` `WrappedInterval` & `MirAbsSlot.uint` Refinement -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds aipcc-interval-refine --width 32 \
--     --var i --src-lo 0 --src-hi 1024 --hyp "i >= 4" --hyp "i + 8 <= 100" \
--     --target-lo 4 --target-hi 92 --json
private def aipccLoopHyps : List NatCutIneq :=
  [ ⟨.cst 0, .var 0⟩
  , ⟨.var 0, .cst 1024⟩
  , ⟨.cst 4, .var 0⟩
  , ⟨.add (.var 0) (.cst 8), .cst 100⟩ ]

private def aipccLoopCertLo : List CutStep :=
  [.hyp 2, .hyp 5, .comb 0 1 1 1]

private def aipccLoopCertHi : List CutStep :=
  [.hyp 3, .hyp 5, .comb 0 1 1 1]

/-- End-to-end loop-bound `AiPcc` `WrappedInterval` and `MirAbsSlot.uint` refinement
using `ci/farkas_cert_gen.py`-generated certificates. -/
theorem test_e2e_aipcc_loop_interval_refinement
    (ty : Ty) (locals : List LocalSlot) (t : Tnum) (sg : StridedCong) (sc : ScalarInt)
    (hSlot : (MirAbsSlot.uint .u32 ⟨.init, t, .iv 0 1024, sg⟩).denote ty locals
      (.init (.scalar sc)))
    (hLo : 4 ≤ sc.bits) (hHi : sc.bits + 8 ≤ 100) :
    WrappedInterval.denote (modPow2 (uintWidth .u32)) (.iv 4 92) sc.bits ∧
    (MirAbsSlot.uint .u32 ⟨.init, t, .iv 4 92, sg⟩).denote ty locals (.init (.scalar sc)) ∧
    (MirAbsSlot.uint .u32
      (reduceAbsVal (uintWidth .u32)
        ⟨.init, t,
         WrappedInterval.meet (modPow2 (uintWidth .u32)) (.iv 0 1024) (.iv 4 92),
         sg⟩)).denote ty locals (.init (.scalar sc)) := by
  have hB := mirAbsSlot_uint_iv_bounds rfl hSlot
  have hWi := farkas_discharges_aipcc_interval_refinement
    aipccLoopHyps (modPow2 (uintWidth .u32)) 4 92 (.var 0)
    aipccLoopCertLo aipccLoopCertHi rfl rfl rfl rfl [sc.bits] hB.1 hB.2.1 hLo hHi
  have hSlotRef := farkas_refines_mirAbsSlot_uint .u32
    aipccLoopHyps 4 92 (.var 0) aipccLoopCertLo aipccLoopCertHi
    rfl rfl rfl rfl [sc.bits] ty locals ⟨.init, t, .iv 0 1024, sg⟩ sc hSlot rfl
    hB.1 hB.2.1 hLo hHi
  exact ⟨hWi, hSlotRef.1, hSlotRef.2⟩

/-! ### 1.6 `uint-sub-no-underflow` (Certified) + `stepMirState` Sub Elimination -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-sub-no-underflow --width 32 \
--     --hyp "b + 16 <= a" --hyp "a <= 4096" --lhs-expr "a" --rhs-expr "b" --json
private def uintSubHyps : List NatCutIneq :=
  [⟨.add (.var 1) (.cst 16), .var 0⟩, ⟨.var 0, .cst 4096⟩]

private def uintSubCertLe : List CutStep :=
  [.hyp 0, .hyp 4, .comb 0 1 1 1]

private def uintSubCertRange : List CutStep :=
  [.hyp 1, .hyp 4, .comb 0 1 1 1]

/-- End-to-end certified `u32` subtraction underflow-freedom + `stepMirState`
checked-to-unchecked subtraction elimination (no external range hypothesis). -/
theorem test_e2e_uint_sub_certified_elim (strat : PanicStrategy) (a b : Nat)
    (hGap : b + 16 ≤ a) (hBound : a ≤ 4096) :
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u32 .sub strat.toUnwindAction) 6 (uintArgs2 .u32 a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u32 .sub) 2 (uintArgs2 .u32 a b))) ∧
    (mirCallTree (mkUncheckedArithBody .u32 .sub) (uintArgs2 .u32 a b)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u32 .sub strat.toUnwindAction) (uintArgs2 .u32 a b)).toPartial :=
  checked_sub_refines_unchecked_of_farkas_cert_certified
    .u32 strat uintSubHyps (.var 0) (.var 1) uintSubCertLe uintSubCertRange
    rfl rfl [a, b] hGap hBound

/-- End-to-end range-hypothesized `u32` subtraction checked-to-unchecked elimination. -/
theorem test_e2e_uint_sub_range_elim (strat : PanicStrategy) (a b : Nat)
    (hRange : a < modPow2 (uintWidth .u32)) (hGap : b + 16 ≤ a) (hBound : a ≤ 4096) :
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u32 .sub strat.toUnwindAction) 6 (uintArgs2 .u32 a b)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u32 .sub) 2 (uintArgs2 .u32 a b))) :=
  (checked_sub_refines_unchecked_of_farkas_cert
    .u32 strat uintSubHyps (.var 0) (.var 1) uintSubCertLe rfl [a, b] hRange hGap hBound).1

/-! ### 1.7 `uint-mul-const-no-overflow` + `stepMirState` Mul Elimination -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-mul-const-no-overflow --width 64 \
--     --hyp "n <= 4096" --scale 16 --var n --json
private def uintMulConstHyps : List NatCutIneq :=
  [⟨.var 0, .cst 4096⟩]

private def uintMulConstCert : List CutStep :=
  [.hyp 0, .hyp 2, .comb 0 16 1 1]

/-- End-to-end `u64` constant-scaled multiplication (`16 * n < 2^64`) checked-to-unchecked
elimination over `stepMirState` and `mirCallTree`. -/
theorem test_e2e_uint_mul_const_elim (strat : PanicStrategy) (n : Nat) (hn : n ≤ 4096) :
    UintScalarInRange .u64 ⟨16, uintBytes .u64⟩ ∧
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u64 .mul strat.toUnwindAction) 6 (uintArgs2 .u64 16 n)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u64 .mul) 2 (uintArgs2 .u64 16 n))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .mul) (uintArgs2 .u64 16 n)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .mul strat.toUnwindAction) (uintArgs2 .u64 16 n)).toPartial :=
  checked_mul_const_refines_unchecked_of_farkas_cert
    .u64 strat uintMulConstHyps 16 (.var 0) uintMulConstCert rfl rfl [n] hn

/-! ## 2. Entailment-Graph Adequacy Non-Vacuity, Strictness, Transitivity, & Negative Checks -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --entailment-check --domain nat \
--     --pre "x <= 10" --pre "y <= 20" --obligation "x + y <= 40" \
--     --witness "x=0,y=0" --strict-witness "x=15,y=25" --json
theorem test_entailment_nat_strict_and_sufficient :
    NatEntailmentAdequacyProp
      [⟨.var 0, .cst 10⟩, ⟨.var 1, .cst 20⟩]
      [⟨.add (.var 0) (.var 1), .cst 40⟩]
      (.strict [15, 25]) ∧
    NatEntailmentAdequacyProp
      [⟨.var 0, .cst 10⟩, ⟨.var 1, .cst 20⟩]
      [⟨.add (.var 0) (.var 1), .cst 40⟩]
      .sufficientOnly :=
  ⟨farkas_entailment_adequacy_cert
     [⟨.var 0, .cst 10⟩, ⟨.var 1, .cst 20⟩]
     [⟨.add (.var 0) (.var 1), .cst 40⟩]
     [[.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 1, .comb 3 1 2 1]]
     [0, 0]
     (.strict [15, 25])
     rfl,
   farkas_entailment_adequacy_cert
     [⟨.var 0, .cst 10⟩, ⟨.var 1, .cst 20⟩]
     [⟨.add (.var 0) (.var 1), .cst 40⟩]
     [[.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 1, .comb 3 1 2 1]]
     [0, 0]
     .sufficientOnly
     rfl⟩

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --entailment-check --domain nat \
--     --pre "x + 2 <= y" --obligation "x + 5 <= y + 3" --witness "x=0,y=2" --check-equiv --json
theorem test_entailment_nat_equiv :
    NatEntailmentAdequacyProp
      [⟨.add (.var 0) (.cst 2), .var 1⟩]
      [⟨.add (.var 0) (.cst 5), .add (.var 1) (.cst 3)⟩]
      (.equiv [[.hyp 0, .hyp 3, .comb 0 1 1 1]]) :=
  farkas_entailment_adequacy_cert
    [⟨.add (.var 0) (.cst 2), .var 1⟩]
    [⟨.add (.var 0) (.cst 5), .add (.var 1) (.cst 3)⟩]
    [[.hyp 0, .hyp 3, .comb 0 1 1 1]]
    [0, 2]
    (.equiv [[.hyp 0, .hyp 3, .comb 0 1 1 1]])
    rfl

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --entailment-check --domain int \
--     --pre "-4 <= x" --pre "x <= 6" --obligation "-8 <= x" \
--     --witness "x=-1" --strict-witness "x=-6" --json
theorem test_entailment_int_strict_and_equiv :
    IntEntailmentAdequacyProp
      [⟨.cst ⟨true, 4⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 6⟩⟩]
      [⟨.cst ⟨true, 8⟩, .var 0⟩]
      (.strict [Int.negOfNat 6]) ∧
    IntEntailmentAdequacyProp
      [⟨.cst ⟨true, 4⟩, .var 0⟩]
      [⟨.cst ⟨true, 4⟩, .var 0⟩]
      (.equiv [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) :=
  ⟨farkas_int_entailment_adequacy_cert
     [⟨.cst ⟨true, 4⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 6⟩⟩]
     [⟨.cst ⟨true, 8⟩, .var 0⟩]
     [[.hyp 0, .hyp 2, .comb 0 1 1 1]]
     [Int.negOfNat 1]
     (.strict [Int.negOfNat 6])
     rfl,
   farkas_int_entailment_adequacy_cert
     [⟨.cst ⟨true, 4⟩, .var 0⟩]
     [⟨.cst ⟨true, 4⟩, .var 0⟩]
     [[.hyp 0, .hyp 1, .comb 0 1 1 1]]
     [Int.ofNat 0]
     (.equiv [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
     rfl⟩

/-- Multi-hop `EntailmentGraph` transitivity over `Nat` (`0 → 1 → 2 → 3`) and `Int` (`0 → 1 → 2`). -/
theorem test_entailment_graph_multi_hop :
    (let gNat : NatEntailmentGraph :=
      { nodes := [[⟨.var 0, .cst 2⟩], [⟨.var 0, .cst 4⟩],
                  [⟨.var 0, .cst 8⟩], [⟨.var 0, .cst 16⟩]]
        edges :=
          [ (0, 1, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
          , (1, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
          , (2, 3, [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) ] }
     ∃ src dst,
       listLookup? gNat.nodes 0 = some src ∧
       listLookup? gNat.nodes 3 = some dst ∧
       (∀ env : List Nat, src.holds env → dst.holds env)) ∧
    (let gInt : IntEntailmentGraph :=
      { nodes := [[⟨.cst ⟨true, 4⟩, .var 0⟩], [⟨.cst ⟨true, 8⟩, .var 0⟩],
                  [⟨.cst ⟨true, 16⟩, .var 0⟩]]
        edges :=
          [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
          , (1, 2, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] }
     ∃ src dst,
       listLookup? gInt.nodes 0 = some src ∧
       listLookup? gInt.nodes 2 = some dst ∧
       (∀ env : List Int, src.holds env → dst.holds env)) :=
  ⟨checkNatGraphIndexPath_sound (g :=
     { nodes := [[⟨.var 0, .cst 2⟩], [⟨.var 0, .cst 4⟩],
                 [⟨.var 0, .cst 8⟩], [⟨.var 0, .cst 16⟩]]
       edges :=
         [ (0, 1, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
         , (1, 2, [[.hyp 0, .hyp 2, .comb 0 1 1 1]])
         , (2, 3, [[.hyp 0, .hyp 2, .comb 0 1 1 1]]) ] })
     rfl [1, 2, 3] 0 3 rfl,
   checkIntGraphIndexPath_sound (g :=
     { nodes := [[⟨.cst ⟨true, 4⟩, .var 0⟩], [⟨.cst ⟨true, 8⟩, .var 0⟩],
                 [⟨.cst ⟨true, 16⟩, .var 0⟩]]
       edges :=
         [ (0, 1, [[.hyp 0, .hyp 1, .comb 0 1 1 1]])
         , (1, 2, [[.hyp 0, .hyp 1, .comb 0 1 1 1]]) ] })
     rfl [1, 2] 0 2 rfl⟩

/-- Negative fail-closed `rfl` checks (`= false`) for vacuous preconditions, bad witnesses,
invalid strict witnesses, false equivalence claims, and unprovable obligations. -/
theorem test_entailment_negative_fail_closed :
    -- Vacuous precondition (`1 ≤ 0`) fails non-vacuity check
    checkNatEntailmentAdequacy [⟨.cst 1, .cst 0⟩] [⟨.var 0, .cst 0⟩]
      [[.hyp 0]] [0] .sufficientOnly = false ∧
    -- Bad sat witness (`x = 11` violates `x ≤ 10`)
    checkNatEntailmentAdequacy [⟨.var 0, .cst 10⟩] [⟨.var 0, .cst 20⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [11] .sufficientOnly = false ∧
    -- Invalid strict witness (`x = 5` satisfies `pre`, so does not prove strictness)
    checkNatEntailmentAdequacy [⟨.var 0, .cst 10⟩] [⟨.var 0, .cst 20⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] (.strict [5]) = false ∧
    -- Invalid strict witness (`x = 25` falsifies `obligation`)
    checkNatEntailmentAdequacy [⟨.var 0, .cst 10⟩] [⟨.var 0, .cst 20⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] (.strict [25]) = false ∧
    -- Unprovable obligation (`x ≤ 20` does not entail `x ≤ 10`)
    checkNatEntailmentAdequacy [⟨.var 0, .cst 20⟩] [⟨.var 0, .cst 10⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [0] .sufficientOnly = false ∧
    -- Int bad strict witness (`x = -2` satisfies `-4 ≤ x ≤ 6`)
    checkIntEntailmentAdequacy
      [⟨.cst ⟨true, 4⟩, .var 0⟩, ⟨.var 0, .cst ⟨false, 6⟩⟩]
      [⟨.cst ⟨true, 8⟩, .var 0⟩]
      [[.hyp 0, .hyp 2, .comb 0 1 1 1]] [Int.negOfNat 1] (.strict [Int.negOfNat 2]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Asymmetric Trap Refinement, `Partial` Duality, & All 15 Negative Soundness Canaries -/

/-- Concrete `stepMirState` traces for both `-C panic=abort` and `-C panic=unwind`,
plus unconditional `unchecked ⊑ checked` on BOTH overflowing and non-overflowing inputs,
fuel monotonicity, `Partial` duality, and `mirCallTree` / `WeakRef` bridges. -/
theorem test_asymmetric_trap_refinement_traces_and_bridges :
    -- Concrete abort vs unwind traces on overflowing u8 add (200 + 100)
    runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100) = .halted .abort ∧
    runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100) = .halted .panic ∧
    -- Fuel monotonicity: larger fuel preserves halted outcome and .ub fault
    runMirCall (mkCheckedArithBody .u8 .add .terminate) 20 (uintArgs2 .u8 200 100) = .halted .abort ∧
    runMirCall (mkUncheckedArithBody .u8 .add) 20 (uintArgs2 .u8 200 100) = .faulted .ub ∧
    -- Unconditional forward refinement on overflowing u8 add under abort and unwind
    MirOutcomeRefines
      (classifyMirExecState .abort (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100)))
      (classifyMirExecState .abort (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100))) ∧
    MirOutcomeRefines
      (classifyMirExecState .unwind (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100)))
      (classifyMirExecState .unwind (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100))) ∧
    -- Unconditional forward refinement on non-overflowing u8 add (100 + 50 = 150)
    MirOutcomeRefines
      (classifyMirExecState .abort (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 100 50)))
      (classifyMirExecState .abort (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 100 50))) ∧
    -- Unconditional forward refinement on underflowing u8 sub (3 - 5) and overflowing u8 mul (20 * 20)
    (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 3 5)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 3 5)).toPartial ∧
    (mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 20 20)).toPartial ≤
      (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 20 20)).toPartial ∧
    -- Trusted.Refinement.Partial exact duality
    ((MirOutcomeClass.trap (Val := Value)).toPartial ≤ (MirOutcomeClass.ub (Val := Value)).toPartial) ∧
    (¬ ((MirOutcomeClass.ub (Val := Value)).toPartial ≤ (MirOutcomeClass.trap (Val := Value)).toPartial)) ∧
    (¬ ((MirExactOutcomeClass.trap (Val := Value) .panic).toPartial ≤
        (MirExactOutcomeClass.trap (Val := Value) .abort).toPartial)) := by
  have hOvAdd : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hAbort6 := runMirCall_checked_add_trap .u8 .abort 200 100 hOvAdd
  have hUnwind6 := runMirCall_checked_add_trap .u8 .unwind 200 100 hOvAdd
  have hUb2 := runMirCall_unchecked_add_ub .u8 200 100 hOvAdd
  refine ⟨hAbort6, hUnwind6,
    runMirSteps_halted_mono _ 6 14 _ _ hAbort6,
    runMirSteps_ub_mono _ 2 18 _ hUb2,
    (unchecked_add_refines_to_checked .u8 .abort 200 100).1,
    (unchecked_add_refines_to_checked .u8 .unwind 200 100).1,
    (unchecked_add_refines_to_checked .u8 .abort 100 50).1,
    (unchecked_sub_refines_to_checked .u8 .unwind 3 5
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)).2.2,
    (unchecked_mul_refines_to_checked .u8 .abort 20 20).2.2,
    (mirOutcomeRefines_iff_partial_le .ub .trap).1 trivial,
    fun h => trap_not_refines_ub ((mirOutcomeRefines_iff_partial_le .trap .ub).2 h),
    fun h => by
      have hEx := (mirExactOutcomeRefines_iff_partial_le (.trap .abort) (.trap .panic)).2 h
      nomatch hEx⟩

/-- Coinductive `Anneal.ITree.WeakRef` bridge canaries (forward, Farkas reverse, & negative). -/
theorem test_weakRef_bridge_canaries (a b : Nat) (ha : a ≤ 1000000) (hb : b ≤ 250000) :
    WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100))
      (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100)) ∧
    WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 3 5))
      (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 3 5)) ∧
    WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 20 20))
      (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 20 20)) ∧
    WeakRef
      (mirCallTree (mkUncheckedAddScaledBody .u64 4) (uintArgs2 .u64 a b))
      (mirCallTree (mkCheckedAddScaledBody .u64 4 .terminate) (uintArgs2 .u64 a b)) ∧
    ¬ WeakRef
      (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)) ∧
    ¬ WeakRef
      (mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100)) ∧
    ¬ WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)) :=
  ⟨unchecked_add_weakRef_to_checked .u8 .abort 200 100,
   unchecked_sub_weakRef_to_checked .u8 .unwind 3 5
     (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl),
   unchecked_mul_weakRef_to_checked .u8 .abort 20 20,
   checked_add_scaled_weakRef_unchecked_of_farkas_cert
     .u64 4 .abort addScaledHyps (.var 0) (.var 1) addScaledCert rfl [a, b] ha hb,
   (checked_add_overflow_not_weakRef_corollaries .abort).1,
   (checked_add_overflow_not_weakRef_corollaries .unwind).2.1,
   (checked_add_overflow_not_weakRef_corollaries .abort).2.2⟩

/-- Direct instantiation of all 15 explicit negative soundness theorems (for both
`-C panic=abort` and `-C panic=unwind` where strategy-parameterized). -/
theorem test_all_fifteen_negative_soundness_theorems :
    (¬ MirOutcomeRefines .trap (.ret (Value.scalar ⟨44, 1⟩))) ∧
    (¬ MirOutcomeRefines (Val := Value) .trap .ub) ∧
    (¬ MirOutcomeRefines (Val := Value) .trap .unsupported) ∧
    (¬ MirOutcomeRefines (.ret (Value.scalar ⟨44, 1⟩)) .ub) ∧
    (¬ MirOutcomeRefines (.ret (Value.scalar ⟨44, 1⟩)) .trap) ∧
    (¬ MirOutcomeRefines (.ret (Value.scalar ⟨44, 1⟩)) .unsupported) ∧
    (¬ MirOutcomeRefines (.ret (Value.scalar ⟨44, 1⟩)) (.ret (Value.scalar ⟨45, 1⟩))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecState .unwind
        (runMirCall (mkWrappingArithBody .u8 .add) 2 (uintArgs2 .u8 200 100)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .sub .terminate) 6 (uintArgs2 .u8 3 5)))
      (classifyMirExecState .abort
        (runMirCall (mkWrappingArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .mul .continue_) 6 (uintArgs2 .u8 20 20)))
      (classifyMirExecState .unwind
        (runMirCall (mkWrappingArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .sub .continue_) 6 (uintArgs2 .u8 3 5)))
      (classifyMirExecState .unwind
        (runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 3 5)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .mul .terminate) 6 (uintArgs2 .u8 20 20)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .mul) 2 (uintArgs2 .u8 20 20)))) ∧
    (¬ MirExactOutcomeRefines
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecStateExact
        (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedAddScaledBody .u8 4 .terminate) 13 (uintArgs2 .u8 200 20)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 200 20)))) :=
  ⟨trap_not_refines_ret _,
   trap_not_refines_ub,
   trap_not_refines_unsupported,
   ret_not_refines_ub _,
   ret_not_refines_trap _,
   ret_not_refines_unsupported _,
   ret_distinct_not_refines (fun h => by injection h with hs; injection hs with hb; nomatch hb),
   (checked_add_overflow_not_refines_unchecked .abort).2.2.1,
   (checked_add_overflow_not_refines_wrapping .unwind).2.2.1,
   (checked_sub_underflow_not_refines_wrapping .abort).2.2.1,
   (checked_mul_overflow_not_refines_wrapping .unwind).2.2.1,
   (checked_sub_underflow_not_refines_unchecked .unwind).2.2.1,
   (checked_mul_overflow_not_refines_unchecked .abort).2.2.1,
   panic_strategy_abort_vs_unwind_distinct.2.2.1,
   (checked_add_scaled_overflow_not_refines_unchecked .abort).2.2.1⟩

/-! ## 4. Programmatic `run_cmd` Hygiene Audit & `#print axioms` Checks -/

open Lean Elab Command in
run_cmd do
  let isConstructive (a : Name) : Bool :=
    a == ``propext || a == ``Quot.sound
  let isStandard (a : Name) : Bool :=
    a == ``propext || a == ``Quot.sound || a == ``Classical.choice
  -- Non-vacuity self-checks on both audit predicates:
  for banned in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler, ``Classical.choice] do
    if isConstructive banned then
      throwError "constructive predicate self-check failed: accepted {banned}"
  for banned in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler] do
    if isStandard banned then
      throwError "standard predicate self-check failed: accepted {banned}"
  let keyFarkasDecls : List Name :=
    [ ``Anneal.FarkasMirCert.farkas_discharges_uint_add_no_overflow
    , ``Anneal.FarkasMirCert.farkas_discharges_u64_add_no_overflow
    , ``Anneal.FarkasMirCert.farkas_discharges_uint_sub_no_underflow
    , ``Anneal.FarkasMirCert.farkas_discharges_uint_sub_no_underflow_certified
    , ``Anneal.FarkasMirCert.farkas_discharges_uint_mul_const_no_overflow
    , ``Anneal.FarkasMirCert.farkas_discharges_uint_mul_const_right_no_overflow
    , ``Anneal.FarkasMirCert.farkas_discharges_slice_bounds
    , ``Anneal.FarkasMirCert.farkas_discharges_slice_split
    , ``Anneal.FarkasMirCert.farkas_discharges_aligned_stride
    , ``Anneal.FarkasMirCert.farkas_discharges_non_overlapping_ptrs
    , ``Anneal.FarkasMirCert.farkas_discharges_array_to_slice_cast
    , ``Anneal.FarkasMirCert.farkas_discharges_aipcc_interval_refinement
    , ``Anneal.FarkasMirCert.farkas_refines_mirAbsSlot_uint
    , ``Anneal.FarkasMirCert.farkas_entailment_adequacy_cert
    , ``Anneal.FarkasMirCert.farkas_int_entailment_adequacy_cert
    , ``Anneal.FarkasMirCert.checkNatGraphIndexPath_sound
    , ``Anneal.FarkasMirCert.checkIntGraphIndexPath_sound
    , ``Anneal.FarkasMirCert.checkFarkasMirGoal_sound ]
  let keyTrapConstructiveDecls : List Name :=
    [ ``Anneal.Mir.OverflowTrapRefinement.mirOutcomeRefines_refl
    , ``Anneal.Mir.OverflowTrapRefinement.mirOutcomeRefines_trans
    , ``Anneal.Mir.OverflowTrapRefinement.mirOutcomeRefines_iff_partial_le
    , ``Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeRefines_iff_partial_le
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_mono
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_ub_mono
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_to_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_ub_to_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_toPartial_equiv_of_same_halted
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_toPartial_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_add_refines_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_sub_refines_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_mul_refines_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_add_scaled_refines_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_equiv_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_refines_unchecked_of_farkas_cert_certified
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_const_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.trap_not_refines_ret
    , ``Anneal.Mir.OverflowTrapRefinement.trap_not_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.trap_not_refines_unsupported
    , ``Anneal.Mir.OverflowTrapRefinement.ret_not_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.ret_not_refines_trap
    , ``Anneal.Mir.OverflowTrapRefinement.ret_not_refines_unsupported
    , ``Anneal.Mir.OverflowTrapRefinement.ret_distinct_not_refines
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_refines_wrapping
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_underflow_not_refines_wrapping
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_overflow_not_refines_wrapping
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_underflow_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_overflow_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_distinct
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_overflow_not_refines_unchecked ]
  -- Coinductive `Anneal.ITree.WeakRef` / `Eutt` bridge corollaries (use `Classical.choice`
  -- solely via Lean 4 `coinductive_fixpoint` in `Anneal.ITree`).
  let keyWeakRefBridgeDecls : List Name :=
    [ ``Anneal.Mir.OverflowTrapRefinement.runMirCall_halted_eutt
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_weakRef_equiv_of_same_halted
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_weakRef_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_add_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_sub_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_mul_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_weakRef_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_weakRef_corollaries ]
  for d in keyFarkasDecls ++ keyTrapConstructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless isConstructive a do
        throwError "constructive audit failure: {d} depends on disallowed symbol {a}"
  for d in keyWeakRefBridgeDecls do
    let axs ← liftCoreM <| Lean.collectAxioms d
    for a in axs do
      unless isStandard a do
        throwError "weakRef bridge audit failure: {d} depends on non-standard symbol {a}"
  -- Also audit every theorem defined in this test module:
  let env ← getEnv
  let mut constructiveTestTheorems : Nat := 0
  let mut weakRefTestTheorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    if (`Anneal.Mir.FarkasMirCertAndTrapRefinementTests).isPrefixOf c then
      if let .thmInfo _ := info then
        let axs ← liftCoreM <| Lean.collectAxioms c
        if c == ``Anneal.Mir.FarkasMirCertAndTrapRefinementTests.test_weakRef_bridge_canaries then
          weakRefTestTheorems := weakRefTestTheorems + 1
          for a in axs do
            unless isStandard a do
              throwError "test-module weakRef audit failure: {c} depends on {a}"
        else
          constructiveTestTheorems := constructiveTestTheorems + 1
          for a in axs do
            unless isConstructive a do
              throwError "test-module constructive audit failure: {c} depends on {a}"
  if constructiveTestTheorems < 12 || weakRefTestTheorems < 1 then
    throwError "test audit is vacuous: constructive={constructiveTestTheorems}, weakRef={weakRefTestTheorems}"
  logInfo m!"hygiene audit passed: {keyFarkasDecls.length} FarkasMirCert + {keyTrapConstructiveDecls.length} constructive OverflowTrapRefinement + {constructiveTestTheorems} constructive test theorems in [propext, Quot.sound] (0 Classical.choice, 0 sorryAx, 0 ofReduceBool); {keyWeakRefBridgeDecls.length} WeakRef bridges + {weakRefTestTheorems} WeakRef canary in [propext, Quot.sound, Classical.choice]"

#print axioms Anneal.Mir.OverflowTrapRefinement.mirOutcomeRefines_iff_partial_le
#print axioms Anneal.Mir.OverflowTrapRefinement.unchecked_add_refines_to_checked
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_refines_unchecked_iff
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_of_farkas_cert
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_refines_wrapping
#print axioms Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_distinct
#print axioms Anneal.FarkasMirCert.checkFarkasMirGoal_sound

end Anneal.Mir.FarkasMirCertAndTrapRefinementTests
