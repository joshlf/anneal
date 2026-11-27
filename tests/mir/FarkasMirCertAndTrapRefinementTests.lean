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
   step-bounded `TauLeN` and general operational `iff` bridges to `mirCallTree` / `WeakRef`,
   `u128` exact boundary canaries, and all 17 explicit negative soundness theorems).
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

/-! ### 1.8 Right-Constant `uint-mul-const-no-overflow` (`n * 16`) + `stepMirState` Mul Elimination -/

-- Same generated certificate as 1.7 (the right-constant bridge reuses the `k * x + 1 <= 2^w` goal):
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-mul-const-no-overflow --width 64 \
--     --hyp "n <= 4096" --scale 16 --var n --json
/-- End-to-end `u64` right-constant multiplication (`n * 16 < 2^64`) checked-to-unchecked
elimination with the constant as the RIGHT `BinOp` operand. -/
theorem test_e2e_uint_mul_const_right_elim (strat : PanicStrategy) (n : Nat) (hn : n ≤ 4096) :
    UintScalarInRange .u64 ⟨16, uintBytes .u64⟩ ∧
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u64 .mul strat.toUnwindAction) 6 (uintArgs2 .u64 n 16)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u64 .mul) 2 (uintArgs2 .u64 n 16))) ∧
    (mirCallTree (mkUncheckedArithBody .u64 .mul) (uintArgs2 .u64 n 16)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u64 .mul strat.toUnwindAction) (uintArgs2 .u64 n 16)).toPartial :=
  checked_mul_const_right_refines_unchecked_of_farkas_cert
    .u64 strat uintMulConstHyps (.var 0) 16 uintMulConstCert rfl rfl [n] hn

/-! ### 1.9 `array-to-slice`, Unified `checkFarkasMirGoal_sound`, & `.u16` / `.usize` Width Coverage -/

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --domain nat \
--     --hyp "4 * q <= off" --hyp "off <= 4 * q" --hyp "4 * q + 4 * n <= total" \
--     --goal "4 * q <= off" / "off <= 4 * q" / "off + 4 * n <= total" --json
private def arrayToSliceHyps : List NatCutIneq :=
  [ ⟨.mulC 4 (.var 1), .var 0⟩
  , ⟨.var 0, .mulC 4 (.var 1)⟩
  , ⟨.add (.mulC 4 (.var 1)) (.mulC 4 (.var 2)), .var 3⟩ ]

private def arrayToSliceAlignLeCert : List CutStep :=
  [.hyp 0, .hyp 7, .comb 0 1 1 1]

private def arrayToSliceAlignGeCert : List CutStep :=
  [.hyp 1, .hyp 7, .comb 0 1 1 1]

private def arrayToSliceRangeCert : List CutStep :=
  [.hyp 1, .hyp 2, .hyp 7, .comb 0 1 1 1, .comb 3 1 2 1]

-- Generated via:
--   python3 -B ci/farkas_cert_gen.py --mir-bounds uint-add-no-overflow --width 16 \
--     --hyp "a <= 40000" --hyp "b <= 25535" --lhs-expr "a" --rhs-expr "b" --json
private def u16MaxHyps : List NatCutIneq :=
  [⟨.var 0, .cst 40000⟩, ⟨.var 1, .cst 25535⟩]

private def u16MaxCert : List CutStep :=
  [.hyp 0, .hyp 1, .hyp 4, .comb 0 1 1 1, .comb 3 1 2 1]

/-- End-to-end `ValidArrayToSliceCast` (both directly via `farkas_discharges_array_to_slice_cast`
and through the unified `checkFarkasMirGoal_sound` dispatcher), plus `.u16` (`40000 + 25535 =
65535 = u16::MAX`) and `.usize` (`add_scaled`) checked-to-unchecked elimination so ALL 6 `UintTy`
variants (`.u8`, `.u16`, `.u32`, `.u64`, `.u128`, `.usize`) are exercised end-to-end. -/
theorem test_e2e_array_to_slice_dispatcher_and_u16_usize (strat : PanicStrategy)
    (rp : RawPtrVal) (q n total a16 b16 aSz bSz : Nat)
    (hAlign1 : 4 * q ≤ rp.offset) (hAlign2 : rp.offset ≤ 4 * q)
    (hTot : 4 * q + 4 * n ≤ total)
    (ha16 : a16 ≤ 40000) (hb16 : b16 ≤ 25535)
    (haSz : aSz ≤ 1000000) (hbSz : bSz ≤ 250000) :
    ValidArrayToSliceCast rp 4 4 n total ∧
    evalPtrOffset rp (n * 4) total = some { rp with offset := rp.offset + n * 4 } ∧
    a16 + b16 < modPow2 (uintWidth .u16) ∧
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u16 .add strat.toUnwindAction) 6
          (uintArgs2 .u16 a16 b16)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u16 .add) 2 (uintArgs2 .u16 a16 b16))) ∧
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedAddScaledBody .usize 4 strat.toUnwindAction) 13
          (uintArgs2 .usize aSz bSz)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedAddScaledBody .usize 4) 5 (uintArgs2 .usize aSz bSz))) := by
  have hArr := farkas_discharges_array_to_slice_cast
    arrayToSliceHyps 4 4 (.var 0) (.var 1) (.var 2) (.var 3)
    arrayToSliceAlignLeCert arrayToSliceAlignGeCert arrayToSliceRangeCert
    rfl rfl rfl rfl [rp.offset, q, n, total] rp rfl hAlign1 hAlign2 hTot
  have hArrDisp := checkFarkasMirGoal_sound
    (.arrayToSliceCast arrayToSliceHyps 4 4 (.var 0) (.var 1) (.var 2) (.var 3))
    (.triple arrayToSliceAlignLeCert arrayToSliceAlignGeCert arrayToSliceRangeCert)
    rfl [rp.offset, q, n, total] rp rfl hAlign1 hAlign2 hTot
  have hU16Disp := checkFarkasMirGoal_sound
    (.uintAddNoOverflow .u16 u16MaxHyps (.var 0) (.var 1))
    (.single u16MaxCert) rfl [a16, b16] [] canonInitMemory ha16 hb16
  have hU16Eq := checked_add_equiv_unchecked_of_farkas_cert
    .u16 strat u16MaxHyps (.var 0) (.var 1) u16MaxCert rfl [a16, b16] ha16 hb16
  have hUsize := checked_add_scaled_refines_unchecked_of_farkas_cert
    .usize 4 strat addScaledHyps (.var 0) (.var 1) addScaledCert rfl rfl [aSz, bSz] haSz hbSz
  exact ⟨hArr.1, hArrDisp.2, hU16Disp.1, hU16Eq, hUsize.2.1⟩

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

/-! ### 3.1 Fuel-Independence, Non-Vacuity, Strategy-Mismatch, Fault-Bridge, & Mutation Canaries -/

/-- Fuel-independence and fail-closed detection of fuel truncation / strategy mismatch:
refinement verdicts are identical at large fuel, while under-fuelled or strategy-mismatched
runs are visibly `.unsupported` (and are proven never to arise for canonical runs). -/
theorem test_fuel_independence_and_nonvacuity :
    -- Reverse refinement verdicts at fuel 100 / 1000 (far above the canonical step counts)
    MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .add .terminate) 100 (uintArgs2 .u8 100 50)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .add) 100 (uintArgs2 .u8 100 50))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .mul .continue_) 1000 (uintArgs2 .u8 20 20)))
      (classifyMirExecState .unwind
        (runMirCall (mkUncheckedArithBody .u8 .mul) 1000 (uintArgs2 .u8 20 20)))) ∧
    MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkUncheckedAddScaledBody .u8 4) 64 (uintArgs2 .u8 200 20)))
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedAddScaledBody .u8 4 .continue_) 64 (uintArgs2 .u8 200 20))) ∧
    -- Under-fuelled runs are visibly truncated (one step short of the canonical count)
    runMirCall (mkCheckedArithBody .u8 .add .terminate) 5 (uintArgs2 .u8 100 50) =
      .faulted .outOfFuel ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 .terminate) 12 (uintArgs2 .u8 1 2) =
      .faulted .outOfFuel ∧
    -- Strategy mismatch is visible: an abort-compiled trap is `.unsupported` under `.unwind`,
    -- while the strategy-exact classifier reports `.trap .abort`
    classifyMirExecState .unwind
      (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)) =
      .unsupported ∧
    classifyMirExecStateExact
      (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)) =
      .trap .abort ∧
    -- Matched-strategy canonical runs are never `.unsupported`
    classifyMirExecState .abort
      (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)) ≠
      .unsupported := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hA := runMirCall_checked_add_trap .u8 .abort 200 100 hOv
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hA
  refine ⟨(checked_add_refines_unchecked_iff_of_fuel .u8 .abort 100 50
            (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)).2
            (Nat.le_of_ble_eq_true rfl),
          fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
            ((checked_mul_refines_unchecked_iff_of_fuel .u8 .unwind 20 20
              (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)).1 h),
          (unchecked_refines_to_checked_of_fuel .u8 .unwind 200 20 4
            (fC := 6) (fU := 2) (Nat.le_refl 6) (Nat.le_refl 2)
            (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)).2.2,
          rfl, rfl, ?_, ?_, (canonical_add_runs_nonvacuous .u8 .abort 200 100).2⟩
  · rw [hA]; rfl
  · rw [hA]; rfl

/-- The general `runMirSteps_faulted_to_tauStar` bridge, instantiated on an underflowing
unchecked `u8` subtraction: the runner-introduced disjuncts (`.unsupported` observation and
`.outOfFuel` truncation) are refuted, leaving the genuine `stepMirState` UB fail node. -/
theorem test_faulted_bridge_ub_instance :
    ∃ u : ITree MirEffect MirOutcome,
      TauStar (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 3 5)) u ∧
      u.observe = .vis (.inl (.fail .ub)) PEmpty.elim := by
  have hU := runMirCall_unchecked_sub_ub .u8 3 5 (Nat.le_of_ble_eq_true rfl)
  have ⟨u, hTau, hCase⟩ := runMirSteps_faulted_to_tauStar _ 2 _ .ub hU
  refine ⟨u, hTau, ?_⟩
  rcases hCase with hObs | ⟨hEq, _⟩ | ⟨hEq, _⟩
  · exact hObs
  · nomatch hEq
  · nomatch hEq

/-- Mutation operator: flip the `expected` polarity of every `TerminatorKind.assert`. -/
def flipAssertPolarity (b : CapturedMir) : CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      match bb.terminator.kind with
      | .assert c e t uw =>
        { bb with terminator := { bb.terminator with kind := .assert c (!e) t uw } }
      | _ => bb }

/-- Mutation-testing canaries proving the refinement theorems are sensitive to the exact
operational content of the checked bodies (and hence are not vacuous):
- (M1) flipping `assert` polarity (`expected := true`) traps on NON-overflowing `100 + 50`,
  breaking the unconditional forward direction, and silently returns the wrapped `44` on
  overflowing `200 + 100`, breaking panic preservation;
- (M2) `UnwindAction.unreachable` turns the overflow trap into UB, which collapses the
  asymmetric separation: the refinement refuted by `checked_add_overflow_not_refines_unchecked`
  now HOLDS, so that negative theorem fails specifically because of the trap-vs-UB rule. -/
theorem test_mutation_canaries :
    runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .add .terminate)) 6
      (uintArgs2 .u8 100 50) = .halted .abort ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 100 50)))
      (classifyMirExecState .abort
        (runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .add .terminate)) 6
          (uintArgs2 .u8 100 50)))) ∧
    runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .add .terminate)) 6
      (uintArgs2 .u8 200 100) = .halted (.normal (.scalar ⟨44, 1⟩, canonInitMemory)) ∧
    runMirCall (mkCheckedArithBody .u8 .add .unreachable) 6 (uintArgs2 .u8 200 100) =
      .faulted .ub ∧
    MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .add .unreachable) 6 (uintArgs2 .u8 200 100)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100))) := by
  have hM1 : runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .add .terminate)) 6
      (uintArgs2 .u8 100 50) = .halted .abort := rfl
  have hU := runMirCall_unchecked_add_ok .u8 100 50 (Nat.le_of_ble_eq_true rfl)
  have hM2 : runMirCall (mkCheckedArithBody .u8 .add .unreachable) 6 (uintArgs2 .u8 200 100) =
      .faulted .ub := rfl
  refine ⟨hM1, ?_, rfl, hM2, ?_⟩
  · rw [hU, hM1]
    exact ret_not_refines_trap _
  · rw [hM2]
    trivial

/-! ### 3.2 Tightness & Second-Site Negative Soundness (#16–#17), `u128` Boundaries, `TauLeN`, General Operational `iff`, & Preorder Exports -/

/-- Direct instantiation of Negative Soundness #16 (out-of-range LHS `subWithOverflow` vs
`subUnchecked` tightness) and #17 (inner multiplication overflow site of `add_scaled`),
under both `-C panic=abort` and `-C panic=unwind`. -/
theorem test_negative_soundness_sixteen_and_seventeen :
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkCheckedArithBody .u8 .sub .terminate) 6 (uintArgs2 .u8 300 10)))
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u8 .sub) 2 (uintArgs2 .u8 300 10)))) ∧
    (¬ ((mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 300 10)).toPartial ≤
        (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 300 10)).toPartial)) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedAddScaledBody .u8 4 .continue_) 13 (uintArgs2 .u8 1 70)))
      (classifyMirExecState .unwind
        (runMirCall (mkUncheckedAddScaledBody .u8 4) 5 (uintArgs2 .u8 1 70)))) ∧
    (¬ ((mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 1 70)).toPartial ≤
        (mirCallTree (mkCheckedAddScaledBody .u8 4 .terminate) (uintArgs2 .u8 1 70)).toPartial)) :=
  ⟨(checked_sub_out_of_range_lhs_not_refines_unchecked .abort).2.2.2.1,
   (checked_sub_out_of_range_lhs_not_refines_unchecked .unwind).2.2.2.2,
   (checked_add_scaled_inner_mul_overflow_not_refines_unchecked .unwind).2.2.2.1,
   (checked_add_scaled_inner_mul_overflow_not_refines_unchecked .abort).2.2.2.2⟩

private def u128Max : Nat := 340282366920938463463374607431768211455

private theorem classify_trap_not_refines_ret (strat : PanicStrategy) (v : Value) (m : Memory) :
    ¬ MirOutcomeRefines
      (classifyMirExecState strat (.halted strat.toTrapOutcome))
      (classifyMirExecState strat (.halted (.normal (v, m)))) := by
  cases strat <;> exact trap_not_refines_ret v

/-- Concrete `u128` exact boundary canaries:
- `u128::MAX + 0`: checked and unchecked both halt returning `u128::MAX`;
- `u128::MAX + 1`: checked traps, unchecked faults `.ub`, wrapping returns `0`
  (`unchecked ⊑ checked`, `¬ checked ⊑ unchecked`, `¬ checked ⊑ wrapping`);
- `0 - 1` (`u128`): checked traps, unchecked faults `.ub`, wrapping returns `u128::MAX`
  (`unchecked ⊑ checked`, `¬ checked ⊑ unchecked`, `¬ checked ⊑ wrapping`). -/
theorem test_u128_exact_boundary_canaries (strat : PanicStrategy) :
    MirOutcomeEquiv
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .add strat.toUnwindAction) 6
          (uintArgs2 .u128 u128Max 0)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .add) 2 (uintArgs2 .u128 u128Max 0))) ∧
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .add) 2 (uintArgs2 .u128 u128Max 1)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .add strat.toUnwindAction) 6
          (uintArgs2 .u128 u128Max 1))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .add strat.toUnwindAction) 6
          (uintArgs2 .u128 u128Max 1)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .add) 2 (uintArgs2 .u128 u128Max 1)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .add strat.toUnwindAction) 6
          (uintArgs2 .u128 u128Max 1)))
      (classifyMirExecState strat
        (runMirCall (mkWrappingArithBody .u128 .add) 2 (uintArgs2 .u128 u128Max 1)))) ∧
    MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .sub) 2 (uintArgs2 .u128 0 1)))
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .sub strat.toUnwindAction) 6
          (uintArgs2 .u128 0 1))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .sub strat.toUnwindAction) 6
          (uintArgs2 .u128 0 1)))
      (classifyMirExecState strat
        (runMirCall (mkUncheckedArithBody .u128 .sub) 2 (uintArgs2 .u128 0 1)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState strat
        (runMirCall (mkCheckedArithBody .u128 .sub strat.toUnwindAction) 6
          (uintArgs2 .u128 0 1)))
      (classifyMirExecState strat
        (runMirCall (mkWrappingArithBody .u128 .sub) 2 (uintArgs2 .u128 0 1)))) := by
  have hMod : modPow2 (uintWidth .u128) = u128Max + 1 := by
    rw [modPow2_eq_pow]
    rfl
  have hMax0 : u128Max + 0 < modPow2 (uintWidth .u128) := by
    rw [hMod, Nat.add_zero]
    exact Nat.lt_succ_self u128Max
  have hMax1 : modPow2 (uintWidth .u128) ≤ u128Max + 1 := by
    rw [hMod]
    exact Nat.le_refl _
  have h0Lt : 0 < modPow2 (uintWidth .u128) := by
    rw [hMod]
    exact Nat.succ_pos _
  have h1Lt : 1 < modPow2 (uintWidth .u128) := by
    rw [hMod]
    exact Nat.succ_lt_succ (Nat.succ_pos _)
  have hUnd : 0 < 1 := Nat.lt_succ_self 0
  have hAddC := runMirCall_checked_add_trap .u128 strat u128Max 1 hMax1
  have hAddW := runMirCall_wrapping_add .u128 u128Max 1
  have hSubC := runMirCall_checked_sub_trap .u128 strat 0 1 h0Lt h1Lt hUnd
  have hSubW := runMirCall_wrapping_sub .u128 0 1 h0Lt h1Lt
  refine ⟨⟨(checked_add_refines_unchecked_iff .u128 strat u128Max 0).2 hMax0,
           (unchecked_add_refines_to_checked .u128 strat u128Max 0).1⟩,
          (unchecked_add_refines_to_checked .u128 strat u128Max 1).1,
          fun h => Nat.not_lt_of_le hMax1
            ((checked_add_refines_unchecked_iff .u128 strat u128Max 1).1 h),
          ?_,
          (unchecked_sub_refines_to_checked .u128 strat 0 1 h0Lt h1Lt).1,
          fun h => Nat.not_le_of_gt hUnd
            ((checked_sub_refines_unchecked_iff .u128 strat 0 1 h0Lt h1Lt).1 h),
          ?_⟩
  · rw [hAddC, hAddW]
    exact classify_trap_not_refines_ret strat _ _
  · rw [hSubC, hSubW]
    exact classify_trap_not_refines_ret strat _ _

/-- Step-bounded `TauLeN` (`≤ fuel`) bridge and the general constructive operational
equivalence `mirExactOutcomeRefines_iff_mirCallTree_toPartial_le`. -/
theorem test_step_bounded_tauLeN_and_general_operational_iff :
    (∃ u : ITree MirEffect MirOutcome,
      TauLeN 10 (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 100 50)) u ∧
      u.observe = .ret (.normal (.scalar ⟨150, 1⟩, canonInitMemory))) ∧
    (∃ u : ITree MirEffect MirOutcome,
      TauLeN 2 (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100)) u ∧
      u.observe = .vis (.inl (.fail .ub)) PEmpty.elim) ∧
    ((mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 100 50)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 100 50)).toPartial) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100)).toPartial)) := by
  have hOk : runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 100 50) =
      .halted (.normal (.scalar ⟨150, 1⟩, canonInitMemory)) :=
    runMirCall_checked_add_ok .u8 .abort 100 50 (Nat.le_of_ble_eq_true rfl)
  have hOkU : runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 100 50) =
      .halted (.normal (.scalar ⟨150, 1⟩, canonInitMemory)) :=
    runMirCall_unchecked_add_ok .u8 100 50 (Nat.le_of_ble_eq_true rfl)
  have hUb : runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100) = .faulted .ub :=
    runMirCall_unchecked_add_ub .u8 200 100 (Nat.le_of_ble_eq_true rfl)
  have hA : runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100) =
      .halted .abort :=
    runMirCall_checked_add_trap .u8 .abort 200 100 (Nat.le_of_ble_eq_true rfl)
  have hP : runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100) =
      .halted .panic :=
    runMirCall_checked_add_trap .u8 .unwind 200 100 (Nat.le_of_ble_eq_true rfl)
  have ⟨u1, hLe1, hObs1⟩ := runMirSteps_halted_to_tauLeN _ 6 _ _ hOk
  have ⟨u2, hLe2, hObs2⟩ := runMirSteps_ub_to_tauLeN _ 2 _ hUb
  have hSettledOk : SettledExec (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 100 50)) := by
    rw [hOk]; trivial
  have hSettledOkU : SettledExec (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 100 50)) := by
    rw [hOkU]; trivial
  have hSettledA : SettledExec (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)) := by
    rw [hA]; trivial
  have hSettledP : SettledExec (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100)) := by
    rw [hP]; trivial
  refine ⟨⟨u1, hLe1.mono (Nat.le_of_ble_eq_true rfl), hObs1⟩, ⟨u2, hLe2, hObs2⟩, ?_, ?_⟩
  · exact (mirExactOutcomeRefines_iff_mirCallTree_toPartial_le hSettledOk hSettledOkU).1
      (by rw [hOk, hOkU]; rfl)
  · intro hLe
    have hEx := (mirExactOutcomeRefines_iff_mirCallTree_toPartial_le hSettledA hSettledP).2 hLe
    rw [hA, hP] at hEx
    nomatch hEx

/-- Coinductive `WeakRef` general operational equivalence canary. -/
theorem test_weakRef_general_operational_iff :
    WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100))
      (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 200 100)) ∧
    (¬ WeakRef
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 200 100))
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 200 100))) := by
  have hOv : modPow2 (uintWidth .u8) ≤ 200 + 100 := Nat.le_of_ble_eq_true rfl
  have hU := runMirCall_unchecked_add_ub .u8 200 100 hOv
  have hA := runMirCall_checked_add_trap .u8 .abort 200 100 hOv
  have hP := runMirCall_checked_add_trap .u8 .unwind 200 100 hOv
  dsimp only [PanicStrategy.toUnwindAction, PanicStrategy.toTrapOutcome] at hA hP
  have hSU : SettledExec (runMirCall (mkUncheckedArithBody .u8 .add) 2 (uintArgs2 .u8 200 100)) := by
    rw [hU]; trivial
  have hSA : SettledExec (runMirCall (mkCheckedArithBody .u8 .add .terminate) 6 (uintArgs2 .u8 200 100)) := by
    rw [hA]; trivial
  have hSP : SettledExec (runMirCall (mkCheckedArithBody .u8 .add .continue_) 6 (uintArgs2 .u8 200 100)) := by
    rw [hP]; trivial
  refine ⟨(mirExactOutcomeRefines_iff_mirCallTree_weakRef hSU hSA).1 (by rw [hU]; trivial), ?_⟩
  intro hW
  have hEx := (mirExactOutcomeRefines_iff_mirCallTree_weakRef hSA hSP).2 hW
  rw [hA, hP] at hEx
  nomatch hEx

/-- Preorder (`≤` `calc` chain), `Trusted.Refinement.Monotone` embeddings, exact equivalence
combinators, and `classifyAnyTrap` coverage. -/
theorem test_preorder_monotonicity_and_classifyAnyTrap :
    classifyAnyTrap (.halted .abort) = .trap ∧
    classifyAnyTrap (.halted .panic) = .trap ∧
    classifyAnyTrap (.faulted .ub) = .ub ∧
    ((MirOutcomeClass.trap (Val := Value)) ≤ .ub) ∧
    ((MirExactOutcomeClass.trap (Val := Value) .abort) ≤ .ub) ∧
    ((MirOutcomeClass.trap (Val := Value)).toPartial ≤ (MirOutcomeClass.ub (Val := Value)).toPartial) ∧
    ((MirExactOutcomeClass.trap (Val := Value) .panic).toPartial ≤
      (MirExactOutcomeClass.ub (Val := Value)).toPartial) ∧
    MirExactOutcomeEquiv (Val := Value) (.trap .abort) (.trap .abort) := by
  have hPre : (MirOutcomeClass.trap (Val := Value)) ≤ .ub :=
    calc (MirOutcomeClass.trap (Val := Value)) ≤ .trap := Std.IsPreorder.le_refl _
      _ ≤ .ub := trivial
  have hExPre : (MirExactOutcomeClass.trap (Val := Value) .abort) ≤ .ub :=
    calc (MirExactOutcomeClass.trap (Val := Value) .abort) ≤ .trap .abort :=
          Std.IsPreorder.le_refl _
      _ ≤ .ub := trivial
  exact ⟨rfl, rfl, rfl, hPre, hExPre,
    mirOutcomeClass_toPartial_monotone hPre,
    mirExactOutcomeClass_toPartial_monotone (show (MirExactOutcomeClass.trap .panic) ≤ .ub from trivial),
    mirExactOutcomeEquiv_trans (mirExactOutcomeEquiv_refl _) (mirExactOutcomeEquiv_symm (mirExactOutcomeEquiv_refl _))⟩

/-- Constructive tree-level Layer 1A `ITree.toPartial` reverse `iff` instances on both sides
of the `u8` overflow boundary (`255 + 0` vs `255 + 1`, `5 - 5` vs `5 - 6`, `15 * 17` vs
`16 * 16`, `3 + 4 * 63` vs `4 + 4 * 63`), plus exact `add_scaled` failure-site pinning on
both `u8` and `u128`. Kept strictly constructive (zero `Classical.choice`). -/
theorem test_tree_level_toPartial_reverse_iff_and_failure_sites :
    (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 255 0)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 255 0)).toPartial ∧
    (¬ (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 255 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 255 1)).toPartial) ∧
    (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 5 5)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 5 5)).toPartial ∧
    (¬ (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 5 6)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .sub .terminate) (uintArgs2 .u8 5 6)).toPartial) ∧
    (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 15 17)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 15 17)).toPartial ∧
    (¬ (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 16 16)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .mul .continue_) (uintArgs2 .u8 16 16)).toPartial) ∧
    (mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 3 63)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody .u8 4 .terminate) (uintArgs2 .u8 3 63)).toPartial ∧
    (¬ (mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 4 63)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody .u8 4 .continue_) (uintArgs2 .u8 4 63)).toPartial) ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 .terminate) 3 (uintArgs2 .u8 1 70) = .halted .abort ∧
    runMirCall (mkCheckedAddScaledBody .u8 4 .continue_) 8 (uintArgs2 .u8 200 20) =
      .faulted .outOfFuel ∧
    runMirCall (mkCheckedAddScaledBody .u128 2 .terminate) 8 (uintArgs2 .u128 u128Max 1) =
      .faulted .outOfFuel ∧
    runMirCall (mkCheckedAddScaledBody .u128 2 .terminate) 9 (uintArgs2 .u128 u128Max 1) =
      .halted .abort := by
  have h5 : (5 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have h6 : (6 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have hMod128 : modPow2 (uintWidth .u128) = u128Max + 1 := by
    rw [modPow2_eq_pow]; rfl
  have h2Lt128 : 2 * 1 < modPow2 (uintWidth .u128) := by
    rw [hMod128]
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos _))
  have hOuter128 : modPow2 (uintWidth .u128) ≤ u128Max + 2 * 1 := by
    rw [hMod128]
    exact Nat.add_le_add_left (Nat.le_succ 1) u128Max
  have hPin128 := runMirCall_checked_add_scaled_outer_add_trap_pinned .u128 2 .abort u128Max 1
    h2Lt128 hOuter128
  refine ⟨(checked_add_toPartial_refines_unchecked_iff .u8 .abort 255 0).2
            (Nat.le_of_ble_eq_true rfl),
          fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
            ((checked_add_toPartial_refines_unchecked_iff .u8 .unwind 255 1).1 h),
          (checked_sub_toPartial_refines_unchecked_iff .u8 .unwind 5 5 h5 h5).2 (Nat.le_refl 5),
          fun h => Nat.not_le_of_gt (Nat.lt_succ_self 5)
            ((checked_sub_toPartial_refines_unchecked_iff .u8 .abort 5 6 h5 h6).1 h),
          (checked_mul_toPartial_refines_unchecked_iff .u8 .abort 15 17).2
            (Nat.le_of_ble_eq_true rfl),
          fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
            ((checked_mul_toPartial_refines_unchecked_iff .u8 .unwind 16 16).1 h),
          (checked_add_scaled_toPartial_refines_unchecked_iff .u8 4 .abort 3 63).2
            (Nat.le_of_ble_eq_true rfl),
          fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
            ((checked_add_scaled_toPartial_refines_unchecked_iff .u8 4 .unwind 4 63).1 h),
          (add_scaled_failure_sites_pinned .abort).2.1,
          (add_scaled_failure_sites_pinned .unwind).2.2.2.2.1,
          hPin128.1, hPin128.2⟩

/-- Coinductive `WeakRef` tree-level reverse `iff` instances (both positive and negative sides
for `add`, `sub`, `mul`, and `add_scaled`) plus unconditional `unchecked_add_scaled_weakRef_to_checked`. -/
theorem test_tree_level_weakRef_reverse_iff :
    WeakRef (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 255 0))
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 255 0)) ∧
    (¬ WeakRef (mirCallTree (mkUncheckedArithBody .u8 .add) (uintArgs2 .u8 255 1))
      (mirCallTree (mkCheckedArithBody .u8 .add .continue_) (uintArgs2 .u8 255 1))) ∧
    WeakRef (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 5 5))
      (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 5 5)) ∧
    (¬ WeakRef (mirCallTree (mkUncheckedArithBody .u8 .sub) (uintArgs2 .u8 5 6))
      (mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 5 6))) ∧
    WeakRef (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 15 17))
      (mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 15 17)) ∧
    (¬ WeakRef (mirCallTree (mkUncheckedArithBody .u8 .mul) (uintArgs2 .u8 16 16))
      (mirCallTree (mkCheckedArithBody .u8 .mul .continue_) (uintArgs2 .u8 16 16))) ∧
    WeakRef (mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 3 63))
      (mirCallTree (mkCheckedAddScaledBody .u8 4 .terminate) (uintArgs2 .u8 3 63)) ∧
    (¬ WeakRef (mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 4 63))
      (mirCallTree (mkCheckedAddScaledBody .u8 4 .continue_) (uintArgs2 .u8 4 63))) ∧
    WeakRef (mirCallTree (mkCheckedAddScaledBody .u8 4 .terminate) (uintArgs2 .u8 200 20))
      (mirCallTree (mkUncheckedAddScaledBody .u8 4) (uintArgs2 .u8 200 20)) := by
  have h5 : (5 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have h6 : (6 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  exact ⟨(checked_add_weakRef_refines_unchecked_iff .u8 .abort 255 0).2
           (Nat.le_of_ble_eq_true rfl),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_add_weakRef_refines_unchecked_iff .u8 .unwind 255 1).1 h),
         (checked_sub_weakRef_refines_unchecked_iff .u8 .unwind 5 5 h5 h5).2 (Nat.le_refl 5),
         fun h => Nat.not_le_of_gt (Nat.lt_succ_self 5)
           ((checked_toWeakRef_refines_unchecked_iff .u8 .unwind 5 6 4 h5 h6).2.1.1 h),
         (checked_mul_weakRef_refines_unchecked_iff .u8 .abort 15 17).2
           (Nat.le_of_ble_eq_true rfl),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_mul_weakRef_refines_unchecked_iff .u8 .unwind 16 16).1 h),
         (checked_add_scaled_weakRef_refines_unchecked_iff .u8 4 .abort 3 63).2
           (Nat.le_of_ble_eq_true rfl),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_add_scaled_weakRef_refines_unchecked_iff .u8 4 .unwind 4 63).1 h),
         unchecked_add_scaled_weakRef_to_checked .u8 4 .abort 200 20⟩

/-- Constructive symmetric incomparability canary for `checked` vs. `wrapping` (`add`, `sub`,
`mul`): on overflowing/underflowing inputs BOTH directions fail (`¬ checked ⊑ wrapping` AND
`¬ wrapping ⊑ checked` at both classifier and Layer 1A `ITree.toPartial`), contrasting
directly with unconditional asymmetric `unchecked ⊑ checked`. -/
theorem test_checked_vs_wrapping_symmetric_iff :
    ((mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 255 0)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 255 0)).toPartial) ∧
    (¬ ((mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 255 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 255 1)).toPartial)) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .u8 .add .terminate) (uintArgs2 .u8 255 1)).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u8 .add) (uintArgs2 .u8 255 1)).toPartial)) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 5 6)).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u8 .sub) (uintArgs2 .u8 5 6)).toPartial)) ∧
    ((mirCallTree (mkCheckedArithBody .u8 .sub .continue_) (uintArgs2 .u8 5 5)).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u8 .sub) (uintArgs2 .u8 5 5)).toPartial) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 16 16)).toPartial ≤
      (mirCallTree (mkWrappingArithBody .u8 .mul) (uintArgs2 .u8 16 16)).toPartial)) ∧
    ((mirCallTree (mkWrappingArithBody .u8 .mul) (uintArgs2 .u8 15 17)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u8 .mul .terminate) (uintArgs2 .u8 15 17)).toPartial) := by
  have h5 : (5 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have h6 : (6 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  exact ⟨(checked_add_wrapping_refines_iff .u8 .abort 255 0).2.2.1.2 (Nat.le_of_ble_eq_true rfl),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_add_wrapping_refines_iff .u8 .abort 255 1).2.2.1.1 h),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_add_wrapping_refines_iff .u8 .abort 255 1).2.2.2.1 h),
         fun h => Nat.not_le_of_gt (Nat.lt_succ_self 5)
           ((checked_sub_wrapping_refines_iff .u8 .unwind 5 6 h5 h6).2.2.2.1 h),
         (checked_sub_wrapping_refines_iff .u8 .unwind 5 5 h5 h5).2.2.2.2 (Nat.le_refl 5),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((checked_mul_wrapping_refines_iff .u8 .abort 16 16).2.2.2.1 h),
         (checked_mul_wrapping_refines_iff .u8 .abort 15 17).2.2.1.2 (Nat.le_of_ble_eq_true rfl)⟩

/-- The test-side mutation operator `flipAssertPolarity` applied to the canonical checked body
is EXACTLY the theory-side polarity mutant (for ALL `u`, `op`, `unwind`), so the parametric
`assert_polarity_mutation_breaks_refinement` covers the concrete mutation canaries above. -/
theorem test_flipAssertPolarity_is_theory_mutant (u : UintTy) (op : ArithKind)
    (uw : UnwindAction) :
    flipAssertPolarity (mkCheckedArithBody u op uw) = mkCheckedArithBodyWithExpected u op uw true :=
  rfl

/-- Universal polarity-mutation refutation instantiated on `u8`/`u64` boundary inputs under both
panic strategies. -/
theorem test_assert_polarity_mutation_universal :
    (¬ MirOutcomeRefines
      (classifyMirExecState .abort
        (runMirCall (mkUncheckedArithBody .u64 .add) 2 (uintArgs2 .u64 7 9)))
      (classifyMirExecState .abort
        (runMirCall (flipAssertPolarity (mkCheckedArithBody .u64 .add .terminate)) 6
          (uintArgs2 .u64 7 9)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .mul .continue_) 6 (uintArgs2 .u8 16 16)))
      (classifyMirExecState .unwind
        (runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .mul .continue_)) 6
          (uintArgs2 .u8 16 16)))) ∧
    (¬ MirOutcomeRefines
      (classifyMirExecState .unwind
        (runMirCall (mkCheckedArithBody .u8 .sub .continue_) 6 (uintArgs2 .u8 5 6)))
      (classifyMirExecState .unwind
        (runMirCall (flipAssertPolarity (mkCheckedArithBody .u8 .sub .continue_)) 6
          (uintArgs2 .u8 5 6)))) := by
  have h7 : (7 : Nat) < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have h9 : (9 : Nat) < modPow2 (uintWidth .u64) := Nat.le_of_ble_eq_true rfl
  have h16 : (16 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have h5 : (5 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  have h6 : (6 : Nat) < modPow2 (uintWidth .u8) := Nat.le_of_ble_eq_true rfl
  rw [test_flipAssertPolarity_is_theory_mutant, test_flipAssertPolarity_is_theory_mutant,
      test_flipAssertPolarity_is_theory_mutant]
  exact ⟨(assert_polarity_mutation_breaks_refinement .u64 .abort 7 9 h7 h9).1
           (Nat.le_of_ble_eq_true rfl),
         (assert_polarity_mutation_breaks_refinement .u8 .unwind 16 16 h16 h16).2.2.2.2.2
           (Nat.le_of_ble_eq_true rfl),
         (assert_polarity_mutation_breaks_refinement .u8 .unwind 5 6 h5 h6).2.2.2.1
           (Nat.lt_succ_self 5)⟩

/-- Parametric `-C panic=abort` vs. `-C panic=unwind` equivalence/incomparability `iff`,
tree-level `ITree.toPartial` polarity-mutation refutation, and universal
`UnwindAction.unreachable` trap-collapse sensitivity across `.u16`, `.u64`, `.usize`, `.u128`. -/
theorem test_parametric_strategy_separation_and_mutation_toPartial :
    -- Cross-strategy equivalence holds on non-overflowing u16/usize, fails on overflowing u128/u16
    ((mirCallTree (mkCheckedArithBody .u16 .add .continue_) (uintArgs2 .u16 40000 25535)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u16 .add .terminate) (uintArgs2 .u16 40000 25535)).toPartial) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .u128 .add .continue_) (uintArgs2 .u128 u128Max 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u128 .add .terminate) (uintArgs2 .u128 u128Max 1)).toPartial)) ∧
    (¬ ((mirCallTree (mkCheckedArithBody .usize .sub .terminate) (uintArgs2 .usize 0 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .usize .sub .continue_) (uintArgs2 .usize 0 1)).toPartial)) ∧
    (¬ ((mirCallTree (mkCheckedAddScaledBody .u16 4 .continue_) (uintArgs2 .u16 65500 20)).toPartial ≤
      (mirCallTree (mkCheckedAddScaledBody .u16 4 .terminate) (uintArgs2 .u16 65500 20)).toPartial)) ∧
    -- Tree-level Layer 1A ITree.toPartial polarity-mutation refutation (add, sub, mul)
    (¬ ((mirCallTree (flipAssertPolarity (mkCheckedArithBody .u64 .add .terminate))
          (uintArgs2 .u64 7 9)).toPartial ≤
        (mirCallTree (mkUncheckedArithBody .u64 .add) (uintArgs2 .u64 7 9)).toPartial)) ∧
    (¬ ((mirCallTree (flipAssertPolarity (mkCheckedArithBody .u128 .sub .continue_))
          (uintArgs2 .u128 0 1)).toPartial ≤
        (mirCallTree (mkCheckedArithBody .u128 .sub .continue_) (uintArgs2 .u128 0 1)).toPartial)) ∧
    (¬ ((mirCallTree (flipAssertPolarity (mkCheckedArithBody .u16 .mul .terminate))
          (uintArgs2 .u16 256 256)).toPartial ≤
        (mirCallTree (mkCheckedArithBody .u16 .mul .terminate) (uintArgs2 .u16 256 256)).toPartial)) ∧
    -- Universal UnwindAction.unreachable sensitivity on u128 add, usize sub, u16 mul
    ((mirCallTree (mkUncheckedArithBody .u128 .add) (uintArgs2 .u128 u128Max 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u128 .add .unreachable) (uintArgs2 .u128 u128Max 1)).toPartial) ∧
    ((mirCallTree (mkUncheckedArithBody .usize .sub) (uintArgs2 .usize 0 1)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .usize .sub .unreachable) (uintArgs2 .usize 0 1)).toPartial) ∧
    ((mirCallTree (mkUncheckedArithBody .u16 .mul) (uintArgs2 .u16 256 256)).toPartial ≤
      (mirCallTree (mkCheckedArithBody .u16 .mul .unreachable) (uintArgs2 .u16 256 256)).toPartial) := by
  have hMod128 : modPow2 (uintWidth .u128) = u128Max + 1 := by
    rw [modPow2_eq_pow]; rfl
  have h0Lt128 : 0 < modPow2 (uintWidth .u128) := by rw [hMod128]; exact Nat.succ_pos _
  have h1Lt128 : 1 < modPow2 (uintWidth .u128) := by
    rw [hMod128]; exact Nat.succ_lt_succ (Nat.succ_pos _)
  have hOv128 : modPow2 (uintWidth .u128) ≤ u128Max + 1 := by rw [hMod128]; exact Nat.le_refl _
  have h0LtSz : 0 < modPow2 (uintWidth .usize) := Nat.le_of_ble_eq_true rfl
  have h1LtSz : 1 < modPow2 (uintWidth .usize) := Nat.le_of_ble_eq_true rfl
  rw [test_flipAssertPolarity_is_theory_mutant, test_flipAssertPolarity_is_theory_mutant,
      test_flipAssertPolarity_is_theory_mutant]
  exact ⟨(panic_strategy_abort_vs_unwind_add_iff .u16 40000 25535).2.2.1.2
           (Nat.le_of_ble_eq_true rfl),
         fun h => Nat.not_lt_of_le hOv128
           ((panic_strategy_abort_vs_unwind_add_iff .u128 u128Max 1).2.2.1.1 h),
         fun h => Nat.not_le_of_gt (Nat.lt_succ_self 0)
           ((panic_strategy_abort_vs_unwind_sub_iff .usize 0 1 h0LtSz h1LtSz).2.2.2.1 h),
         fun h => Nat.not_lt_of_le (Nat.le_of_ble_eq_true rfl)
           ((panic_strategy_abort_vs_unwind_add_scaled_iff .u16 4 65500 20).2.2.1.1 h),
         (assert_polarity_mutation_breaks_toPartial_add .u64 .abort 7 9).1
           (Nat.le_of_ble_eq_true rfl),
         (assert_polarity_mutation_breaks_toPartial_sub .u128 .unwind 0 1 h0Lt128 h1Lt128).2
           (Nat.lt_succ_self 0),
         (assert_polarity_mutation_breaks_toPartial_mul .u16 .abort 256 256).2
           (Nat.le_of_ble_eq_true rfl),
         ((unwind_unreachable_collapses_trap_separation .u128 .abort u128Max 1).1 hOv128).2,
         ((unwind_unreachable_collapses_trap_separation .usize .unwind 0 1).2.1
           h0LtSz h1LtSz (Nat.lt_succ_self 0)).2,
         ((unwind_unreachable_collapses_trap_separation .u16 .abort 256 256).2.2
           (Nat.le_of_ble_eq_true rfl)).2⟩

/-! ## 4. Programmatic `run_cmd` Hygiene Audit & `#print axioms` Checks -/

open Lean Elab Command in
run_cmd do
  let isConstructive (a : Name) : Bool :=
    a == ``propext || a == ``Quot.sound
  let isStandard (a : Name) : Bool :=
    a == ``propext || a == ``Quot.sound || a == ``Classical.choice
  -- Non-vacuity self-checks on both audit predicates (including synthetic `_native.*` rejection):
  let fakeNative : Name := Name.mkStr2 "_native" "fake"
  for banned in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler, ``Classical.choice, fakeNative] do
    if isConstructive banned then
      throwError "constructive predicate self-check failed: accepted {banned}"
  for banned in [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler, fakeNative] do
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
    , ``Anneal.Mir.OverflowTrapRefinement.mirOutcomeClass_toPartial_monotone
    , ``Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeRefines_iff_partial_le
    , ``Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeClass_toPartial_monotone
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_mono
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_ub_mono
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_settled_mono
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_fuel_stable
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_to_tauLeN
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_ub_to_tauLeN
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_faulted_to_tauLeN
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_to_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_ub_to_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.runMirSteps_faulted_to_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_toPartial_equiv_of_same_halted
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_toPartial_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeRefines_iff_mirCallTree_toPartial_le
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
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_const_right_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_refines_unchecked_iff_of_fuel
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_refines_unchecked_iff_of_fuel
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_refines_unchecked_iff_of_fuel
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_iff_of_fuel
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_refines_to_checked_of_fuel
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_sub_refines_to_checked_of_fuel
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
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_overflow_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_out_of_range_lhs_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_inner_mul_overflow_not_refines_unchecked
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_unchecked_add_scaled_inner_mul_ub_pinned
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_unchecked_add_scaled_outer_add_ub_pinned
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_checked_add_scaled_inner_mul_trap_pinned
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_checked_add_scaled_outer_add_trap_pinned
    , ``Anneal.Mir.OverflowTrapRefinement.add_scaled_failure_sites_pinned
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_toPartial_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_toPartial_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_toPartial_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_toPartial_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_wrapping_refines_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_wrapping_refines_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_wrapping_refines_iff
    , ``Anneal.Mir.OverflowTrapRefinement.mkCheckedArithBody_eq_withExpected_false
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_add_polarity_mutant
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_sub_polarity_mutant
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_mul_polarity_mutant
    , ``Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_refinement
    , ``Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_add_iff
    , ``Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_sub_iff
    , ``Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_mul_iff
    , ``Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_add_scaled_iff
    , ``Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_toPartial_add
    , ``Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_toPartial_sub
    , ``Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_toPartial_mul
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_checked_unreachable_ub
    , ``Anneal.Mir.OverflowTrapRefinement.unwind_unreachable_collapses_trap_separation ]
  -- Exact allowlist of coinductive `Anneal.ITree.WeakRef` / `Eutt` bridge corollaries in
  -- `Anneal.Mir.OverflowTrapRefinement` (these use `Classical.choice` solely via Lean 4
  -- `coinductive_fixpoint` in `Anneal.ITree`; NO other declaration in either module may).
  let allowedOverflowCoinductiveThms : List Name :=
    [ ``Anneal.Mir.OverflowTrapRefinement.eutt_ret_of_tauStar
    , ``Anneal.Mir.OverflowTrapRefinement.runMirCall_halted_eutt
    , ``Anneal.Mir.OverflowTrapRefinement.weakRef_of_faultNow
    , ``Anneal.Mir.OverflowTrapRefinement.not_weakRef_of_faultNow_ret
    , ``Anneal.Mir.OverflowTrapRefinement.not_weakRef_of_distinct_ret
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_weakRef_equiv_of_same_halted
    , ``Anneal.Mir.OverflowTrapRefinement.mirCallTree_weakRef_refines_ub
    , ``Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeRefines_iff_mirCallTree_weakRef
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_add_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_sub_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_mul_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.unchecked_add_scaled_weakRef_to_checked
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_weakRef_unchecked_of_farkas_cert
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_weakRef_corollaries
    , ``Anneal.Mir.OverflowTrapRefinement.weakRef_reverse_iff_of_dichotomy
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_weakRef_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_sub_weakRef_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_mul_weakRef_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_weakRef_refines_unchecked_iff
    , ``Anneal.Mir.OverflowTrapRefinement.checked_toWeakRef_refines_unchecked_iff ]
  let keyWeakRefBridgeDecls : List Name := allowedOverflowCoinductiveThms
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
  -- Exhaustive sweep: audit EVERY `.thmInfo` AND `.defnInfo` (public, private, and auxiliary)
  -- defined in `Anneal.FarkasMirCert`, `Anneal.Mir.OverflowTrapRefinement`, and this test
  -- module:
  -- - `Anneal.FarkasMirCert`: ZERO `Classical.choice` across ALL theorems AND definitions.
  -- - `Anneal.Mir.OverflowTrapRefinement`: `Classical.choice` is permitted ONLY on the exact
  --   `allowedOverflowCoinductiveThms` allowlist (each of whose statements must also mention
  --   `WeakRef`/`Eutt`) and their compiler-generated auxiliary matcher defs.
  let env ← getEnv
  let coinductiveRels : List Name := [``Anneal.ITree.WeakRef, ``Anneal.ITree.Eutt]
  let mentionsCoinductive (ty : Expr) : Bool :=
    ty.getUsedConstants.any (fun c => coinductiveRels.contains c)
  let auditDeclsInModule (mod : Name) (minThms minDefns : Nat)
      (allowedCoindThms : List Name) : CommandElabM String := do
    let some idx := env.header.moduleNames.findIdx? (· == mod)
      | throwError "audit: module {mod} is not imported"
    let mut nConstThm : Nat := 0
    let mut nCoindThm : Nat := 0
    let mut nConstDefn : Nat := 0
    let mut nCoindAuxDefn : Nat := 0
    let mut seenCoind : List Name := []
    for c in env.header.moduleData[idx]!.constNames do
      match env.find? c with
      | some (.thmInfo info) =>
        let axs ← liftCoreM <| Lean.collectAxioms c
        if axs.any (fun a => !isConstructive a) then
          unless mentionsCoinductive info.type && allowedCoindThms.contains c do
            throwError "unallowlisted non-constructive theorem in {mod}: {c} depends on {axs}"
          for a in axs do
            unless isStandard a do
              throwError "coinductive audit failure: {c} depends on non-standard symbol {a}"
          nCoindThm := nCoindThm + 1
          seenCoind := c :: seenCoind
        else
          nConstThm := nConstThm + 1
      | some (.defnInfo _) =>
        let axs ← liftCoreM <| Lean.collectAxioms c
        if axs.any (fun a => !isConstructive a) then
          unless allowedCoindThms.contains c.getPrefix do
            throwError "non-constructive definition in {mod}: {c} depends on {axs}"
          for a in axs do
            unless isStandard a do
              throwError "coinductive aux def audit failure: {c} depends on non-standard symbol {a}"
          nCoindAuxDefn := nCoindAuxDefn + 1
        else
          nConstDefn := nConstDefn + 1
      | _ => pure ()
    if nConstThm + nCoindThm < minThms then
      throwError "module theorem sweep vacuous for {mod}: {nConstThm + nCoindThm} < {minThms}"
    if nConstDefn + nCoindAuxDefn < minDefns then
      throwError "module defn sweep vacuous for {mod}: {nConstDefn + nCoindAuxDefn} < {minDefns}"
    if allowedCoindThms.isEmpty && (nCoindThm != 0 || nCoindAuxDefn != 0) then
      throwError "module {mod} must be 100% constructive, found coinductive decls"
    -- Allowlist exactness (duplicate-free set bijection): every allowlisted theorem must
    -- genuinely depend on `Classical.choice` in THIS module (no duplicates, stale, or
    -- over-broad entries).
    unless allowedCoindThms.eraseDups.length == allowedCoindThms.length do
      throwError "duplicate entry in coinductive allowlist for {mod}"
    for expected in allowedCoindThms do
      unless seenCoind.contains expected do
        throwError "over-broad coinductive allowlist: {expected} is not a Classical-dependent theorem of {mod}"
    unless seenCoind.length == allowedCoindThms.length do
      throwError "coinductive allowlist mismatch in {mod}: seen {seenCoind.length}, allowlisted {allowedCoindThms.length}"
    return s!"{mod}: {nConstThm}c+{nCoindThm}w thms, {nConstDefn}c+{nCoindAuxDefn}aux defs"
  let sFarkas ← auditDeclsInModule `Anneal.FarkasMirCert 195 390 []
  let sTrap ← auditDeclsInModule `Anneal.Mir.OverflowTrapRefinement 258 310
    allowedOverflowCoinductiveThms
  -- Every curated key declaration must live in one of the swept modules.
  for d in keyFarkasDecls ++ keyTrapConstructiveDecls ++ keyWeakRefBridgeDecls do
    let some mIdx := env.getModuleIdxFor? d
      | throwError "audit: curated declaration {d} is not imported"
    let modName := env.header.moduleNames[mIdx.toNat]!
    unless modName == `Anneal.FarkasMirCert || modName == `Anneal.Mir.OverflowTrapRefinement do
      throwError "audit: curated declaration {d} lives outside the swept modules ({modName})"
  -- Also audit every theorem and definition defined in this test module with an exact
  -- coinductive allowlist (preventing constructive tests from silently becoming coinductive):
  let allowedTestCoinductiveThms : List Name :=
    [ ``Anneal.Mir.FarkasMirCertAndTrapRefinementTests.test_weakRef_bridge_canaries
    , ``Anneal.Mir.FarkasMirCertAndTrapRefinementTests.test_weakRef_general_operational_iff
    , ``Anneal.Mir.FarkasMirCertAndTrapRefinementTests.test_tree_level_weakRef_reverse_iff ]
  unless allowedTestCoinductiveThms.eraseDups.length == allowedTestCoinductiveThms.length do
    throwError "duplicate entry in test coinductive allowlist"
  let mut constructiveTestTheorems : Nat := 0
  let mut weakRefTestTheorems : Nat := 0
  let mut seenTestCoind : List Name := []
  let mut constructiveTestDefns : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    match info with
    | .thmInfo thm =>
      let axs ← liftCoreM <| Lean.collectAxioms c
      if axs.any (fun a => !isConstructive a) then
        unless mentionsCoinductive thm.type && allowedTestCoinductiveThms.contains c do
          throwError "unallowlisted non-constructive test theorem: {c} depends on {axs}"
        for a in axs do
          unless isStandard a do
            throwError "coinductive test audit failure: {c} depends on non-standard symbol {a}"
        weakRefTestTheorems := weakRefTestTheorems + 1
        seenTestCoind := c :: seenTestCoind
      else
        constructiveTestTheorems := constructiveTestTheorems + 1
    | .defnInfo _ =>
      let axs ← liftCoreM <| Lean.collectAxioms c
      for a in axs do
        unless isConstructive a do
          throwError "constructive test defn audit failure: {c} depends on disallowed symbol {a}"
      constructiveTestDefns := constructiveTestDefns + 1
    | _ => pure ()
  for expected in allowedTestCoinductiveThms do
    unless seenTestCoind.contains expected do
      throwError "over-broad test coinductive allowlist: {expected} is not Classical-dependent"
  unless seenTestCoind.length == allowedTestCoinductiveThms.length do
    throwError "test coinductive allowlist mismatch: seen {seenTestCoind.length}, allowlisted {allowedTestCoinductiveThms.length}"
  if constructiveTestTheorems < 31 || weakRefTestTheorems != 3 || constructiveTestDefns < 15 then
    throwError "test audit is vacuous: thms={constructiveTestTheorems}c+{weakRefTestTheorems}w, defs={constructiveTestDefns}"
  logInfo m!"hygiene audit passed: [{sFarkas}; {sTrap}]; curated {keyFarkasDecls.length} FarkasMirCert + {keyTrapConstructiveDecls.length} constructive OverflowTrapRefinement + {keyWeakRefBridgeDecls.length} WeakRef bridges; test module {constructiveTestTheorems}c+{weakRefTestTheorems}w thms, {constructiveTestDefns}c defs (0 sorryAx, 0 ofReduceBool, 0 trustCompiler, Classical.choice strictly allowlisted under WeakRef/Eutt)"

#print axioms Anneal.Mir.OverflowTrapRefinement.mirOutcomeRefines_iff_partial_le
#print axioms Anneal.Mir.OverflowTrapRefinement.runMirSteps_halted_to_tauLeN
#print axioms Anneal.Mir.OverflowTrapRefinement.mirExactOutcomeRefines_iff_mirCallTree_toPartial_le
#print axioms Anneal.Mir.OverflowTrapRefinement.unchecked_add_refines_to_checked
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_refines_unchecked_iff
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_refines_unchecked_of_farkas_cert
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_overflow_not_refines_wrapping
#print axioms Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_distinct
#print axioms Anneal.Mir.OverflowTrapRefinement.panic_strategy_abort_vs_unwind_add_iff
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_sub_out_of_range_lhs_not_refines_unchecked
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_scaled_inner_mul_overflow_not_refines_unchecked
#print axioms Anneal.Mir.OverflowTrapRefinement.runMirCall_checked_add_scaled_outer_add_trap_pinned
#print axioms Anneal.Mir.OverflowTrapRefinement.add_scaled_failure_sites_pinned
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_add_wrapping_refines_iff
#print axioms Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_refinement
#print axioms Anneal.Mir.OverflowTrapRefinement.assert_polarity_mutation_breaks_toPartial_add
#print axioms Anneal.Mir.OverflowTrapRefinement.unwind_unreachable_collapses_trap_separation
#print axioms Anneal.Mir.OverflowTrapRefinement.runMirSteps_faulted_to_tauStar
#print axioms Anneal.Mir.OverflowTrapRefinement.checked_mul_const_right_refines_unchecked_of_farkas_cert
#print axioms Anneal.Mir.OverflowTrapRefinement.unchecked_refines_to_checked_of_fuel
#print axioms Anneal.FarkasMirCert.checkFarkasMirGoal_sound

end Anneal.Mir.FarkasMirCertAndTrapRefinementTests
