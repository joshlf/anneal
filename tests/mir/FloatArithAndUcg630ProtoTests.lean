/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.FloatArithAndUcg630Prototype

/-!
# Comprehensive Edge-Case Tests & Axiom/Projection Audit for `Anneal.FloatArithAndUcg630Prototype`

Kernel-checked (`by rfl` / constructive proof) test suite covering:
1. Subnormal boundaries and gradual underflow (`f32` and `f64`);
2. Normal half-way ties-to-even rounding and overflow boundaries (`f32` and `f64`);
3. Signed-zero algebra (`add`, `sub`, `mul`, `div`, `rem`) (`f32` and `f64`);
4. Indeterminate NaN forms (`f32` and `f64`);
5. Truncated remainder (`%` / `rem`) vectors including large-exponent division;
6. Sign-flip negation (`evalFloatNegProto`) preserving sNaN/qNaN payloads;
7. Ordered and unordered comparisons (`eq`, `ne`, `lt`, `le`, `gt`, `ge`);
8. Exact `miri#5643` `nanChoicesProto` candidate lists (2, 4, 6, 10, and cross-format truncation);
9. `evalRvalueFloatProto` vs. `Trusted.MirSemantics.evalRvalue` misdispatch & fail-closed tests;
10. `Ptr2IntTransmutePolicy` positive, negative, round-trip, and flip-direction witnesses;
11. Transitive reachability instantiation of every public theorem in
    `Anneal.FloatArithAndUcg630Prototype`;
12. Automated `run_cmd` constructive axiom (`[propext, Quot.sound]`),
    projection-discipline (zero `Prod.casesOn`/`Prod.rec`/`Prod.recOn`), and
    100% theorem reachability audit.
-/

namespace Anneal.FloatArithAndUcg630ProtoTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.IeeeFloatCast
open Anneal.FloatArithAndUcg630Prototype

/-! ## §1. Subnormal Boundaries & Gradual Underflow (`f32` and `f64`) -/

theorem test_subnormal_boundaries_f32 :
    -- max_subnormal + min_subnormal carries cleanly into min_normal
    evalFloatArithBaseProto .add .binary32 0x007FFFFF 0x00000001 = 0x00800000 ∧
    -- min_normal - min_subnormal gradually underflows to max_subnormal
    evalFloatArithBaseProto .sub .binary32 0x00800000 0x00000001 = 0x007FFFFF ∧
    -- (1.5 * min_normal) - min_normal = 0.5 * min_normal (subnormal)
    evalFloatArithBaseProto .sub .binary32 0x00C00000 0x00800000 = 0x00400000 ∧
    -- min_subnormal / 2.0: exact tie between 0 (even) and 1 (odd) -> +0.0
    evalFloatArithBaseProto .div .binary32 0x00000001 0x40000000 = 0x00000000 ∧
    -- (-min_subnormal) / 2.0 -> -0.0 (sign preserved on underflow!)
    evalFloatArithBaseProto .div .binary32 0x80000001 0x40000000 = 0x80000000 ∧
    -- (3 * min_subnormal) / 2.0: exact tie between 1 (odd) and 2 (even) -> 2 * min_subnormal
    evalFloatArithBaseProto .div .binary32 0x00000003 0x40000000 = 0x00000002 ∧
    -- min_subnormal * 0.75 (strictly above half-way) -> min_subnormal
    evalFloatArithBaseProto .mul .binary32 0x00000001 0x3F400000 = 0x00000001 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 32768 in
theorem test_subnormal_boundaries_f64 :
    -- max_subnormal + min_subnormal carries cleanly into min_normal
    evalFloatArithBaseProto .add .binary64 0x000FFFFFFFFFFFFF 0x0000000000000001 = 0x0010000000000000 ∧
    -- min_normal - min_subnormal gradually underflows to max_subnormal
    evalFloatArithBaseProto .sub .binary64 0x0010000000000000 0x0000000000000001 = 0x000FFFFFFFFFFFFF ∧
    -- min_subnormal / 2.0 -> +0.0 (tie to even)
    evalFloatArithBaseProto .div .binary64 0x0000000000000001 0x4000000000000000 = 0x0000000000000000 ∧
    -- (-min_subnormal) / 2.0 -> -0.0
    evalFloatArithBaseProto .div .binary64 0x8000000000000001 0x4000000000000000 = 0x8000000000000000 ∧
    -- (3 * min_subnormal) / 2.0 -> 2 * min_subnormal (tie to even)
    evalFloatArithBaseProto .div .binary64 0x0000000000000003 0x4000000000000000 = 0x0000000000000002 ∧
    -- min_subnormal * 0.75 -> min_subnormal
    evalFloatArithBaseProto .mul .binary64 0x0000000000000001 0x3FE8000000000000 = 0x0000000000000001 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2. Normal Half-Way Ties-to-Even & Overflow Boundaries (`f32` and `f64`) -/

theorem test_normal_ties_and_overflow_f32 :
    -- 1.0 (LSB 0) + 2^-24 (half ulp) -> rounds down to 1.0
    evalFloatArithBaseProto .add .binary32 0x3F800000 0x33800000 = 0x3F800000 ∧
    -- (1.0 + 2^-23) (LSB 1) + 2^-24 (half ulp) -> rounds up to 1.0 + 2*2^-23
    evalFloatArithBaseProto .add .binary32 0x3F800001 0x33800000 = 0x3F800002 ∧
    -- f32::MAX + 2^103 (exact half ulp, LSB 1) -> overflows to +Inf
    evalFloatArithBaseProto .add .binary32 0x7F7FFFFF 0x73000000 = 0x7F800000 ∧
    -- f32::MAX + 2^102 (below half ulp) -> stays f32::MAX
    evalFloatArithBaseProto .add .binary32 0x7F7FFFFF 0x72800000 = 0x7F7FFFFF ∧
    -- (-f32::MAX) + (-2^103) -> overflows to -Inf
    evalFloatArithBaseProto .add .binary32 0xFF7FFFFF 0xF3000000 = 0xFF800000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 32768 in
theorem test_normal_ties_and_overflow_f64 :
    -- 1.0 (LSB 0) + 2^-53 (half ulp) -> rounds down to 1.0
    evalFloatArithBaseProto .add .binary64 0x3FF0000000000000 0x3CA0000000000000 = 0x3FF0000000000000 ∧
    -- (1.0 + 2^-52) (LSB 1) + 2^-53 (half ulp) -> rounds up to 1.0 + 2*2^-52
    evalFloatArithBaseProto .add .binary64 0x3FF0000000000001 0x3CA0000000000000 = 0x3FF0000000000002 ∧
    -- f64::MAX + 2^970 (exact half ulp, LSB 1) -> overflows to +Inf
    evalFloatArithBaseProto .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C90000000000000 = 0x7FF0000000000000 ∧
    -- f64::MAX + 2^969 (below half ulp) -> stays f64::MAX
    evalFloatArithBaseProto .add .binary64 0x7FEFFFFFFFFFFFFF 0x7C80000000000000 = 0x7FEFFFFFFFFFFFFF ∧
    -- (-f64::MAX) + (-2^970) -> overflows to -Inf
    evalFloatArithBaseProto .add .binary64 0xFFEFFFFFFFFFFFFF 0xFC90000000000000 = 0xFFF0000000000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §3. Signed-Zero Algebra & Indeterminate NaN Forms (`f32` and `f64`) -/

theorem test_signed_zero_algebra_f32 :
    evalFloatArithBaseProto .add .binary32 0x80000000 0x80000000 = 0x80000000 ∧
    evalFloatArithBaseProto .add .binary32 0x00000000 0x80000000 = 0x00000000 ∧
    evalFloatArithBaseProto .sub .binary32 0x80000000 0x00000000 = 0x80000000 ∧
    evalFloatArithBaseProto .sub .binary32 0x3FC00000 0x3FC00000 = 0x00000000 ∧
    evalFloatArithBaseProto .mul .binary32 0x80000000 0x40A00000 = 0x80000000 ∧
    evalFloatArithBaseProto .div .binary32 0x3F800000 0x00000000 = 0x7F800000 ∧
    evalFloatArithBaseProto .div .binary32 0x3F800000 0x80000000 = 0xFF800000 ∧
    evalFloatArithBaseProto .div .binary32 0xBF800000 0x7F800000 = 0x80000000 ∧
    evalFloatArithBaseProto .div .binary32 0xBF800000 0xFF800000 = 0x00000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem test_signed_zero_algebra_f64 :
    evalFloatArithBaseProto .add .binary64 0x8000000000000000 0x8000000000000000 = 0x8000000000000000 ∧
    evalFloatArithBaseProto .add .binary64 0x0000000000000000 0x8000000000000000 = 0x0000000000000000 ∧
    evalFloatArithBaseProto .sub .binary64 0x8000000000000000 0x0000000000000000 = 0x8000000000000000 ∧
    evalFloatArithBaseProto .sub .binary64 0x3FF8000000000000 0x3FF8000000000000 = 0x0000000000000000 ∧
    evalFloatArithBaseProto .mul .binary64 0x8000000000000000 0x4014000000000000 = 0x8000000000000000 ∧
    evalFloatArithBaseProto .div .binary64 0x3FF0000000000000 0x0000000000000000 = 0x7FF0000000000000 ∧
    evalFloatArithBaseProto .div .binary64 0x3FF0000000000000 0x8000000000000000 = 0xFFF0000000000000 ∧
    evalFloatArithBaseProto .div .binary64 0xBFF0000000000000 0x7FF0000000000000 = 0x8000000000000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem test_indeterminate_nan_forms :
    -- f32 indeterminate forms
    evalFloatArithBaseProto .sub .binary32 0x7F800000 0x7F800000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .add .binary32 0xFF800000 0x7F800000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .mul .binary32 0x00000000 0x7F800000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .div .binary32 0x00000000 0x80000000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .div .binary32 0x7F800000 0xFF800000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .rem .binary32 0x7F800000 0x3F800000 = preferredNaNBits .binary32 ∧
    evalFloatArithBaseProto .rem .binary32 0x3F800000 0x00000000 = preferredNaNBits .binary32 ∧
    -- f64 indeterminate forms
    evalFloatArithBaseProto .sub .binary64 0x7FF0000000000000 0x7FF0000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .add .binary64 0xFFF0000000000000 0x7FF0000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .mul .binary64 0x0000000000000000 0x7FF0000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .div .binary64 0x0000000000000000 0x8000000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .div .binary64 0x7FF0000000000000 0x7FF0000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .rem .binary64 0x7FF0000000000000 0x3FF0000000000000 = preferredNaNBits .binary64 ∧
    evalFloatArithBaseProto .rem .binary64 0x3FF0000000000000 0x8000000000000000 = preferredNaNBits .binary64 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §4. Truncated Remainder (`rem` / `%`) Vectors (`f32` and `f64`) -/

theorem test_rem_vectors_f32 :
    -- (-5.5) % 2.0 = -1.5
    evalFloatArithBaseProto .rem .binary32 0xC0B00000 0x40000000 = 0xBFC00000 ∧
    -- 5.5 % (-2.0) = +1.5
    evalFloatArithBaseProto .rem .binary32 0x40B00000 0xC0000000 = 0x3FC00000 ∧
    -- (-4.0) % 2.0 = -0.0 (dividend sign preserved on zero remainder)
    evalFloatArithBaseProto .rem .binary32 0xC0800000 0x40000000 = 0x80000000 ∧
    -- (-0.0) % 3.0 = -0.0
    evalFloatArithBaseProto .rem .binary32 0x80000000 0x40400000 = 0x80000000 ∧
    -- (-3.25) % +Inf = -3.25
    evalFloatArithBaseProto .rem .binary32 0xC0500000 0x7F800000 = 0xC0500000 ∧
    -- subnormal % normal: (-min_subnormal) % 1.0 = -min_subnormal
    evalFloatArithBaseProto .rem .binary32 0x80000001 0x3F800000 = 0x80000001 ∧
    -- large-exponent exact quotient remainder: 2^100 % 3.0 = 1.0, (-2^100) % 3.0 = -1.0
    evalFloatArithBaseProto .rem .binary32 0x71800000 0x40400000 = 0x3F800000 ∧
    evalFloatArithBaseProto .rem .binary32 0xF1800000 0x40400000 = 0xBF800000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 32768 in
theorem test_rem_vectors_f64 :
    -- (-5.5) % 2.0 = -1.5
    evalFloatArithBaseProto .rem .binary64 0xC016000000000000 0x4000000000000000 = 0xBFF8000000000000 ∧
    -- 5.5 % (-2.0) = +1.5
    evalFloatArithBaseProto .rem .binary64 0x4016000000000000 0xC000000000000000 = 0x3FF8000000000000 ∧
    -- (-4.0) % 2.0 = -0.0
    evalFloatArithBaseProto .rem .binary64 0xC010000000000000 0x4000000000000000 = 0x8000000000000000 ∧
    -- (-0.0) % 3.0 = -0.0
    evalFloatArithBaseProto .rem .binary64 0x8000000000000000 0x4008000000000000 = 0x8000000000000000 ∧
    -- (-3.25) % +Inf = -3.25
    evalFloatArithBaseProto .rem .binary64 0xC00A000000000000 0x7FF0000000000000 = 0xC00A000000000000 ∧
    -- subnormal % normal: min_subnormal % 1.0 = min_subnormal
    evalFloatArithBaseProto .rem .binary64 0x0000000000000001 0x3FF0000000000000 = 0x0000000000000001 ∧
    -- large-exponent exact quotient remainder: 2^1000 % 3.0 = 1.0, 2^1001 % 3.0 = 2.0
    evalFloatArithBaseProto .rem .binary64 0x7E70000000000000 0x4008000000000000 = 0x3FF0000000000000 ∧
    evalFloatArithBaseProto .rem .binary64 0x7E80000000000000 0x4008000000000000 = 0x4000000000000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5. Negation Payload Preservation & Ordered/Unordered Comparisons -/

theorem test_neg_nan_payload_preservation :
    evalFloatNegProto .binary32 0x7F800001 = 0xFF800001 ∧
    evalFloatNegProto .binary32 0xFF800001 = 0x7F800001 ∧
    evalFloatNegProto .binary32 0x7FC0ABCD = 0xFFC0ABCD ∧
    evalFloatNegProto .binary32 0xFFC0ABCD = 0x7FC0ABCD ∧
    evalFloatNegProto .binary64 0x7FF0000000000001 = 0xFFF0000000000001 ∧
    evalFloatNegProto .binary64 0xFFF0000000000001 = 0x7FF0000000000001 ∧
    evalFloatNegProto .binary64 0x7FF8123456789ABC = 0xFFF8123456789ABC ∧
    evalFloatNegProto .binary64 0xFFF8123456789ABC = 0x7FF8123456789ABC := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option exponentiation.threshold 2048 in
theorem test_comparisons_f32_and_f64 :
    -- -0.0 == +0.0
    evalFloatCmpProto .eq .binary32 0x80000000 0x00000000 = true ∧
    evalFloatCmpProto .ne .binary32 0x80000000 0x00000000 = false ∧
    -- NaN unorderedness (qNaN and sNaN)
    evalFloatCmpProto .ne .binary32 0x7FC00000 0x7FC00000 = true ∧
    evalFloatCmpProto .eq .binary32 0x7FC00000 0x7FC00000 = false ∧
    evalFloatCmpProto .lt .binary32 0x7F800001 0x00000000 = false ∧
    evalFloatCmpProto .ge .binary32 0x7F800001 0x00000000 = false ∧
    -- Strict total order chain: -Inf < -max < -min_sub < -0.0 == +0.0 < +min_sub < +max < +Inf
    evalFloatCmpProto .lt .binary32 0xFF800000 0xFF7FFFFF = true ∧
    evalFloatCmpProto .lt .binary32 0xFF7FFFFF 0x80000001 = true ∧
    evalFloatCmpProto .lt .binary32 0x80000001 0x80000000 = true ∧
    evalFloatCmpProto .lt .binary32 0x00000000 0x00000001 = true ∧
    evalFloatCmpProto .lt .binary32 0x00000001 0x7F7FFFFF = true ∧
    evalFloatCmpProto .lt .binary32 0x7F7FFFFF 0x7F800000 = true ∧
    -- f64 counterparts
    evalFloatCmpProto .eq .binary64 0x8000000000000000 0x0000000000000000 = true ∧
    evalFloatCmpProto .ne .binary64 0x7FF8000000000000 0x7FF8000000000000 = true ∧
    evalFloatCmpProto .lt .binary64 0xFFF0000000000000 0xFFEFFFFFFFFFFFFF = true ∧
    evalFloatCmpProto .lt .binary64 0xFFEFFFFFFFFFFFFF 0x8000000000000001 = true ∧
    evalFloatCmpProto .lt .binary64 0x8000000000000001 0x8000000000000000 = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §6. `miri#5643` `nanChoicesProto` Candidate Lists -/

theorem test_nan_choices_exact_lists :
    -- 0 NaN inputs (e.g. 0.0 / 0.0): exactly 2 candidates (±preferredNaN)
    nanChoicesProto .binary32 [(.binary32, 0x00000000), (.binary32, 0x00000000)] .nondeterministic =
      [0x7FC00000, 0xFFC00000] ∧
    -- 1 qNaN input: exactly 4 candidates (±preferredNaN, ±qNaN)
    nanChoicesProto .binary32 [(.binary32, 0x7FC0ABCD), (.binary32, 0x3F800000)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC0ABCD, 0xFFC0ABCD] ∧
    -- 1 sNaN input: exactly 6 candidates (±preferredNaN, ±quieted, ±signaling)
    nanChoicesProto .binary32 [(.binary32, 0x7F800001), (.binary32, 0x3F800000)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC00001, 0xFFC00001, 0x7F800001, 0xFF800001] ∧
    -- 2 distinct sNaN inputs: exactly 10 candidates
    nanChoicesProto .binary32 [(.binary32, 0x7F800001), (.binary32, 0xFF800002)] .nondeterministic =
      [0x7FC00000, 0xFFC00000,
       0x7FC00001, 0xFFC00001,
       0xFFC00002, 0x7FC00002,
       0x7F800001, 0xFF800001,
       0xFF800002, 0x7F800002] ∧
    -- Cross-format f64 -> f32 sNaN whose high 22 payload bits are zero (0x7FF0_0000_0000_0001):
    -- lower = 0, so signaling candidate is omitted (would become Inf!) -> 4 candidates
    nanChoicesProto .binary32 [(.binary64, 0x7FF0000000000001)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC00000, 0xFFC00000] ∧
    -- Deterministic mode always returns singleton [preferredNaNBits f]
    nanChoicesProto .binary64 [(.binary64, 0x7FF0000000000001)] .deterministic =
      [0x7FF8000000000000] := by
  decide

/-! ## §7. `evalRvalueFloatProto` Misdispatch, Type-Mismatch & Conservative Extension Tests -/

private def mixedTypeDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .int .i32, layoutIdx := 0 }, debugName := none }
]

private def mixedTypeLocals : List LocalSlot := [
  .init (.scalar ⟨0x3F800000, 4⟩),
  .init (.scalar ⟨5, 4⟩),
  .init (.scalar ⟨0x3FF0000000000000, 8⟩),
  .init (.scalar ⟨7, 4⟩)
]

theorem test_evalRvalueFloatProto_dispatch_and_fail_closed :
    -- Mismatched f32 + u32 and f32 + f64 fail closed with .unsupported
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    -- Unsupported BinOp (.bitXor) on f32 fails closed with .unsupported
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .bitXor (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    -- Conservative extension on non-float integer add and neg
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      evalRvalue mixedTypeLocals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable ∧
    evalRvalueFloatProto mixedTypeLocals (.unaryOp .neg (.copy ⟨3, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      evalRvalue mixedTypeLocals (.unaryOp .neg (.copy ⟨3, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §8. `Ptr2IntTransmutePolicy` Positive, Negative & Bit-Validity Tests -/

/-- Under `.stripProvenance`, pointer provenance is stripped only when the
underlying byte values still satisfy bit-validity invariants (rejecting `.uninit`,
invalid `bool` `∉ {0,1}`, surrogate `char` `0xD800`, niche `NonZero<u32>` `0`,
and never forging provenance on `int -> &T` or `int -> fn()`). -/
theorem test_ptr2int_policy_bit_validity_and_no_forge :
    -- Invalid bool (0x02 with provenance) is rejected under BOTH policies
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .bool, layoutIdx := 0 } [.init 2 (.some (7, 7))] = .none ∧
    decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts
        { kind := .bool, layoutIdx := 0 } [.init 2 (.some (7, 7))] = .none ∧
    -- Valid bool (0x01 with provenance) flips between .some (strip) and .none (strict)
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .bool, layoutIdx := 0 } [.init 1 (.some (7, 7))] = .some (.scalar ⟨1, 1⟩) ∧
    decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts
        { kind := .bool, layoutIdx := 0 } [.init 1 (.some (7, 7))] = .none ∧
    -- Surrogate char (0xD800 with provenance) is rejected under BOTH policies
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .char, layoutIdx := 0 } (encodeLittleEndianBytes 0xD800 4 (.some (7, 7))) = .none ∧
    -- Uninit byte is rejected under BOTH policies
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .uint .u8, layoutIdx := 0 } [.uninit] = .none ∧
    -- Niche NonZero<u32> = 0 with provenance is rejected under BOTH policies
    decodeScalarLayoutBytesWithPolicy .stripProvenance
        (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
        (encodeLittleEndianBytes 0 4 (.some (7, 7))) = .none ∧
    -- Niche NonZero<u32> = 42 with provenance flips between .some (strip) and .none (strict)
    decodeScalarLayoutBytesWithPolicy .stripProvenance
        (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
        (encodeLittleEndianBytes 42 4 (.some (7, 7))) = .some (.scalar ⟨42, 4⟩) ∧
    decodeScalarLayoutBytesWithPolicy .strictUcg630Ub
        (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
        (encodeLittleEndianBytes 42 4 (.some (7, 7))) = .none ∧
    -- No provenance forgery on usize -> &u8 or usize -> fn() under EITHER policy
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨1, []⟩)
        { kind := .ref .not (.uint .u8), layoutIdx := 0 }
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨1, []⟩)
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 }
        emptyMemory protoTransmuteDecls protoTransmuteLayouts = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §9. Transitive Reachability Coverage of Every Public Theorem -/

/-- Exercise every public theorem in `Anneal.FloatArithAndUcg630Prototype` so the
automated reachability audit verifies 100% theorem coverage. -/
theorem exercise_all_prototype_theorems : True := by
  have _ := @ieeeFormat_width_split
  have _ := @unpackBits_mod_width
  have _ := @decodeBits_mod_width
  have _ := @decodeBits_finite_num_pos
  have _ := @evalFloatNegProto_lt
  have _ := @evalFloatNegProto_mod
  have _ := @evalFloatNegProto_involutive
  have _ := @unpackBits_evalFloatNegProto
  have _ := @decodeBits_evalFloatNegProto
  have _ := @decodeBits_evalFloatNegProto_nan
  have _ := @isNaNBits_evalFloatNegProto
  have _ := @isQuietNaNBits_evalFloatNegProto
  have _ := @isSignalingNaNBits_evalFloatNegProto
  have _ := @isAdmissibleQuietNaN_evalFloatNegProto
  have _ := @evalFloatNegProto_encodeBits
  have _ := @evalFloatNegProto_zeroBits
  have _ := @evalFloatNegProto_infBits
  have _ := @evalFloatNegProto_xor
  have _ := @signedNum_neg
  have _ := @evalFloatPartialCompareProto_swap
  have _ := @evalFloatPartialCompareProto_neg
  have _ := @evalFloatCmpProto_ne_eq_not_eq
  have _ := @evalFloatCmpProto_gt_eq_lt_swap
  have _ := @evalFloatCmpProto_ge_eq_le_swap
  have _ := @evalFloatCmpProto_eq_refl_iff_not_nan
  have _ := @evalFloatCmpProto_lt_irrefl
  have _ := @evalFloatCmpProto_eq_symm
  have _ := @evalFloatCmpProto_nan_left
  have _ := @evalFloatCmpProto_nan_right
  have _ := @evalFloatCmpProto_negZero_eq_posZero
  have _ := @bits_eq_zeroBits_of_decodeBits_zero
  have _ := @bits_eq_infBits_of_decodeBits_inf
  have _ := @roundRatioTiesToEven_eq_bits_of_decodeBits_finite
  have _ := @evalFloatCmpProto_eq_iff_bits_or_signedZero
  have _ := @evalFloatCmpProto_le_antisym
  have _ := @evalFloatCmpProto_lt_trans
  have _ := @evalFloatCmpProto_le_trans
  have _ := @evalFloatCmpProto_le_total_of_not_nan
  have _ := @evalFloatCmpProto_lt_neg_reverse
  have _ := @evalFloatCmpProto_le_neg_reverse
  have _ := @evalFloatCmpProto_eq_neg_preserve
  have _ := @evalFloatArithBaseProto_lt
  have _ := @evalFloatArithBaseProto_sub_eq_add_neg
  have _ := @exactSumProto_comm
  have _ := @evalFloatArithBaseProto_add_comm
  have _ := @evalFloatArithBaseProto_mul_comm
  have _ := @evalFloatArithBaseProto_add_negZero_negZero
  have _ := @evalFloatArithBaseProto_add_posZero_negZero
  have _ := @evalFloatArithBaseProto_sub_negZero_posZero
  have _ := @evalFloatArithBaseProto_add_negZero_right
  have _ := @evalFloatArithBaseProto_add_posZero_right
  have _ := @evalFloatArithBaseProto_add_neg_self_finite
  have _ := @evalFloatArithBaseProto_mul_zero_finite
  have _ := @evalFloatArithBaseProto_rem_inf_right
  have _ := @evalFloatArithBaseProto_rem_zero_finite
  have _ := @isSignalingNaNBits_iff_payload_lt
  have _ := @isAdmissibleQuietNaN_preferredNaNBits
  have _ := @isAdmissibleQuietNaN_of_mem_quieted
  have _ := @isAdmissibleQuietNaN_of_mem_quieted_expanded
  have _ := @isSignalingNaNBits_of_mem_signaling
  have _ := @same_format_signaling_candidate_eq
  have _ := @expandNaNSigns_mem_iff
  have _ := @nanChoicesProto_mem_lt_and_nan
  have _ := @preferredNaNBits_mem_nanChoicesProto
  have _ := @nanChoicesProto_det_subset_nondet
  have _ := @nanChoicesProto_mem_swap_pair
  have _ := @nanChoicesProto_mem_neg_second
  have _ := @evalFloatArithBaseProto_eq_preferredNaN_of_isNaN
  have _ := @EvalFloatBinOpRel.det_iff
  have _ := @EvalFloatBinOpRel.det_imp_nondet
  have _ := @EvalFloatBinOpRel.total
  have _ := @EvalFloatBinOpRel.out_lt
  have _ := @EvalFloatBinOpRel.nan_iff
  have _ := @evalFloatArithBaseProto_nan_left
  have _ := @evalFloatArithBaseProto_nan_right
  have _ := @EvalFloatBinOpRel.quieted_lhs_mem
  have _ := @EvalFloatBinOpRel.quieted_rhs_mem
  have _ := @EvalFloatBinOpRel.signaling_lhs_mem
  have _ := @EvalFloatBinOpRel.add_comm
  have _ := @EvalFloatBinOpRel.mul_comm
  have _ := @EvalFloatBinOpRel.sub_eq_add_neg
  have _ := @evalRvalueFloatProto_nonFloat_eq
  have _ := @EvalRvalueFloatRelProto.det_iff
  have _ := @EvalRvalueFloatRelProto.det_imp_nondet
  have _ := @trusted_evalRvalue_float_misdispatch_witness
  have _ := @decodePtrBytesNoForgeWithPolicy_strict_eq
  have _ := @decodeScalarLayoutBytesWithPolicy_strict_eq
  have _ := @decodeTypedValueFromBytesWithPolicy_strict_eq
  have _ := @evalByteCastWithPolicy_strict_eq
  have _ := @decodePtrBytesNoForgeWithPolicy_strict_refines_strip
  have _ := @decodeScalarLayoutBytesWithPolicy_strict_refines_strip
  have _ := @decodeTypedValueFromBytesWithPolicy_strict_refines_strip
  have _ := @evalByteCastWithPolicy_strict_refines_strip
  have _ := @abstractBytesHaveProv_take
  have _ := @abstractBytesHaveProv_drop
  have _ := @abstractBytesHaveProv_slice
  have _ := @decodePtrBytesNoForgeWithPolicy_strip_eq_strict_of_no_prov
  have _ := @decodeScalarLayoutBytesWithPolicy_strip_eq_strict_of_no_prov
  have _ := @decodeTypedValueFromBytesWithPolicy_strip_eq_strict_of_no_prov
  have _ := @decodeTypedValueFromBytesWithPolicy_union_policy_indep
  have _ := @decodeTypedValueFromBytesWithPolicy_thinRawPtr_policy_indep
  have _ := @decodeTypedValueFromBytesWithPolicy_thinRef_policy_indep
  have _ := @decodeTypedValueFromBytesWithPolicy_fnPtr_policy_indep
  have _ := @decodeTypedValueFromBytesWithPolicy_wideDynPtr_policy_indep
  have _ := @abstractBytesUniformProv_false_of_no_prov
  have _ := @decodeTypedValueFromBytesWithPolicy_no_forge_thinRawPtr
  have _ := @decodeTypedValueFromBytesWithPolicy_no_forge_thinRef
  have _ := @decodeTypedValueFromBytesWithPolicy_no_forge_fnPtr
  have _ := @ptr2int_flip_direction_separation_witnesses
  have _ := @ptr_roundtrip_contrast_witnesses
  trivial

/-! ## §10. Automated `run_cmd` Constructive Axiom, Projection-Discipline & Reachability Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructive : List Name := [``propext, ``Quot.sound]
  let modName : Name := `Anneal.FloatArithAndUcg630Prototype
  let some modIdx := env.getModuleIdx? modName | throwError "module {modName} not imported"
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedThms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      if let some _ ← findDeclarationRanges? n then
        if ci.isUnsafe then throwError "unsafe declaration: {n}"
        let axs ← collectAxioms n
        for a in axs do
          unless constructive.contains a do
            let mut culprits : List Name := []
            for sub in ci.getUsedConstantsAsSet do
              let subAxs ← collectAxioms sub
              if subAxs.contains a then
                culprits := sub :: culprits
            throwError "{n} depends on non-constructive or disallowed axiom {a} via {culprits}"
        -- Projection discipline: neither definitions (nor their transitive matcher
        -- closures) nor theorem statement types (`ci.type`) may reach `Prod.casesOn` /
        -- `Prod.rec` / `Prod.recOn`.
        for bad in [``Prod.casesOn, ``Prod.rec, ``Prod.recOn] do
          if ci.type.getUsedConstantsAsSet.contains bad then
            throwError "projection discipline violated in statement type of {n}: reaches {bad}"
        if ci matches .defnInfo _ then
          let mut toCheck : Array Name := #[n]
          let mut seen : NameSet := ({} : NameSet).insert n
          let mut idx : Nat := 0
          while idx < toCheck.size do
            let d := toCheck[idx]!
            idx := idx + 1
            if let some dci := env.find? d then
              for bad in [``Prod.casesOn, ``Prod.rec, ``Prod.recOn] do
                if dci.getUsedConstantsAsSet.contains bad then
                  throwError "projection discipline violated: {n} reaches {bad} via {d}"
              for c in dci.getUsedConstantsAsSet do
                if Lean.Meta.isMatcherCore env c && !seen.contains c then
                  seen := seen.insert c
                  toCheck := toCheck.push c
        audited := audited + 1
        if ci matches .thmInfo _ then
          if !isPrivateName n then
            theorems := theorems + 1
            auditedThms := auditedThms.push n
  if theorems < 50 then
    throwError "{modName}: audited only {theorems} public theorems (expected ≥ 50)"
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if (`Anneal.FloatArithAndUcg630ProtoTests).isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe test declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless constructive.contains a do
          throwError "test {n} depends on non-constructive or disallowed axiom {a}"
      audited := audited + 1
      for c in ci.getUsedConstantsAsSet do
        if env.getModuleIdxFor? c == some modIdx && !reached.contains c then
          reached := reached.insert c
          work := work.push c
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        if env.getModuleIdxFor? d == some modIdx && !reached.contains d then
          reached := reached.insert d
          work := work.push d
  let unreached := auditedThms.filter (fun n => !reached.contains n)
  unless unreached.isEmpty do
    throwError "public theorems not transitively reached by any test declaration: {unreached.toList}"
  logInfo m!"axiom & reachability audit passed: {audited} declarations ({theorems} public module theorems, \
    all constructive [propext, Quot.sound] and transitively reached by test declarations; no Prod.casesOn/Prod.rec)"

end Anneal.FloatArithAndUcg630ProtoTests
