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
11. Extra IEEE-754 vectors (division rounding, overflow, gradual underflow, `rem` with
    extreme quotients), all cross-checked against hardware `binary32` / `binary64`;
12. Applied instantiations of the sign rules, width canonicalization, exact rational
    specifications, correct-rounding theorems (`add`/`sub`/`mul`/`div`), exactness &
    magnitude bound of `rem`, and gradual underflow (`x - y == 0 ↔ x == y`);
13. Rust NaN rules: relational semantics (`EvalFloatBinOpRel`) positive / negative tests,
    exact candidate characterization, candidate counts, and cross-format widening/narrowing;
14. Dispatcher comparisons, unsupported float ops, float constants, the untyped-place
    residual gap, and general fail-closed / well-formedness theorems (functional & relational);
15. `.stripProvenance` composite erasure (arrays, tuples, wide-slice metadata), extra flip /
    preservation witnesses, full cast-level policy independence, no-forgery theorems, and
    the prototyped Finding #3 policy-aware multi-variant enum fix;
16. Applied non-`True`-typed instantiations reaching 100% of public theorems in
    `Anneal.FloatArithAndUcg630Prototype` (zero bare `True`-typed catch-all list);
17. Automated `run_cmd` constructive axiom (`[propext, Quot.sound]`),
    projection-discipline (zero `Prod.casesOn`/`Prod.rec`/`Prod.recOn`, closed over
    matchers for definitions *and* theorem statements), zero-host-`Float`,
    zero-`True`-typed-test, and 100% applied theorem reachability audit.
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

/-! ## §9. Extra IEEE-754 Vectors: Division Rounding, Overflow, Gradual Underflow & `rem` Extremes -/

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 65536 in
theorem test_div_mul_rounding_and_underflow_f32 :
    -- inexact quotients 1/3, 2/3, 1/10 round to nearest
    evalFloatArithBaseProto .div .binary32 0x3F800000 0x40400000 = 0x3EAAAAAB ∧
    evalFloatArithBaseProto .div .binary32 0x40000000 0x40400000 = 0x3F2AAAAB ∧
    evalFloatArithBaseProto .div .binary32 0x3F800000 0x41200000 = 0x3DCCCCCD ∧
    -- ±MAX * 2.0 overflows to ±Inf
    evalFloatArithBaseProto .mul .binary32 0x7F7FFFFF 0x40000000 = 0x7F800000 ∧
    evalFloatArithBaseProto .mul .binary32 0xFF7FFFFF 0x40000000 = 0xFF800000 ∧
    -- min_normal * 0.5 is an exact subnormal; min_subnormal * 0.5 ties to +0.0;
    -- (3 * min_subnormal) * 0.5 ties to 2 * min_subnormal
    evalFloatArithBaseProto .mul .binary32 0x00800000 0x3F000000 = 0x00400000 ∧
    evalFloatArithBaseProto .mul .binary32 0x00000001 0x3F000000 = 0x00000000 ∧
    evalFloatArithBaseProto .mul .binary32 0x00000003 0x3F000000 = 0x00000002 ∧
    -- odd 24-bit significand halved: the subnormal tie rounds to even, carrying into min_normal
    evalFloatArithBaseProto .mul .binary32 0x00FFFFFF 0x3F000000 = 0x00800000 ∧
    evalFloatArithBaseProto .div .binary32 0x00FFFFFF 0x40000000 = 0x00800000 ∧
    evalFloatArithBaseProto .div .binary32 0x00FFFFFD 0x40000000 = 0x007FFFFE ∧
    -- (1 + ulp)^2 = 1 + 2 ulp + ulp^2 rounds down to 1 + 2 ulp
    evalFloatArithBaseProto .mul .binary32 0x3F800001 0x3F800001 = 0x3F800002 ∧
    -- extreme quotients: min_subnormal / MAX underflows to +0.0; MAX / min_subnormal overflows
    evalFloatArithBaseProto .div .binary32 0x00000001 0x7F7FFFFF = 0x00000000 ∧
    evalFloatArithBaseProto .div .binary32 0x7F7FFFFF 0x00000001 = 0x7F800000 ∧
    -- significand carry, Sterbenz-exact subtraction, overflow by addition, exact cancellation
    evalFloatArithBaseProto .add .binary32 0x00FFFFFF 0x00000001 = 0x01000000 ∧
    evalFloatArithBaseProto .sub .binary32 0x3F800000 0x3F7FFFFF = 0x33800000 ∧
    evalFloatArithBaseProto .add .binary32 0x7F7FFFFF 0x7F7FFFFF = 0x7F800000 ∧
    evalFloatArithBaseProto .sub .binary32 0x00000001 0x00000001 = 0x00000000 ∧
    evalFloatArithBaseProto .sub .binary32 0x80000001 0x80000001 = 0x00000000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 65536 in
theorem test_div_mul_rounding_and_underflow_f64 :
    evalFloatArithBaseProto .div .binary64 0x3FF0000000000000 0x4008000000000000 =
      0x3FD5555555555555 ∧
    evalFloatArithBaseProto .div .binary64 0x3FF0000000000000 0x4024000000000000 =
      0x3FB999999999999A ∧
    evalFloatArithBaseProto .mul .binary64 0x7FEFFFFFFFFFFFFF 0x4000000000000000 =
      0x7FF0000000000000 ∧
    evalFloatArithBaseProto .mul .binary64 0x0010000000000000 0x3FE0000000000000 =
      0x0008000000000000 ∧
    evalFloatArithBaseProto .mul .binary64 0x0000000000000001 0x3FE0000000000000 =
      0x0000000000000000 ∧
    evalFloatArithBaseProto .mul .binary64 0x3FF0000000000001 0x3FF0000000000001 =
      0x3FF0000000000002 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 65536 in
theorem test_rem_extreme_quotients :
    -- min_normal % (3 * min_subnormal) = 2 * min_subnormal (2^23 mod 3 = 2)
    evalFloatArithBaseProto .rem .binary32 0x00800000 0x00000003 = 0x00000002 ∧
    -- MAX % min_subnormal = +0.0 (exact quotient of magnitude ~2^277)
    evalFloatArithBaseProto .rem .binary32 0x7F7FFFFF 0x00000001 = 0x00000000 ∧
    -- MAX % 3.0 = +0.0 and (-MAX) % 7.0 = -0.0 (dividend sign on exact zero remainder)
    evalFloatArithBaseProto .rem .binary32 0x7F7FFFFF 0x40400000 = 0x00000000 ∧
    evalFloatArithBaseProto .rem .binary32 0xFF7FFFFF 0x40E00000 = 0x80000000 ∧
    -- |a| < |b| returns a unchanged; x % x = +0.0; (-x) % (-x) = -0.0
    evalFloatArithBaseProto .rem .binary32 0x3F800000 0x7F7FFFFF = 0x3F800000 ∧
    evalFloatArithBaseProto .rem .binary32 0x40A00000 0x40A00000 = 0x00000000 ∧
    evalFloatArithBaseProto .rem .binary32 0xC0A00000 0xC0A00000 = 0x80000000 ∧
    -- f64: MAX % 3.0 = 2.0, (-MAX) % 7.0 = -5.0, MAX % min_subnormal = +0.0 (quotient ~2^2098),
    -- min_normal % (3 * min_subnormal) = min_subnormal (2^52 mod 3 = 1)
    evalFloatArithBaseProto .rem .binary64 0x7FEFFFFFFFFFFFFF 0x4008000000000000 =
      0x4000000000000000 ∧
    evalFloatArithBaseProto .rem .binary64 0xFFEFFFFFFFFFFFFF 0x401C000000000000 =
      0xC014000000000000 ∧
    evalFloatArithBaseProto .rem .binary64 0x7FEFFFFFFFFFFFFF 0x0000000000000001 =
      0x0000000000000000 ∧
    evalFloatArithBaseProto .rem .binary64 0x0010000000000000 0x0000000000000003 =
      0x0000000000000001 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §10. Sign Rules, Width Canonicalization & Exact Rational Specs (Applied Instantiations) -/

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 65536 in
theorem test_sign_rules_applied :
    -- (-2.0) * 3.0 is negative; (-6.0) / (-3.0) is positive
    (unpackBits .binary32 (evalFloatArithBaseProto .mul .binary32 0xC0000000 0x40400000)).neg =
      true ∧
    (unpackBits .binary32 (evalFloatArithBaseProto .div .binary32 0xC0C00000 0xC0400000)).neg =
      false ∧
    -- (-5.5) % 2.0 is negative; 5.5 % (-2.0) is positive (dividend sign)
    (unpackBits .binary32 (evalFloatArithBaseProto .rem .binary32 0xC0B00000 0x40000000)).neg =
      true ∧
    (unpackBits .binary32 (evalFloatArithBaseProto .rem .binary32 0x40B00000 0xC0000000)).neg =
      false ∧
    -- underflow to zero and overflow to infinity keep the XOR sign (f64)
    (unpackBits .binary64
      (evalFloatArithBaseProto .mul .binary64 0x8000000000000001 0x0000000000000001)).neg =
      true ∧
    (unpackBits .binary64
      (evalFloatArithBaseProto .div .binary64 0xFFEFFFFFFFFFFFFF 0x0000000000000001)).neg =
      true :=
  ⟨(evalFloatArithBaseProto_mul_sign .binary32 0xC0000000 0x40400000 rfl).trans rfl,
   (evalFloatArithBaseProto_div_sign .binary32 0xC0C00000 0xC0400000 rfl).trans rfl,
   (evalFloatArithBaseProto_rem_sign .binary32 0xC0B00000 0x40000000 rfl).trans rfl,
   (evalFloatArithBaseProto_rem_sign .binary32 0x40B00000 0xC0000000 rfl).trans rfl,
   (evalFloatArithBaseProto_mul_sign .binary64 0x8000000000000001 0x0000000000000001 rfl).trans
     rfl,
   (evalFloatArithBaseProto_div_sign .binary64 0xFFEFFFFFFFFFFFFF 0x0000000000000001 rfl).trans
     rfl⟩

theorem test_width_canonicalization :
    -- direct kernel evaluation on out-of-width scalar payloads
    evalFloatArithBaseProto .add .binary32 0x13F800000 0xFF3F800000 = 0x40000000 ∧
    evalFloatNegProto .binary32 0x13F800000 = 0xBF800000 ∧
    evalFloatCmpProto .eq .binary32 0x17FC00000 0x7FC00000 = false ∧
    evalFloatCmpProto .lt .binary32 0x1BF800000 0x3F800000 = true ∧
    evalFloatArithBaseProto .rem .binary32 0x1C0500000 0x7F800000 = 0xC0500000 ∧
    nanChoicesProto .binary32 [(.binary32, 0x17F800001), (.binary32, 0x3F800000)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FC00001, 0xFFC00001, 0x7F800001, 0xFF800001] ∧
    -- the general canonicalization theorems instantiated on the same payloads
    evalFloatArithBaseProto .add .binary32 (0x13F800000 % 2 ^ IeeeFormat.binary32.width)
        (0xFF3F800000 % 2 ^ IeeeFormat.binary32.width) =
      evalFloatArithBaseProto .add .binary32 0x13F800000 0xFF3F800000 ∧
    evalFloatCmpProto .lt .binary32 (0x1BF800000 % 2 ^ IeeeFormat.binary32.width)
        (0x3F800000 % 2 ^ IeeeFormat.binary32.width) =
      evalFloatCmpProto .lt .binary32 0x1BF800000 0x3F800000 ∧
    nanChoicesProto .binary32
        (canonFloatInputs [(.binary32, 0x17F800001), (.binary32, 0x3F800000)])
        .nondeterministic =
      nanChoicesProto .binary32 [(.binary32, 0x17F800001), (.binary32, 0x3F800000)]
        .nondeterministic ∧
    (EvalFloatBinOpRel .nondeterministic .add .binary32
        (0x17F800001 % 2 ^ IeeeFormat.binary32.width)
        (0x3F800000 % 2 ^ IeeeFormat.binary32.width) 0xFF800001 ↔
      EvalFloatBinOpRel .nondeterministic .add .binary32 0x17F800001 0x3F800000 0xFF800001) :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide,
   evalFloatArithBaseProto_mod_width .add .binary32 0x13F800000 0xFF3F800000,
   evalFloatCmpProto_mod_width .lt .binary32 0x1BF800000 0x3F800000,
   nanChoicesProto_canon .binary32 [(.binary32, 0x17F800001), (.binary32, 0x3F800000)]
     .nondeterministic,
   EvalFloatBinOpRel.mod_width .nondeterministic .add .binary32 0x17F800001 0x3F800000
     0xFF800001⟩

/-- Exact rational specifications instantiated on `2.0 = 8388608 / 4194304`,
`3.0 = 12582912 / 4194304`, `5.5 = 11534336 / 2097152`, and
`1.0 = 8388608 / 8388608` (`binary32`). -/
theorem test_exact_rational_specs_applied :
    evalFloatArithBaseProto .mul .binary32 0x40000000 0x40400000 =
      roundRatioTiesToEven .binary32 false (8388608 * 12582912) (4194304 * 4194304) ∧
    evalFloatArithBaseProto .div .binary32 0x40000000 0x40400000 =
      roundRatioTiesToEven .binary32 false (8388608 * 4194304) (4194304 * 12582912) ∧
    evalFloatArithBaseProto .rem .binary32 0x40B00000 0x40000000 =
      roundRatioTiesToEven .binary32 false ((11534336 * 4194304) % (2097152 * 8388608))
        (2097152 * 4194304) ∧
    (11534336 * 4194304) % (2097152 * 8388608) < 2097152 * 8388608 ∧
    evalFloatArithBaseProto .add .binary32 0x40000000 0x40400000 = 0x40A00000 ∧
    evalFloatArithBaseProto .sub .binary32 0x40000000 0x40400000 = 0xBF800000 :=
  ⟨evalFloatArithBaseProto_mul_finite .binary32 0x40000000 0x40400000 false false
      8388608 4194304 12582912 4194304 rfl rfl,
   evalFloatArithBaseProto_div_finite .binary32 0x40000000 0x40400000 false false
      8388608 4194304 12582912 4194304 rfl rfl,
   (evalFloatArithBaseProto_rem_finite .binary32 0x40B00000 0x40000000 false false
      11534336 2097152 8388608 4194304 rfl rfl).1,
   (evalFloatArithBaseProto_rem_finite .binary32 0x40B00000 0x40000000 false false
      11534336 2097152 8388608 4194304 rfl rfl).2.1,
   (evalFloatArithBaseProto_add_finite .binary32 0x40000000 0x40400000 false false
      8388608 4194304 12582912 4194304 rfl rfl).trans rfl,
   (evalFloatArithBaseProto_sub_finite .binary32 0x40000000 0x40400000 false false
      8388608 4194304 12582912 4194304 rfl rfl).trans rfl⟩

/-- Correct-rounding (`add`, `sub`, `mul`, `div`), exact IEEE-754 `rem`
(`|a % b| < |b|`, zero rounding error), gradual underflow (`x - y == 0 ↔ x == y`),
and dyadic/abs theorems instantiated with concrete non-trivial conclusions. -/
theorem test_correct_rounding_rem_exact_and_underflow_applied :
    -- `add`, `sub`, `mul`, `div` correct rounding (half-ulp error bound on finite binary32 inputs)
    (let sumInt := signedNum false 8388608 * Int.ofNat 4194304 +
        signedNum false 12582912 * Int.ofNat 4194304
     let exponent := max (ratioExponent sumInt.natAbs (4194304 * 4194304))
       IeeeFormat.binary32.minExponent
     let scaled := powScale sumInt.natAbs (4194304 * 4194304)
       ((IeeeFormat.binary32.fractionBits : Int) - exponent)
     let sig := roundQuotientTiesToEven scaled.1 scaled.2
     2 * ((sig * scaled.2 : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2) ∧
    (let diffInt := signedNum false 8388608 * Int.ofNat 4194304 -
        signedNum false 12582912 * Int.ofNat 4194304
     let exponent := max (ratioExponent diffInt.natAbs (4194304 * 4194304))
       IeeeFormat.binary32.minExponent
     let scaled := powScale diffInt.natAbs (4194304 * 4194304)
       ((IeeeFormat.binary32.fractionBits : Int) - exponent)
     let sig := roundQuotientTiesToEven scaled.1 scaled.2
     2 * ((sig * scaled.2 : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2) ∧
    (let exponent := max (ratioExponent (8388609 * 8388609) (8388608 * 8388608))
       IeeeFormat.binary32.minExponent
     let scaled := powScale (8388609 * 8388609) (8388608 * 8388608)
       ((IeeeFormat.binary32.fractionBits : Int) - exponent)
     let sig := roundQuotientTiesToEven scaled.1 scaled.2
     2 * ((sig * scaled.2 : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2) ∧
    (let exponent := max (ratioExponent (8388608 * 4194304) (8388608 * 12582912))
       IeeeFormat.binary32.minExponent
     let scaled := powScale (8388608 * 4194304) (8388608 * 12582912)
       ((IeeeFormat.binary32.fractionBits : Int) - exponent)
     let sig := roundQuotientTiesToEven scaled.1 scaled.2
     2 * ((sig * scaled.2 : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2) ∧
    -- exactness & magnitude bound of IEEE-754 `rem`: `|(-5.5) % 2.0| < |2.0|` and exact rational
    (∃ remN remD,
      decodeBits .binary32 (evalFloatArithBaseProto .rem .binary32 0xC0B00000 0x40000000) =
        .finite true remN remD ∧
      remN * (2097152 * 4194304) =
        ((11534336 * 4194304) % (2097152 * 8388608)) * remD ∧
      0 < remD) ∧
    evalFloatCmpProto .lt .binary32
      (evalFloatAbsProto .binary32 (evalFloatArithBaseProto .rem .binary32 0xC0B00000 0x40000000))
      (evalFloatAbsProto .binary32 0x40000000) = true ∧
    -- gradual underflow: `min_subnormal - (2 * min_subnormal)` cannot underflow to ±0
    ((∃ zneg, decodeBits .binary32
        (evalFloatArithBaseProto .sub .binary32 0x00000001 0x00000002) = .zero zneg) ↔
      evalFloatCmpProto .eq .binary32 0x00000001 0x00000002 = true) ∧
    -- dyadic representation, exact dyadic rounding, non-zero above min_subnormal, finite roundtrip
    (∃ m t, 0 < m ∧ m < 2 ^ (IeeeFormat.binary32.fractionBits + 1) ∧
      IeeeFormat.binary32.minExponent - (IeeeFormat.binary32.fractionBits : Int) ≤ t ∧
      t ≤ IeeeFormat.binary32.maxExponent - (IeeeFormat.binary32.fractionBits : Int) ∧
      (t = IeeeFormat.binary32.minExponent - (IeeeFormat.binary32.fractionBits : Int) ∨
        2 ^ IeeeFormat.binary32.fractionBits ≤ m) ∧
      8388608 = (powScale m 1 t).1 ∧ 8388608 = (powScale m 1 t).2) ∧
    (∃ rN rD,
      decodeBits .binary32
          (roundRatioTiesToEven .binary32 false (powScale 3 1 (-149)).1 (powScale 3 1 (-149)).2) =
        .finite false rN rD ∧
      rN * (powScale 3 1 (-149)).2 = (powScale 3 1 (-149)).1 * rD ∧ 0 < rD) ∧
    decodeBits .binary32 (roundRatioTiesToEven .binary32 false 1 (2 ^ 149)) ≠ .zero false ∧
    roundRatioTiesToEven .binary32 false 8388608 8388608 = 0x3F800000 ∧
    evalFloatAbsProto .binary32 0xBF800000 < 2 ^ IeeeFormat.binary32.width ∧
    decodeBits .binary32 (evalFloatAbsProto .binary32 0xBF800000) = .finite false 8388608 8388608 :=
  ⟨(evalFloatArithBaseProto_add_finite_correctly_rounded .binary32 0x40000000 0x40400000
      false false 8388608 4194304 12582912 4194304 rfl rfl (by decide)).1,
   (evalFloatArithBaseProto_sub_finite_correctly_rounded .binary32 0x40000000 0x40400000
      false false 8388608 4194304 12582912 4194304 rfl rfl (by decide)).1,
   (evalFloatArithBaseProto_mul_finite_correctly_rounded .binary32 0x3F800001 0x3F800001
      false false 8388609 8388608 8388609 8388608 rfl rfl).1,
   (evalFloatArithBaseProto_div_finite_correctly_rounded .binary32 0x3F800000 0x40400000
      false false 8388608 8388608 12582912 4194304 rfl rfl).1,
   (evalFloatArithBaseProto_rem_finite_exact .binary32 0xC0B00000 0x40000000 true false
      11534336 2097152 8388608 4194304 rfl rfl).2 (by decide),
   evalFloatArithBaseProto_rem_finite_lt_abs_rhs .binary32 0xC0B00000 0x40000000 true false
      11534336 2097152 8388608 4194304 rfl rfl,
   evalFloatArithBaseProto_sub_finite_eq_zero_iff .binary32 0x00000001 0x00000002
      (Or.inr ⟨false, 1, 2 ^ 149, rfl⟩) (Or.inr ⟨false, 2, 2 ^ 149, rfl⟩),
   decodeBits_finite_dyadic .binary32 0x3F800000 false 8388608 8388608 rfl,
   roundRatioTiesToEven_exact_dyadic .binary32 false 3 (-149) (by decide) (by decide)
      (by decide) (by decide),
   roundRatioTiesToEven_ne_zero_of_ge_minSubnormal .binary32 false 1 (2 ^ 149)
      (by decide) (by decide) (by decide) false,
   roundRatioTiesToEven_eq_bits_of_decodeBits_finite .binary32 0x3F800000 false 8388608 8388608
      (by decide) rfl,
   evalFloatAbsProto_lt .binary32 0xBF800000,
   (decodeBits_evalFloatAbsProto .binary32 0xBF800000).trans rfl⟩

/-! ## §11. Rust NaN Rules: Relational Semantics & Exact Candidate Characterization -/

theorem test_nan_choices_cross_format :
    -- widening f32 sNaN -> f64: the payload is left-aligned, so the signaling candidate survives
    nanChoicesProto .binary64 [(.binary32, 0x7F800001)] .nondeterministic =
      [0x7FF8000000000000, 0xFFF8000000000000,
       0x7FF8000020000000, 0xFFF8000020000000,
       0x7FF0000020000000, 0xFFF0000020000000] ∧
    -- narrowing f64 sNaN -> f32 whose surviving high payload bits are nonzero keeps the candidate
    nanChoicesProto .binary32 [(.binary64, 0x7FF4000000000001)] .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0x7FE00000, 0xFFE00000, 0x7FA00000, 0xFFA00000] ∧
    -- two identical qNaN operands: duplicates are kept (index choice), 6 entries
    nanChoicesProto .binary32 [(.binary32, 0xFFC00001), (.binary32, 0xFFC00001)]
        .nondeterministic =
      [0x7FC00000, 0xFFC00000, 0xFFC00001, 0x7FC00001, 0xFFC00001, 0x7FC00001] := by
  decide

theorem test_relational_nan_rules :
    -- 0.0 / 0.0: both signs of the preferred NaN are admissible nondeterministically...
    EvalFloatBinOpRel .nondeterministic .div .binary32 0 0 0x7FC00000 ∧
    EvalFloatBinOpRel .nondeterministic .div .binary32 0 0 0xFFC00000 ∧
    -- ...but no other payload is (there is no NaN input to propagate)
    ¬ EvalFloatBinOpRel .nondeterministic .div .binary32 0 0 0x7FC00001 ∧
    -- sNaN + 1.0: unchanged propagation of the signaling NaN is admissible with either sign
    EvalFloatBinOpRel .nondeterministic .add .binary32 0x7F800001 0x3F800000 0x7F800001 ∧
    EvalFloatBinOpRel .nondeterministic .add .binary32 0x7F800001 0x3F800000 0xFF800001 ∧
    -- 1.0 - sNaN: unchanged propagation of the right operand
    EvalFloatBinOpRel .nondeterministic .sub .binary32 0x3F800000 0xFF800002 0xFF800002 ∧
    -- quieting propagation of the right operand of a product
    EvalFloatBinOpRel .nondeterministic .mul .binary32 0x3F800000 0xFF800002 0xFFC00002 ∧
    -- deterministic mode admits only the preferred NaN
    EvalFloatBinOpRel .deterministic .add .binary32 0x7F800001 0x3F800000 0x7FC00000 ∧
    ¬ EvalFloatBinOpRel .deterministic .add .binary32 0x7F800001 0x3F800000 0x7F800001 ∧
    -- non-NaN results are deterministic under both modes
    EvalFloatBinOpRel .nondeterministic .add .binary32 0x3F800000 0x3F800000 0x40000000 ∧
    ¬ EvalFloatBinOpRel .nondeterministic .add .binary32 0x3F800000 0x3F800000 0x40000001 ∧
    -- comparisons are not arithmetic ops: the arithmetic relation is empty on them
    ¬ EvalFloatBinOpRel .nondeterministic .eq .binary32 0 0 1 := by
  have hpref : EvalFloatBinOpRel .nondeterministic .div .binary32 0 0 0x7FC00000 :=
    EvalFloatBinOpRel.det_imp_nondet .div .binary32 0 0 _
      ((EvalFloatBinOpRel.det_iff .div .binary32 0 0 _).mpr ⟨rfl, rfl⟩)
  have hsnan : EvalFloatBinOpRel .nondeterministic .add .binary32 0x7F800001 0x3F800000
      0x7F800001 :=
    EvalFloatBinOpRel.signaling_lhs_mem .add .binary32 0x7F800001 0x3F800000 rfl rfl
  refine ⟨hpref, ?_, ?_, hsnan, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EvalFloatBinOpRel.nondet_neg_closed .div .binary32 0 0 0x7FC00000 rfl hpref
  · intro h
    have hmem : 0x7FC00001 ∈
        nanChoicesProto .binary32 [(.binary32, 0), (.binary32, 0)] .nondeterministic := h.2
    exact absurd hmem (by decide)
  · exact EvalFloatBinOpRel.nondet_neg_closed .add .binary32 0x7F800001 0x3F800000 0x7F800001
      rfl hsnan
  · exact EvalFloatBinOpRel.signaling_rhs_mem .sub .binary32 0x3F800000 0xFF800002 rfl rfl
  · exact EvalFloatBinOpRel.quieted_rhs_mem .mul .binary32 0x3F800000 0xFF800002 rfl rfl
  · exact (EvalFloatBinOpRel.det_iff .add .binary32 0x7F800001 0x3F800000 _).mpr ⟨rfl, rfl⟩
  · intro h
    exact absurd ((EvalFloatBinOpRel.det_iff .add .binary32 0x7F800001 0x3F800000 _).mp h).2
      (by decide)
  · exact EvalFloatBinOpRel.det_imp_nondet .add .binary32 0x3F800000 0x3F800000 _
      ((EvalFloatBinOpRel.det_iff .add .binary32 0x3F800000 0x3F800000 _).mpr ⟨rfl, rfl⟩)
  · intro h
    exact absurd
      (EvalFloatBinOpRel.eq_base_of_not_nan .nondeterministic .add .binary32 0x3F800000
        0x3F800000 0x40000001 h rfl)
      (by decide)
  · intro h
    exact absurd h.1 (by decide)

/-- Exact candidate characterization instantiated: the flipped-sign unchanged
propagation of the right signaling operand is a member, the candidate set is
closed under negation, and the complete relational characterization yields the
admissible disjunction for `1.0 - sNaN`. -/
theorem test_nan_choice_characterization_applied :
    0x7F800002 ∈ nanChoicesProto .binary32 [(.binary32, 0x3F800000), (.binary32, 0xFF800002)]
      .nondeterministic ∧
    evalFloatNegProto .binary32 0x7FC0ABCD ∈
      nanChoicesProto .binary32 [(.binary32, 0x7FC0ABCD), (.binary32, 0x3F800000)]
        .nondeterministic ∧
    0x7FE00000 ∈ nanChoicesProto .binary32 [(.binary64, 0x7FF4000000000001)]
      .nondeterministic :=
  ⟨(nanChoicesProto_binary_nondet_mem_iff .binary32 0x3F800000 0xFF800002 0x7F800002).mpr
      ⟨0xFF800002, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), Or.inr rfl⟩,
   nanChoicesProto_nondet_neg_closed .binary32 _ 0x7FC0ABCD (by decide),
   (nanChoicesProto_nondet_mem_iff .binary32 [(.binary64, 0x7FF4000000000001)] 0x7FE00000).mpr
      ⟨0x7FE00000, Or.inr (Or.inl ⟨(.binary64, 0x7FF4000000000001), List.Mem.head _, rfl, rfl⟩),
        Or.inl rfl⟩⟩

theorem test_relational_nondet_iff_applied :
    EvalFloatBinOpRel .nondeterministic .sub .binary32 0x3F800000 0xFF800002 0x7F800002 :=
  (EvalFloatBinOpRel.nondet_iff .sub .binary32 0x3F800000 0xFF800002 0x7F800002).mpr
    ⟨rfl, Or.inr ⟨rfl, 0xFF800002, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), Or.inr rfl⟩⟩

/-! ## §12. Dispatcher: Comparisons, Unsupported Ops & General Fail-Closed / Well-Formedness -/

theorem test_dispatch_comparisons_and_unsupported_ops :
    -- f64 comparisons through the dispatcher on `1.0, 1.0`
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .lt (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0, 1⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .le (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨1, 1⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .ge (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨1, 1⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .gt (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0, 1⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .ne (.copy ⟨2, []⟩) (.copy ⟨2, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0, 1⟩) mixedTypeLocals emptyMemory ∧
    -- f32 `rem`, `div`, `sub`, `mul` through the dispatcher on `1.0, 1.0`
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .rem (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0x00000000, 4⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .div (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0x3F800000, 4⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .sub (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0x00000000, 4⟩) mixedTypeLocals emptyMemory ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .mul (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable =
      .ok (.scalar ⟨0x3F800000, 4⟩) mixedTypeLocals emptyMemory ∧
    -- `UnOp.not`, three-way `Cmp`, shifts, unchecked / overflowing ops, bit ops and `Offset`
    -- on floats fail closed
    evalRvalueFloatProto mixedTypeLocals (.unaryOp .not (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .cmp (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .shl (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .addUnchecked (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals
        (.binaryOp .addWithOverflow (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .bitAnd (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .offset (.copy ⟨0, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    -- float-typed operand on the right of an integer also fails closed
    evalRvalueFloatProto mixedTypeLocals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .unsupported ∧
    -- reading an out-of-bounds float local is `.ub`, not `.unsupported`
    evalRvalueFloatProto [] (.unaryOp .neg (.copy ⟨0, []⟩))
        emptyMemory mixedTypeDecls emptyLayoutTable = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- General dispatcher theorems instantiated on the `f16` / `f128` / mixed
fixtures (for arbitrary `locals` and `mem`, not only the concrete witnesses). -/
theorem test_dispatch_general_theorems_applied (locals : List LocalSlot) (mem : Memory)
    (op : BinOp) :
    -- f16 negation and f128 binary ops never return `.ok`, for every state
    (evalRvalueFloatProto locals (.unaryOp .neg (.copy ⟨5, []⟩)) mem floatMisdispatchDecls
        emptyLayoutTable = .ub ∨
      evalRvalueFloatProto locals (.unaryOp .neg (.copy ⟨5, []⟩)) mem floatMisdispatchDecls
        emptyLayoutTable = .unsupported) ∧
    (evalRvalueFloatProto locals (.binaryOp op (.copy ⟨6, []⟩) (.copy ⟨6, []⟩)) mem
        floatMisdispatchDecls emptyLayoutTable = .ub ∨
      evalRvalueFloatProto locals (.binaryOp op (.copy ⟨6, []⟩) (.copy ⟨6, []⟩)) mem
        floatMisdispatchDecls emptyLayoutTable = .unsupported) ∧
    -- f32 (op) f64 never returns `.ok`; f32 (op) u32 is exactly `.unsupported`
    (evalRvalueFloatProto locals (.binaryOp op (.copy ⟨0, []⟩) (.copy ⟨2, []⟩)) mem
        mixedTypeDecls emptyLayoutTable = .ub ∨
      evalRvalueFloatProto locals (.binaryOp op (.copy ⟨0, []⟩) (.copy ⟨2, []⟩)) mem
        mixedTypeDecls emptyLayoutTable = .unsupported) ∧
    evalRvalueFloatProto locals (.binaryOp op (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)) mem
        mixedTypeDecls emptyLayoutTable = .unsupported ∧
    -- `!x` on an f32 never returns `.ok`
    (evalRvalueFloatProto locals (.unaryOp .not (.copy ⟨0, []⟩)) mem mixedTypeDecls
        emptyLayoutTable = .ub ∨
      evalRvalueFloatProto locals (.unaryOp .not (.copy ⟨0, []⟩)) mem mixedTypeDecls
        emptyLayoutTable = .unsupported) ∧
    -- the relational semantics is total for every state and mode
    (∃ res, EvalRvalueFloatRelProto .nondeterministic locals
      (.binaryOp op (.copy ⟨0, []⟩) (.copy ⟨0, []⟩)) mem mixedTypeDecls emptyLayoutTable res) :=
  ⟨evalRvalueFloatProto_neg_fail_closed_of_unmodeled locals (.copy ⟨5, []⟩) mem
      floatMisdispatchDecls emptyLayoutTable .f16 rfl rfl,
   evalRvalueFloatProto_binaryOp_fail_closed_of_unmodeled_or_mismatch locals op
      (.copy ⟨6, []⟩) (.copy ⟨6, []⟩) mem floatMisdispatchDecls emptyLayoutTable .f128 .f128
      rfl rfl (fun _ h => by cases h.1),
   evalRvalueFloatProto_binaryOp_fail_closed_of_unmodeled_or_mismatch locals op
      (.copy ⟨0, []⟩) (.copy ⟨2, []⟩) mem mixedTypeDecls emptyLayoutTable .f32 .f64
      rfl rfl (fun fmt h => by
        cases fmt
        · cases h.2
        · cases h.1),
   evalRvalueFloatProto_binaryOp_float_nonFloat_unsupported locals op
      (.copy ⟨0, []⟩) (.copy ⟨1, []⟩) mem mixedTypeDecls emptyLayoutTable .f32
      (Or.inl ⟨rfl, rfl⟩),
   evalRvalueFloatProto_not_float_fail_closed locals (.copy ⟨0, []⟩) mem mixedTypeDecls
      emptyLayoutTable .f32 rfl,
   EvalRvalueFloatRelProto.total .nondeterministic locals _ mem mixedTypeDecls emptyLayoutTable⟩

/-- Well-formedness (functional & relational), conservative non-float extension,
constant interception, untyped-place residual gap, and the TCB float misdispatch
witness instantiated with concrete non-trivial conclusions. -/
theorem test_dispatch_wf_and_misdispatch_applied (locals : List LocalSlot) (mem : Memory) :
    -- functional well-formedness on `1.0_f32 + 1.0_f32` and `-1.0_f32`
    (emptyMemory = emptyMemory ∧
      ∃ fmt, ieeeFormatOfFloatTy? .f32 = some fmt ∧ ieeeFormatOfFloatTy? .f32 = some fmt ∧
        ((isFloatArithBinOp .add = true ∧
            ∃ bits, Value.scalar ⟨0x40000000, 4⟩ = .scalar ⟨bits, fmt.byteWidth⟩ ∧
              bits < 2 ^ fmt.width) ∨
          (isFloatArithBinOp .add = false ∧ isFloatCmpBinOp .add = true ∧
            ∃ b, Value.scalar ⟨0x40000000, 4⟩ = .scalar (boolToScalar b)))) ∧
    (emptyMemory = emptyMemory ∧
      ∃ fmt bits, ieeeFormatOfFloatTy? .f32 = some fmt ∧
        Value.scalar ⟨0xBF800000, 4⟩ = .scalar ⟨bits, fmt.byteWidth⟩ ∧
          bits < 2 ^ fmt.width) ∧
    -- relational well-formedness under `.nondeterministic` on `1.0_f32 + 1.0_f32`
    (∀ v locals' mem',
      EvalRvalueFloatRelProto .nondeterministic floatMisdispatchLocals
          (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)) emptyMemory floatMisdispatchDecls
          emptyLayoutTable (.ok v locals' mem') →
        mem' = emptyMemory ∧
          ∃ fmt, ieeeFormatOfFloatTy? .f32 = some fmt ∧ ieeeFormatOfFloatTy? .f32 = some fmt ∧
            ((isFloatArithBinOp .add = true ∧
                ∃ bits, v = .scalar ⟨bits, fmt.byteWidth⟩ ∧ bits < 2 ^ fmt.width) ∨
              (isFloatArithBinOp .add = false ∧ isFloatCmpBinOp .add = true ∧
                ∃ b, v = .scalar (boolToScalar b)))) ∧
    -- general conservative extension on non-float integer `add` (both functional & relational)
    evalRvalueFloatProto locals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem
        mixedTypeDecls emptyLayoutTable =
      evalRvalue locals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem
        mixedTypeDecls emptyLayoutTable ∧
    (∀ res, EvalRvalueFloatRelProto .nondeterministic locals
        (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem mixedTypeDecls emptyLayoutTable res ↔
      res = evalRvalue locals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem
        mixedTypeDecls emptyLayoutTable) ∧
    -- constant interception & untyped-place residual gap witness
    evalRvalueFloatProto [] (.binaryOp .add (f32ConstOperandProto 0x3FC00000)
        (f32ConstOperandProto 0x40100000)) emptyMemory [] emptyLayoutTable =
      .ok (.scalar ⟨0x40700000, 4⟩) [] emptyMemory ∧
    -- TCB float misdispatch witness (`-1.0_f32` misdispatched to `0xC0800000`)
    evalRvalue floatMisdispatchLocals (.unaryOp .neg (.copy ⟨0, []⟩)) emptyMemory
        floatMisdispatchDecls emptyLayoutTable =
      .ok (.scalar ⟨0xC0800000, 4⟩) floatMisdispatchLocals emptyMemory :=
  ⟨evalRvalueFloatProto_binaryOp_float_ok_wf floatMisdispatchLocals .add
      (.copy ⟨0, []⟩) (.copy ⟨1, []⟩) emptyMemory floatMisdispatchDecls emptyLayoutTable
      .f32 .f32 (.scalar ⟨0x40000000, 4⟩) floatMisdispatchLocals emptyMemory rfl rfl rfl,
   evalRvalueFloatProto_neg_float_ok_wf floatMisdispatchLocals (.copy ⟨0, []⟩)
      emptyMemory floatMisdispatchDecls emptyLayoutTable .f32 (.scalar ⟨0xBF800000, 4⟩)
      floatMisdispatchLocals emptyMemory rfl rfl,
   fun v locals' mem' h =>
     EvalRvalueFloatRelProto.binaryOp_float_ok_wf .nondeterministic floatMisdispatchLocals .add
       (.copy ⟨0, []⟩) (.copy ⟨1, []⟩) emptyMemory floatMisdispatchDecls emptyLayoutTable
       .f32 .f32 v locals' mem' rfl rfl h,
   evalRvalueFloatProto_nonFloat_eq locals (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem
      mixedTypeDecls emptyLayoutTable
      ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h; exact ⟨rfl, rfl⟩)⟩,
   fun res => EvalRvalueFloatRelProto.nonFloat_iff .nondeterministic locals
      (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)) mem mixedTypeDecls emptyLayoutTable res
      ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h; exact ⟨rfl, rfl⟩)⟩,
   evalRvalueFloatProto_constant_interception_and_untyped_place_residual_witness.1,
   trusted_evalRvalue_float_misdispatch_witness.1⟩

/-! ## §13. `.stripProvenance` Characterization, Extra Flip Witnesses & General Policy Theorems -/

theorem test_ptr2int_extra_flip_and_preservation_witnesses :
    -- ptr -> i64: address under `.stripProvenance`, UB under `.strictUcg630Ub`
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .int .i64, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .int .i64, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts = .ub ∧
    -- ptr -> [u16; 4] and ptr -> (u32, u32): aggregates of integers flip as well
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .array (.uint .u16) 4, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts =
      .ok (.aggregate 0 [.scalar ⟨0, 2⟩, .scalar ⟨0, 2⟩, .scalar ⟨0, 2⟩, .scalar ⟨0x4008, 2⟩])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .array (.uint .u16) 4, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts = .ub ∧
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.scalar ⟨0, 4⟩, .scalar ⟨0x40080000, 4⟩])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    -- ptr -> [bool; 8]: stripping provenance never bypasses bit validity (0x08 / 0x40 are
    -- invalid `bool`s): UB under both policies
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .array .bool 8, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts = .ub ∧
    -- ptr -> &u8 and ptr -> fn(): provenance is preserved under both policies
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts =
      .ok (.ptr protoSamplePtr 8) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩)
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts =
      .ok (.ptr protoSamplePtr 8) protoTransmuteLocals emptyMemory ∧
    -- [ptr; 2] -> *const dyn Trait: the vtable half keeps its provenance under both policies
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.ptr protoSamplePtr 8, .ptr protoSamplePtr 8])
        protoTransmuteLocals emptyMemory ∧
    -- [ptr; 2] -> &[u8]: the slice length must be a plain integer (flip)
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts =
      .ok (.aggregate 0 [.ptr protoSamplePtr 8, .scalar ⟨protoSamplePtr.offsetBytes, 8⟩])
        protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 } emptyMemory
        protoTransmuteDecls protoTransmuteLayouts = .ub ∧
    -- [ptr; 2] -> [usize; 2] (flip)
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .array (.uint .usize) 2, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts =
      .ok (.aggregate 0 [.scalar ⟨protoSamplePtr.offsetBytes, 8⟩,
          .scalar ⟨protoSamplePtr.offsetBytes, 8⟩]) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨3, []⟩)
        { kind := .array (.uint .usize) 2, layoutIdx := 0 } emptyMemory protoTransmuteDecls
        protoTransmuteLayouts = .ub ∧
    -- usize -> *const u8: a provenance-less address under both policies (never `Value.ptr`)
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨1, []⟩)
        protoConstU8PtrTy emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory ∧
    -- usize -> f64: integer bytes carry no provenance, so both policies agree
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨1, []⟩) protoF64Ty
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `.stripProvenance` = `.strictUcg630Ub` ∘ provenance erasure, instantiated on
the concrete pointer image of `protoSamplePtr` at `usize`, `f64`, `char`, and a
niche `NonZero<u64>` scalar layout. -/
theorem test_strip_characterization_applied :
    stripAbstractBytesProv (encodeLittleEndianBytes 0x1122 2 (.some (7, 7))) =
      encodeLittleEndianBytes 0x1122 2 .none ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts protoUsizeTy
        (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7))) =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts protoUsizeTy
        (stripAbstractBytesProv
          (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7)))) ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts protoUsizeTy
        (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7))) =
      .some (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts protoF64Ty
        (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7))) =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts protoF64Ty
        (stripAbstractBytesProv
          (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7)))) ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .char, layoutIdx := 0 } (encodeLittleEndianBytes 0x1F600 4 (.some (7, 7))) =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts
        { kind := .char, layoutIdx := 0 }
        (stripAbstractBytesProv (encodeLittleEndianBytes 0x1F600 4 (.some (7, 7)))) ∧
    decodeScalarLayoutBytesWithPolicy .stripProvenance
        (.initialized (.int 64 false) ⟨1, scalarModulus 8 - 1⟩)
        (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7))) =
      decodeScalarLayoutBytesWithPolicy .strictUcg630Ub
        (.initialized (.int 64 false) ⟨1, scalarModulus 8 - 1⟩)
        (stripAbstractBytesProv
          (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7)))) :=
  ⟨rfl,
   decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased 4 protoTransmuteLayouts
      protoUsizeTy _ rfl,
   rfl,
   decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased 4 protoTransmuteLayouts
      protoF64Ty _ rfl,
   decodeTypedValueFromBytesWithPolicy_strip_scalar_eq_strict_erased 4 protoTransmuteLayouts
      { kind := .char, layoutIdx := 0 } _ rfl,
   decodeScalarLayoutBytesWithPolicy_strip_eq_strict_erased _ _ rfl⟩

/-- General policy theorems instantiated for **every** byte image, operand,
`locals`, and `mem` on the concrete transmute fixture. -/
theorem test_policy_general_theorems_applied (bytes : List AbstractByte)
    (locals : List LocalSlot) (op : Operand) (mem : Memory) :
    -- `[MaybeUninit<u8>; 8]` decodes identically under both policies for every byte image
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        protoMaybeUninitU8Arr8Ty bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts
        protoMaybeUninitU8Arr8Ty bytes ∧
    -- every transmute into `*mut u8` is policy-independent
    evalByteCastWithPolicy .stripProvenance locals op protoMutU8PtrTy mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op protoMutU8PtrTy mem protoTransmuteDecls
        protoTransmuteLayouts ∧
    -- every transmute into `usize` agrees between the policies unless the strict one is UB
    (evalByteCastWithPolicy .stripProvenance locals op protoUsizeTy mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op protoUsizeTy mem protoTransmuteDecls
        protoTransmuteLayouts ∨
      evalByteCastWithPolicy .strictUcg630Ub locals op protoUsizeTy mem protoTransmuteDecls
        protoTransmuteLayouts = .ub) ∧
    -- `&dyn Trait` decodes identically under both policies
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .ref .not (.dynamic "Trait"), layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub 4 protoTransmuteLayouts
        { kind := .ref .not (.dynamic "Trait"), layoutIdx := 0 } bytes :=
  ⟨decodeTypedValueFromBytesWithPolicy_unionArray_policy_indep 2 protoTransmuteLayouts
      "core::mem::maybe_uninit::MaybeUninit" [.uint .u8] 8 2 1 protoMaybeUninitU8Arr8Layout
      protoMaybeUninitU8Layout { bytes := 1 } 8 2 [] bytes rfl rfl rfl rfl rfl rfl,
   evalByteCastWithPolicy_thinRawPtr_policy_indep locals op protoMutU8PtrTy mem
      protoTransmuteDecls protoTransmuteLayouts .mut (.uint .u8) rfl rfl,
   evalByteCastWithPolicy_strip_eq_strict_or_strict_ub locals op protoUsizeTy mem
      protoTransmuteDecls protoTransmuteLayouts,
   decodeTypedValueFromBytesWithPolicy_wideDynRef_policy_indep 3 protoTransmuteLayouts .not
      "Trait" 0 bytes⟩

/-- No-forgery theorems instantiated: provenance-free bytes never decode to a
wide `&[u8]`, a decoded `*const u8` pointer value implies an intact pointer
image, and a policy disagreement implies the bytes carry provenance. -/
theorem test_no_forge_theorems_applied :
    decodeTypedValueFromBytesWithPolicy .stripProvenance 4 protoTransmuteLayouts
        { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
        (encodeLittleEndianBytes 5 16 .none) = .none ∧
    abstractBytesUniformProv (encodeLittleEndianBytes 0x10 8 (.some (7, 7))) = true ∧
    abstractBytesHaveProv (encodeLittleEndianBytes protoSamplePtr.offsetBytes 8 (.some (7, 7))) =
      true ∧
    stripAbstractBytesProv (stripAbstractBytesProv [.init 1 (.some (7, 7)), .uninit]) =
      stripAbstractBytesProv [.init 1 (.some (7, 7)), .uninit] ∧
    stripAbstractBytesProv [.init 1 .none, .uninit] = [.init 1 .none, .uninit] :=
  ⟨decodeTypedValueFromBytesWithPolicy_no_forge_ref .stripProvenance 3 protoTransmuteLayouts
      .not (.slice (.uint .u8)) 0 _ rfl,
   (decodeTypedValueFromBytesWithPolicy_thinRawPtr_ptr_imp_uniformProv .stripProvenance 3
      protoTransmuteLayouts .not (.uint .u8) 0 (encodeLittleEndianBytes 0x10 8 (.some (7, 7)))
      { allocId := 7, offsetBytes := 0x10 } 8 rfl rfl).1,
   decodeTypedValueFromBytesWithPolicy_policies_differ_imp_prov 4 protoTransmuteLayouts
      protoUsizeTy _ (fun h => by
        have h' : (some (Value.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) : Option Value) = none := h
        cases h'),
   stripAbstractBytesProv_idem _,
   stripAbstractBytesProv_of_no_prov _ rfl⟩

/-- The kernel-checked TCB strictness leak on multi-variant enums, projected to
its two headline facts: the pointer image carries provenance, yet the trusted
`evalByteCast` decodes it into integer enum fields without UB. -/
theorem test_trusted_multiVariant_enum_strict_leak :
    abstractBytesHaveProv
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) = true ∧
    evalByteCast protoEnumLocals (.copy ⟨0, []⟩) protoTwoVariantEnumTy emptyMemory
        protoEnumDecls protoEnumLayouts =
      .ok (.aggregate 1 [.scalar ⟨42, 4⟩]) protoEnumLocals emptyMemory :=
  ⟨trusted_evalByteCast_multiVariant_enum_strict_leak_witness.1,
   trusted_evalByteCast_multiVariant_enum_strict_leak_witness.2.2.1⟩

/-! ## §14. Complete Applied Instantiations of Remaining Part A & Part B Theorems -/

/-- Bitwise negation and canonical decoding theorems instantiated across
signed zeros, infinities, encoded bitfields, qNaNs, and sNaNs. -/
theorem test_negation_theorems_applied (f : IeeeFormat) (bits : Nat) :
    evalFloatNegProto f (bits % 2 ^ f.width) = evalFloatNegProto f bits ∧
    evalFloatNegProto f (zeroBits f false) = zeroBits f true ∧
    evalFloatNegProto f (infBits f true) = infBits f false ∧
    evalFloatNegProto .binary32 (encodeBits .binary32 false 127 0) =
      encodeBits .binary32 true 127 0 ∧
    evalFloatNegProto f bits = (bits % 2 ^ f.width).xor (2 ^ (f.width - 1)) ∧
    decodeBits .binary32 (evalFloatNegProto .binary32 0x7F800001) = .nan true false 1 ∧
    isQuietNaNBits f (evalFloatNegProto f bits) = isQuietNaNBits f bits ∧
    isSignalingNaNBits f (evalFloatNegProto f bits) = isSignalingNaNBits f bits ∧
    isAdmissibleQuietNaN .binary32 (evalFloatNegProto .binary32 0x7FC0ABCD) = true ∧
    (0x80000000 : Nat) = zeroBits .binary32 true ∧
    (0xFF800000 : Nat) = infBits .binary32 true :=
  ⟨evalFloatNegProto_mod f bits,
   evalFloatNegProto_zeroBits f false,
   evalFloatNegProto_infBits f true,
   evalFloatNegProto_encodeBits .binary32 false 127 0 (by decide) (by decide),
   evalFloatNegProto_xor f bits,
   decodeBits_evalFloatNegProto_nan .binary32 0x7F800001 false false 1 rfl,
   isQuietNaNBits_evalFloatNegProto f bits,
   isSignalingNaNBits_evalFloatNegProto f bits,
   isAdmissibleQuietNaN_evalFloatNegProto .binary32 0x7FC0ABCD rfl,
   bits_eq_zeroBits_of_decodeBits_zero .binary32 0x80000000 true (by decide) rfl,
   bits_eq_infBits_of_decodeBits_inf .binary32 0xFF800000 true (by decide) rfl⟩

/-- Partial-order and IEEE-754 comparison algebra instantiated for arbitrary
`f`, `a`, `b` and concrete ordered chains. -/
theorem test_comparison_order_theorems_applied (f : IeeeFormat) (a b : Nat) :
    evalFloatPartialCompareProto f a b =
      Option.map Ordering.swap (evalFloatPartialCompareProto f b a) ∧
    evalFloatPartialCompareProto f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatPartialCompareProto f b a ∧
    evalFloatCmpProto .ne f a b = !evalFloatCmpProto .eq f a b ∧
    evalFloatCmpProto .gt f a b = evalFloatCmpProto .lt f b a ∧
    evalFloatCmpProto .ge f a b = evalFloatCmpProto .le f b a ∧
    evalFloatCmpProto .eq f a a = !isNaNBits f a ∧
    evalFloatCmpProto .lt f a a = false ∧
    evalFloatCmpProto .eq f a b = evalFloatCmpProto .eq f b a ∧
    evalFloatCmpProto .lt .binary32 0x7FC00000 b = false ∧
    evalFloatCmpProto .ne .binary32 a 0x7F800001 = true ∧
    evalFloatCmpProto .eq f (zeroBits f true) (zeroBits f false) = true ∧
    (evalFloatCmpProto .eq .binary32 0x80000000 0x00000000 = true ↔
      isNaNBits .binary32 0x80000000 = false ∧
        (0x80000000 = 0x00000000 ∨
          0x80000000 = zeroBits .binary32 false ∧ 0x00000000 = zeroBits .binary32 true ∨
          0x80000000 = zeroBits .binary32 true ∧ 0x00000000 = zeroBits .binary32 false)) ∧
    evalFloatCmpProto .eq .binary32 0x80000000 0x00000000 = true ∧
    evalFloatCmpProto .lt .binary32 0xBF800000 0x40000000 = true ∧
    evalFloatCmpProto .le .binary32 0xBF800000 0x40000000 = true ∧
    (evalFloatCmpProto .le .binary32 0x3F800000 0x40000000 = true ∨
      evalFloatCmpProto .le .binary32 0x40000000 0x3F800000 = true) ∧
    evalFloatCmpProto .lt f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .lt f b a ∧
    evalFloatCmpProto .le f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .le f b a ∧
    evalFloatCmpProto .eq f (evalFloatNegProto f a) (evalFloatNegProto f b) =
      evalFloatCmpProto .eq f a b :=
  ⟨evalFloatPartialCompareProto_swap f a b,
   evalFloatPartialCompareProto_neg f a b,
   evalFloatCmpProto_ne_eq_not_eq f a b,
   evalFloatCmpProto_gt_eq_lt_swap f a b,
   evalFloatCmpProto_ge_eq_le_swap f a b,
   evalFloatCmpProto_eq_refl_iff_not_nan f a,
   evalFloatCmpProto_lt_irrefl f a,
   evalFloatCmpProto_eq_symm f a b,
   evalFloatCmpProto_nan_left .lt .binary32 0x7FC00000 b rfl,
   evalFloatCmpProto_nan_right .ne .binary32 a 0x7F800001 rfl,
   (evalFloatCmpProto_negZero_eq_posZero f).1,
   evalFloatCmpProto_eq_iff_bits_or_signedZero .binary32 0x80000000 0x00000000
      (by decide) (by decide),
   (evalFloatCmpProto_le_antisym .binary32 0x80000000 0x00000000
      (by decide) (by decide) rfl rfl).1,
   evalFloatCmpProto_lt_trans .binary32 0xBF800000 0x3F800000 0x40000000 rfl rfl,
   evalFloatCmpProto_le_trans .binary32 0xBF800000 0x3F800000 0x40000000 rfl rfl,
   evalFloatCmpProto_le_total_of_not_nan .binary32 0x3F800000 0x40000000 rfl rfl,
   evalFloatCmpProto_lt_neg_reverse f a b,
   evalFloatCmpProto_le_neg_reverse f a b,
   evalFloatCmpProto_eq_neg_preserve f a b⟩

/-- Base arithmetic width-bound, commutativity, signed-zero, cancellation, and
`rem` boundary theorems instantiated universally and on concrete operands. -/
theorem test_arith_algebra_theorems_applied (op : BinOp) (f : IeeeFormat) (a b : Nat)
    (l r : FloatKind) :
    evalFloatArithBaseProto op f a b < 2 ^ f.width ∧
    exactSumProto f l r = exactSumProto f r l ∧
    evalFloatArithBaseProto .sub f a b =
      evalFloatArithBaseProto .add f a (evalFloatNegProto f b) ∧
    evalFloatArithBaseProto .add f a b = evalFloatArithBaseProto .add f b a ∧
    evalFloatArithBaseProto .mul f a b = evalFloatArithBaseProto .mul f b a ∧
    evalFloatArithBaseProto .add f (zeroBits f true) (zeroBits f true) = zeroBits f true ∧
    evalFloatArithBaseProto .add f (zeroBits f false) (zeroBits f true) = zeroBits f false ∧
    evalFloatArithBaseProto .sub f (zeroBits f true) (zeroBits f false) = zeroBits f true ∧
    evalFloatArithBaseProto .add .binary32 0x3F800000 (zeroBits .binary32 true) =
      0x3F800000 % 2 ^ IeeeFormat.binary32.width ∧
    evalFloatArithBaseProto .add .binary32 0x3F800000 (zeroBits .binary32 false) =
      0x3F800000 % 2 ^ IeeeFormat.binary32.width ∧
    evalFloatArithBaseProto .add .binary32 0x3F800000 (evalFloatNegProto .binary32 0x3F800000) =
      zeroBits .binary32 false ∧
    evalFloatArithBaseProto .mul .binary32 (zeroBits .binary32 true) 0x3F800000 =
      zeroBits .binary32 (true ^^ (unpackBits .binary32 0x3F800000).neg) ∧
    evalFloatArithBaseProto .rem .binary32 0x3F800000 (infBits .binary32 false) =
      0x3F800000 % 2 ^ IeeeFormat.binary32.width ∧
    evalFloatArithBaseProto .rem .binary32 (zeroBits .binary32 true) 0x3F800000 =
      zeroBits .binary32 true :=
  ⟨evalFloatArithBaseProto_lt op f a b,
   exactSumProto_comm f l r,
   evalFloatArithBaseProto_sub_eq_add_neg f a b,
   evalFloatArithBaseProto_add_comm f a b,
   evalFloatArithBaseProto_mul_comm f a b,
   evalFloatArithBaseProto_add_negZero_negZero f,
   evalFloatArithBaseProto_add_posZero_negZero f,
   evalFloatArithBaseProto_sub_negZero_posZero f,
   evalFloatArithBaseProto_add_negZero_right .binary32 0x3F800000 rfl,
   evalFloatArithBaseProto_add_posZero_right .binary32 0x3F800000 rfl (by decide),
   evalFloatArithBaseProto_add_neg_self_finite .binary32 0x3F800000 false 8388608 8388608 rfl,
   evalFloatArithBaseProto_mul_zero_finite .binary32 true 0x3F800000
      (Or.inr ⟨false, 8388608, 8388608, rfl⟩),
   evalFloatArithBaseProto_rem_inf_right .binary32 0x3F800000 false
      (Or.inr ⟨false, 8388608, 8388608, rfl⟩),
   evalFloatArithBaseProto_rem_zero_finite .binary32 true 0x3F800000 8388608 8388608 false rfl⟩

/-- `miri#5643` NaN candidate lengths, cross-format widening/narrowing sNaN
survival theorems, and `EvalFloatBinOpRel` algebraic properties instantiated. -/
theorem test_nan_and_rel_theorems_applied (mode : FloatArithMode) (f : IeeeFormat)
    (a b out : Nat) (e₁ e₂ : IeeeFormat × Nat) (l : List Nat) (inputs : List (IeeeFormat × Nat)) :
    isAdmissibleQuietNaN f (preferredNaNBits f) = true ∧
    isAdmissibleQuietNaN .binary32 0x7FC0ABCD = true ∧
    (out ∈ nanChoicesProto f [e₁, e₂] mode ↔ out ∈ nanChoicesProto f [e₂, e₁] mode) ∧
    (out ∈ nanChoicesProto f [(f, a), (f, evalFloatNegProto f b)] mode ↔
      out ∈ nanChoicesProto f [(f, a), (f, b)] mode) ∧
    (expandNaNSigns f l).length = 2 * l.length ∧
    (nanChoicesProto f inputs .nondeterministic).length =
      2 * (1 + (quietedNaNCandidates f inputs).length +
        (signalingNaNCandidates f inputs).length) ∧
    (signalingNaNLowerOf .binary64 .binary32 0x7F800001 ≠ 0 ∧
      signalingNaNCandidateOf .binary64 .binary32 0x7F800001 ∈
        signalingNaNCandidates .binary64 [(.binary32, 0x7F800001)]) ∧
    ((signalingNaNLowerOf .binary32 .binary64 0x7FF4000000000001 ≠ 0 ↔
        (0x0004000000000001 : Nat) / 2 ^ (IeeeFormat.binary64.fractionBits -
          IeeeFormat.binary32.fractionBits) ≠ 0) ∧
      (signalingNaNCandidateOf .binary32 .binary64 0x7FF4000000000001 ∈
          signalingNaNCandidates .binary32 [(.binary64, 0x7FF4000000000001)] ↔
        (0x0004000000000001 : Nat) / 2 ^ (IeeeFormat.binary64.fractionBits -
          IeeeFormat.binary32.fractionBits) ≠ 0)) ∧
    (∃ r, EvalFloatBinOpRel mode .add f a b r) ∧
    (EvalFloatBinOpRel mode .add f a b out → out < 2 ^ f.width) ∧
    EvalFloatBinOpRel .nondeterministic .add .binary32 0x7F800001 b
      (evalFloatToFloatRoundTiesToEven .binary32 .binary32 0x7F800001) ∧
    (EvalFloatBinOpRel mode .add f a b out ↔ EvalFloatBinOpRel mode .add f b a out) ∧
    (EvalFloatBinOpRel mode .mul f a b out ↔ EvalFloatBinOpRel mode .mul f b a out) ∧
    (EvalFloatBinOpRel mode .sub f a b out ↔
      EvalFloatBinOpRel mode .add f a (evalFloatNegProto f b) out) :=
  ⟨isAdmissibleQuietNaN_preferredNaNBits f,
   isAdmissibleQuietNaN_of_mem_quieted_expanded .binary32 [(.binary32, 0x7FC0ABCD)] 0x7FC0ABCD
      (by decide),
   nanChoicesProto_mem_swap_pair f e₁ e₂ mode out,
   nanChoicesProto_mem_neg_second f a b mode out,
   length_expandNaNSigns f l,
   length_nanChoicesProto_nondet f inputs,
   widening_signaling_candidate_survives .binary32 .binary64 0x7F800001 (by decide) rfl,
   narrowing_signaling_candidate_iff .binary64 .binary32 0x7FF4000000000001 false
      0x0004000000000001 (by decide) rfl,
   EvalFloatBinOpRel.total mode .add f a b rfl,
   EvalFloatBinOpRel.out_lt mode .add f a b out,
   EvalFloatBinOpRel.quieted_lhs_mem .add .binary32 0x7F800001 b rfl rfl,
   EvalFloatBinOpRel.add_comm mode f a b out,
   EvalFloatBinOpRel.mul_comm mode f a b out,
   EvalFloatBinOpRel.sub_eq_add_neg mode f a b out⟩

/-- Exact TCB correspondence at `.strictUcg630Ub`, cast refinement, byte-slice
commutation with provenance erasure, composite array/tuple erasure, and
hybrid wide-slice metadata erasure instantiated universally. -/
theorem test_policy_correspondence_and_composite_erasure_applied
    (isRef : Bool) (pointee : RigidTy) (ptrBytes n off len totalSize : Nat)
    (offsets : List Size) (sl : ScalarLayout) (fuel : Nat) (layouts : LayoutTable)
    (ty : Ty) (bytes : List AbstractByte) (locals : List LocalSlot) (op : Operand)
    (mem : Memory) (localDecls : List LocalDecl) :
    decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef pointee ptrBytes bytes =
      decodePtrBytesNoForge isRef pointee ptrBytes bytes ∧
    decodeScalarLayoutBytesWithPolicy .strictUcg630Ub sl bytes =
      decodeScalarLayoutBytesNoForge sl bytes ∧
    decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel layouts ty bytes =
      decodeTypedValueFromBytes fuel layouts ty bytes ∧
    evalByteCastWithPolicy .strictUcg630Ub locals op ty mem localDecls layouts =
      evalByteCast locals op ty mem localDecls layouts ∧
    (∀ v locals',
      evalByteCastWithPolicy .strictUcg630Ub locals op ty mem localDecls layouts =
          .ok v locals' mem →
        evalByteCastWithPolicy .stripProvenance locals op ty mem localDecls layouts =
          .ok v locals' mem) ∧
    takeAbstractBytes n (stripAbstractBytesProv bytes) =
      stripAbstractBytesProv (takeAbstractBytes n bytes) ∧
    dropAbstractBytes n (stripAbstractBytesProv bytes) =
      stripAbstractBytesProv (dropAbstractBytes n bytes) ∧
    sliceAbstractBytes (stripAbstractBytesProv bytes) off len =
      (match sliceAbstractBytes bytes off len with
       | some s => some (stripAbstractBytesProv s)
       | none => none) ∧
    decodeFieldsBySpan (stripAbstractBytesProv bytes) totalSize offsets =
      decodeFieldsBySpan bytes totalSize offsets ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel.succ.succ layouts
        { kind := .array (.uint .u16) 4, layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel.succ.succ layouts
        { kind := .array (.uint .u16) 4, layoutIdx := 0 } (stripAbstractBytesProv bytes) ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel.succ.succ layouts
        { kind := .tuple [.uint .u32, .float .f32], layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel.succ.succ layouts
        { kind := .tuple [.uint .u32, .float .f32], layoutIdx := 0 }
        (stripAbstractBytesProv bytes) ∧
    (Trusted.Sequence.length bytes = ptrBytes.add ptrBytes →
      decodePtrBytesNoForgeWithPolicy .stripProvenance isRef (.slice (.uint .u8)) ptrBytes bytes =
        decodePtrBytesNoForgeWithPolicy .strictUcg630Ub isRef (.slice (.uint .u8)) ptrBytes
          (appendAbstractBytes (takeAbstractBytes ptrBytes bytes)
            (stripAbstractBytesProv (dropAbstractBytes ptrBytes bytes)))) :=
  ⟨decodePtrBytesNoForgeWithPolicy_strict_eq isRef pointee ptrBytes bytes,
   decodeScalarLayoutBytesWithPolicy_strict_eq sl bytes,
   decodeTypedValueFromBytesWithPolicy_strict_eq fuel layouts ty bytes,
   evalByteCastWithPolicy_strict_eq locals op ty mem localDecls layouts,
   fun v locals' h =>
     evalByteCastWithPolicy_strict_refines_strip locals op ty mem localDecls layouts v locals' h,
   takeAbstractBytes_stripAbstractBytesProv n bytes,
   dropAbstractBytes_stripAbstractBytesProv n bytes,
   sliceAbstractBytes_stripAbstractBytesProv bytes off len,
   decodeFieldsBySpan_stripAbstractBytesProv bytes totalSize offsets,
   decodeTypedValueFromBytesWithPolicy_strip_array_scalar_eq_strict_erased
      fuel layouts (.uint .u16) 4 0 bytes rfl,
   decodeTypedValueFromBytesWithPolicy_strip_tuple_scalar_eq_strict_erased
      fuel layouts [.uint .u32, .float .f32] 0 bytes rfl,
   fun hlen =>
     decodePtrBytesNoForgeWithPolicy_strip_wideSlice_eq_strict_meta_erased
       isRef (.slice (.uint .u8)) ptrBytes bytes (Or.inl ⟨.uint .u8, rfl⟩) hlen⟩

/-- Decoder-level and cast-level policy independence (`&T`, `fn()`, `*const dyn Trait`,
`&dyn Trait`, unions, union arrays), no-forgery, separation/roundtrip witnesses, and
the prototyped Finding #3 policy-aware multi-variant enum fix instantiated. -/
theorem test_policy_indep_no_forge_and_enum_fix_applied
    (policy : Ptr2IntTransmutePolicy) (fuel : Nat) (bytes : List AbstractByte)
    (locals : List LocalSlot) (op : Operand) (mem : Memory) :
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel.succ protoTransmuteLayouts
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel.succ protoTransmuteLayouts
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } bytes ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel.succ protoTransmuteLayouts
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel.succ protoTransmuteLayouts
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } bytes ∧
    decodeTypedValueFromBytesWithPolicy .stripProvenance fuel.succ protoTransmuteLayouts
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } bytes =
      decodeTypedValueFromBytesWithPolicy .strictUcg630Ub fuel.succ protoTransmuteLayouts
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } bytes ∧
    (abstractBytesHaveProv bytes = false →
      ∀ v, decodeTypedValueFromBytesWithPolicy policy fuel.succ protoTransmuteLayouts
          protoConstU8PtrTy bytes = some v → ∃ sv, v = .scalar sv) ∧
    (abstractBytesHaveProv bytes = false →
      decodeTypedValueFromBytesWithPolicy policy fuel.succ protoTransmuteLayouts
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } bytes = none) ∧
    (abstractBytesHaveProv bytes = false →
      decodeTypedValueFromBytesWithPolicy policy fuel.succ protoTransmuteLayouts
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } bytes = none) ∧
    evalByteCastWithPolicy .stripProvenance locals op
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op
        { kind := .ref .not (.uint .u8), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance locals op
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op
        { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance locals op
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op
        { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance locals op
        { kind := .ref .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op
        { kind := .ref .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
        protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance locals op
        { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8], layoutIdx := 1 }
        mem protoTransmuteDecls protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op
        { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8], layoutIdx := 1 }
        mem protoTransmuteDecls protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance locals op protoMaybeUninitU8Arr8Ty
        mem protoTransmuteDecls protoTransmuteLayouts =
      evalByteCastWithPolicy .strictUcg630Ub locals op protoMaybeUninitU8Arr8Ty
        mem protoTransmuteDecls protoTransmuteLayouts ∧
    evalByteCastWithPolicy .stripProvenance protoTransmuteLocals (.copy ⟨0, []⟩) protoUsizeTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.scalar ⟨protoSamplePtr.offsetBytes, 8⟩) protoTransmuteLocals emptyMemory ∧
    evalByteCastWithPolicy .strictUcg630Ub protoTransmuteLocals (.copy ⟨0, []⟩) protoMutU8PtrTy
        emptyMemory protoTransmuteDecls protoTransmuteLayouts =
      .ok (.ptr protoSamplePtr 8) protoTransmuteLocals emptyMemory ∧
    (∀ v, decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] bytes = some v →
      decodeMultiVariantEnumWithPolicy .stripProvenance protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] bytes = some v) ∧
    decodeMultiVariantEnumWithPolicy .stripProvenance protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] bytes =
      decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
        (stripAbstractBytesProv bytes) ∧
    decodeMultiVariantEnumWithPolicy .strictUcg630Ub protoTwoVariantEnumLayout
        (.initialized (.int 32 false) ⟨0, 1⟩) 0
        [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]]
        (encodeLittleEndianBytes protoEnumShapedPtr.offsetBytes 8 (.some (7, 7))) = none :=
  ⟨decodeTypedValueFromBytesWithPolicy_thinRef_policy_indep fuel protoTransmuteLayouts .not
      (.uint .u8) 0 bytes rfl,
   decodeTypedValueFromBytesWithPolicy_fnPtr_policy_indep fuel protoTransmuteLayouts []
      (.tuple []) .safe .rust 0 bytes,
   decodeTypedValueFromBytesWithPolicy_wideDynPtr_policy_indep fuel protoTransmuteLayouts .not
      "Trait" 0 bytes,
   fun hnp v hv => decodeTypedValueFromBytesWithPolicy_no_forge_thinRawPtr policy fuel
      protoTransmuteLayouts .not (.uint .u8) 0 bytes v rfl hnp hv,
   fun hnp => decodeTypedValueFromBytesWithPolicy_no_forge_thinRef policy fuel
      protoTransmuteLayouts .not (.uint .u8) 0 bytes rfl hnp,
   fun hnp => decodeTypedValueFromBytesWithPolicy_no_forge_fnPtr policy fuel
      protoTransmuteLayouts [] (.tuple []) .safe .rust 0 bytes hnp,
   evalByteCastWithPolicy_thinRef_policy_indep locals op
      { kind := .ref .not (.uint .u8), layoutIdx := 0 } mem protoTransmuteDecls
      protoTransmuteLayouts .not (.uint .u8) rfl rfl,
   evalByteCastWithPolicy_fnPtr_policy_indep locals op
      { kind := .fnPtr [] (.tuple []) .safe .rust, layoutIdx := 0 } mem protoTransmuteDecls
      protoTransmuteLayouts [] (.tuple []) .safe .rust rfl,
   evalByteCastWithPolicy_wideDynPtr_policy_indep locals op
      { kind := .rawPtr .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
      protoTransmuteLayouts .not "Trait" rfl,
   evalByteCastWithPolicy_wideDynRef_policy_indep locals op
      { kind := .ref .not (.dynamic "Trait"), layoutIdx := 0 } mem protoTransmuteDecls
      protoTransmuteLayouts .not "Trait" rfl,
   evalByteCastWithPolicy_union_policy_indep locals op
      { kind := .adt "core::mem::maybe_uninit::MaybeUninit" [.uint .u8], layoutIdx := 1 }
      mem protoTransmuteDecls protoTransmuteLayouts "core::mem::maybe_uninit::MaybeUninit"
      [.uint .u8] protoMaybeUninitU8Layout 2 rfl rfl rfl rfl,
   evalByteCastWithPolicy_unionArray_policy_indep locals op protoMaybeUninitU8Arr8Ty
      mem protoTransmuteDecls protoTransmuteLayouts "core::mem::maybe_uninit::MaybeUninit"
      [.uint .u8] 8 1 protoMaybeUninitU8Arr8Layout protoMaybeUninitU8Layout { bytes := 1 } 8 2 []
      rfl rfl rfl rfl rfl rfl rfl,
   ptr2int_flip_direction_separation_witnesses.1,
   ptr_roundtrip_contrast_witnesses.2.2.2.2,
   fun v hv => decodeMultiVariantEnumWithPolicy_strict_refines_strip protoTwoVariantEnumLayout
      (.initialized (.int 32 false) ⟨0, 1⟩) 0
      [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] bytes v hv,
   decodeMultiVariantEnumWithPolicy_strip_eq_strict_erased protoTwoVariantEnumLayout
      (.initialized (.int 32 false) ⟨0, 1⟩) 0
      [.arbitrary [{ bytes := 4 }] [0], .arbitrary [{ bytes := 4 }] [0]] bytes rfl,
   multiVariant_enum_fix_separation_witness.1⟩

/-! ## §15. Automated `run_cmd` Constructive Axiom, Projection-Discipline & Reachability Audit -/

/-
Audit rules (every violation is a hard `throwError`):
1. Every constant of `Anneal.FloatArithAndUcg630Prototype` — including compiler-generated
   auxiliaries without declaration ranges (matchers, structural-recursion helpers, proof
   terms) — depends only on `[propext, Quot.sound]` and is safe and non-`partial` (except
   the compiler-only `_unsafe_rec` twins of structurally recursive definitions).
2. Projection discipline: no definition body and no theorem statement type reaches
   `Prod.casesOn` / `Prod.rec` / `Prod.recOn`, directly or through the transitive closure of
   the matcher constants it mentions (a `match p with | (a, b) => _` hidden inside a matcher
   of a theorem *statement* is rejected just like one inside a definition).
3. Zero host `Float`: no module or test constant mentions a core constant with a `Float`
   name component (`Float`, `Float32`, `Float.add`, `instOfScientificFloat`, `Nat.toFloat`, …).
4. Zero trivial `: True` test theorems: no test theorem in `Anneal.FloatArithAndUcg630ProtoTests`
   may have a stripped return type equal to `True` (preventing empty `have _ := ...; trivial`
   reachability stubs).
5. 100% applied reachability: every public theorem of `Anneal.FloatArithAndUcg630Prototype`
   (≥ 200 theorems) is transitively instantiated by non-`True`-typed test declarations.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constructive : List Name := [``propext, ``Quot.sound]
  let prodElims : List Name := [``Prod.casesOn, ``Prod.rec, ``Prod.recOn]
  let modName : Name := `Anneal.FloatArithAndUcg630Prototype
  let testNs : Name := `Anneal.FloatArithAndUcg630ProtoTests
  let minPublicTheorems : Nat := 200
  let some modIdx := env.getModuleIdx? modName | throwError "module {modName} not imported"
  let isHostFloat : Name → Bool := fun c =>
    let user := (privateToUserName? c).getD c
    let root := user.getRoot
    root != `Anneal && root != `Trusted &&
      user.components.any (fun comp => (comp.toString.splitOn "Float").length > 1)
  let rec isTrivialTrueType : Expr → Bool
    | .forallE _ _ body _ => isTrivialTrueType body
    | .letE _ _ _ body _ => isTrivialTrueType body
    | e => e.isConstOf ``True
  -- Reject `Prod` eliminators reachable from `seeds` through the matcher closure.
  let checkProjectionDiscipline : Name → String → Array Name → CommandElabM Unit :=
    fun owner what seeds => do
      let mut toCheck : Array Name := seeds
      let mut seen : NameSet := {}
      for c in seeds do
        seen := seen.insert c
      let mut idx : Nat := 0
      while idx < toCheck.size do
        let d := toCheck[idx]!
        idx := idx + 1
        if prodElims.contains d then
          throwError "projection discipline violated in {what} of {owner}: reaches {d}"
        if Lean.Meta.isMatcherCore env d then
          if let some dci := env.find? d then
            for c in dci.getUsedConstantsAsSet do
              if !seen.contains c then
                seen := seen.insert c
                toCheck := toCheck.push c
  let mut audited : Nat := 0
  let mut auxAudited : Nat := 0
  let mut theorems : Nat := 0
  let mut auditedThms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx then
      -- `_unsafe_rec` twins are compiler-only implementations of structurally recursive
      -- definitions (never referenced by kernel terms); everything else must be safe.
      unless (Lean.Compiler.isUnsafeRecName? n).isSome do
        if ci.isUnsafe then throwError "unsafe declaration: {n}"
        if ci.isPartial then throwError "partial declaration: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless constructive.contains a do
          let mut culprits : List Name := []
          for sub in ci.getUsedConstantsAsSet do
            let subAxs ← collectAxioms sub
            if subAxs.contains a then
              culprits := sub :: culprits
          throwError "{n} depends on non-constructive or disallowed axiom {a} via {culprits}"
      for c in ci.getUsedConstantsAsSet do
        if isHostFloat c then
          throwError "host Float usage: {n} mentions {c}"
      if let some _ ← findDeclarationRanges? n then
        checkProjectionDiscipline n "statement type" ci.type.getUsedConstantsAsSet.toArray
        if ci matches .defnInfo _ then
          checkProjectionDiscipline n "definition body" ci.getUsedConstantsAsSet.toArray
        audited := audited + 1
        if ci matches .thmInfo _ then
          if !isPrivateName n then
            theorems := theorems + 1
            auditedThms := auditedThms.push n
      else
        auxAudited := auxAudited + 1
  if theorems < minPublicTheorems then
    throwError "{modName}: audited only {theorems} public theorems (expected ≥ {minPublicTheorems})"
  let mut reached : NameSet := {}
  let mut work : Array Name := #[]
  let mut testDecls : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    if testNs.isPrefixOf n then
      if ci.isUnsafe then throwError "unsafe test declaration: {n}"
      if ci.isPartial then throwError "partial test declaration: {n}"
      if (ci matches .thmInfo _) && isTrivialTrueType ci.type then
        throwError "trivial True-typed test theorem forbidden: {n}"
      let axs ← collectAxioms n
      for a in axs do
        unless constructive.contains a do
          throwError "test {n} depends on non-constructive or disallowed axiom {a}"
      for c in ci.getUsedConstantsAsSet do
        if isHostFloat c then
          throwError "host Float usage: test {n} mentions {c}"
        if env.getModuleIdxFor? c == some modIdx && !reached.contains c then
          reached := reached.insert c
          work := work.push c
      testDecls := testDecls + 1
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
    throwError "public theorems not transitively instantiated by non-True applied tests ({unreached.size}): {unreached.toList}"
  logInfo m!"axiom & reachability audit passed: {audited + testDecls} declarations \
    ({theorems} public module theorems, all constructive [propext, Quot.sound] and 100% \
    transitively instantiated by non-True applied tests; zero True-typed test stubs; no \
    Prod.casesOn/Prod.rec; {auxAudited} auxiliary module constants axiom-audited; zero host Float)"

end Anneal.FloatArithAndUcg630ProtoTests
