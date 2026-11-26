-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.AiPcc.Canaries
import Anneal.ParametricCore.V2026Bridge

/-!
# MIR-Level AI-PCC Soundness and Refutation Tests

Regression tests for the single-pass Bourdoncle cutpoint MIR PCC checker
(`Anneal.AiPcc.MirPcc`) over concrete `V2026_06_01` `CapturedMir` bodies built
with the canary helpers of `Anneal.AiPcc.Canaries`:

1. Positive certificates, each checked by `rfl` and transported through
   `checkMirCert_sound_call` or `verifyMirCutpoints_sound_call` to `SafeFrom`,
   a return-value property, and `MirNoUBTree (mirCallTree body args)`:
   checked `u8` addition with an `assert` on the overflow flag, unchecked
   `u8` arithmetic, a `switchInt` guard refinement, a stride-4 `u32` loop with
   one Bourdoncle cutpoint, a widening `IntToInt` cast, and checked `i32`
   addition.
2. `Anneal.ParametricCore` and `V2026Bridge` end-to-end transport: a
   fuel-bounded run of the deterministic step function proves `wpOutcome` at a
   concrete start state, `checkMirCert_sound_call` upgrades it to fault-free
   `wpStateOk` with the certified return postcondition, and `V2026Bridge`
   transports `wpStateOk` / `wpUntilOk` into `MirWpConverges`,
   `MirStepsConverges`, `DWP`, and `TotalVerificationResult` (with
   `MirMemFrame`).
3. `#print axioms` guards: the soundness theorems, trusted certificate
   bridges, and canaries depend only on `propext` and `Quot.sound`.
4. Fail-closed refutations (`= false` by `rfl`) of unsound bodies,
   certificates (including length mismatches), and schedules.
5. Signed-integer and `AutoProve` tests: one-`rfl` certificates through
   `AutoProve.autoVerifyAcyclic` and `AutoProve.autoVerifyCutpoints`, and
   positive / near-miss / negative pairs for signed overflow, `MIN / -1`,
   narrowing casts, signed shift amounts, unsigned `neg`, signed `switchInt`
   refinement, schedules of CFGs whose numbering is not a topological order,
   and cyclic CFGs.
6. `AutoProve.ValidEntryArgs` rejections on `bool` and `()`, exact signed
   constant products, and signed loops (a sign-straddling counter and a count
   up to `i32::MAX`) certified through `AutoProve.autoVerifyCutpoints` and its
   `VerificationResult` / stateful / trace certificates.
7. Congruence-tightened stride-aligned loops (negative, sign-straddling
   count-up and countdown, and non-power-of-two unsigned bounds), bounded
   signed interval multiplication (`sintNoOverflowMulBiased`, including
   opposite-sign `INT_MIN` boundaries and `i128` overflow boundaries), and a
   `bb0`-as-cutpoint loop verified via `AutoProve.autoVerifyCutpoints`.
8. Exact biased signed widening casts (`sintCastAbs` via
   `signedBias_signExtendBits`), signed `*WithOverflow` relational guards
   (`sintAddOverflowBoolAbs` / `sintSubOverflowBoolAbs`, including `0 - y`
   ruling out `i8::MIN / -1` on the `!ov` branch), and exact-constant
   `ov = true` folding.
-/

namespace Anneal.AiPccMirTests

open Anneal.AiPcc
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Helpers -/

/-- Field projection `_r.idx` of type `ty`. -/
def fieldPlace (r idx : Nat) (ty : Ty) : Place := ⟨r, [.field idx ty]⟩

/-- An abstract value that is initialized with bit pattern in `[lo, hi]`. -/
def ivAbs (w lo hi : Nat) : AbsVal :=
  reduceAbsVal w ⟨.init, Tnum.top w, .iv lo hi, .top⟩

/-- A `u8` argument slot: an arbitrary `u8` value. -/
def u8ArgSlots : List MirAbsSlot := [.uint .u8 (AbsVal.topInit 8)]

/-- One-block `fn(x: u8) -> u8` body with locals `_0, _1 : u8`. -/
def oneBlockU8 (stmts : List StatementKind) (t : TerminatorKind) :
    CapturedMir :=
  canaryBody "ai_pcc_tests::one_block_u8" 1
    [canaryUintTy .u8, canaryUintTy .u8] [canaryBlock stmts t]

/-- Entry environment of `oneBlockU8`. -/
def oneBlockU8Entry : MirAbsEnv :=
  entryEnv [canaryDecl (canaryUintTy .u8), canaryDecl (canaryUintTy .u8)]
    u8ArgSlots

/-- Any initialized `u8`. -/
def u8Top : MirAbsSlot := .uint .u8 (AbsVal.topInit 8)

/-! ## 1. Positive Certificates -/

/-! ### 1a. Checked `u8` addition with an overflow `assert` -/

/-- `fn f(x: u8) -> u8 { (x & 127) + 1 }` in debug mode: the sum goes through
`AddWithOverflow` into the tuple `_3 : (u8, bool)`, and
`assert(!move (_3.1))` guards the read of `_3.0`.
- `_0 : u8`; `_1 : u8` argument; `_2 : u8` mask; `_3 : (u8, bool)`. -/
def checkedIncBody : CapturedMir :=
  canaryBody "ai_pcc_tests::checked_inc" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8,
     canaryUintPairTy .u8]
    [ -- bb0: mask, checked add, and assert the overflow flag is clear
      canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2)
          (.binaryOp .bitAnd (canaryCopy 1) (canaryUConst .u8 127)),
        .assign (canaryPlace 3)
          (.binaryOp .addWithOverflow (canaryCopy 2) (canaryUConst .u8 1))]
        (.assert (.move (fieldPlace 3 1 canaryBoolTy)) false 1 .continue_),
      -- bb1: return the sum
      canaryBlock [.assign (canaryPlace 0)
          (.use (.move (fieldPlace 3 0 (canaryUintTy .u8)))),
        .storageDead 3, .storageDead 2] .return_ ]

/-- Return postcondition: the sum lies in `[1, 128]`. -/
def checkedIncRetInv : MirAbsSlot := .uint .u8 (ivAbs 8 1 128)

/-- Entry environment of `checkedIncBody`. -/
def checkedIncEntry : MirAbsEnv :=
  entryEnv checkedIncBody.localDecls u8ArgSlots

/-- Full-map invariant table of `checkedIncBody`. -/
def checkedIncInvs : List (Option MirAbsEnv) :=
  materializeCutpoints checkedIncBody checkedIncEntry [] [0, 1]

/-- Full-map certificate check of `checkedIncBody` by `rfl`. -/
theorem checkedInc_cert_ok :
    checkMirCert checkedIncBody checkedIncEntry checkedIncRetInv
      checkedIncInvs = true := rfl

/-- End-to-end soundness of `checkedIncBody` for every `u8` input: the
`assert` never fails and the result is at most `128`. -/
theorem checkedInc_pcc_safe (x : Nat) (hx : x < modPow2 8) :
    SafeFrom checkedIncBody (initMachineState checkedIncBody [.scalar ⟨x, 1⟩]) ∧
    (∀ v, ReturnsFrom checkedIncBody
        (initMachineState checkedIncBody [.scalar ⟨x, 1⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 1⟩ ∧ bits ≤ 128) ∧
    MirNoUBTree (mirCallTree checkedIncBody [.scalar ⟨x, 1⟩]) := by
  have hArgs : entryArgsOk (checkedIncBody.localDecls.drop 1) u8ArgSlots
      [.scalar ⟨x, 1⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := checkMirCert_sound_call checkedInc_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_ubound rfl hDen

/-! ### 1b. Unchecked `u8` arithmetic -/

/-- `fn f(x: u8) -> u8 { ((x >> 1) + 100) - 50 }` with unchecked shift,
addition, and subtraction: `x >> 1 ≤ 127`, so neither operation overflows.
- `_0 : u8`; `_1 : u8` argument; `_2 : u8` scratch. -/
def uncheckedArithBody : CapturedMir :=
  canaryBody "ai_pcc_tests::unchecked_arith" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .shrUnchecked (canaryCopy 1) (canaryUConst .u8 1)),
        .assign (canaryPlace 2)
          (.binaryOp .addUnchecked (canaryCopy 2) (canaryUConst .u8 100)),
        .assign (canaryPlace 0)
          (.binaryOp .subUnchecked (canaryCopy 2) (canaryUConst .u8 50)),
        .storageDead 2] .return_]

/-- Return postcondition: the result lies in `[50, 177]`. -/
def uncheckedArithRetInv : MirAbsSlot := .uint .u8 (ivAbs 8 50 177)

/-- Single-pass certificate check of `uncheckedArithBody` by `rfl`. -/
theorem uncheckedArith_cert_ok :
    verifyMirCutpoints uncheckedArithBody
      (entryEnv uncheckedArithBody.localDecls u8ArgSlots)
      uncheckedArithRetInv [] [0] = true := rfl

/-- End-to-end soundness of `uncheckedArithBody` for every `u8` input. -/
theorem uncheckedArith_pcc_safe (x : Nat) (hx : x < modPow2 8) :
    SafeFrom uncheckedArithBody
      (initMachineState uncheckedArithBody [.scalar ⟨x, 1⟩]) ∧
    (∀ v, ReturnsFrom uncheckedArithBody
        (initMachineState uncheckedArithBody [.scalar ⟨x, 1⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 1⟩ ∧ bits ≤ 177) ∧
    MirNoUBTree (mirCallTree uncheckedArithBody [.scalar ⟨x, 1⟩]) := by
  have hArgs : entryArgsOk (uncheckedArithBody.localDecls.drop 1) u8ArgSlots
      [.scalar ⟨x, 1⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call uncheckedArith_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_ubound rfl hDen

/-! ### 1c. `switchInt` guard refinement -/

/-- `fn f(x: u8) -> u8 { if x < 10 { x + 1 } else { 0 } }` with an unchecked
increment, as rustc lowers it: the comparison reads the copy temporary `_3`,
and the `true` arm relies on the guard `_1 < 10` refined into `_1`.
- `_0 : u8`; `_1 : u8` argument; `_2 : bool`; `_3 : u8` temporary. -/
def guardIncBody : CapturedMir :=
  canaryBody "ai_pcc_tests::guard_inc" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryBoolTy, canaryUintTy .u8]
    [ -- bb0: `_2 = Lt(move _3, 10)` on `_3 = copy _1`
      canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 3) (.use (canaryCopy 1)),
        .assign (canaryPlace 2)
          (.binaryOp .lt (canaryMove 3) (canaryUConst .u8 10)),
        .storageDead 3] (.switchInt (canaryMove 2) ⟨[(0, 2)], 1⟩),
      -- bb1: `x < 10`, so `x + 1` cannot overflow
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u8 1))]
        (.goto 3),
      -- bb2: `x >= 10`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryUConst .u8 0))]
        (.goto 3),
      -- bb3: join and return
      canaryBlock [.storageDead 2] .return_ ]

/-- Return postcondition: the result is at most `10`. -/
def guardIncRetInv : MirAbsSlot := .uint .u8 (ivAbs 8 0 10)

/-- Single-pass certificate check of `guardIncBody` (CFG join at `bb3`). -/
theorem guardInc_cert_ok :
    verifyMirCutpoints guardIncBody
      (entryEnv guardIncBody.localDecls u8ArgSlots)
      guardIncRetInv [] [0, 1, 2, 3] = true := rfl

/-- End-to-end soundness of `guardIncBody` for every `u8` input. -/
theorem guardInc_pcc_safe (x : Nat) (hx : x < modPow2 8) :
    SafeFrom guardIncBody (initMachineState guardIncBody [.scalar ⟨x, 1⟩]) ∧
    (∀ v, ReturnsFrom guardIncBody
        (initMachineState guardIncBody [.scalar ⟨x, 1⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 1⟩ ∧ bits ≤ 10) ∧
    MirNoUBTree (mirCallTree guardIncBody [.scalar ⟨x, 1⟩]) := by
  have hArgs : entryArgsOk (guardIncBody.localDecls.drop 1) u8ArgSlots
      [.scalar ⟨x, 1⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call guardInc_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_ubound rfl hDen

/-! ### 1d. Stride-4 `u32` loop with one Bourdoncle cutpoint -/

/-- Certified loop-header value: `0 ≤ _1 ≤ 64` and `_1 ≡ 0 (mod 4)`. -/
def stride4HeaderAbs : AbsVal :=
  reduceAbsVal 32
    { init := .init
      tnum := ⟨0, 124⟩  -- bits 2..6 unknown (0x7C = 124), bits 0..1 = 0
      wi := .iv 0 64
      sc := .cong 4 0 }

/-- `fn stride4() -> u32`: count `_1` from `0` to `64` in steps of `4` with
an unchecked addition, then return `_1` after a `_1 == 64` test whose
`false` edge reaches a dead `unreachable` trap. The addition is safe only
because the header invariant is aligned: `_1 < 64` and `_1 ≡ 0 (mod 4)` give
`_1 ≤ 60`.
- `_0 : u32`; `_1 : u32` index; `_2 : bool` guard. -/
def stride4LoopBody : CapturedMir :=
  canaryBody "ai_pcc_tests::stride4_loop" 0
    [canaryUintTy .u32, canaryUintTy .u32, canaryBoolTy]
    [ -- bb0: entry
      canaryBlock [.storageLive 1,
        .assign (canaryPlace 1) (.use (canaryUConst .u32 0)),
        .storageLive 2] (.goto 1),
      -- bb1: loop header (the only cutpoint)
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp .lt (canaryCopy 1) (canaryUConst .u32 64))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      -- bb2: loop body
      canaryBlock [.assign (canaryPlace 1)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u32 4))]
        (.goto 1),
      -- bb3: loop exit (`_1 ≥ 64` and `_1 ≤ 64` give `_1 = 64`)
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp .eq (canaryCopy 1) (canaryUConst .u32 64))]
        (.switchInt (canaryCopy 2) ⟨[(0, 4)], 5⟩),
      -- bb4: dead trap
      canaryBlock [] .unreachable,
      -- bb5: return `_1`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 2, .storageDead 1] .return_ ]

/-- Loop-header invariant of `stride4LoopBody` (`bb1`). -/
def stride4Cutpoints : List (Nat × MirAbsEnv) :=
  [(1, [.uint .u32 (AbsVal.uninit 32), .uint .u32 stride4HeaderAbs,
        .bool .uninit])]

/-- Exact return postcondition `_0 = 64`. -/
def stride4RetInv : MirAbsSlot := .uint .u32 (AbsVal.const 32 64)

/-- Single-pass certificate check of `stride4LoopBody` by `rfl`. -/
theorem stride4Loop_cert_ok :
    verifyMirCutpoints stride4LoopBody (entryEnv stride4LoopBody.localDecls [])
      stride4RetInv stride4Cutpoints [0, 1, 2, 3, 4, 5] = true := rfl

/-- End-to-end soundness of `stride4LoopBody`: safety across unboundedly many
iterations and the exact return value `64`. -/
theorem stride4Loop_pcc_safe :
    SafeFrom stride4LoopBody (initMachineState stride4LoopBody []) ∧
    (∀ v, ReturnsFrom stride4LoopBody (initMachineState stride4LoopBody []) v →
      v = .scalar ⟨64, 4⟩) ∧
    MirNoUBTree (mirCallTree stride4LoopBody []) := by
  have h := verifyMirCutpoints_sound_call stride4Loop_cert_ok
    (entryArgsOk_nil _)
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_exact rfl hDen

/-! ### 1e. Widening `IntToInt` cast -/

/-- `fn f(x: u8) -> u32 { (x as u32) * 1000 }` with an unchecked
multiplication: the widened value is at most `255`, so the product fits.
- `_0 : u32`; `_1 : u8` argument; `_2 : u32` widened copy. -/
def widenMulBody : CapturedMir :=
  canaryBody "ai_pcc_tests::widen_mul" 1
    [canaryUintTy .u32, canaryUintTy .u8, canaryUintTy .u32]
    [canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.cast .intToInt (canaryCopy 1) (canaryUintTy .u32)),
        .assign (canaryPlace 0)
          (.binaryOp .mulUnchecked (canaryMove 2) (canaryUConst .u32 1000)),
        .storageDead 2] .return_]

/-- Return postcondition: the product is at most `255000`. -/
def widenMulRetInv : MirAbsSlot := .uint .u32 (ivAbs 32 0 255000)

/-- Single-pass certificate check of `widenMulBody` by `rfl`. -/
theorem widenMul_cert_ok :
    verifyMirCutpoints widenMulBody (entryEnv widenMulBody.localDecls u8ArgSlots)
      widenMulRetInv [] [0] = true := rfl

/-- End-to-end soundness of `widenMulBody` for every `u8` input. -/
theorem widenMul_pcc_safe (x : Nat) (hx : x < modPow2 8) :
    SafeFrom widenMulBody (initMachineState widenMulBody [.scalar ⟨x, 1⟩]) ∧
    (∀ v, ReturnsFrom widenMulBody
        (initMachineState widenMulBody [.scalar ⟨x, 1⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 4⟩ ∧ bits ≤ 255000) ∧
    MirNoUBTree (mirCallTree widenMulBody [.scalar ⟨x, 1⟩]) := by
  have hArgs : entryArgsOk (widenMulBody.localDecls.drop 1) u8ArgSlots
      [.scalar ⟨x, 1⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call widenMul_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_ubound rfl hDen

/-! ### 1f. Checked `i32` addition -/

/-- Signed `(i32, bool)` checked-arithmetic tuple type. -/
def intPairTy (i : IntTy) : Ty := ⟨.tuple [.int i, .bool], 0⟩

/-- `fn f(x: i32) -> i32 { (x & 127) + 1 }` in debug mode, with the sum in the
tuple `_3 : (i32, bool)` and `assert(!move (_3.1))`.
- `_0 : i32`; `_1 : i32` argument; `_2 : i32` mask; `_3 : (i32, bool)`. -/
def signedCheckedIncBody : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_checked_inc" 1
    [canaryIntTy .i32, canaryIntTy .i32, canaryIntTy .i32, intPairTy .i32]
    [ canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2)
          (.binaryOp .bitAnd (canaryCopy 1) (canaryIConst .i32 127)),
        .assign (canaryPlace 3)
          (.binaryOp .addWithOverflow (canaryCopy 2) (canaryIConst .i32 1))]
        (.assert (.move (fieldPlace 3 1 canaryBoolTy)) false 1 .continue_),
      canaryBlock [.assign (canaryPlace 0)
          (.use (.move (fieldPlace 3 0 (canaryIntTy .i32)))),
        .storageDead 3, .storageDead 2] .return_ ]

/-- Argument slot: an arbitrary `i32` value. -/
def i32ArgSlots : List MirAbsSlot := [.sint .i32 (AbsVal.topInit 32)]

/-- Return postcondition: the bit pattern lies in `[1, 128]`. -/
def signedCheckedIncRetInv : MirAbsSlot := .sint .i32 (ivAbs 32 1 128)

/-- Single-pass certificate check of `signedCheckedIncBody` by `rfl`. -/
theorem signedCheckedInc_cert_ok :
    verifyMirCutpoints signedCheckedIncBody
      (entryEnv signedCheckedIncBody.localDecls i32ArgSlots)
      signedCheckedIncRetInv [] [0, 1] = true := rfl

/-- End-to-end soundness of `signedCheckedIncBody` for every `i32` input. -/
theorem signedCheckedInc_pcc_safe (x : Nat) (hx : x < modPow2 32) :
    SafeFrom signedCheckedIncBody
      (initMachineState signedCheckedIncBody [.scalar ⟨x, 4⟩]) ∧
    (∀ v, ReturnsFrom signedCheckedIncBody
        (initMachineState signedCheckedIncBody [.scalar ⟨x, 4⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 4⟩ ∧ bits ≤ 128) ∧
    MirNoUBTree (mirCallTree signedCheckedIncBody [.scalar ⟨x, 4⟩]) := by
  have hArgs : entryArgsOk (signedCheckedIncBody.localDecls.drop 1)
      i32ArgSlots [.scalar ⟨x, 4⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call signedCheckedInc_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact sint_valDenote_ubound rfl hDen

/-! ## 2. `Anneal.ParametricCore` Transport -/

/-- Fuel-bounded run of a deterministic step function: `true` when every
execution from `s` stops (terminates or faults) within `n` steps. -/
def detStops {S O F : Type} (step : S → Anneal.ParametricCore.StepOutcome S O F) :
    Nat → S → Bool
  | 0, _ => false
  | n + 1, s =>
    match step s with
    | .step s' => detStops step n s'
    | .done _ => true
    | .fault _ => true

/-- A fuel-bounded run that stops gives the fault-tolerant `wpOutcome` of the
deterministic `MirWpOps` interface. -/
theorem wpOutcome_of_detStops {S O F : Type}
    (step : S → Anneal.ParametricCore.StepOutcome S O F)
    (tag : S → Option Nat) :
    ∀ (n : Nat) (s : S), detStops step n s = true →
      @Anneal.ParametricCore.wpOutcome _ _ _
        (Anneal.ParametricCore.MirWpOps.ofDetStep step tag)
        (fun _ => True) (fun _ => True) s
  | 0, _, h => nomatch h
  | n + 1, s, h => by
    apply @Anneal.ParametricCore.wpOutcome_step _ _ _
      (Anneal.ParametricCore.MirWpOps.ofDetStep step tag)
    show (step s).wp _ _ _
    revert h
    simp only [detStops]
    cases step s with
    | step s' => exact wpOutcome_of_detStops step tag n s'
    | done _ => intro _; exact True.intro
    | fault _ => intro _; exact True.intro

/-- Concrete input of the `ParametricCore` transport test. -/
def checkedIncArgs : List Value := [.scalar ⟨200, 1⟩]

/-- A fuel-bounded run of `checkedIncBody` on `x = 200` stops. -/
theorem checkedInc_detStops :
    detStops (fun s => mirNodeOutcome (stepMirFn checkedIncBody s)) 32
      (initMachineState checkedIncBody checkedIncArgs) = true := rfl

/-- Fault-free total correctness of `checkedIncBody` on `x = 200` in the
`Anneal.ParametricCore` weakest-precondition calculus: the run terminates
without faults and returns a value described by `checkedIncRetInv`. The
termination proof is fault-tolerant; `checkMirCert_sound_call` removes the
faults and adds the postcondition. -/
theorem checkedInc_wpStateOk :
    @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps checkedIncBody)
      (mirRetPost checkedIncBody checkedIncRetInv)
      (initMachineState checkedIncBody checkedIncArgs) := by
  have hArgs : entryArgsOk (checkedIncBody.localDecls.drop 1) u8ArgSlots
      checkedIncArgs :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound (by decide)⟩, True.intro⟩
  exact (checkMirCert_sound_call checkedInc_cert_ok hArgs).2.2.2
    (wpOutcome_of_detStops _ _ 32 _ checkedInc_detStops)

/-- Fault-free `wpUntilOk` over `mirPccWpOps` refines into `V2026Bridge`'s
call-free coalgebraic `mirNoCallCoalWpOps`. -/
theorem wpUntilOk_noCallCoal_of_mirPcc {body : CapturedMir}
    {stop : MachineState → Prop} {post : MirOutcome → Prop}
    {s : MachineState}
    (h : @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body) stop post s) :
    @Anneal.ParametricCore.wpUntilOk _ _ _
      (Anneal.ParametricCore.V2026Bridge.mirNoCallCoalWpOps body)
      stop post s := by
  refine Anneal.ParametricCore.wpUntil_induction (ops := mirPccWpOps body)
    (C := fun s' =>
      @Anneal.ParametricCore.wpUntilOk _ _ _
        (Anneal.ParametricCore.V2026Bridge.mirNoCallCoalWpOps body)
        stop post s')
    (fun _ hStop => Anneal.ParametricCore.wpUntil_here
      (ops := Anneal.ParametricCore.V2026Bridge.mirNoCallCoalWpOps body) hStop)
    (fun s' hStep => by
      refine Anneal.ParametricCore.wpUntil_step
        (ops := Anneal.ParametricCore.V2026Bridge.mirNoCallCoalWpOps body) ?_
      change (mirNodeOutcome (stepMirFn body s')).wp _ _ _ at hStep
      change match stepMirState body (.running s') with
        | .ret out => post out
        | .tau st' => Anneal.ParametricCore.V2026Bridge.liftExecCont
            _ post (fun _ => False) st'
        | .vis i k => Anneal.Rustc.V2026_06_01.Lower.mirNoCallWP.wp i
            (fun o _ => Anneal.ParametricCore.V2026Bridge.liftExecCont
              _ post (fun _ => False) (k o)) PUnit.unit
      dsimp only [stepMirState]
      cases hFn : stepMirFn body s' with
      | ret out => rw [hFn] at hStep; exact hStep
      | tau st' =>
        rw [hFn] at hStep
        cases st' with
        | running s'' => exact hStep
        | halted out => exact hStep
        | faulted _ => exact False.elim hStep
      | vis i k =>
        rw [hFn] at hStep
        rcases i with f | (e | c)
        · cases f; exact False.elim hStep
        · cases e
          dsimp only [mirNodeOutcome] at hStep
          change Anneal.ParametricCore.V2026Bridge.liftExecCont
            _ post (fun _ => False) (k PUnit.unit)
          cases hK : k PUnit.unit with
          | running s'' => rw [hK] at hStep; exact hStep
          | halted out => rw [hK] at hStep; exact hStep
          | faulted _ => rw [hK] at hStep; exact False.elim hStep
        · cases c; exact False.elim hStep)
    h

/-- Transport from `mirPccWpOps` `wpUntilOk` into `MirStepsConverges` via
`Anneal.ParametricCore.V2026Bridge`. -/
theorem mirStepsConverges_of_mirPccWpUntilOk {body : CapturedMir}
    {stop : MachineState → Prop} {post : MirOutcome → Prop}
    {s : MachineState}
    (h : @Anneal.ParametricCore.wpUntilOk _ _ _ (mirPccWpOps body) stop post s) :
    Anneal.MirFuelFree.MirStepsConverges body s stop post :=
  Anneal.ParametricCore.V2026Bridge.mirStepsConverges_of_noCallCoalWpUntilOk
    (wpUntilOk_noCallCoal_of_mirPcc h)

/-- Transport from `mirPccWpOps` `wpStateOk` into `MirWpConverges` via
`Anneal.ParametricCore.V2026Bridge`. -/
theorem mirWpConverges_of_mirPccWpStateOk {body : CapturedMir}
    {post : MirOutcome → Prop} {s : MachineState}
    (h : @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body) post s) :
    Anneal.MirFuelFree.MirWpConverges body s post :=
  Anneal.ParametricCore.V2026Bridge.mirWpConverges_of_noCallCoalWpStateOk
    (wpUntilOk_noCallCoal_of_mirPcc h)

/-- Transport from `mirPccWpOps` `wpStateOk` into total-correctness `DWP` over
`mirDefaultWP` via `Anneal.ParametricCore.V2026Bridge`. -/
theorem dwp_of_mirPccWpStateOk {body : CapturedMir}
    {post : MirOutcome → Prop} {s : MachineState}
    (h : @Anneal.ParametricCore.wpStateOk _ _ _ (mirPccWpOps body) post s) :
    Anneal.ITreeWP.DWP Anneal.Rustc.V2026_06_01.Lower.mirDefaultWP
      (mirTree body s) (fun out _ => post out) PUnit.unit :=
  Anneal.ParametricCore.V2026Bridge.dwp_of_coalWpStateOk
    (Anneal.ParametricCore.wpUntil_of_refines
      (Anneal.ParametricCore.V2026Bridge.mirNoCallCoalWpOps_refines_mirCoalWpOps
        body)
      (wpUntilOk_noCallCoal_of_mirPcc h))

/-- End-to-end `MirWpConverges`, `MirStepsConverges`, and `DWP` soundness for
`checkedIncBody` on `x = 200`, bridged through
`Anneal.ParametricCore.V2026Bridge`. -/
theorem checkedInc_v2026Bridge_converges :
    Anneal.MirFuelFree.MirWpConverges checkedIncBody
      (initMachineState checkedIncBody checkedIncArgs)
      (mirRetPost checkedIncBody checkedIncRetInv) ∧
    Anneal.MirFuelFree.MirStepsConverges checkedIncBody
      (initMachineState checkedIncBody checkedIncArgs) (fun _ => False)
      (mirRetPost checkedIncBody checkedIncRetInv) ∧
    Anneal.ITreeWP.DWP Anneal.Rustc.V2026_06_01.Lower.mirDefaultWP
      (mirCallTree checkedIncBody checkedIncArgs)
      (fun out _ => mirRetPost checkedIncBody checkedIncRetInv out)
      PUnit.unit :=
  ⟨mirWpConverges_of_mirPccWpStateOk checkedInc_wpStateOk,
   mirStepsConverges_of_mirPccWpUntilOk checkedInc_wpStateOk,
   dwp_of_mirPccWpStateOk checkedInc_wpStateOk⟩

/-- A `checkMirCert` certificate plus a fault-tolerant `wpOutcome` termination
proof yields a trusted `TotalVerificationResult` (`TreeSafe`, `Productive`,
`¬ MayDiverge`, and normal-only `ReachesRet` satisfying `c.post`). Placed in
the test bridge because `Trusted.ITree.Diverges` uses `coinductive_fixpoint`
(`Classical.choice`), keeping `theory/Anneal/AiPcc/MirPcc.lean` strictly
`[propext, Quot.sound]`. -/
theorem checkMirCert_totalVerificationResult
    {c : Trusted.VerificationResult.TotalClaim} {argSlots : List MirAbsSlot}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    (hChk : checkMirCert c.body (entryEnv c.body.localDecls argSlots) retInv
      invs = true)
    (hPre : ∀ args mem, c.pre args mem →
      mem.callStack = [] ∧ mem.activeCallee = none ∧
      mem.activeProtectors = [] ∧
      entryArgsOk (c.body.localDecls.drop 1) argSlots args)
    (hTerm : ∀ args mem, c.pre args mem →
      @Anneal.ParametricCore.wpOutcome _ _ _ (mirPccWpOps c.body)
        (fun _ => True) (fun _ => True)
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees))
    (hPost : ∀ args mem retVal mem', c.pre args mem →
      MirMemFrame mem' mem →
      (∃ d, get? c.body.localDecls 0 = some d ∧
        retInv.valDenote d.ty retVal) →
      c.post args mem retVal mem') :
    Trusted.VerificationResult.TotalVerificationResult c := by
  have hPhase := bool_and_true_left hChk
  have hAll := bool_and_true_right (bool_and_true_right
    (bool_and_true_right (bool_and_true_right hChk)))
  refine ⟨?_⟩
  intro args mem hDef
  have hP := hPre args mem hDef
  have hRoot := initMachineStateWithMemoryAndCallees_root c.body args mem
    c.callees hP.1 hP.2.1 hP.2.2.1
  have hEntry : mirAbsEnvDenote c.body.localDecls
      (entryEnv c.body.localDecls argSlots)
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        c.body args mem c.callees).frame.locals := by
    rw [hRoot.2.1]
    exact entryEnv_sound hP.2.2.2
  have hInv0 := mirPccInv_start hChk hRoot.1 hEntry
  have hSound := checkMirCert_sound hChk hRoot.1 hEntry
  have hProd := productive_of_mirPccInv hPhase hAll hInv0 (hTerm args mem hDef)
  have hNoDiv : ¬ Trusted.ITree.MayDiverge
      (Trusted.VerificationResult.mirStatefulTreeWithCallees c.body args mem
        c.callees) := by
    intro hM
    match hM with
    | ⟨tr, u, hR, hD⟩ =>
      match hProd tr u hR with
      | ⟨u', hT, hNe⟩ =>
        exact Anneal.ITree.Diverges.not_nonTau hD hT hNe
  refine ⟨hSound.2.2.1, hProd, hNoDiv, ?_⟩
  intro tr out hRR
  match reachesRet_normal_of_mirPccInv (retInv := retInv) hPhase hAll hInv0 hRR
    with
  | ⟨retVal, mem', hEq, _, hFrame, hRet⟩ =>
    exact ⟨retVal, mem', hEq,
      hPost args mem retVal mem' hDef (hFrame.trans hRoot.2.2)
        (hSound.2.1 retVal hRet)⟩

/-- Total-correctness claim for `checkedIncBody` on `x = 200` and default
empty memory: UB-free, productive, non-diverging, preserving `MirMemFrame`,
and returning a `u8` in `[1, 128]`. -/
def checkedIncTotalClaim : Trusted.VerificationResult.TotalClaim where
  body := checkedIncBody
  pre args mem := args = checkedIncArgs ∧ mem = {}
  post _ mem ret mem' :=
    MirMemFrame mem' mem ∧ ∃ b, ret = .scalar ⟨b, 1⟩ ∧ 1 ≤ b ∧ b ≤ 128

/-- End-to-end `TotalVerificationResult checkedIncTotalClaim` from the `rfl`
certificate and fuel-bounded `detStops` termination proof. -/
theorem checkedInc_totalVerificationResult :
    Trusted.VerificationResult.TotalVerificationResult checkedIncTotalClaim :=
  checkMirCert_totalVerificationResult (argSlots := u8ArgSlots)
    checkedInc_cert_ok
    (fun args mem hPre => by
      match hPre with
      | ⟨hArgs, hMem⟩ =>
        subst hArgs
        subst hMem
        exact ⟨rfl, rfl, rfl,
          ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound (by decide)⟩, True.intro⟩⟩)
    (fun args mem hPre => by
      match hPre with
      | ⟨hArgs, hMem⟩ =>
        subst hArgs
        subst hMem
        exact wpOutcome_of_detStops _ _ 32 _ checkedInc_detStops)
    (fun _ _ retVal _ _ hFrame hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        have h2 := hDen.2
        cases retVal with
        | scalar sc =>
          cases sc with
          | mk bits sz =>
            have hSz : sz = 1 := h2.1
            subst hSz
            exact ⟨hFrame, bits, rfl, absVal_lbound?_sound (lo := 1) rfl h2.2,
              absVal_ubound?_sound (hi := 128) rfl h2.2⟩
        | _ => exact False.elim h2)

/-! ## 3. Axiom Guards -/

/--
info: 'Anneal.AiPcc.productive_of_mirPccInv' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms productive_of_mirPccInv

/--
info: 'Anneal.AiPcc.checkMirCert_statefulVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkMirCert_statefulVerificationResult

/--
info: 'Anneal.AiPcc.canary_bitmask_div_cast_statefulVerificationResult'
depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_bitmask_div_cast_statefulVerificationResult

/--
info: 'Anneal.AiPcc.checkMirCert_sound_call' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkMirCert_sound_call

/--
info: 'Anneal.AiPcc.verifyMirCutpoints_sound_call' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms verifyMirCutpoints_sound_call

/--
info: 'Anneal.AiPcc.checkMirCert_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkMirCert_verificationResult

/--
info: 'Anneal.AiPcc.canary_stride8_loop_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_stride8_loop_verificationResult

/--
info: 'Anneal.AiPcc.canary_signed_half_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_half_verificationResult

/--
info: 'Anneal.AiPcc.checkMirCert_traceVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkMirCert_traceVerificationResult

/--
info: 'Anneal.AiPcc.canary_signed_half_traceVerificationResult' depends on
axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_half_traceVerificationResult

/--
info: 'Anneal.AiPcc.canary_spin_loop_safe_never_returns' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_spin_loop_safe_never_returns

/--
info: 'Anneal.AiPcc.checkMirCert_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkMirCert_sound

/--
info: 'Anneal.AiPcc.verifyMirCutpoints_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms verifyMirCutpoints_sound

/--
info: 'Anneal.AiPcc.canary_stride8_loop_pcc_safe' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_stride8_loop_pcc_safe

/--
info: 'Anneal.AiPcc.canary_signed_half_pcc_safe' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_half_pcc_safe

/--
info: 'Anneal.AiPccMirTests.checkedInc_wpStateOk' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkedInc_wpStateOk

/--
info: 'Anneal.AiPcc.AutoProve.autoVerifyAcyclic_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.autoVerifyAcyclic_sound

/--
info: 'Anneal.AiPcc.AutoProve.autoVerifyCutpoints_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.autoVerifyCutpoints_sound

/--
info: 'Anneal.AiPcc.AutoProve.bodyVerified_of_autoVerifyAcyclic' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.bodyVerified_of_autoVerifyAcyclic

/--
info: 'Anneal.AiPcc.AutoProve.bodyVerified_of_autoVerifyCutpoints' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.bodyVerified_of_autoVerifyCutpoints

/--
info: 'Anneal.AiPcc.AutoProve.statefulVerificationResult_of_autoVerifyAcyclic' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.statefulVerificationResult_of_autoVerifyAcyclic

/--
info: 'Anneal.AiPcc.AutoProve.traceVerificationResult_of_autoVerifyAcyclic' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.traceVerificationResult_of_autoVerifyAcyclic

/--
info: 'Anneal.AiPcc.AutoProve.buildEntryEnv?_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.buildEntryEnv?_sound

/--
info: 'Anneal.AiPcc.canary_signed_guarded_ops_auto_safe' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_guarded_ops_auto_safe

/--
info: 'Anneal.AiPcc.canary_signed_guarded_ops_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_guarded_ops_verificationResult

/--
info: 'Anneal.AiPcc.canary_signed_isize_to_usize_auto_safe' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_signed_isize_to_usize_auto_safe

/--
info: 'Anneal.AiPcc.canary_non_monotonic_rpo_auto_verified' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canary_non_monotonic_rpo_auto_verified

/--
info: 'Anneal.AiPcc.refineEnvByGuard_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refineEnvByGuard_sound

/--
info: 'Anneal.AiPcc.stepStmtAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepStmtAbs_sound

/--
info: 'Anneal.AiPcc.stepTermAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepTermAbs_sound

/--
info: 'Anneal.AiPcc.autoVerifyAcyclic_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms autoVerifyAcyclic_verificationResult

/-! ## 4. Fail-Closed Refutations -/

/-- Unchecked arithmetic that may overflow, shift by at least the width, or
divide by zero is rejected. -/
theorem unsafe_arith_rejected :
    -- `x + 1` may overflow `u8`.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u8 1))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `x - 1` may underflow.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .subUnchecked (canaryCopy 1) (canaryUConst .u8 1))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `x << 8` shifts by the full width.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .shlUnchecked (canaryCopy 1) (canaryUConst .u8 8))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `x >> 9` shifts past the width.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .shrUnchecked (canaryCopy 1) (canaryUConst .u8 9))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `x / 0`.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .div (canaryCopy 1) (canaryUConst .u8 0))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `x % 0`.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .rem (canaryCopy 1) (canaryUConst .u8 0))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `10 / x` with `x` possibly zero.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .div (canaryUConst .u8 10) (canaryCopy 1))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- `10 % x` with `x` possibly zero.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .rem (canaryUConst .u8 10) (canaryCopy 1))] .return_)
      oneBlockU8Entry u8Top [] [0] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Positive twins of `unsafe_arith_rejected` that stay in range. -/
theorem safe_arith_accepted :
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .shlUnchecked (canaryCopy 1) (canaryUConst .u8 7))] .return_)
      oneBlockU8Entry u8Top [] [0] = true ∧
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .shrUnchecked (canaryCopy 1) (canaryUConst .u8 7))] .return_)
      oneBlockU8Entry u8Top [] [0] = true ∧
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .rem (canaryCopy 1) (canaryUConst .u8 3))] .return_)
      oneBlockU8Entry u8Top [] [0] = true :=
  ⟨rfl, rfl, rfl⟩

/-- `fn(x: u8) -> u8` with a third local `_2 : u8` that is never
initialized. -/
def threeLocalU8 (stmts : List StatementKind) : CapturedMir :=
  canaryBody "ai_pcc_tests::three_local_u8" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock stmts .return_]

/-- Reads of dead or uninitialized locals, a reachable `unreachable`, and an
uninitialized return place are rejected. -/
theorem bad_reads_and_traps_rejected :
    -- `_0 = copy _2` with `_2` dead (no `StorageLive`).
    verifyMirCutpoints (threeLocalU8 [.assign (canaryPlace 0) (.use (canaryCopy 2))])
      (entryEnv (threeLocalU8 []).localDecls u8ArgSlots) u8Top [] [0] = false ∧
    -- `_0 = copy _2` with `_2` live but uninitialized.
    verifyMirCutpoints
      (threeLocalU8 [.storageLive 2, .assign (canaryPlace 0) (.use (canaryCopy 2))])
      (entryEnv (threeLocalU8 []).localDecls u8ArgSlots) u8Top [] [0] = false ∧
    -- Positive twin: `_0 = copy _1`.
    verifyMirCutpoints
      (threeLocalU8 [.storageLive 2, .assign (canaryPlace 0) (.use (canaryCopy 1))])
      (entryEnv (threeLocalU8 []).localDecls u8ArgSlots) u8Top [] [0] = true ∧
    -- Use after move: `_0 = Add(move _1, copy _1)`.
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0)
        (.binaryOp .add (canaryMove 1) (canaryCopy 1))] .return_)
      oneBlockU8Entry u8Top [] [0] = false ∧
    -- Reachable `unreachable`.
    verifyMirCutpoints (oneBlockU8 [] .unreachable) oneBlockU8Entry u8Top [] [0] =
      false ∧
    -- Returning the uninitialized `_0`.
    verifyMirCutpoints (oneBlockU8 [] .return_) oneBlockU8Entry u8Top [] [0] =
      false ∧
    -- An `assert` that may fail: `assert(_1 < 10)` on an arbitrary `u8`.
    verifyMirCutpoints
      (canaryBody "ai_pcc_tests::maybe_assert" 1
        [canaryUintTy .u8, canaryUintTy .u8, canaryBoolTy]
        [canaryBlock [.storageLive 2, .assign (canaryPlace 2)
            (.binaryOp .lt (canaryCopy 1) (canaryUConst .u8 10))]
          (.assert (canaryMove 2) true 1 .continue_),
         canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
           .storageDead 2] .return_])
      (entryEnv [canaryDecl (canaryUintTy .u8), canaryDecl (canaryUintTy .u8),
        canaryDecl canaryBoolTy] u8ArgSlots) u8Top [] [0, 1] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Return postconditions the body does not establish are rejected. -/
theorem violated_retInv_rejected :
    -- `checkedIncBody` can return `128`.
    checkMirCert checkedIncBody checkedIncEntry (.uint .u8 (ivAbs 8 1 127))
      checkedIncInvs = false ∧
    -- `stride4LoopBody` returns `64`, not `60`.
    verifyMirCutpoints stride4LoopBody (entryEnv stride4LoopBody.localDecls [])
      (.uint .u32 (AbsVal.const 32 60)) stride4Cutpoints [0, 1, 2, 3, 4, 5] =
      false ∧
    -- `guardIncBody` can return `10`.
    verifyMirCutpoints guardIncBody (entryEnv guardIncBody.localDecls u8ArgSlots)
      (.uint .u8 (ivAbs 8 0 9)) [] [0, 1, 2, 3] = false ∧
    -- A frame-relative guard in the return postcondition.
    verifyMirCutpoints
      (canaryBody "ai_pcc_tests::guard_ret" 1 [canaryBoolTy, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .lt (canaryCopy 1) (canaryUConst .u8 8))] .return_])
      (entryEnv [canaryDecl canaryBoolTy, canaryDecl (canaryUintTy .u8)]
        u8ArgSlots)
      (.bool (.top (.uleConst 1 .u8 7))) [] [0] = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Full-map certificates that claim a reachable block unreachable, omit a
block, or do not cover the entry environment are rejected. -/
theorem bad_full_map_rejected :
    let body := canaryBody "ai_pcc_tests::two_block" 1
      [canaryUintTy .u8, canaryUintTy .u8]
      [canaryBlock [] (.goto 1),
       canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_]
    let e0 := entryEnv body.localDecls u8ArgSlots
    -- Positive control: both blocks certified with the entry environment.
    checkMirCert body e0 u8Top [some e0, some e0] = true ∧
    -- `bb1` claimed unreachable although `bb0` jumps to it.
    checkMirCert body e0 u8Top [some e0, none] = false ∧
    -- The table omits `bb1`.
    checkMirCert body e0 u8Top [some e0] = false ∧
    -- `bb0`'s invariant does not cover the entry environment.
    checkMirCert body e0 u8Top
      [some [.uint .u8 (AbsVal.uninit 8), .uint .u8 (AbsVal.const 8 0)],
       some e0] = false ∧
    -- `entryEnv` has wrong length (3 slots on a 2-local body).
    checkMirCert body (e0 ++ [.dead]) u8Top
      [some (e0 ++ [.dead]), some (e0 ++ [.dead])] = false ∧
    verifyMirCutpoints body (e0 ++ [.dead]) u8Top [] [0, 1] = false ∧
    -- An unreachable block invariant in `invs` with wrong length is rejected.
    checkMirCert
      (canaryBody "ai_pcc_tests::dead_block" 1
        [canaryUintTy .u8, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_,
         canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_])
      e0 u8Top [some e0, some (e0 ++ [.dead])] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Invalid Bourdoncle schedules are rejected by `validRpoSchedule` and by
`verifyMirCutpoints`. -/
theorem bad_schedules_rejected :
    let env := entryEnv stride4LoopBody.localDecls []
    -- Positive control.
    validRpoSchedule stride4LoopBody stride4Cutpoints [0, 1, 2, 3, 4, 5] =
      true ∧
    -- The back-edge `bb2 -> bb1` targets a non-cutpoint.
    validRpoSchedule stride4LoopBody [] [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints stride4LoopBody env stride4RetInv []
      [0, 1, 2, 3, 4, 5] = false ∧
    -- `bb5` scheduled before `bb3`, although the edge `bb3 -> bb5` targets a
    -- non-cutpoint.
    validRpoSchedule stride4LoopBody stride4Cutpoints [0, 1, 2, 5, 3, 4] =
      false ∧
    -- Not headed by `bb0`.
    validRpoSchedule stride4LoopBody stride4Cutpoints [1, 0, 2, 3, 4, 5] =
      false ∧
    -- Duplicate block.
    validRpoSchedule stride4LoopBody stride4Cutpoints [0, 1, 1, 2, 3, 4] =
      false ∧
    verifyMirCutpoints stride4LoopBody env stride4RetInv stride4Cutpoints
      [0, 1, 1, 2, 3, 4] = false ∧
    -- Out-of-range block.
    validRpoSchedule stride4LoopBody stride4Cutpoints [0, 99, 2, 3, 4, 5] =
      false ∧
    verifyMirCutpoints stride4LoopBody env stride4RetInv stride4Cutpoints
      [0, 99, 2, 3, 4, 5] = false ∧
    -- Incomplete schedule.
    validRpoSchedule stride4LoopBody stride4Cutpoints [0, 1, 2, 3, 5] = false ∧
    -- Duplicate cutpoint keys.
    validRpoSchedule stride4LoopBody (stride4Cutpoints ++ stride4Cutpoints)
      [0, 1, 2, 3, 4, 5] = false ∧
    -- Out-of-range cutpoint key.
    validRpoSchedule stride4LoopBody
      ((7, [.uint .u32 (AbsVal.uninit 32), .uint .u32 stride4HeaderAbs,
        .bool .uninit]) :: stride4Cutpoints)
      [0, 1, 2, 3, 4, 5] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A loop-header invariant that is not inductive is rejected: `_1 ≤ 32` does
not survive the back-edge, and with only `_1 ≡ 0 (mod 2)` the guard `_1 < 64`
gives `_1 ≤ 62`, so the increment can leave `[0, 64]`. -/
theorem non_inductive_cutpoint_rejected :
    verifyMirCutpoints stride4LoopBody (entryEnv stride4LoopBody.localDecls [])
      (.uint .u32 (AbsVal.topInit 32))
      [(1, [.uint .u32 (AbsVal.uninit 32),
            .uint .u32 (reduceAbsVal 32
              { init := .init, tnum := ⟨0, 60⟩, wi := .iv 0 32,
                sc := .cong 4 0 }),
            .bool .uninit])]
      [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints stride4LoopBody (entryEnv stride4LoopBody.localDecls [])
      (.uint .u32 (AbsVal.topInit 32))
      [(1, [.uint .u32 (AbsVal.uninit 32),
            .uint .u32 (reduceAbsVal 32
              { init := .init, tnum := ⟨0, 126⟩, wi := .iv 0 64,
                sc := .cong 2 0 }),
            .bool .uninit])]
      [0, 1, 2, 3, 4, 5] = false :=
  ⟨rfl, rfl⟩

/-! ## 5. Signed Integers and the `AutoProve` Front-End -/

/-- Two-argument signed body `fn(_1 : i8, _2 : i8) -> i8` with one scratch
local `_3 : i8`. -/
def twoArgI8 (stmts : List StatementKind) : CapturedMir :=
  canaryBody "ai_pcc_tests::two_arg_i8" 2
    [canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8]
    [canaryBlock stmts .return_]

/-- `fn(x: i32) -> i32`: when `x > lo`, evaluate `rhs` into `_0`, otherwise
return `0` (`lo` is a two's-complement bit pattern).
- `_0 : i32`; `_1 : i32` argument; `_2 : bool`. -/
def guardedAboveI32 (lo : Nat) (rhs : Rvalue) : CapturedMir :=
  canaryBody "ai_pcc_tests::guarded_above_i32" 1
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy]
    [ canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .gt (canaryCopy 1) (canaryIConst .i32 lo))]
        (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
      canaryBlock [.assign (canaryPlace 0) rhs] .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
        .return_ ]

/-- `fn f(x: i32) -> i32`: `x.unchecked_add(24)` when `-1000 <= x <= 1000`,
otherwise `0`.
- `_0 : i32`; `_1 : i32` argument; `_2, _3 : bool`. -/
def signedClampAddBody : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_clamp_add" 1
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy, canaryBoolTy]
    [ canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .ge (canaryCopy 1)
            (canaryIConst .i32 (modPow2 32 - 1000)))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 1⟩),
      canaryBlock [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .le (canaryCopy 1) (canaryIConst .i32 1000))]
        (.switchInt (canaryCopy 3) ⟨[(0, 3)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i32 24))]
        .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
        .return_ ]

/-- `signedClampAddBody` is verified by one `rfl`, for every `i32`
argument, with no hand-written entry frame, return invariant, or schedule. -/
theorem signedClampAdd_auto_safe (x : Nat) (hx : x < modPow2 32) :
    SafeFrom signedClampAddBody
      (initMachineState signedClampAddBody [.scalar ⟨x, 4⟩]) ∧
    (∀ v, ReturnsFrom signedClampAddBody
        (initMachineState signedClampAddBody [.scalar ⟨x, 4⟩]) v →
      AutoProve.AutoRetOk signedClampAddBody v) ∧
    MirNoUBTree (mirCallTree signedClampAddBody [.scalar ⟨x, 4⟩]) :=
  AutoProve.autoVerifyAcyclic_sound rfl ⟨⟨x, rfl, hx⟩, rfl⟩

/-- Trusted certificate for `signedClampAddBody` with a non-empty linked
callee table, by one `rfl`. -/
theorem signedClampAdd_verificationResult :
    Trusted.VerificationResult.VerificationResult
      (AutoProve.autoClaim signedClampAddBody [stride4LoopBody]) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl

/-- `ValidEntryArgs` requires exactly `argCount` in-range values of the
declared width: an empty argument list, an out-of-range bit pattern, a wrong
byte width, and a surplus argument are all invalid. -/
theorem validEntryArgs_rejects_bad_args :
    ¬ AutoProve.ValidEntryArgs signedClampAddBody [] ∧
    ¬ AutoProve.ValidEntryArgs signedClampAddBody
        [.scalar ⟨modPow2 32, 4⟩] ∧
    ¬ AutoProve.ValidEntryArgs signedClampAddBody [.scalar ⟨7, 1⟩] ∧
    ¬ AutoProve.ValidEntryArgs signedClampAddBody
        [.scalar ⟨7, 4⟩, .scalar ⟨7, 4⟩] := by
  refine ⟨fun h => h, ?_, ?_, ?_⟩
  · intro h
    match h.1 with
    | ⟨bits, hEq, hLt⟩ =>
      injection hEq with hEq
      injection hEq with hBits _
      subst hBits
      exact Nat.lt_irrefl _ hLt
  · intro h
    match h.1 with
    | ⟨bits, hEq, _⟩ =>
      injection hEq with hEq
      injection hEq with _ hSz
      have hSz' : (1 : Nat) = 4 := hSz
      exact absurd hSz' (by decide)
  · intro h
    have h2 : [Value.scalar ⟨7, 4⟩] = ([] : List Value) := h.2
    nomatch h2

/-- An explicit return postcondition is checked: the top `i32` slot is
accepted and a postcondition the body violates (`_0 = 0`) is rejected. -/
theorem auto_with_ret_checks_postcondition :
    AutoProve.autoVerifyAcyclicWithRet signedClampAddBody
      (.sint .i32 (AbsVal.topInit 32)) = true ∧
    AutoProve.autoVerifyAcyclicWithRet signedClampAddBody
      (.sint .i32 (AbsVal.const 32 0)) = false :=
  ⟨rfl, rfl⟩

/-- Signed overflow, division, and negation hazards on `i32` are rejected;
each guarded or in-range twin is accepted. -/
theorem signed_i32_hazards_rejected :
    -- `x / -1` computes `i32::MIN / -1` at `x = i32::MIN`.
    AutoProve.autoVerifyAcyclic
      (oneBlockI32Body [.assign (canaryPlace 0)
        (.binaryOp .div (canaryCopy 1)
          (canaryIConst .i32 (modPow2 32 - 1)))] .return_) = false ∧
    -- `x % -1` likewise.
    AutoProve.autoVerifyAcyclic
      (oneBlockI32Body [.assign (canaryPlace 0)
        (.binaryOp .rem (canaryCopy 1)
          (canaryIConst .i32 (modPow2 32 - 1)))] .return_) = false ∧
    -- Guarded by `x > i32::MIN`, `x / -1` is defined.
    AutoProve.autoVerifyAcyclic
      (guardedAboveI32 (modPow2 31)
        (.binaryOp .div (canaryCopy 1)
          (canaryIConst .i32 (modPow2 32 - 1)))) = true ∧
    -- `0i32.unchecked_sub(x)` overflows at `x = i32::MIN`.
    AutoProve.autoVerifyAcyclic
      (oneBlockI32Body [.assign (canaryPlace 0)
        (.binaryOp .subUnchecked (canaryIConst .i32 0) (canaryCopy 1))]
        .return_) = false ∧
    -- Guarded by `x > i32::MIN`, `0 - x` is in range.
    AutoProve.autoVerifyAcyclic
      (guardedAboveI32 (modPow2 31)
        (.binaryOp .subUnchecked (canaryIConst .i32 0) (canaryCopy 1))) =
      true ∧
    -- The guard `x > i32::MIN + 1` still admits `x.unchecked_sub(2)`
    -- overflowing at `x = i32::MIN + 2`.
    AutoProve.autoVerifyAcyclic
      (guardedAboveI32 (modPow2 31 + 1)
        (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i32 3))) =
      false ∧
    AutoProve.autoVerifyAcyclic
      (guardedAboveI32 (modPow2 31 + 1)
        (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i32 2))) =
      true ∧
    -- Exact operands: `0i8.unchecked_sub(i8::MIN)` overflows.
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0)
        (.binaryOp .subUnchecked (canaryIConst .i8 0) (canaryIConst .i8 128))]
        .return_) = false ∧
    -- Exact operands: `i8::MIN / -1` and `i8::MIN % -1`.
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0)
        (.binaryOp .div (canaryIConst .i8 128) (canaryIConst .i8 255))]
        .return_) = false ∧
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0)
        (.binaryOp .rem (canaryIConst .i8 128) (canaryIConst .i8 255))]
        .return_) = false ∧
    -- `-127i8 / -1` is defined.
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0)
        (.binaryOp .div (canaryIConst .i8 129) (canaryIConst .i8 255))]
        .return_) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A narrowing `i32 -> i8` cast keeps only the low byte, so the range of the
source says nothing about the sign of the result; negative and out-of-range
signed shift amounts are rejected; `UnOp.neg` is rejected on unsigned
operands. -/
theorem narrowing_shift_and_neg_hazards_rejected :
    -- `(x as i8).unchecked_add(1)` overflows whenever the low byte is `127`.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::narrow_add" 1
        [canaryIntTy .i8, canaryIntTy .i32, canaryIntTy .i8]
        [canaryBlock [.storageLive 2,
          .assign (canaryPlace 2)
            (.cast .intToInt (canaryCopy 1) (canaryIntTy .i8)),
          .assign (canaryPlace 0)
            (.binaryOp .addUnchecked (canaryCopy 2) (canaryIConst .i8 1))]
          .return_]) = false ∧
    -- Masking the narrowed value to `[0, 63]` makes the sum safe.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::narrow_add" 1
        [canaryIntTy .i8, canaryIntTy .i32, canaryIntTy .i8]
        [canaryBlock [.storageLive 2,
          .assign (canaryPlace 2)
            (.cast .intToInt (canaryCopy 1) (canaryIntTy .i8)),
          .assign (canaryPlace 2)
            (.binaryOp .bitAnd (canaryCopy 2) (canaryIConst .i8 63)),
          .assign (canaryPlace 0)
            (.binaryOp .addUnchecked (canaryCopy 2) (canaryIConst .i8 1))]
          .return_]) = true ∧
    -- `x` in `[0, 200]` narrows to a possibly negative `i8`.
    AutoProve.autoVerifyAcyclic (narrowThenAddBody 200) = false ∧
    AutoProve.autoVerifyAcyclic (narrowThenAddBody 128) = false ∧
    AutoProve.autoVerifyAcyclic (narrowThenAddBody 127) = true ∧
    -- `x.unchecked_shl(y)` with an arbitrary (possibly negative) `y`.
    AutoProve.autoVerifyAcyclic
      (twoArgI8 [.assign (canaryPlace 0)
        (.binaryOp .shlUnchecked (canaryCopy 1) (canaryCopy 2))]) = false ∧
    AutoProve.autoVerifyAcyclic
      (twoArgI8 [.assign (canaryPlace 0)
        (.binaryOp .shrUnchecked (canaryCopy 1) (canaryCopy 2))]) = false ∧
    -- Masking the amount to `[0, 7]` makes both shifts safe.
    AutoProve.autoVerifyAcyclic
      (twoArgI8 [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .bitAnd (canaryCopy 2) (canaryIConst .i8 7)),
        .assign (canaryPlace 0)
          (.binaryOp .shlUnchecked (canaryCopy 1) (canaryCopy 3)),
        .assign (canaryPlace 0)
          (.binaryOp .shrUnchecked (canaryCopy 0) (canaryCopy 3))]) = true ∧
    -- Constant negative and width-sized amounts.
    AutoProve.autoVerifyAcyclic
      (twoArgI8 [.assign (canaryPlace 0)
        (.binaryOp .shrUnchecked (canaryCopy 1) (canaryIConst .i8 255))]) =
      false ∧
    AutoProve.autoVerifyAcyclic
      (twoArgI8 [.assign (canaryPlace 0)
        (.binaryOp .shlUnchecked (canaryCopy 1) (canaryIConst .i8 8))]) =
      false ∧
    -- `UnOp.neg` on `u8` is rejected, by the auto front-end and by an
    -- explicit certificate; `UnOp.not` on `u8` and `UnOp.neg` on `i8` pass.
    AutoProve.autoVerifyAcyclic
      (oneBlockU8 [.assign (canaryPlace 0) (.unaryOp .neg (canaryCopy 1))]
        .return_) = false ∧
    verifyMirCutpoints
      (oneBlockU8 [.assign (canaryPlace 0) (.unaryOp .neg (canaryCopy 1))]
        .return_) oneBlockU8Entry u8Top [] [0] = false ∧
    AutoProve.autoVerifyAcyclic
      (oneBlockU8 [.assign (canaryPlace 0) (.unaryOp .not (canaryCopy 1))]
        .return_) = true ∧
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0) (.unaryOp .neg (canaryCopy 1))]
        .return_) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn(x: i8) -> i8 { match x { c => on_eq, _ => on_ne } }` as a signed
`switchInt` on `_1` (`c` is a two's-complement bit pattern).
- `_0 : i8`; `_1 : i8` argument. -/
def signedSwitchBody (c : Nat) (onEq onNe : Rvalue) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_switch" 1
    [canaryIntTy .i8, canaryIntTy .i8]
    [ canaryBlock [] (.switchInt (canaryCopy 1) ⟨[(c, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0) onEq] .return_,
      canaryBlock [.assign (canaryPlace 0) onNe] .return_ ]

/-- A signed `switchInt` refines its discriminant on both edges: the matched
edge pins the value (`.seqConst`) and the `otherwise` edge excludes it
(`.sneConst`). -/
theorem signed_switch_refines_both_edges :
    -- `match x { 127 => 0, _ => x + 1 }`: `x != i8::MAX` on `otherwise`.
    AutoProve.autoVerifyAcyclic
      (signedSwitchBody 127 (.use (canaryIConst .i8 0))
        (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 1))) =
      true ∧
    -- `match x { 126 => 0, _ => x + 1 }` still overflows at `i8::MAX`.
    AutoProve.autoVerifyAcyclic
      (signedSwitchBody 126 (.use (canaryIConst .i8 0))
        (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 1))) =
      false ∧
    -- `match x { -128 => 0, _ => x - 1 }`: `x != i8::MIN` on `otherwise`.
    AutoProve.autoVerifyAcyclic
      (signedSwitchBody 128 (.use (canaryIConst .i8 0))
        (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i8 1))) =
      true ∧
    -- `match x { -128 => x - 1, _ => 0 }`: the matched edge is exact, so the
    -- overflow is certain.
    AutoProve.autoVerifyAcyclic
      (signedSwitchBody 128
        (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i8 1))
        (.use (canaryIConst .i8 0))) = false ∧
    -- `match x { -1 => x + 1, _ => 0 }`: `-1 + 1` is exact.
    AutoProve.autoVerifyAcyclic
      (signedSwitchBody 255
        (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 1))
        (.use (canaryIConst .i8 0))) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Diamond whose join block is numbered before both branches
(`0 -> 3 -> 1`, `0 -> 2 -> 1`): `fn(x: u8) -> u8` returning `x & 15` or
`x & 7`.
- `_0 : u8`; `_1 : u8` argument; `_2 : bool`. -/
def lateJoinDiamondBody : CapturedMir :=
  canaryBody "ai_pcc_tests::late_join_diamond" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryBoolTy]
    [ canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .lt (canaryCopy 1) (canaryUConst .u8 100))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      canaryBlock [.storageDead 2] .return_,
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .bitAnd (canaryCopy 1) (canaryUConst .u8 15))] (.goto 1),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .bitAnd (canaryCopy 1) (canaryUConst .u8 7))] (.goto 1) ]

/-- Two blocks jumping to each other (`0 -> 1 -> 0`). -/
def pingPongBody : CapturedMir :=
  canaryBody "ai_pcc_tests::ping_pong" 0 [canaryUintTy .u8]
    [canaryBlock [] (.goto 1), canaryBlock [] (.goto 0)]

/-- `AutoProve.defaultRpoOrder` schedules a CFG whose block numbering is not
a topological order; the index order is rejected. On cyclic CFGs the
fuel-bounded search terminates, `AutoProve.autoVerifyAcyclic` rejects the
body, and `AutoProve.autoVerifyCutpoints` accepts it with a cutpoint on the
loop header. -/
theorem auto_schedules_and_cycles :
    AutoProve.defaultRpoOrder lateJoinDiamondBody = [0, 3, 2, 1] ∧
    AutoProve.autoVerifyAcyclic lateJoinDiamondBody = true ∧
    AutoProve.autoVerifyAcyclic lateJoinDiamondBody [0, 1, 2, 3] = false ∧
    AutoProve.autoVerifyAcyclic lateJoinDiamondBody [0, 2, 3, 1] = true ∧
    AutoProve.autoVerifyAcyclicWithRet lateJoinDiamondBody
      (.uint .u8 (ivAbs 8 0 15)) = true ∧
    AutoProve.autoVerifyAcyclicWithRet lateJoinDiamondBody
      (.uint .u8 (ivAbs 8 0 7)) = false ∧
    -- Cyclic CFGs.
    AutoProve.defaultRpoOrder stride4LoopBody = [0, 1, 3, 4, 5, 2] ∧
    AutoProve.autoVerifyAcyclic stride4LoopBody = false ∧
    AutoProve.autoVerifyCutpoints stride4LoopBody stride4RetInv
      stride4Cutpoints = true ∧
    AutoProve.autoVerifyCutpoints stride4LoopBody stride4RetInv [] = false ∧
    AutoProve.defaultRpoOrder pingPongBody = [1, 0] ∧
    AutoProve.autoVerifyAcyclic pingPongBody = false ∧
    AutoProve.autoVerifyCutpoints pingPongBody .dead
      [(0, entryEnv pingPongBody.localDecls [])] = true ∧
    -- An empty body has no schedule and is rejected.
    AutoProve.defaultRpoOrder
      (canaryBody "ai_pcc_tests::no_blocks" 0 [canaryUintTy .u8] []) = [] ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::no_blocks" 0 [canaryUintTy .u8] []) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Audited claim for the looping `stride4LoopBody` through
`AutoProve.autoVerifyCutpoints`: called with no arguments, it returns
exactly `64`. -/
def stride4AutoClaim : Trusted.VerificationResult.Claim where
  body := stride4LoopBody
  pre args := args = []
  post _ ret := ret = .scalar ⟨64, 4⟩

/-- `VerificationResult stride4AutoClaim` from one `rfl` run of
`AutoProve.autoVerifyCutpoints` on the computed default schedule. -/
theorem stride4_auto_verificationResult :
    Trusted.VerificationResult.VerificationResult stride4AutoClaim :=
  AutoProve.bodyVerified_of_autoVerifyCutpoints (retInv := stride4RetInv)
    (cutpoints := stride4Cutpoints)
    (rpoOrder := AutoProve.defaultRpoOrder stride4LoopBody stride4Cutpoints)
    rfl
    (fun args hPre => by
      have hArgs : args = [] := hPre
      subst hArgs
      exact rfl)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        exact uint_valDenote_exact rfl hDen)

/-- Stateful audited claim for `signedClampAddBody` via `AutoProve`:
any root-entry memory and valid `i32` argument preserves `MirMemFrame` and
returns an in-range `i32` (`AutoRetOk`). -/
def signedClampAddStatefulClaim : Trusted.VerificationResult.StatefulClaim where
  body := signedClampAddBody
  pre args mem :=
    mem.callStack = [] ∧ mem.activeCallee = none ∧
    mem.activeProtectors = [] ∧ AutoProve.ValidEntryArgs signedClampAddBody args
  post _ mem retVal mem' :=
    MirMemFrame mem' mem ∧ AutoProve.AutoRetOk signedClampAddBody retVal

/-- `StatefulVerificationResult signedClampAddStatefulClaim` by one `rfl`. -/
theorem signedClampAdd_statefulVerificationResult :
    Trusted.VerificationResult.StatefulVerificationResult
      signedClampAddStatefulClaim :=
  AutoProve.statefulVerificationResult_of_autoVerifyAcyclic rfl
    (fun _ _ h => h)
    (fun _ _ _ _ _ hFrame hRet => ⟨hFrame, hRet⟩)

/-- Trace audited claim for `signedClampAddBody` via `AutoProve`: every
reachable return is `.normal (retVal, mem')` along an observation-only trace
preserving `MirMemFrame`. -/
def signedClampAddTraceClaim : Trusted.VerificationResult.TraceClaim where
  body := signedClampAddBody
  pre args mem :=
    mem.callStack = [] ∧ mem.activeCallee = none ∧
    mem.activeProtectors = [] ∧ AutoProve.ValidEntryArgs signedClampAddBody args
  post _ mem tr out :=
    TraceObsOnly tr ∧
    ∃ retVal mem', out = .normal (retVal, mem') ∧
      MirMemFrame mem' mem ∧ AutoProve.AutoRetOk signedClampAddBody retVal

/-- `TraceVerificationResult signedClampAddTraceClaim` by one `rfl`. -/
theorem signedClampAdd_traceVerificationResult :
    Trusted.VerificationResult.TraceVerificationResult
      signedClampAddTraceClaim :=
  AutoProve.traceVerificationResult_of_autoVerifyAcyclic rfl
    (fun _ _ h => h)
    (fun _ _ _ retVal mem' _ hTr hFrame hRet =>
      ⟨hTr, retVal, mem', rfl, hFrame, hRet⟩)

/-- `VerificationResult` for `lateJoinDiamondBody` using an explicit
non-default topological schedule `[0, 2, 3, 1]` via
`AutoProve.bodyVerified_of_autoVerifyAcyclicOrder`. -/
theorem lateJoinDiamond_explicitOrder_verificationResult :
    Trusted.VerificationResult.VerificationResult
      (AutoProve.autoClaim lateJoinDiamondBody) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclicOrder (rpoOrder := [0, 2, 3, 1]) rfl

/-- `fn(b: bool) -> bool { !b }` exercising `AutoProve` on `bool` arguments
and return values. -/
def boolNotBody : CapturedMir :=
  canaryBody "ai_pcc_tests::bool_not" 1 [canaryBoolTy, canaryBoolTy]
    [canaryBlock [.assign (canaryPlace 0) (.unaryOp .not (canaryCopy 1))]
      .return_]

/-- `boolNotBody` is verified for every `bool` argument (witnessing non-vacuity
of `ValidEntryArgs` on `bool`). -/
theorem boolNot_auto_safe (b : Bool) :
    SafeFrom boolNotBody (initMachineState boolNotBody [.scalar (boolToScalar b)]) ∧
    (∀ v, ReturnsFrom boolNotBody
        (initMachineState boolNotBody [.scalar (boolToScalar b)]) v →
      AutoProve.AutoRetOk boolNotBody v) ∧
    MirNoUBTree (mirCallTree boolNotBody [.scalar (boolToScalar b)]) :=
  AutoProve.autoVerifyAcyclic_sound rfl ⟨⟨b, rfl⟩, rfl⟩

/-- Trusted `VerificationResult` for `boolNotBody` by one `rfl`. -/
theorem boolNot_verificationResult :
    Trusted.VerificationResult.VerificationResult (AutoProve.autoClaim boolNotBody) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl

/-- `fn(u: ()) -> () { u }` exercising `AutoProve` on unit `()` arguments and
return values. -/
def unitIdBody : CapturedMir :=
  let unitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
  canaryBody "ai_pcc_tests::unit_id" 1 [unitTy, unitTy]
    [canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_]

/-- `unitIdBody` is verified for both `Value.unit` and `Value.aggregate 0 []`
(witnessing non-vacuity of `ValidEntryArgs` on `()`). -/
theorem unitId_auto_safe :
    (SafeFrom unitIdBody (initMachineState unitIdBody [.unit]) ∧
      (∀ v, ReturnsFrom unitIdBody (initMachineState unitIdBody [.unit]) v →
        AutoProve.AutoRetOk unitIdBody v) ∧
      MirNoUBTree (mirCallTree unitIdBody [.unit])) ∧
    (SafeFrom unitIdBody (initMachineState unitIdBody [.aggregate 0 []]) ∧
      (∀ v, ReturnsFrom unitIdBody
          (initMachineState unitIdBody [.aggregate 0 []]) v →
        AutoProve.AutoRetOk unitIdBody v) ∧
      MirNoUBTree (mirCallTree unitIdBody [.aggregate 0 []])) :=
  ⟨AutoProve.autoVerifyAcyclic_sound rfl ⟨Or.inl rfl, rfl⟩,
   AutoProve.autoVerifyAcyclic_sound rfl ⟨Or.inr rfl, rfl⟩⟩

/-- Trusted `VerificationResult` for `unitIdBody` by one `rfl`. -/
theorem unitId_verificationResult :
    Trusted.VerificationResult.VerificationResult (AutoProve.autoClaim unitIdBody) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl

/-- `fn(x: i8) -> i8`: if `-100 <= x && hi >= x` (using constant-on-left
comparison `hi >= x`), compute `(res, ov) = x.overflowing_add(10)`,
`assert(!ov)`, and return `res`. -/
def straddlingCheckedAddConstLBody (hi : Nat) : CapturedMir :=
  let pairTy : Ty := { kind := .tuple [.int .i8, .bool], layoutIdx := 0 }
  canaryBody "ai_pcc_tests::straddling_checked_add_const_l" 1
    [canaryIntTy .i8, canaryIntTy .i8, canaryBoolTy, canaryBoolTy, pairTy, canaryBoolTy]
    [ canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .le (canaryIConst .i8 156) (canaryCopy 1))]
        (.switchInt (canaryCopy 2) ⟨[(0, 4)], 1⟩),
      canaryBlock [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .ge (canaryIConst .i8 hi) (canaryCopy 1))]
        (.switchInt (canaryCopy 3) ⟨[(0, 4)], 2⟩),
      canaryBlock [.storageLive 4, .storageLive 5,
        .assign (canaryPlace 4)
          (.binaryOp .addWithOverflow (canaryCopy 1) (canaryIConst .i8 10)),
        .assign (canaryPlace 5)
          (.use (.copy { local_ := 4, projection := [.field 1 canaryBoolTy] }))]
        (.assert (canaryCopy 5) false 3 .continue_),
      canaryBlock [
        .assign (canaryPlace 0)
          (.use (.copy { local_ := 4, projection := [.field 0 (canaryIntTy .i8)] }))]
        .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- `fn(x: i8, y: i8) -> i8`: when `loX <= x` and `loY <= y <= hiY`, compute
`x / y`. -/
def guardedSignedDivRangeBody (loX loY hiY : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::guarded_signed_div_range" 2
    [canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8,
     canaryBoolTy, canaryBoolTy, canaryBoolTy]
    [ canaryBlock [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .ge (canaryCopy 1) (canaryIConst .i8 loX))]
        (.switchInt (canaryCopy 3) ⟨[(0, 4)], 1⟩),
      canaryBlock [.storageLive 4,
        .assign (canaryPlace 4)
          (.binaryOp .ge (canaryCopy 2) (canaryIConst .i8 loY))]
        (.switchInt (canaryCopy 4) ⟨[(0, 4)], 2⟩),
      canaryBlock [.storageLive 5,
        .assign (canaryPlace 5)
          (.binaryOp .le (canaryCopy 2) (canaryIConst .i8 hiY))]
        (.switchInt (canaryCopy 5) ⟨[(0, 4)], 3⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .div (canaryCopy 1) (canaryCopy 2))] .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- Adversarial edge-case regression suite: sign-straddling checked arithmetic
with constant-on-left guards, extreme `INT_MIN`/`INT_MAX` comparison trap
pruning, signed division by negative intervals, `i8::MIN * -1`, mixed
`u128 << i8` negative shifts, missing lower-bound shift guards, non-exact
negative widening, `(-i8::MIN) - 1`, `!0i8 + i8::MIN`, unsigned `.neg`, and
disconnected cycles. -/
theorem signed_adversarial_edge_cases :
    -- Sign-straddling `[-100, 117] + 10` passes `addWithOverflow` + `assert(!.1)`;
    -- `[-100, 118] + 10` can overflow `128` and is rejected.
    AutoProve.autoVerifyAcyclic (straddlingCheckedAddConstLBody 117) = true ∧
    AutoProve.autoVerifyAcyclic (straddlingCheckedAddConstLBody 118) = false ∧
    -- Extreme comparisons `x < i8::MIN` and `x > i8::MAX` are statically false,
    -- pruning unreachable trap blocks.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::extreme_lt_min" 1
        [canaryIntTy .i8, canaryIntTy .i8, canaryBoolTy]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .lt (canaryCopy 1) (canaryIConst .i8 128))]
            (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
          canaryBlock [] .unreachable,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
            .return_ ]) = true ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::extreme_gt_max" 1
        [canaryIntTy .i8, canaryIntTy .i8, canaryBoolTy]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .gt (canaryCopy 1) (canaryIConst .i8 127))]
            (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
          canaryBlock [] .unreachable,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
            .return_ ]) = true ∧
    -- Signed division by negative intervals:
    -- `[-128, 127] / [-2, -1]` admits `MIN / -1` -> false;
    -- `[-127, 127] / [-2, -1]` excludes `MIN` -> true;
    -- `[-128, 127] / [-3, -2]` excludes `-1` and `0` -> true;
    -- `[-128, 127] / [-1, 1]` admits `0` -> false.
    AutoProve.autoVerifyAcyclic (guardedSignedDivRangeBody 128 254 255) = false ∧
    AutoProve.autoVerifyAcyclic (guardedSignedDivRangeBody 129 254 255) = true ∧
    AutoProve.autoVerifyAcyclic (guardedSignedDivRangeBody 128 253 254) = true ∧
    AutoProve.autoVerifyAcyclic (guardedSignedDivRangeBody 128 255 1) = false ∧
    -- `i8::MIN.unchecked_mul(-1)` overflows.
    AutoProve.autoVerifyAcyclic
      (oneBlockI8Body [.assign (canaryPlace 0)
        (.binaryOp .mulUnchecked (canaryIConst .i8 128) (canaryIConst .i8 255))]
        .return_) = false ∧
    -- Mixed `u128.unchecked_shl(-128i8)` and `u128.unchecked_shl(-1i8)` fail closed.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::u128_shl_i8min" 1
        [canaryUintTy .u128, canaryUintTy .u128]
        [canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .shlUnchecked (canaryCopy 1) (canaryIConst .i8 128))]
          .return_]) = false ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::u128_shl_i8neg1" 1
        [canaryUintTy .u128, canaryUintTy .u128]
        [canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .shlUnchecked (canaryCopy 1) (canaryIConst .i8 255))]
          .return_]) = false ∧
    -- Signed shift guard `y < 8` without `y >= 0` allows negative `y` -> rejected.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::shl_lt8_only" 2
        [canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8, canaryBoolTy]
        [ canaryBlock [.storageLive 3,
            .assign (canaryPlace 3)
              (.binaryOp .lt (canaryCopy 2) (canaryIConst .i8 8))]
            (.switchInt (canaryCopy 3) ⟨[(0, 2)], 1⟩),
          canaryBlock [.assign (canaryPlace 0)
            (.binaryOp .shlUnchecked (canaryCopy 1) (canaryCopy 2))] .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
            .return_ ]) = false ∧
    -- Exact biased signed widening (`sintCastAbs`): widening negative `x : i8`
    -- to `i32` preserves `[-128, -1]`, so `(x as i32).unchecked_add(1)` verifies,
    -- while `(x as i32).unchecked_add(i32::MIN)` genuinely overflows and fails closed.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_widen_add" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryBoolTy, canaryIntTy .i32]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .lt (canaryCopy 1) (canaryIConst .i8 0))]
            (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
          canaryBlock [.storageLive 3,
            .assign (canaryPlace 3)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 0)
              (.binaryOp .addUnchecked (canaryCopy 3) (canaryIConst .i32 1))]
            .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
            .return_ ]) = true ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_widen_add_min" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryBoolTy, canaryIntTy .i32]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .lt (canaryCopy 1) (canaryIConst .i8 0))]
            (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
          canaryBlock [.storageLive 3,
            .assign (canaryPlace 3)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 0)
              (.binaryOp .addUnchecked (canaryCopy 3)
                (canaryIConst .i32 (modPow2 31)))]
            .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
            .return_ ]) = false ∧
    -- `(-i8::MIN).unchecked_sub(1)` wraps `-i8::MIN` to `i8::MIN` and overflows.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_min_sub1" 0
        [canaryIntTy .i8, canaryIntTy .i8]
        [canaryBlock [.storageLive 1,
          .assign (canaryPlace 1) (.unaryOp .neg (canaryIConst .i8 128)),
          .assign (canaryPlace 0)
            (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i8 1))]
          .return_]) = false ∧
    -- `(!0i8).unchecked_add(i8::MIN)` overflows (`-1 + -128`), whereas
    -- `(!(-1i8)).unchecked_add(i8::MAX)` is `0 + 127` and succeeds.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::not0_add_min" 0
        [canaryIntTy .i8, canaryIntTy .i8]
        [canaryBlock [.storageLive 1,
          .assign (canaryPlace 1) (.unaryOp .not (canaryIConst .i8 0)),
          .assign (canaryPlace 0)
            (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 128))]
          .return_]) = false ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::not_neg1_add_max" 0
        [canaryIntTy .i8, canaryIntTy .i8]
        [canaryBlock [.storageLive 1,
          .assign (canaryPlace 1) (.unaryOp .not (canaryIConst .i8 255)),
          .assign (canaryPlace 0)
            (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 127))]
          .return_]) = true ∧
    -- Unsigned `.neg` on `u32` and `usize` fails closed.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_u32" 1 [canaryUintTy .u32, canaryUintTy .u32]
        [canaryBlock [.assign (canaryPlace 0) (.unaryOp .neg (canaryCopy 1))]
          .return_]) = false ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_usize" 1 [canaryUintTy .usize, canaryUintTy .usize]
        [canaryBlock [.assign (canaryPlace 0) (.unaryOp .neg (canaryCopy 1))]
          .return_]) = false ∧
    -- A body containing a disconnected cycle (`bb1 <-> bb2`) is rejected by
    -- `autoVerifyAcyclic` (`validRpoSchedule` requires a full DAG order).
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::disconnected_cycle" 0 [canaryUintTy .u8]
        [ canaryBlock [.assign (canaryPlace 0) (.use (canaryUConst .u8 0))] .return_,
          canaryBlock [] (.goto 2),
          canaryBlock [] (.goto 1) ]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩

/--
info: 'Anneal.AiPccMirTests.signedClampAdd_auto_safe' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedClampAdd_auto_safe

/--
info: 'Anneal.AiPccMirTests.signedClampAdd_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedClampAdd_verificationResult

/--
info: 'Anneal.AiPccMirTests.signedClampAdd_statefulVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedClampAdd_statefulVerificationResult

/--
info: 'Anneal.AiPccMirTests.signedClampAdd_traceVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedClampAdd_traceVerificationResult

/--
info: 'Anneal.AiPccMirTests.lateJoinDiamond_explicitOrder_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lateJoinDiamond_explicitOrder_verificationResult

/--
info: 'Anneal.AiPccMirTests.boolNot_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms boolNot_verificationResult

/--
info: 'Anneal.AiPccMirTests.unitId_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unitId_verificationResult

/--
info: 'Anneal.AiPccMirTests.stride4_auto_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stride4_auto_verificationResult

/-! ## 6. `AutoProve` Argument Validity, Signed Products, and Signed Loops -/

/-- `ValidEntryArgs` is tight on `bool` and `()`: a non-canonical `bool`
scalar, a `bool` of the wrong byte width, a unit passed for a `bool`, a
missing argument, a scalar passed for `()`, and a surplus argument are all
invalid. -/
theorem validEntryArgs_rejects_bad_bool_and_unit :
    ¬ AutoProve.ValidEntryArgs boolNotBody [.scalar ⟨2, 1⟩] ∧
    ¬ AutoProve.ValidEntryArgs boolNotBody [.scalar ⟨1, 4⟩] ∧
    ¬ AutoProve.ValidEntryArgs boolNotBody [.unit] ∧
    ¬ AutoProve.ValidEntryArgs boolNotBody [] ∧
    ¬ AutoProve.ValidEntryArgs unitIdBody [.scalar ⟨0, 1⟩] ∧
    ¬ AutoProve.ValidEntryArgs unitIdBody [.unit, .unit] := by
  refine ⟨?_, ?_, ?_, fun h => h, ?_, ?_⟩
  · intro h
    match h.1 with
    | ⟨b, hEq⟩ =>
      cases b with
      | false =>
        have hEq' : Value.scalar ⟨2, 1⟩ = Value.scalar ⟨0, 1⟩ := hEq
        injection hEq' with h1
        injection h1 with h2 _
        exact absurd h2 (by decide)
      | true =>
        have hEq' : Value.scalar ⟨2, 1⟩ = Value.scalar ⟨1, 1⟩ := hEq
        injection hEq' with h1
        injection h1 with h2 _
        exact absurd h2 (by decide)
  · intro h
    match h.1 with
    | ⟨b, hEq⟩ =>
      cases b with
      | false =>
        have hEq' : Value.scalar ⟨1, 4⟩ = Value.scalar ⟨0, 1⟩ := hEq
        injection hEq' with h1
        injection h1 with h2 _
        exact absurd h2 (by decide)
      | true =>
        have hEq' : Value.scalar ⟨1, 4⟩ = Value.scalar ⟨1, 1⟩ := hEq
        injection hEq' with h1
        injection h1 with _ h3
        exact absurd h3 (by decide)
  · intro h
    match h.1 with
    | ⟨_, hEq⟩ => nomatch hEq
  · intro h
    cases h.1 with
    | inl h1 => nomatch h1
    | inr h1 => nomatch h1
  · intro h
    have h2 : [Value.unit] = ([] : List Value) := h.2
    nomatch h2

/-- `fn() -> i8 { c1.unchecked_mul(c2) }` on `i8` constants given as
two's-complement bit patterns. -/
def signedMulConstBody (c1 c2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_mul_const" 0 [canaryIntTy .i8]
    [canaryBlock [.assign (canaryPlace 0)
      (.binaryOp .mulUnchecked (canaryIConst .i8 c1) (canaryIConst .i8 c2))]
      .return_]

/-- `fn() -> i8 { c1 * c2 }` in debug mode: the product goes through
`MulWithOverflow` into `_1 : (i8, bool)`, and `assert(!move (_1.1))` guards
the read of `_1.0`.
- `_0 : i8`; `_1 : (i8, bool)`. -/
def signedCheckedMulConstBody (c1 c2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_checked_mul_const" 0
    [canaryIntTy .i8, intPairTy .i8]
    [ canaryBlock [.storageLive 1,
        .assign (canaryPlace 1)
          (.binaryOp .mulWithOverflow (canaryIConst .i8 c1)
            (canaryIConst .i8 c2))]
        (.assert (.move (fieldPlace 1 1 canaryBoolTy)) false 1 .continue_),
      canaryBlock [.assign (canaryPlace 0)
          (.use (.move (fieldPlace 1 0 (canaryIntTy .i8))))] .return_ ]

/-- Products of exact signed constants are decided by the trusted overflow
test, for operands of either sign. -/
theorem signed_constant_products :
    -- `-2 * 3 = -6` and `-1 * -1 = 1`.
    AutoProve.autoVerifyAcyclic (signedMulConstBody 254 3) = true ∧
    AutoProve.autoVerifyAcyclic (signedMulConstBody 255 255) = true ∧
    -- `-64 * 2` is exactly `i8::MIN`; `-64 * -2 = 128` overflows.
    AutoProve.autoVerifyAcyclic (signedMulConstBody 192 2) = true ∧
    AutoProve.autoVerifyAcyclic (signedMulConstBody 192 254) = false ∧
    -- `10 * 12 = 120` fits; `11 * 12 = 132` overflows.
    AutoProve.autoVerifyAcyclic (signedMulConstBody 10 12) = true ∧
    AutoProve.autoVerifyAcyclic (signedMulConstBody 11 12) = false ∧
    -- `i8::MIN * -1` overflows in either operand order; `i8::MIN * 1` fits.
    AutoProve.autoVerifyAcyclic (signedMulConstBody 128 255) = false ∧
    AutoProve.autoVerifyAcyclic (signedMulConstBody 255 128) = false ∧
    AutoProve.autoVerifyAcyclic (signedMulConstBody 128 1) = true ∧
    -- Checked form: the overflow flag is certified clear exactly when the
    -- product fits.
    AutoProve.autoVerifyAcyclic (signedCheckedMulConstBody 254 3) = true ∧
    AutoProve.autoVerifyAcyclic (signedCheckedMulConstBody 192 2) = true ∧
    AutoProve.autoVerifyAcyclic (signedCheckedMulConstBody 192 254) = false ∧
    AutoProve.autoVerifyAcyclic (signedCheckedMulConstBody 128 255) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn() -> i32 { let mut i = start; while i op bound { i += 1 }; i }` with
an unchecked increment (`op` is `Lt` or `Le`; `start` and `bound` are
two's-complement bit patterns).
- `_0 : i32`; `_1 : i32` counter; `_2 : bool` guard. -/
def signedCountLoopBody (op : BinOp) (start bound : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_count_loop" 0
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy]
    [ -- bb0: entry
      canaryBlock [.storageLive 1,
        .assign (canaryPlace 1) (.use (canaryIConst .i32 start)),
        .storageLive 2] (.goto 1),
      -- bb1: loop header (the only cutpoint)
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp op (canaryCopy 1) (canaryIConst .i32 bound))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      -- bb2: loop body
      canaryBlock [.assign (canaryPlace 1)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i32 1))]
        (.goto 1),
      -- bb3: return `_1`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 2, .storageDead 1] .return_ ]

/-- Loop-header cutpoint of `signedCountLoopBody` with counter value `a`. -/
def signedCountCutpoints (a : AbsVal) : List (Nat × MirAbsEnv) :=
  [(1, [.sint .i32 (AbsVal.uninit 32), .sint .i32 a, .bool .uninit])]

/-- `-32` as an `i32` bit pattern. -/
def i32Neg32 : Nat := modPow2 32 - 32

/-- The loop `i = -32; while i < 32 { i += 1 }`. -/
def signedCount64Body : CapturedMir := signedCountLoopBody .lt i32Neg32 32

/-- Header invariant of `signedCount64Body`: `-32 <= i <= 32`, a wrapped
interval of bit patterns. -/
def signedCount64Cutpoints : List (Nat × MirAbsEnv) :=
  signedCountCutpoints (ivAbs 32 i32Neg32 32)

/-- Exact return postcondition `_0 = 32`. -/
def signedCount64RetInv : MirAbsSlot := .sint .i32 (AbsVal.const 32 32)

/-- Signed loops through `AutoProve.autoVerifyCutpoints` on the computed
default schedule: a sign-straddling counter with an exact exit value, its
near-miss certificates, and counting up to `i32::MAX`. -/
theorem signed_loops_via_cutpoints :
    AutoProve.autoVerifyCutpoints signedCount64Body signedCount64RetInv
      signedCount64Cutpoints = true ∧
    -- A wrong return value, a header that is not inductive, a header that
    -- excludes the entry value, and a missing cutpoint are rejected.
    AutoProve.autoVerifyCutpoints signedCount64Body
      (.sint .i32 (AbsVal.const 32 31)) signedCount64Cutpoints = false ∧
    AutoProve.autoVerifyCutpoints signedCount64Body signedCount64RetInv
      (signedCountCutpoints (ivAbs 32 i32Neg32 31)) = false ∧
    AutoProve.autoVerifyCutpoints signedCount64Body signedCount64RetInv
      (signedCountCutpoints (ivAbs 32 (i32Neg32 + 1) 32)) = false ∧
    AutoProve.autoVerifyCutpoints signedCount64Body signedCount64RetInv [] =
      false ∧
    AutoProve.autoVerifyAcyclic signedCount64Body = false ∧
    -- `i = i32::MIN; while i < i32::MAX { i += 1 }` never overflows and
    -- exits at exactly `i32::MAX`, under the trivial header invariant.
    AutoProve.autoVerifyCutpoints
      (signedCountLoopBody .lt (modPow2 31) (modPow2 31 - 1))
      (.sint .i32 (AbsVal.const 32 (modPow2 31 - 1)))
      (signedCountCutpoints (AbsVal.topInit 32)) = true ∧
    -- With `<=` the increment overflows at `i32::MAX`.
    AutoProve.autoVerifyCutpoints
      (signedCountLoopBody .le (modPow2 31) (modPow2 31 - 1))
      (.sint .i32 (AbsVal.topInit 32))
      (signedCountCutpoints (AbsVal.topInit 32)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A signed return slot holding an exact constant pins the returned value. -/
theorem sint_valDenote_exact {ty : Ty} {i : IntTy} {a : AbsVal} {v : Value}
    {c : Nat} (hEx : a.exactVal? (uintWidth (intTwin i)) = some c)
    (h : (MirAbsSlot.sint i a).valDenote ty v) :
    v = .scalar ⟨c, uintBytes (intTwin i)⟩ := by
  have h2 := h.2
  cases v
  case scalar sc =>
    cases sc with
    | mk bits sz =>
      have hBits := (absVal_exactVal?_sound hEx h2.2).1
      injection hBits with hBits
      have hSz : sz = uintBytes (intTwin i) := h2.1
      subst hBits
      subst hSz
      rfl
  all_goals exact False.elim h2

/-- Audited claim for `signedCount64Body`: called with no arguments, it
returns exactly `32`. -/
def signedCount64Claim : Trusted.VerificationResult.Claim where
  body := signedCount64Body
  pre args := args = []
  post _ ret := ret = .scalar ⟨32, 4⟩

/-- `VerificationResult signedCount64Claim` from one `rfl` run of
`AutoProve.autoVerifyCutpoints`. -/
theorem signedCount64_verificationResult :
    Trusted.VerificationResult.VerificationResult signedCount64Claim :=
  AutoProve.bodyVerified_of_autoVerifyCutpoints
    (retInv := signedCount64RetInv) (cutpoints := signedCount64Cutpoints)
    (rpoOrder :=
      AutoProve.defaultRpoOrder signedCount64Body signedCount64Cutpoints)
    rfl
    (fun args hPre => by
      have hArgs : args = [] := hPre
      subst hArgs
      exact rfl)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        exact sint_valDenote_exact rfl hDen)

/-- Stateful audited claim for `signedCount64Body`: from a root-entry memory
it preserves `MirMemFrame` and returns exactly `32`. -/
def signedCount64StatefulClaim :
    Trusted.VerificationResult.StatefulClaim where
  body := signedCount64Body
  pre args mem :=
    mem.callStack = [] ∧ mem.activeCallee = none ∧
    mem.activeProtectors = [] ∧ args = []
  post _ mem ret mem' := MirMemFrame mem' mem ∧ ret = .scalar ⟨32, 4⟩

/-- `StatefulVerificationResult signedCount64StatefulClaim` through
`AutoProve.statefulVerificationResult_of_autoVerifyCutpoints`. -/
theorem signedCount64_statefulVerificationResult :
    Trusted.VerificationResult.StatefulVerificationResult
      signedCount64StatefulClaim :=
  AutoProve.statefulVerificationResult_of_autoVerifyCutpoints
    (retInv := signedCount64RetInv) (cutpoints := signedCount64Cutpoints)
    (rpoOrder :=
      AutoProve.defaultRpoOrder signedCount64Body signedCount64Cutpoints)
    rfl
    (fun args mem hPre => by
      have hArgs : args = [] := hPre.2.2.2
      subst hArgs
      exact ⟨hPre.1, hPre.2.1, hPre.2.2.1, rfl⟩)
    (fun _ _ _ _ _ hFrame hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        exact ⟨hFrame, sint_valDenote_exact rfl hDen⟩)

/-- Trace audited claim for `signedCount64Body`: every reachable outcome is a
normal return of exactly `32` along an observation-only trace. -/
def signedCount64TraceClaim : Trusted.VerificationResult.TraceClaim where
  body := signedCount64Body
  pre args mem :=
    mem.callStack = [] ∧ mem.activeCallee = none ∧
    mem.activeProtectors = [] ∧ args = []
  post _ mem tr out :=
    TraceObsOnly tr ∧
    ∃ mem', out = .normal (.scalar ⟨32, 4⟩, mem') ∧ MirMemFrame mem' mem

/-- `TraceVerificationResult signedCount64TraceClaim` through
`AutoProve.traceVerificationResult_of_autoVerifyCutpoints`. -/
theorem signedCount64_traceVerificationResult :
    Trusted.VerificationResult.TraceVerificationResult
      signedCount64TraceClaim :=
  AutoProve.traceVerificationResult_of_autoVerifyCutpoints
    (retInv := signedCount64RetInv) (cutpoints := signedCount64Cutpoints)
    (rpoOrder :=
      AutoProve.defaultRpoOrder signedCount64Body signedCount64Cutpoints)
    rfl
    (fun args mem hPre => by
      have hArgs : args = [] := hPre.2.2.2
      subst hArgs
      exact ⟨hPre.1, hPre.2.1, hPre.2.2.1, rfl⟩)
    (fun _ _ _ retVal mem' _ hTr hFrame hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        have hV : retVal = .scalar ⟨32, 4⟩ := sint_valDenote_exact rfl hDen
        subst hV
        exact ⟨hTr, mem', rfl, hFrame⟩)

/--
info: 'Anneal.AiPcc.AutoProve.statefulVerificationResult_of_autoVerifyCutpoints' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.statefulVerificationResult_of_autoVerifyCutpoints

/--
info: 'Anneal.AiPcc.AutoProve.traceVerificationResult_of_autoVerifyCutpoints' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AutoProve.traceVerificationResult_of_autoVerifyCutpoints

/--
info: 'Anneal.AiPcc.sintMulOk_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sintMulOk_sound

/--
info: 'Anneal.AiPcc.binOpSintAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms binOpSintAbs_sound

/--
info: 'Anneal.AiPccMirTests.signedCount64_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedCount64_verificationResult

/--
info: 'Anneal.AiPccMirTests.signedCount64_statefulVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedCount64_statefulVerificationResult

/--
info: 'Anneal.AiPccMirTests.signedCount64_traceVerificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedCount64_traceVerificationResult

/-! ## 7. Congruence-Tightened Stride Loops, Signed Interval Products, and `bb0` Cutpoints -/

/-- An initialized abstract value in `[lo, hi]` with stride congruence
`x ≡ rem (mod m)`. -/
def strideIvAbs (w lo hi m rem : Nat) : AbsVal :=
  reduceAbsVal w ⟨.init, Tnum.top w, .iv lo hi, .cong m rem⟩

/-- `-64` as an `i32` bit pattern. -/
def i32Neg64 : Nat := modPow2 32 - 64

/-- `fn() -> i32 { let mut i = start; while i op bound { i = stepOp(i, step) }; i }`
for two's-complement bit patterns `start`, `bound`, `step`. -/
def signedStrideLoopBody (op stepOp : BinOp) (start bound step : Nat) :
    CapturedMir :=
  canaryBody "ai_pcc_tests::signed_stride_loop" 0
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy]
    [ canaryBlock [.storageLive 1,
        .assign (canaryPlace 1) (.use (canaryIConst .i32 start)),
        .storageLive 2] (.goto 1),
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp op (canaryCopy 1) (canaryIConst .i32 bound))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      canaryBlock [.assign (canaryPlace 1)
          (.binaryOp stepOp (canaryCopy 1) (canaryIConst .i32 step))]
        (.goto 1),
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 2, .storageDead 1] .return_ ]

/-- `fn() -> u32 { let mut i = start; while i op bound { i += step }; i }`. -/
def unsignedStrideLoopBody (op : BinOp) (start bound step : Nat) :
    CapturedMir :=
  canaryBody "ai_pcc_tests::unsigned_stride_loop" 0
    [canaryUintTy .u32, canaryUintTy .u32, canaryBoolTy]
    [ canaryBlock [.storageLive 1,
        .assign (canaryPlace 1) (.use (canaryUConst .u32 start)),
        .storageLive 2] (.goto 1),
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp op (canaryCopy 1) (canaryUConst .u32 bound))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      canaryBlock [.assign (canaryPlace 1)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u32 step))]
        (.goto 1),
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 2, .storageDead 1] .return_ ]

/-- Loop-header cutpoint of `unsignedStrideLoopBody` with counter value `a`. -/
def unsignedStrideCutpoints (a : AbsVal) : List (Nat × MirAbsEnv) :=
  [(1, [.uint .u32 (AbsVal.uninit 32), .uint .u32 a, .bool .uninit])]

/-- Sign-straddling stride-4 loop `i = -64; while i < 32 { i += 4 }`. -/
def signedStraddlingStride4Body : CapturedMir :=
  signedStrideLoopBody .lt .addUnchecked i32Neg64 32 4

/-- Header cutpoint of `signedStraddlingStride4Body`:
`-64 <= i <= 32` and `i ≡ 0 (mod 4)`. -/
def signedStraddlingStride4Cutpoints : List (Nat × MirAbsEnv) :=
  signedCountCutpoints (strideIvAbs 32 i32Neg64 32 4 0)

/-- Congruence-aware guard refinement (`refineSleConstWithCong`,
`refineSgtConstWithCong`, `refineUleConstWithCong`, `refineUgtConstWithCong`)
certifies stride-aligned loops across negative intervals, sign-straddling
count-up and countdown intervals, and non-power-of-two unsigned bounds, while
rejecting off-by-one guards and unaligned entry values. -/
theorem stride_aligned_loops_via_congruence_refinement :
    -- Negative range: `i = -64; while i < -32 { i += 4 }` exits at `-32`.
    AutoProve.autoVerifyCutpoints
      (signedStrideLoopBody .lt .addUnchecked i32Neg64 i32Neg32 4)
      (.sint .i32 (AbsVal.const 32 i32Neg32))
      (signedCountCutpoints (strideIvAbs 32 i32Neg64 i32Neg32 4 0)) = true ∧
    -- Near-miss: `i <= -32` steps to `-28`, violating `[-64, -32]`.
    AutoProve.autoVerifyCutpoints
      (signedStrideLoopBody .le .addUnchecked i32Neg64 i32Neg32 4)
      (.sint .i32 (AbsVal.topInit 32))
      (signedCountCutpoints (strideIvAbs 32 i32Neg64 i32Neg32 4 0)) = false ∧
    -- Near-miss: unaligned start `-63` violates `i ≡ 0 (mod 4)`.
    AutoProve.autoVerifyCutpoints
      (signedStrideLoopBody .lt .addUnchecked (i32Neg64 + 1) i32Neg32 4)
      (.sint .i32 (AbsVal.const 32 i32Neg32))
      (signedCountCutpoints (strideIvAbs 32 i32Neg64 i32Neg32 4 0)) = false ∧
    -- Sign-straddling count-up: `i = -64; while i < 32 { i += 4 }` exits at `32`.
    AutoProve.autoVerifyCutpoints signedStraddlingStride4Body
      (.sint .i32 (AbsVal.const 32 32))
      signedStraddlingStride4Cutpoints = true ∧
    -- Sign-straddling countdown: `i = 32; while i > -64 { i -= 4 }` exits at `-64`.
    AutoProve.autoVerifyCutpoints
      (signedStrideLoopBody .gt .subUnchecked 32 i32Neg64 4)
      (.sint .i32 (AbsVal.const 32 i32Neg64))
      signedStraddlingStride4Cutpoints = true ∧
    -- Near-miss countdown: `i >= -64` steps to `-68`, violating `[-64, 32]`.
    AutoProve.autoVerifyCutpoints
      (signedStrideLoopBody .ge .subUnchecked 32 i32Neg64 4)
      (.sint .i32 (AbsVal.topInit 32))
      signedStraddlingStride4Cutpoints = false ∧
    -- Non-power-of-two unsigned: `i = 0; while i < 24 { i += 4 }` exits at `24`.
    AutoProve.autoVerifyCutpoints
      (unsignedStrideLoopBody .lt 0 24 4)
      (.uint .u32 (AbsVal.const 32 24))
      (unsignedStrideCutpoints (strideIvAbs 32 0 24 4 0)) = true ∧
    -- Near-miss unsigned: `i <= 24` steps to `28`, violating `[0, 24]`.
    AutoProve.autoVerifyCutpoints
      (unsignedStrideLoopBody .le 0 24 4)
      (.uint .u32 (AbsVal.topInit 32))
      (unsignedStrideCutpoints (strideIvAbs 32 0 24 4 0)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Audited claim for `signedStraddlingStride4Body`: returns `32`. -/
def signedStraddlingStride4Claim : Trusted.VerificationResult.Claim where
  body := signedStraddlingStride4Body
  pre args := args = []
  post _ ret := ret = .scalar ⟨32, 4⟩

/-- `VerificationResult signedStraddlingStride4Claim` from one `rfl`. -/
theorem signedStraddlingStride4_verificationResult :
    Trusted.VerificationResult.VerificationResult
      signedStraddlingStride4Claim :=
  AutoProve.bodyVerified_of_autoVerifyCutpoints
    (retInv := .sint .i32 (AbsVal.const 32 32))
    (cutpoints := signedStraddlingStride4Cutpoints)
    (rpoOrder := AutoProve.defaultRpoOrder signedStraddlingStride4Body
      signedStraddlingStride4Cutpoints)
    rfl
    (fun args hPre => by
      have hArgs : args = [] := hPre
      subst hArgs
      exact rfl)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        exact sint_valDenote_exact rfl hDen)

/-- `fn(x: i8, y: i8) -> i8`: when `lo1 <= x <= hi1` and `lo2 <= y <= hi2`
(all two's-complement bit patterns), compute `x.unchecked_mul(y)`. -/
def guardedSignedMulBody (lo1 hi1 lo2 hi2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::guarded_signed_mul" 2
    [canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8,
     canaryBoolTy, canaryBoolTy, canaryBoolTy, canaryBoolTy]
    [ canaryBlock [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .ge (canaryCopy 1) (canaryIConst .i8 lo1))]
        (.switchInt (canaryCopy 3) ⟨[(0, 5)], 1⟩),
      canaryBlock [.storageLive 4,
        .assign (canaryPlace 4)
          (.binaryOp .le (canaryCopy 1) (canaryIConst .i8 hi1))]
        (.switchInt (canaryCopy 4) ⟨[(0, 5)], 2⟩),
      canaryBlock [.storageLive 5,
        .assign (canaryPlace 5)
          (.binaryOp .ge (canaryCopy 2) (canaryIConst .i8 lo2))]
        (.switchInt (canaryCopy 5) ⟨[(0, 5)], 3⟩),
      canaryBlock [.storageLive 6,
        .assign (canaryPlace 6)
          (.binaryOp .le (canaryCopy 2) (canaryIConst .i8 hi2))]
        (.switchInt (canaryCopy 6) ⟨[(0, 5)], 4⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .mulUnchecked (canaryCopy 1) (canaryCopy 2))] .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- Checked (`mulWithOverflow` + `assert(!.1)`) counterpart of
`guardedSignedMulBody`. -/
def guardedSignedCheckedMulBody (lo1 hi1 lo2 hi2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::guarded_signed_checked_mul" 2
    [canaryIntTy .i8, canaryIntTy .i8, canaryIntTy .i8,
     canaryBoolTy, canaryBoolTy, canaryBoolTy, canaryBoolTy, intPairTy .i8]
    [ canaryBlock [.storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .ge (canaryCopy 1) (canaryIConst .i8 lo1))]
        (.switchInt (canaryCopy 3) ⟨[(0, 6)], 1⟩),
      canaryBlock [.storageLive 4,
        .assign (canaryPlace 4)
          (.binaryOp .le (canaryCopy 1) (canaryIConst .i8 hi1))]
        (.switchInt (canaryCopy 4) ⟨[(0, 6)], 2⟩),
      canaryBlock [.storageLive 5,
        .assign (canaryPlace 5)
          (.binaryOp .ge (canaryCopy 2) (canaryIConst .i8 lo2))]
        (.switchInt (canaryCopy 5) ⟨[(0, 6)], 3⟩),
      canaryBlock [.storageLive 6,
        .assign (canaryPlace 6)
          (.binaryOp .le (canaryCopy 2) (canaryIConst .i8 hi2))]
        (.switchInt (canaryCopy 6) ⟨[(0, 6)], 4⟩),
      canaryBlock [.storageLive 7,
        .assign (canaryPlace 7)
          (.binaryOp .mulWithOverflow (canaryCopy 1) (canaryCopy 2))]
        (.assert (.move (fieldPlace 7 1 canaryBoolTy)) false 5 .continue_),
      canaryBlock [.assign (canaryPlace 0)
          (.use (.move (fieldPlace 7 0 (canaryIntTy .i8))))] .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- `fn() -> i128 { c1.unchecked_mul(c2) }` on `i128` constants. -/
def i128ConstMulBody (c1 c2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::i128_const_mul" 0 [canaryIntTy .i128]
    [canaryBlock [.assign (canaryPlace 0)
      (.binaryOp .mulUnchecked (canaryIConst .i128 c1) (canaryIConst .i128 c2))]
      .return_]

/-- Bounded signed interval products (`sintNoOverflowMulBiased`): sign-straddling
and opposite-sign `INT_MIN`-boundary products verify in both unchecked and
checked forms, while overflowing products (`+128`, `-130`, `i128::MIN * -1`)
fail closed. -/
theorem signed_interval_products :
    -- `[-10, 10] * 2` fits (`[-20, 20]`).
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 246 10 2 2) = true ∧
    AutoProve.autoVerifyAcyclic (guardedSignedCheckedMulBody 246 10 2 2) = true ∧
    -- `[-10, -1] * [-5, 5]` fits (`[-50, 50]`).
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 246 255 251 5) = true ∧
    -- Opposite-sign exact `i8::MIN` boundary: `[-64, -1] * [1, 2]` and symmetric.
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 192 255 1 2) = true ∧
    AutoProve.autoVerifyAcyclic (guardedSignedCheckedMulBody 192 255 1 2) = true ∧
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 1 2 192 255) = true ∧
    -- Overflowing symmetric product `[-64, 64] * 2` (`+128` overflows).
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 192 64 2 2) = false ∧
    AutoProve.autoVerifyAcyclic (guardedSignedCheckedMulBody 192 64 2 2) = false ∧
    -- Overflowing same-sign negative product `[-64, -1] * [-2, -1]` (`+128`).
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 192 255 254 255) = false ∧
    AutoProve.autoVerifyAcyclic (guardedSignedCheckedMulBody 192 255 254 255) = false ∧
    -- Overflowing opposite-sign product `[-65, -1] * [1, 2]` (`-130`).
    AutoProve.autoVerifyAcyclic (guardedSignedMulBody 191 255 1 2) = false ∧
    -- `i128` exact boundary: `(-2) * 2^126 = i128::MIN` fits;
    -- `(-2) * (2^126 + 1)` and `i128::MIN * -1` overflow.
    AutoProve.autoVerifyAcyclic
      (i128ConstMulBody (modPow2 128 - 2) (modPow2 126)) = true ∧
    AutoProve.autoVerifyAcyclic
      (i128ConstMulBody (modPow2 128 - 2) (modPow2 126 + 1)) = false ∧
    AutoProve.autoVerifyAcyclic
      (i128ConstMulBody (modPow2 127) (modPow2 128 - 1)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn(mut x: i32) -> i32 { while x < 0 { x = x.unchecked_add(1); } x }`
where the entry block `bb0` itself is the loop header (`bb0 -> bb1 -> bb0`,
exit `bb2`).
- `_0 : i32`; `_1 : i32` argument/counter; `_2 : bool` guard. -/
def bb0CutpointLoopBody : CapturedMir :=
  canaryBody "ai_pcc_tests::bb0_cutpoint_loop" 1
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy]
    [ -- bb0: entry & loop header (cutpoint)
      canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.binaryOp .lt (canaryCopy 1) (canaryIConst .i32 0))]
        (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
      -- bb1: `x < 0`, so `x.unchecked_add(1)` cannot overflow
      canaryBlock [.assign (canaryPlace 1)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i32 1)),
        .storageDead 2] (.goto 0),
      -- bb2: `x >= 0`, return `x`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 2] .return_ ]

/-- Cutpoint invariant on `bb0` (equal to the entry environment). -/
def bb0CutpointLoopCutpoints : List (Nat × MirAbsEnv) :=
  [(0, entryEnv bb0CutpointLoopBody.localDecls [.sint .i32 (AbsVal.topInit 32)])]

/-- Return postcondition of `bb0CutpointLoopBody`: non-negative `i32`
(`0 <= bits < 2^31`). -/
def bb0CutpointLoopRetInv : MirAbsSlot :=
  .sint .i32 (ivAbs 32 0 (modPow2 31 - 1))

/-- A loop whose entry block `bb0` is the cutpoint: `defaultRpoOrder` without
cutpoints rejects the cyclic CFG (`autoVerifyAcyclic = false`), while adding
the `bb0` cutpoint computes `[0, 2, 1]` and certifies the loop and its
non-negative return bound. -/
theorem bb0_as_cutpoint_loop :
    AutoProve.defaultRpoOrder bb0CutpointLoopBody = [1, 0, 2] ∧
    AutoProve.autoVerifyAcyclic bb0CutpointLoopBody = false ∧
    AutoProve.defaultRpoOrder bb0CutpointLoopBody bb0CutpointLoopCutpoints =
      [0, 2, 1] ∧
    AutoProve.autoVerifyCutpoints bb0CutpointLoopBody bb0CutpointLoopRetInv
      bb0CutpointLoopCutpoints = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Audited claim for `bb0CutpointLoopBody`: for every valid `i32` input it is
UB-free and every normal return is non-negative (`bits < 2^31`). -/
def bb0CutpointLoopClaim : Trusted.VerificationResult.Claim where
  body := bb0CutpointLoopBody
  pre args := AutoProve.ValidEntryArgs bb0CutpointLoopBody args
  post _ ret := ∃ bits, ret = .scalar ⟨bits, 4⟩ ∧ bits < modPow2 31

/-- `VerificationResult bb0CutpointLoopClaim` from one `rfl`. -/
theorem bb0CutpointLoop_verificationResult :
    Trusted.VerificationResult.VerificationResult bb0CutpointLoopClaim :=
  AutoProve.bodyVerified_of_autoVerifyCutpoints
    (retInv := bb0CutpointLoopRetInv) (cutpoints := bb0CutpointLoopCutpoints)
    (rpoOrder := AutoProve.defaultRpoOrder bb0CutpointLoopBody
      bb0CutpointLoopCutpoints)
    rfl
    (fun _ hPre => hPre)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        match sint_valDenote_ubound (hi := modPow2 31 - 1) rfl hDen with
        | ⟨bits, hV, hLe⟩ =>
          exact ⟨bits, hV,
            Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 31) Nat.one_pos)⟩)

/--
info: 'Anneal.AiPcc.refineSleConstWithCong_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refineSleConstWithCong_sound

/--
info: 'Anneal.AiPcc.refineSgtConstWithCong_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refineSgtConstWithCong_sound

/--
info: 'Anneal.AiPcc.refineUleConstWithCong_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refineUleConstWithCong_sound

/--
info: 'Anneal.AiPcc.refineUgtConstWithCong_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refineUgtConstWithCong_sound

/--
info: 'Anneal.AiPcc.sintNoOverflowMulBiased_sound' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms sintNoOverflowMulBiased_sound

/--
info: 'Anneal.AiPccMirTests.signedStraddlingStride4_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedStraddlingStride4_verificationResult

/--
info: 'Anneal.AiPccMirTests.bb0CutpointLoop_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bb0CutpointLoop_verificationResult

/-! ## 8. Exact Biased Signed Widening and Signed `*WithOverflow` Guards -/

/-- `fn(x: i8) -> i32 { (x as i32).unchecked_add(1) }`: exact biased signed
widening maps arbitrary `x : i8` into `[-128, 127]` in `i32`. -/
def widenI8ToI32Add1Body : CapturedMir :=
  canaryBody "ai_pcc_tests::widen_i8_i32_add1" 1
    [canaryIntTy .i32, canaryIntTy .i8, canaryIntTy .i32]
    [canaryBlock [.storageLive 2,
        .assign (canaryPlace 2)
          (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
        .assign (canaryPlace 0)
          (.binaryOp .addUnchecked (canaryCopy 2) (canaryIConst .i32 1)),
        .storageDead 2] .return_]

/-- Trusted `VerificationResult` for `widenI8ToI32Add1Body` from one `rfl`. -/
theorem widenI8ToI32Add1_verificationResult :
    Trusted.VerificationResult.VerificationResult
      (AutoProve.autoClaim widenI8ToI32Add1Body) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl

/-- Exact biased signed widening (`sintCastAbs`) preserves signed ranges across
arbitrary `i8 -> i32` and negative `i8 -> {i32, u32}` casts, pruning dead traps
while still rejecting genuine overflow after widening. -/
theorem signed_widening_casts_exact :
    -- Arbitrary `x : i8 -> (x as i32).unchecked_add(1)` and `unchecked_sub(1)`.
    AutoProve.autoVerifyAcyclic widenI8ToI32Add1Body = true ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::widen_i8_i32_sub1" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryIntTy .i32]
        [canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 0)
              (.binaryOp .subUnchecked (canaryCopy 2) (canaryIConst .i32 1)),
            .storageDead 2] .return_]) = true ∧
    -- Negative `x : i8` widened to `i32` stays `< 0` and `(x as i32) + 128 >= 0`
    -- (pruning unreachable traps on the false edges).
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_widen_sign_and_shift" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryBoolTy, canaryIntTy .i32,
         canaryBoolTy]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .lt (canaryCopy 1) (canaryIConst .i8 0))]
            (.switchInt (canaryCopy 2) ⟨[(0, 4)], 1⟩),
          canaryBlock [.storageLive 3, .storageLive 4,
            .assign (canaryPlace 3)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 4)
              (.binaryOp .lt (canaryCopy 3) (canaryIConst .i32 0))]
            (.switchInt (canaryCopy 4) ⟨[(0, 3)], 2⟩),
          canaryBlock [.assign (canaryPlace 3)
              (.binaryOp .addUnchecked (canaryCopy 3) (canaryIConst .i32 128)),
            .assign (canaryPlace 4)
              (.binaryOp .ge (canaryCopy 3) (canaryIConst .i32 0))]
            (.switchInt (canaryCopy 4) ⟨[(0, 3)], 5⟩),
          canaryBlock [] .unreachable,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
            .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 3))]
            .return_ ]) = true ∧
    -- Negative `x : i8` widened to `u32` lies in `[2^32 - 128, 2^32 - 1]`.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_widen_u32_bound" 1
        [canaryUintTy .u32, canaryIntTy .i8, canaryBoolTy, canaryUintTy .u32,
         canaryBoolTy]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .lt (canaryCopy 1) (canaryIConst .i8 0))]
            (.switchInt (canaryCopy 2) ⟨[(0, 3)], 1⟩),
          canaryBlock [.storageLive 3, .storageLive 4,
            .assign (canaryPlace 3)
              (.cast .intToInt (canaryCopy 1) (canaryUintTy .u32)),
            .assign (canaryPlace 4)
              (.binaryOp .ge (canaryCopy 3)
                (canaryUConst .u32 (modPow2 32 - 128)))]
            (.switchInt (canaryCopy 4) ⟨[(0, 2)], 4⟩),
          canaryBlock [] .unreachable,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryUConst .u32 0))]
            .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 3))]
            .return_ ]) = true ∧
    -- Genuine overflow after widening: `x : i8` widened to `i32` can be `+127`,
    -- so `(x as i32).unchecked_add(i32::MAX)` overflows; negative `x <= -100`
    -- widened to `i32` and subtracting `i32::MAX` also overflows.
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::widen_i8_i32_add_max" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryIntTy .i32]
        [canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 0)
              (.binaryOp .addUnchecked (canaryCopy 2)
                (canaryIConst .i32 (modPow2 31 - 1)))] .return_]) = false ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::neg_widen_sub_max" 1
        [canaryIntTy .i32, canaryIntTy .i8, canaryBoolTy, canaryIntTy .i32]
        [ canaryBlock [.storageLive 2,
            .assign (canaryPlace 2)
              (.binaryOp .le (canaryCopy 1) (canaryIConst .i8 156))]
            (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
          canaryBlock [.storageLive 3,
            .assign (canaryPlace 3)
              (.cast .intToInt (canaryCopy 1) (canaryIntTy .i32)),
            .assign (canaryPlace 0)
              (.binaryOp .subUnchecked (canaryCopy 3)
                (canaryIConst .i32 (modPow2 31 - 1)))] .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
            .return_ ]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn(x: i8) -> i8`: compute `(_, ov) = x.overflowing_add(c)` (or
`c.overflowing_add(x)` when `constLeft = true`); if `!ov`, return
`x.unchecked_add(uncheckedC)`, else `0`. -/
def signedOverflowBranchAddBody (c uncheckedC : Nat) (constLeft : Bool) :
    CapturedMir :=
  let addRhs :=
    match constLeft with
    | false => Rvalue.binaryOp .addWithOverflow (canaryCopy 1) (canaryIConst .i8 c)
    | true => Rvalue.binaryOp .addWithOverflow (canaryIConst .i8 c) (canaryCopy 1)
  canaryBody "ai_pcc_tests::signed_ov_branch_add" 1
    [canaryIntTy .i8, canaryIntTy .i8, intPairTy .i8, canaryBoolTy]
    [ canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2) addRhs,
        .assign (canaryPlace 3)
          (.use (.copy (fieldPlace 2 1 canaryBoolTy)))]
        (.switchInt (canaryCopy 3) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 uncheckedC))]
        .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- `fn(x: i8) -> i8`: compute `(_, ov) = x.overflowing_sub(c)`; if `!ov`,
return `x.unchecked_sub(uncheckedC)`, else `0`. -/
def signedOverflowBranchSubRBody (c uncheckedC : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_ov_branch_sub_r" 1
    [canaryIntTy .i8, canaryIntTy .i8, intPairTy .i8, canaryBoolTy]
    [ canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2)
          (.binaryOp .subWithOverflow (canaryCopy 1) (canaryIConst .i8 c)),
        .assign (canaryPlace 3)
          (.use (.copy (fieldPlace 2 1 canaryBoolTy)))]
        (.switchInt (canaryCopy 3) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .subUnchecked (canaryCopy 1) (canaryIConst .i8 uncheckedC))]
        .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- `fn(y: i8) -> i8`: compute `(_, ov) = c.overflowing_sub(y)`; if `!ov`,
return `uncheckedC.unchecked_sub(y)`, else `0`. -/
def signedOverflowBranchSubLBody (c uncheckedC : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_ov_branch_sub_l" 1
    [canaryIntTy .i8, canaryIntTy .i8, intPairTy .i8, canaryBoolTy]
    [ canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2)
          (.binaryOp .subWithOverflow (canaryIConst .i8 c) (canaryCopy 1)),
        .assign (canaryPlace 3)
          (.use (.copy (fieldPlace 2 1 canaryBoolTy)))]
        (.switchInt (canaryCopy 3) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .subUnchecked (canaryIConst .i8 uncheckedC) (canaryCopy 1))]
        .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- `fn(y: i8) -> i8`: `let (_, ov) = 0i8.overflowing_sub(y); if !ov { y / -1 } else { 0 }`.
On the `!ov` arm, `sintSubOverflowBoolAbs`'s `.sleConst _ .i8 128` guard negates
to `y > i8::MIN`, certifying `y / -1` UB-free. -/
def signedNegGuardDivBody : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_neg_guard_div" 1
    [canaryIntTy .i8, canaryIntTy .i8, intPairTy .i8, canaryBoolTy]
    [ canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 2)
          (.binaryOp .subWithOverflow (canaryIConst .i8 0) (canaryCopy 1)),
        .assign (canaryPlace 3)
          (.use (.copy (fieldPlace 2 1 canaryBoolTy)))]
        (.switchInt (canaryCopy 3) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .div (canaryCopy 1) (canaryIConst .i8 255))] .return_,
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
        .return_ ]

/-- Trusted `VerificationResult` for `signedNegGuardDivBody` from one `rfl`. -/
theorem signedNegGuardDiv_verificationResult :
    Trusted.VerificationResult.VerificationResult
      (AutoProve.autoClaim signedNegGuardDivBody) :=
  AutoProve.bodyVerified_of_autoVerifyAcyclic rfl

/-- Exact-constant signed `*WithOverflow` body asserting `ov == true`. -/
def signedConstAssertOverflowBody (op : BinOp) (c1 c2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc_tests::signed_const_assert_ov" 0
    [canaryIntTy .i8, intPairTy .i8]
    [ canaryBlock [.storageLive 1,
        .assign (canaryPlace 1)
          (.binaryOp op (canaryIConst .i8 c1) (canaryIConst .i8 c2))]
        (.assert (.move (fieldPlace 1 1 canaryBoolTy)) true 1 .continue_),
      canaryBlock [.assign (canaryPlace 0)
          (.use (.move (fieldPlace 1 0 (canaryIntTy .i8))))] .return_ ]

/-- Signed `*WithOverflow` relational guards (`sintAddOverflowBoolAbs`,
`sintSubOverflowBoolAbs`) and exact-constant `ov = true` folding: branching on
`!ov` (or `ov`) refines the variable operand tightly for positive, negative,
`INT_MIN`, and `0 - y` cases, while rejecting off-by-one unchecked follow-ups. -/
theorem signed_overflow_relational_guards :
    -- `x + 10` and `10 + x`: `!ov` certifies `x + 10` but rejects `x + 11`.
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 10 10 false) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 10 10 true) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 10 11 false) = false ∧
    -- `x + (-10)` and `(-10) + x`: `!ov` certifies `x + (-10)` but rejects `x + (-11)`.
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 246 246 false) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 246 246 true) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 246 245 false) = false ∧
    -- `x + i8::MIN`: `!ov` refines `x >= 0` (certifying `x + i8::MIN`), and on
    -- the `ov` arm `x < 0` (certifying `x.unchecked_add(1)`).
    AutoProve.autoVerifyAcyclic (signedOverflowBranchAddBody 128 128 false) = true ∧
    AutoProve.autoVerifyAcyclic
      (canaryBody "ai_pcc_tests::signed_ov_true_arm_add_min" 1
        [canaryIntTy .i8, canaryIntTy .i8, intPairTy .i8, canaryBoolTy]
        [ canaryBlock [.storageLive 2, .storageLive 3,
            .assign (canaryPlace 2)
              (.binaryOp .addWithOverflow (canaryCopy 1) (canaryIConst .i8 128)),
            .assign (canaryPlace 3)
              (.use (.copy (fieldPlace 2 1 canaryBoolTy)))]
            (.switchInt (canaryCopy 3) ⟨[(0, 2)], 1⟩),
          canaryBlock [.assign (canaryPlace 0)
              (.binaryOp .addUnchecked (canaryCopy 1) (canaryIConst .i8 1))]
            .return_,
          canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i8 0))]
            .return_ ]) = true ∧
    -- `x - 10`, `x - (-10)`, `x - i8::MIN` (`!ov` refines `x` tightly).
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubRBody 10 10) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubRBody 10 11) = false ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubRBody 246 246) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubRBody 246 245) = false ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubRBody 128 128) = true ∧
    -- `0 - y`, `10 - y`, `(-2) - y` (`!ov` refines `y` tightly).
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubLBody 0 0) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubLBody 10 10) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubLBody 10 11) = false ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubLBody 254 254) = true ∧
    AutoProve.autoVerifyAcyclic (signedOverflowBranchSubLBody 254 253) = false ∧
    -- Cross-operation refinement: `0 - y` overflow-free => `y != i8::MIN` => `y / -1` safe.
    AutoProve.autoVerifyAcyclic signedNegGuardDivBody = true ∧
    -- Exact constant overflowing `*WithOverflow` folds `ov = true`.
    AutoProve.autoVerifyAcyclic
      (signedConstAssertOverflowBody .addWithOverflow 127 1) = true ∧
    AutoProve.autoVerifyAcyclic
      (signedConstAssertOverflowBody .subWithOverflow 128 1) = true ∧
    AutoProve.autoVerifyAcyclic
      (signedConstAssertOverflowBody .mulWithOverflow 128 255) = true ∧
    -- Non-overflowing constant cannot satisfy `assert(ov == true)`.
    AutoProve.autoVerifyAcyclic
      (signedConstAssertOverflowBody .addWithOverflow 10 20) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
info: 'Anneal.AiPcc.signedBias_signExtendBits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedBias_signExtendBits

/--
info: 'Anneal.AiPcc.signedOverflowAdd_iff_sgt' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedOverflowAdd_iff_sgt

/--
info: 'Anneal.AiPcc.signedOverflowSub_constL_nonneg_iff_sle' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedOverflowSub_constL_nonneg_iff_sle

/--
info: 'Anneal.AiPcc.sintAddOverflowBoolAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sintAddOverflowBoolAbs_sound

/--
info: 'Anneal.AiPcc.sintSubOverflowBoolAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sintSubOverflowBoolAbs_sound

/--
info: 'Anneal.AiPcc.sintMulOverflowBoolAbs_sound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sintMulOverflowBoolAbs_sound

/--
info: 'Anneal.AiPccMirTests.widenI8ToI32Add1_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms widenI8ToI32Add1_verificationResult

/--
info: 'Anneal.AiPccMirTests.signedNegGuardDiv_verificationResult' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedNegGuardDiv_verificationResult

end Anneal.AiPccMirTests
