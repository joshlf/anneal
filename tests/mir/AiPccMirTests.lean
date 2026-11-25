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
2. An `Anneal.ParametricCore` end-to-end use: a fuel-bounded run of the
   deterministic step function proves `wpOutcome` at a concrete start state,
   and the fourth conjunct of `checkMirCert_sound` upgrades it to fault-free
   `wpStateOk` with the certified return postcondition.
3. `#print axioms` guards: the soundness theorems and the canaries depend
   only on `propext` and `Quot.sound`.
4. Fail-closed refutations (`= false` by `rfl`) of unsound bodies,
   certificates, and schedules.
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

/-! ## 3. Axiom Guards -/

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

end Anneal.AiPccMirTests
