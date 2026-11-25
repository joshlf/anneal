-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct
import Anneal.AiPcc.MirBridge
import Anneal.AiPcc.MirTransfer
import Anneal.AiPcc.MirPcc

namespace Anneal.AiPcc

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# AI-PCC Canaries (`Anneal.AiPcc.Canaries`)

Canary suite for the `Anneal.AiPcc` stack. It is not imported by
`theory/Anneal.lean`.

1. Domain canaries for the MIR-agnostic reduced product (`BitArith`, `Tnum`,
   `WrappedInterval`, `ReducedProduct`).
2. End-to-end MIR canaries over concrete `V2026_06_01` `CapturedMir` bodies,
   each certified by `rfl` and transported through
   `verifyMirCutpoints_sound_call` to `SafeFrom`, a return-value property,
   and `MirNoUBTree (mirCallTree body args)`:
   * a stride-8 `u64` loop with one Bourdoncle cutpoint, unchecked
     `add`/`sub`/`shl`/`shr`, and a dead `unreachable` trap (returns exactly
     `1024`);
   * a `u32` bitmask with a certified nonzero divisor, `div`/`rem`, and a
     widening `IntToInt` cast (returns a value `< 2^32`);
   * a signed `i32` branch `if x >= 0 { x / 2 } else { 0 }` refined through a
     `switchInt` guard on a copy temporary (returns a value in `[0, 2^30)`).
   The loop and signed canaries are also packaged as trusted
   `VerificationResult` certificates of concrete `Claim`s.
3. Positive controls and CFG joins (`switchInt` diamonds, `move` aliasing,
   checked arithmetic with `assert`).
4. A fail-closed negative suite and a `validRpoSchedule` suite.
-/

/-- Certified loop-header abstract value for `_1`: `0 ≤ _1 ≤ 1024` and low 3
bits known zero (`_1 ≡ 0 (mod 8)`). -/
def stride8HeaderIdxAbs : AbsVal :=
  reduceAbsVal 64
    { init := .init
      tnum := ⟨0, 2040⟩  -- bits 3..10 unknown (0x7F8 = 2040), bits 0..2 = 0
      wi := .iv 0 1024
      sc := .cong 8 0 }

/-- Direct positive and fail-closed unit checks for standalone reduced-product
domain helpers (`InitDom.meet`, `AbsVal.isAligned8`,
`AbsVal.noOverflowAddConst`, `AbsVal.addConstWrap`, and
`AbsVal.subConstWrap`). -/
theorem canary_domain_helpers_tests :
    InitDom.meet .uninit .init = .init ∧
    InitDom.meet .init .bot = .bot ∧
    stride8HeaderIdxAbs.isAligned8 = true ∧
    (AbsVal.const 64 12).isAligned8 = false ∧
    stride8HeaderIdxAbs.noOverflowAddConst 64 8 = true ∧
    (AbsVal.topInit 8).noOverflowAddConst 8 1 = false ∧
    (AbsVal.addConstWrap 8 (AbsVal.const 8 250) 10).exactVal? 8 = some 4 ∧
    (AbsVal.subConstWrap 8 (AbsVal.const 8 4) 10).exactVal? 8 = some 250 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## MIR Construction Helpers -/

/-- Unsigned integer type `u` (layout index `0`, unused by the checker). -/
def canaryUintTy (u : UintTy) : Ty := ⟨.uint u, 0⟩

/-- Signed integer type `i`. -/
def canaryIntTy (i : IntTy) : Ty := ⟨.int i, 0⟩

/-- `bool`. -/
def canaryBoolTy : Ty := ⟨.bool, 0⟩

/-- `(u, bool)` checked-arithmetic tuple type. -/
def canaryUintPairTy (u : UintTy) : Ty := ⟨.tuple [.uint u, .bool], 0⟩

/-- Mutable local declaration of type `ty`. -/
def canaryDecl (ty : Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := none }

/-- Unprojected place `_r`. -/
def canaryPlace (r : Nat) : Place := ⟨r, []⟩

/-- `copy _r`. -/
def canaryCopy (r : Nat) : Operand := .copy (canaryPlace r)

/-- `move _r`. -/
def canaryMove (r : Nat) : Operand := .move (canaryPlace r)

/-- Unsigned constant `n : u`. -/
def canaryUConst (u : UintTy) (n : Nat) : Operand :=
  .constant ⟨canaryUintTy u, .scalar (.int ⟨n, uintBytes u⟩)⟩

/-- Signed constant with two's-complement bit pattern `bits : i`. -/
def canaryIConst (i : IntTy) (bits : Nat) : Operand :=
  .constant ⟨canaryIntTy i, .scalar (.int ⟨bits, uintBytes (intTwin i)⟩)⟩

/-- Non-cleanup basic block from statement kinds and a terminator kind. -/
def canaryBlock (stmts : List StatementKind) (t : TerminatorKind) :
    BasicBlockData :=
  { statements := stmts.map (fun k => ⟨k, ""⟩)
    terminator := ⟨t, ""⟩
    isCleanup := false }

/-- Zero-sized placeholder layout for the canary ABI. -/
def canaryZstLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

/-- Placeholder Rust ABI (not inspected by the checker). -/
def canaryAbi : FnAbi :=
  { args := [], ret := { layout := canaryZstLayout, mode := .ignore }
    conv := .rust, canUnwind := false }

/-- Runtime-phase `CapturedMir` body on a 64-bit target. -/
def canaryBody (path : String) (argCount : Nat) (tys : List Ty)
    (bbs : List BasicBlockData) : CapturedMir :=
  { defPath := path, phase := .runtimePostCleanup, role := .subject
    argCount := argCount, localDecls := tys.map canaryDecl, basicBlocks := bbs
    fnAbi := canaryAbi
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [] }
    allocations := [] }

/-- An exact unsigned return slot pins the returned value. -/
theorem uint_valDenote_exact {ty : Ty} {u : UintTy} {a : AbsVal}
    {v : Value} {c : Nat} (hEx : a.exactVal? (uintWidth u) = some c)
    (h : (MirAbsSlot.uint u a).valDenote ty v) :
    v = .scalar ⟨c, uintBytes u⟩ := by
  have h2 := h.2
  cases v
  case scalar sc =>
    cases sc with
    | mk bits sz =>
      have hBits := (absVal_exactVal?_sound hEx h2.2).1
      injection hBits with hBits
      have hSz : sz = uintBytes u := h2.1
      subst hBits
      subst hSz
      rfl
  all_goals exact False.elim h2

/-- An unsigned return slot with an upper bound bounds the returned value. -/
theorem uint_valDenote_ubound {ty : Ty} {u : UintTy} {a : AbsVal}
    {v : Value} {hi : Nat} (hUb : a.ubound? = some hi)
    (h : (MirAbsSlot.uint u a).valDenote ty v) :
    ∃ bits, v = .scalar ⟨bits, uintBytes u⟩ ∧ bits ≤ hi := by
  have h2 := h.2
  cases v
  case scalar sc =>
    cases sc with
    | mk bits sz =>
      have hSz : sz = uintBytes u := h2.1
      subst hSz
      exact ⟨bits, rfl, absVal_ubound?_sound hUb h2.2⟩
  all_goals exact False.elim h2

/-- A signed return slot with an upper bound on its bit pattern bounds the
returned bit pattern. -/
theorem sint_valDenote_ubound {ty : Ty} {i : IntTy} {a : AbsVal}
    {v : Value} {hi : Nat} (hUb : a.ubound? = some hi)
    (h : (MirAbsSlot.sint i a).valDenote ty v) :
    ∃ bits, v = .scalar ⟨bits, uintBytes (intTwin i)⟩ ∧ bits ≤ hi := by
  have h2 := h.2
  cases v
  case scalar sc =>
    cases sc with
    | mk bits sz =>
      have hSz : sz = uintBytes (intTwin i) := h2.1
      subst hSz
      exact ⟨bits, rfl, absVal_ubound?_sound hUb h2.2⟩
  all_goals exact False.elim h2

/-! ## Canary 1: Stride-8 `u64` Loop with One Bourdoncle Cutpoint -/

/-- `fn stride8() -> u64`: count `_1` from `0` to `1024` in steps of `8`,
exercising unchecked `add`/`sub`/`shl`/`shr` in the loop body, then return
`_1` after a `_1 == 1024` test whose `false` edge reaches a dead
`unreachable` trap.
- `_0 : u64` return value; `_1 : u64` index; `_2 : bool` guard;
  `_3 : u64` scratch. -/
def stride8LoopBody : CapturedMir :=
  canaryBody "ai_pcc::stride8_loop" 0
    [canaryUintTy .u64, canaryUintTy .u64, canaryBoolTy, canaryUintTy .u64]
    [ -- bb0: entry
      canaryBlock [.storageLive 1,
        .assign (canaryPlace 1) (.use (canaryUConst .u64 0)),
        .storageLive 2, .storageLive 3] (.goto 1),
      -- bb1: loop header (the only cutpoint)
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp .lt (canaryCopy 1) (canaryUConst .u64 1024))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩),
      -- bb2: loop body (`_1 < 1024` and `_1 ≡ 0 (mod 8)` give `_1 ≤ 1016`)
      canaryBlock [
        .assign (canaryPlace 3)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u64 8)),
        .assign (canaryPlace 3)
          (.binaryOp .subUnchecked (canaryCopy 3) (canaryUConst .u64 8)),
        .assign (canaryPlace 3)
          (.binaryOp .shlUnchecked (canaryCopy 1) (canaryUConst .u64 3)),
        .assign (canaryPlace 3)
          (.binaryOp .shrUnchecked (canaryCopy 3) (canaryUConst .u64 3)),
        .assign (canaryPlace 1)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u64 8))]
        (.goto 1),
      -- bb3: loop exit (`_1 ≥ 1024` and `_1 ≤ 1024` give `_1 = 1024`)
      canaryBlock [.assign (canaryPlace 2)
          (.binaryOp .eq (canaryCopy 1) (canaryUConst .u64 1024))]
        (.switchInt (canaryCopy 2) ⟨[(0, 4)], 5⟩),
      -- bb4: dead trap (the `false` edge is infeasible)
      canaryBlock [] .unreachable,
      -- bb5: return `_1`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
        .storageDead 3, .storageDead 2, .storageDead 1] .return_ ]

/-- Certified loop-header invariant of `stride8LoopBody` (`bb1`). -/
def stride8LoopCutpoints : List (Nat × MirAbsEnv) :=
  [(1, [.uint .u64 (AbsVal.uninit 64), .uint .u64 stride8HeaderIdxAbs,
        .bool .uninit, .uint .u64 (AbsVal.uninit 64)])]

/-- Exact return postcondition `_0 = 1024`. -/
def stride8LoopRetInv : MirAbsSlot := .uint .u64 (AbsVal.const 64 1024)

/-- Single-pass certificate check of `stride8LoopBody` by `rfl`. -/
theorem stride8Loop_cert_ok :
    verifyMirCutpoints stride8LoopBody (entryEnv stride8LoopBody.localDecls [])
      stride8LoopRetInv stride8LoopCutpoints [0, 1, 2, 3, 4, 5] = true := rfl

/-- End-to-end soundness of `stride8LoopBody`: unbounded-iteration safety,
exact return value `1024`, and an all-prefix UB-free interaction tree. -/
theorem canary_stride8_loop_pcc_safe :
    SafeFrom stride8LoopBody (initMachineState stride8LoopBody []) ∧
    (∀ v, ReturnsFrom stride8LoopBody (initMachineState stride8LoopBody []) v →
      v = .scalar ⟨1024, 8⟩) ∧
    MirNoUBTree (mirCallTree stride8LoopBody []) := by
  have h := verifyMirCutpoints_sound_call stride8Loop_cert_ok
    (entryArgsOk_nil _)
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    exact uint_valDenote_exact rfl hDen

/-! ## Canary 2: `u32` Bitmask, Nonzero `div` / `rem`, Widening Cast -/

/-- `fn f(a: u32, b: u32) -> u64 { ((a / ((b & 255) | 1)) as u64) }` with an
extra `rem`: the divisor `(b & 255) | 1` is certified to lie in `[1, 255]`.
- `_0 : u64`; `_1, _2 : u32` arguments; `_3, _4 : u32` temporaries. -/
def bitmaskDivCastBody : CapturedMir :=
  canaryBody "ai_pcc::bitmask_div_cast" 2
    [canaryUintTy .u64, canaryUintTy .u32, canaryUintTy .u32,
     canaryUintTy .u32, canaryUintTy .u32]
    [canaryBlock [.storageLive 3, .storageLive 4,
        .assign (canaryPlace 3)
          (.binaryOp .bitAnd (canaryCopy 2) (canaryUConst .u32 255)),
        .assign (canaryPlace 3)
          (.binaryOp .bitOr (canaryCopy 3) (canaryUConst .u32 1)),
        .assign (canaryPlace 4) (.binaryOp .rem (canaryCopy 1) (canaryCopy 3)),
        .assign (canaryPlace 4) (.binaryOp .div (canaryCopy 1) (canaryCopy 3)),
        .assign (canaryPlace 0)
          (.cast .intToInt (canaryCopy 4) (canaryUintTy .u64)),
        .storageDead 4, .storageDead 3] .return_]

/-- Argument slots: arbitrary `u32` values. -/
def bitmaskDivCastArgSlots : List MirAbsSlot :=
  [.uint .u32 (AbsVal.topInit 32), .uint .u32 (AbsVal.topInit 32)]

/-- Return postcondition: the widened value is `< 2^32`. -/
def bitmaskDivCastRetInv : MirAbsSlot :=
  .uint .u64 (reduceAbsVal 64
    ⟨.init, Tnum.top 64, .iv 0 (modPow2 32 - 1), .top⟩)

/-- Single-pass certificate check of `bitmaskDivCastBody` by `rfl`. -/
theorem bitmaskDivCast_cert_ok :
    verifyMirCutpoints bitmaskDivCastBody
      (entryEnv bitmaskDivCastBody.localDecls bitmaskDivCastArgSlots)
      bitmaskDivCastRetInv [] [0] = true := rfl

/-- End-to-end soundness of `bitmaskDivCastBody` for all `u32` inputs. -/
theorem canary_bitmask_div_cast_pcc_safe (a b : Nat)
    (ha : a < modPow2 32) (hb : b < modPow2 32) :
    let args : List Value := [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]
    SafeFrom bitmaskDivCastBody (initMachineState bitmaskDivCastBody args) ∧
    (∀ v, ReturnsFrom bitmaskDivCastBody
        (initMachineState bitmaskDivCastBody args) v →
      ∃ bits, v = .scalar ⟨bits, 8⟩ ∧ bits < modPow2 32) ∧
    MirNoUBTree (mirCallTree bitmaskDivCastBody args) := by
  intro args
  have hArgs : entryArgsOk (bitmaskDivCastBody.localDecls.drop 1)
      bitmaskDivCastArgSlots args :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound ha⟩,
     rfl, ⟨rfl, rfl, absVal_topInit_sound hb⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call bitmaskDivCast_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    match uint_valDenote_ubound (hi := modPow2 32 - 1) rfl hDen with
    | ⟨bits, hV, hLe⟩ =>
      exact ⟨bits, hV,
        Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 32) Nat.one_pos)⟩

/-! ## Canary 3: Signed `i32` Branch on a Copy-Temporary Guard -/

/-- `fn f(x: i32) -> i32 { if x >= 0 { x / 2 } else { 0 } }` as rustc lowers
it: the comparison reads a copy temporary `_3` that is moved into the
comparison and killed before the `switchInt`.
- `_0 : i32`; `_1 : i32` argument; `_2 : bool`; `_3 : i32` temporary. -/
def signedHalfBody : CapturedMir :=
  canaryBody "ai_pcc::signed_half" 1
    [canaryIntTy .i32, canaryIntTy .i32, canaryBoolTy, canaryIntTy .i32]
    [ -- bb0: `_2 = Ge(move _3, 0)` on `_3 = copy _1`
      canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 3) (.use (canaryCopy 1)),
        .assign (canaryPlace 2)
          (.binaryOp .ge (canaryMove 3) (canaryIConst .i32 0)),
        .storageDead 3] (.switchInt (canaryMove 2) ⟨[(0, 2)], 1⟩),
      -- bb1: `x >= 0`, so `x / 2` is UB-free and in `[0, 2^30)`
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .div (canaryCopy 1) (canaryIConst .i32 2))] (.goto 3),
      -- bb2: `x < 0`
      canaryBlock [.assign (canaryPlace 0) (.use (canaryIConst .i32 0))]
        (.goto 3),
      -- bb3: join and return
      canaryBlock [.storageDead 2] .return_ ]

/-- Argument slot: an arbitrary `i32` value. -/
def signedHalfArgSlots : List MirAbsSlot := [.sint .i32 (AbsVal.topInit 32)]

/-- Return postcondition: the bit pattern is in `[0, 2^30)`. -/
def signedHalfRetInv : MirAbsSlot :=
  .sint .i32 (reduceAbsVal 32
    ⟨.init, Tnum.top 32, .iv 0 (modPow2 30 - 1), .top⟩)

/-- Single-pass certificate check of `signedHalfBody` (CFG join at `bb3`) by
`rfl`. -/
theorem signedHalf_cert_ok :
    verifyMirCutpoints signedHalfBody
      (entryEnv signedHalfBody.localDecls signedHalfArgSlots)
      signedHalfRetInv [] [0, 1, 2, 3] = true := rfl

/-- End-to-end soundness of `signedHalfBody` for every `i32` input. -/
theorem canary_signed_half_pcc_safe (x : Nat) (hx : x < modPow2 32) :
    SafeFrom signedHalfBody (initMachineState signedHalfBody [.scalar ⟨x, 4⟩]) ∧
    (∀ v, ReturnsFrom signedHalfBody
        (initMachineState signedHalfBody [.scalar ⟨x, 4⟩]) v →
      ∃ bits, v = .scalar ⟨bits, 4⟩ ∧ bits < modPow2 30) ∧
    MirNoUBTree (mirCallTree signedHalfBody [.scalar ⟨x, 4⟩]) := by
  have hArgs : entryArgsOk (signedHalfBody.localDecls.drop 1)
      signedHalfArgSlots [.scalar ⟨x, 4⟩] :=
    ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩
  have h := verifyMirCutpoints_sound_call signedHalf_cert_ok hArgs
  refine ⟨h.1, ?_, h.2.2.1⟩
  intro v hRet
  match h.2.1 v hRet with
  | ⟨d, hD, hDen⟩ =>
    injection hD with hD
    subst hD
    match sint_valDenote_ubound (hi := modPow2 30 - 1) rfl hDen with
    | ⟨bits, hV, hLe⟩ =>
      exact ⟨bits, hV,
        Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 30) Nat.one_pos)⟩

/-! ## Trusted `VerificationResult` Certificates -/

/-- Audited claim for `stride8LoopBody`: called with no arguments, it is
UB-free and every normal return is exactly `1024`. -/
def stride8LoopClaim : Trusted.VerificationResult.Claim where
  body := stride8LoopBody
  pre args := args = []
  post _ ret := ret = .scalar ⟨1024, 8⟩

/-- `VerificationResult stride8LoopClaim`, from the `rfl` certificate. -/
theorem canary_stride8_loop_verificationResult :
    Trusted.VerificationResult.VerificationResult stride8LoopClaim :=
  verifyMirCutpoints_verificationResult (argSlots := [])
    stride8Loop_cert_ok
    (fun args hPre => by
      have hArgs : args = [] := hPre
      subst hArgs
      exact entryArgsOk_nil _)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        exact uint_valDenote_exact rfl hDen)

/-- Audited claim for `signedHalfBody`: for every `i32` argument it is
UB-free and every normal return is an `i32` with bit pattern `< 2^30`, even
with a non-empty linked callee table. -/
def signedHalfClaim : Trusted.VerificationResult.Claim where
  body := signedHalfBody
  pre args := ∃ x, x < modPow2 32 ∧ args = [.scalar ⟨x, 4⟩]
  post _ ret := ∃ bits, ret = .scalar ⟨bits, 4⟩ ∧ bits < modPow2 30
  callees := [stride8LoopBody]

/-- `VerificationResult signedHalfClaim`, from the `rfl` certificate. -/
theorem canary_signed_half_verificationResult :
    Trusted.VerificationResult.VerificationResult signedHalfClaim :=
  verifyMirCutpoints_verificationResult (argSlots := signedHalfArgSlots)
    signedHalf_cert_ok
    (fun args hPre => by
      match hPre with
      | ⟨x, hx, hArgs⟩ =>
        subst hArgs
        exact ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound hx⟩, True.intro⟩)
    (fun _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        match sint_valDenote_ubound (hi := modPow2 30 - 1) rfl hDen with
        | ⟨bits, hV, hLe⟩ =>
          exact ⟨bits, hV,
            Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 30) Nat.one_pos)⟩)

/-- Audited stateful claim for `bitmaskDivCastBody`: from any root-entry
memory and any `u32` inputs, execution is UB-free and returns `< 2^32`. -/
def bitmaskDivCastStatefulClaim :
    Trusted.VerificationResult.StatefulClaim where
  body := bitmaskDivCastBody
  pre args mem :=
    mem.callStack = [] ∧ mem.activeCallee = none ∧
    mem.activeProtectors = [] ∧
    ∃ a b, a < modPow2 32 ∧ b < modPow2 32 ∧
      args = [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩]
  post _ _ ret _ := ∃ bits, ret = .scalar ⟨bits, 8⟩ ∧ bits < modPow2 32

/-- `StatefulVerificationResult bitmaskDivCastStatefulClaim`, from the `rfl`
certificate. -/
theorem canary_bitmask_div_cast_statefulVerificationResult :
    Trusted.VerificationResult.StatefulVerificationResult
      bitmaskDivCastStatefulClaim :=
  verifyMirCutpoints_statefulVerificationResult
    (argSlots := bitmaskDivCastArgSlots) bitmaskDivCast_cert_ok
    (fun args mem hPre => by
      match hPre with
      | ⟨hCS, hCal, hProt, a, b, ha, hb, hArgs⟩ =>
        subst hArgs
        exact ⟨hCS, hCal, hProt,
          ⟨rfl, ⟨rfl, rfl, absVal_topInit_sound ha⟩,
           rfl, ⟨rfl, rfl, absVal_topInit_sound hb⟩, True.intro⟩⟩)
    (fun _ _ _ _ _ hRet => by
      match hRet with
      | ⟨d, hD, hDen⟩ =>
        injection hD with hD
        subst hD
        match uint_valDenote_ubound (hi := modPow2 32 - 1) rfl hDen with
        | ⟨bits, hV, hLe⟩ =>
          exact ⟨bits, hV,
            Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 32) Nat.one_pos)⟩)

/-! ## Positive Controls and CFG Joins -/

/-- `switchInt` diamond on an arbitrary `u8` argument `_1`: the `0` edge
refines `_1` to exactly `0`, so `_1 + 1` cannot overflow; the `otherwise`
edge refines `_1 ≠ 0`, so `_1 - 1` cannot underflow. Both arms join at
`bb3`. -/
def u8DiamondBody : CapturedMir :=
  canaryBody "ai_pcc::u8_diamond" 1 [canaryUintTy .u8, canaryUintTy .u8]
    [ canaryBlock [] (.switchInt (canaryCopy 1) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .addUnchecked (canaryCopy 1) (canaryUConst .u8 1))]
        (.goto 3),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .subUnchecked (canaryCopy 1) (canaryUConst .u8 1))]
        (.goto 3),
      canaryBlock [] .return_ ]

/-- Arbitrary `u8` argument. -/
def u8TopArgSlots : List MirAbsSlot := [.uint .u8 (AbsVal.topInit 8)]

/-- Return postcondition `_0 ≤ 254`. -/
def u8DiamondRetInv : MirAbsSlot :=
  .uint .u8 (reduceAbsVal 8 ⟨.init, Tnum.top 8, .iv 0 254, .top⟩)

/-- `move` of an argument into a temporary, then a checked add of a masked
value whose overflow flag is certified `false` by `assert`. -/
def moveCheckedBody : CapturedMir :=
  canaryBody "ai_pcc::move_checked" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8,
     canaryUintPairTy .u8]
    [ canaryBlock [.storageLive 2,
        .assign (canaryPlace 2) (.use (canaryMove 1)),
        .assign (canaryPlace 2)
          (.binaryOp .bitAnd (canaryCopy 2) (canaryUConst .u8 127)),
        .storageLive 3,
        .assign (canaryPlace 3)
          (.binaryOp .addWithOverflow (canaryCopy 2) (canaryUConst .u8 1))]
        (.assert (.copy ⟨3, [.field 1 canaryBoolTy]⟩) false 1 .unreachable),
      canaryBlock [.assign (canaryPlace 0)
          (.use (.copy ⟨3, [.field 0 (canaryUintTy .u8)]⟩)),
        .storageDead 3, .storageDead 2] .return_ ]

/-- Return postcondition `1 ≤ _0 ≤ 128`. -/
def moveCheckedRetInv : MirAbsSlot :=
  .uint .u8 (reduceAbsVal 8 ⟨.init, Tnum.top 8, .iv 1 128, .top⟩)

/-- Guard-refinement body: compares `_1 < 8` into `_2`, executes `midStmts`,
and branches on `_2` to `shlUnchecked(1, _1)` on the `true` arm. -/
def guardShiftBody (midStmts : List StatementKind) : CapturedMir :=
  canaryBody "ai_pcc::guard_shift_u8" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryBoolTy, canaryUintTy .u8]
    [ canaryBlock
        ([.storageLive 2, .storageLive 3,
          .assign (canaryPlace 2)
            (.binaryOp .lt (canaryCopy 1) (canaryUConst .u8 8))] ++ midStmts)
        (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .shlUnchecked (canaryUConst .u8 1) (canaryCopy 1))]
        (.goto 3),
      canaryBlock [.assign (canaryPlace 0) (.use (canaryUConst .u8 0))]
        (.goto 3),
      canaryBlock [.storageDead 3, .storageDead 2] .return_ ]

/-- Four-block diamond whose branches produce `[128, 12]` (straddling
`255 -> 0`) and `[0, 140]` (covering the full `u8` ring on join at `bb3`). -/
def diamondWrapJoinU8Body : CapturedMir :=
  canaryBody "ai_pcc::diamond_wrap_join_u8" 2
    [canaryUintTy .u8, canaryUintTy .u8, canaryBoolTy]
    [ canaryBlock [] (.switchInt (canaryCopy 2) ⟨[(0, 2)], 1⟩),
      canaryBlock [.assign (canaryPlace 0)
          (.binaryOp .add (canaryCopy 1) (canaryUConst .u8 128))] (.goto 3),
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] (.goto 3),
      canaryBlock [] .return_ ]

/-- Four-local `u8` body isolating a read of `_2` or `_1` into scratch `_3`
before returning initialized `_1` in `_0`. -/
def isolatedReadBody (src : Nat) : CapturedMir :=
  canaryBody "ai_pcc::isolated_read" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock [.storageLive 2, .storageLive 3,
        .assign (canaryPlace 3) (.use (canaryCopy src)),
        .assign (canaryPlace 0) (.use (canaryCopy 1))] .return_]

/-- Positive controls: the `stride8` header invariant is inductive under
re-checking with `checkMirCert` on the materialized table, a `switchInt`
diamond certifies both refined arms and their join, a `move` followed by
checked arithmetic and `assert` certifies, `Add(copy _1, move _1)` sequences
validly, an unrelated write preserves a relational guard, a straddling
`WrappedInterval` diamond join covers the full `u8` ring, and reading an
initialized local into scratch certifies. -/
theorem canary_positive_controls_and_cfg_joins :
    checkMirCert stride8LoopBody (entryEnv stride8LoopBody.localDecls [])
      stride8LoopRetInv
      (materializeCutpoints stride8LoopBody
        (entryEnv stride8LoopBody.localDecls []) stride8LoopCutpoints
        [0, 1, 2, 3, 4, 5]) = true ∧
    verifyMirCutpoints u8DiamondBody
      (entryEnv u8DiamondBody.localDecls u8TopArgSlots) u8DiamondRetInv []
      [0, 1, 2, 3] = true ∧
    verifyMirCutpoints moveCheckedBody
      (entryEnv moveCheckedBody.localDecls u8TopArgSlots) moveCheckedRetInv []
      [0, 1] = true ∧
    verifyMirCutpoints
      (canaryBody "ai_pcc::copy_then_move" 1 [canaryUintTy .u8, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0)
            (.binaryOp .add (canaryCopy 1) (canaryMove 1))] .return_])
      [.uint .u8 (AbsVal.uninit 8), .uint .u8 (AbsVal.topInit 8)]
      (.uint .u8 (AbsVal.topInit 8)) [] [0] = true ∧
    verifyMirCutpoints
      (guardShiftBody [.assign (canaryPlace 3) (.use (canaryUConst .u8 99))])
      (entryEnv (guardShiftBody []).localDecls u8TopArgSlots)
      (.uint .u8 (AbsVal.topInit 8)) [] [0, 1, 2, 3] = true ∧
    verifyMirCutpoints diamondWrapJoinU8Body
      [.uint .u8 (AbsVal.uninit 8),
       .uint .u8 (reduceAbsVal 8 ⟨.init, Tnum.top 8, .iv 0 140, .top⟩),
       .bool (.top .none)]
      (.uint .u8 (AbsVal.topInit 8)) [] [0, 1, 2, 3] = true ∧
    verifyMirCutpoints (isolatedReadBody 1)
      (entryEnv (isolatedReadBody 1).localDecls u8TopArgSlots)
      (.uint .u8 (AbsVal.topInit 8)) [] [0] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Fail-Closed Negative Suite -/

/-- One-block `u8` body `_0 = op(c1, c2)` (constants). -/
def u8ConstOpBody (op : BinOp) (c1 c2 : Nat) : CapturedMir :=
  canaryBody "ai_pcc::neg_const_op" 0 [canaryUintTy .u8]
    [canaryBlock [.assign (canaryPlace 0)
        (.binaryOp op (canaryUConst .u8 c1) (canaryUConst .u8 c2))] .return_]

/-- Straight-line `u8` certificate check with an unconstrained `u8`
postcondition. -/
def u8StraightLineOk (body : CapturedMir) (argSlots : List MirAbsSlot) :
    Bool :=
  verifyMirCutpoints body (entryEnv body.localDecls argSlots)
    (.uint .u8 (AbsVal.topInit 8)) [] [0]

/-- `_0 = copy _1` where `_1` was never made live. -/
def readDeadBody : CapturedMir :=
  canaryBody "ai_pcc::neg_read_dead" 0 [canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_]

/-- `_0 = copy _1` where `_1` is live but uninitialized. -/
def readUninitBody : CapturedMir :=
  canaryBody "ai_pcc::neg_read_uninit" 0 [canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock [.storageLive 1, .assign (canaryPlace 0) (.use (canaryCopy 1))]
      .return_]

/-- Return without writing `_0`. -/
def retUninitBody : CapturedMir :=
  canaryBody "ai_pcc::neg_ret_uninit" 0 [canaryUintTy .u8]
    [canaryBlock [] .return_]

/-- `_2 = move _1; _0 = copy _1` (use after move). -/
def useAfterMoveBody : CapturedMir :=
  canaryBody "ai_pcc::neg_use_after_move" 1
    [canaryUintTy .u8, canaryUintTy .u8, canaryUintTy .u8]
    [canaryBlock [.storageLive 2, .assign (canaryPlace 2) (.use (canaryMove 1)),
        .assign (canaryPlace 0) (.use (canaryCopy 1))] .return_]

/-- A reachable `unreachable` on the `otherwise` edge of an unrefined
`switchInt`. -/
def reachableTrapBody : CapturedMir :=
  canaryBody "ai_pcc::neg_reachable_trap" 1 [canaryUintTy .u8, canaryUintTy .u8]
    [ canaryBlock [] (.switchInt (canaryCopy 1) ⟨[(0, 1)], 2⟩),
      canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_,
      canaryBlock [] .unreachable ]

/-- `stride8LoopBody` with an off-by-eight bound `_1 < 1032`, under which the
header invariant `_1 ≤ 1024` is not inductive. -/
def stride8BadBoundBody : CapturedMir :=
  { stride8LoopBody with
    basicBlocks := stride8LoopBody.basicBlocks.set 1
      (canaryBlock [.assign (canaryPlace 2)
          (.binaryOp .lt (canaryCopy 1) (canaryUConst .u64 1032))]
        (.switchInt (canaryCopy 2) ⟨[(0, 3)], 2⟩)) }

/-- Fail-closed regression suite: unchecked overflow and underflow,
out-of-range unchecked shifts, division and remainder by zero, reads of dead
and uninitialized locals (including isolated scratch reads), an uninitialized
return, `StorageDead 0` on the return place, use after `move` (sequential and
within one binary operation), a clobbered relational guard, a reachable
`unreachable`, a violated return postcondition, a guard-carrying return
postcondition, a non-inductive loop invariant, a schedule that omits the loop
cutpoint, an `entryEnv` length mismatch, a cutpoint length mismatch, and an
unsupported MIR phase. -/
theorem canary_negative_fail_closed_pcc_tests :
    u8StraightLineOk (u8ConstOpBody .addUnchecked 255 1) [] = false ∧
    u8StraightLineOk (u8ConstOpBody .subUnchecked 0 1) [] = false ∧
    u8StraightLineOk (u8ConstOpBody .shlUnchecked 1 8) [] = false ∧
    u8StraightLineOk (u8ConstOpBody .shrUnchecked 1 8) [] = false ∧
    u8StraightLineOk (u8ConstOpBody .div 1 0) [] = false ∧
    u8StraightLineOk (u8ConstOpBody .rem 1 0) [] = false ∧
    u8StraightLineOk readDeadBody [] = false ∧
    u8StraightLineOk readUninitBody [] = false ∧
    u8StraightLineOk (isolatedReadBody 2) u8TopArgSlots = false ∧
    u8StraightLineOk retUninitBody [] = false ∧
    u8StraightLineOk
      (canaryBody "ai_pcc::neg_storage_dead_ret" 1
        [canaryUintTy .u8, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1)),
          .storageDead 0] .return_])
      u8TopArgSlots = false ∧
    u8StraightLineOk useAfterMoveBody u8TopArgSlots = false ∧
    u8StraightLineOk
      (canaryBody "ai_pcc::neg_move_then_copy" 1
        [canaryUintTy .u8, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0)
            (.binaryOp .add (canaryMove 1) (canaryCopy 1))] .return_])
      u8TopArgSlots = false ∧
    verifyMirCutpoints
      (guardShiftBody
        [.assign (canaryPlace 1)
          (.binaryOp .add (canaryCopy 1) (canaryUConst .u8 1))])
      (entryEnv (guardShiftBody []).localDecls u8TopArgSlots)
      (.uint .u8 (AbsVal.topInit 8)) [] [0, 1, 2, 3] = false ∧
    verifyMirCutpoints reachableTrapBody
      (entryEnv reachableTrapBody.localDecls u8TopArgSlots)
      (.uint .u8 (AbsVal.topInit 8)) [] [0, 1, 2] = false ∧
    verifyMirCutpoints u8DiamondBody
      (entryEnv u8DiamondBody.localDecls u8TopArgSlots)
      (.uint .u8 (reduceAbsVal 8 ⟨.init, Tnum.top 8, .iv 0 100, .top⟩)) []
      [0, 1, 2, 3] = false ∧
    verifyMirCutpoints stride8LoopBody (entryEnv stride8LoopBody.localDecls [])
      (.bool (.top (.ueqConst 1 .u64 1024))) stride8LoopCutpoints
      [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints stride8BadBoundBody
      (entryEnv stride8BadBoundBody.localDecls []) stride8LoopRetInv
      stride8LoopCutpoints [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints stride8LoopBody (entryEnv stride8LoopBody.localDecls [])
      stride8LoopRetInv [] [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints
      (canaryBody "ai_pcc::neg_entry_len" 1 [canaryUintTy .u8, canaryUintTy .u8]
        [canaryBlock [.assign (canaryPlace 0) (.use (canaryCopy 1))] .return_])
      [.uint .u8 (AbsVal.uninit 8), .uint .u8 (AbsVal.topInit 8), .dead]
      (.uint .u8 (AbsVal.topInit 8)) [] [0] = false ∧
    verifyMirCutpoints stride8LoopBody (entryEnv stride8LoopBody.localDecls [])
      stride8LoopRetInv [(1, [])] [0, 1, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints { stride8LoopBody with phase := .other "Analysis" }
      (entryEnv stride8LoopBody.localDecls []) stride8LoopRetInv
      stride8LoopCutpoints [0, 1, 2, 3, 4, 5] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `validRpoSchedule` Suite -/

/-- `validRpoSchedule` accepts the reverse postorder of `stride8LoopBody`
modulo its header cutpoint, and rejects schedules that are not headed by
`0`, are incomplete, repeat or overrun a block, run a non-cutpoint edge
backward, or carry duplicate or out-of-range cutpoint keys. -/
theorem canary_validRpoSchedule_tests :
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 2, 3, 4, 5] = true ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 3, 2, 5, 4] = true ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [1, 0, 2, 3, 4, 5] = false ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 2, 3, 4] = false ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 2, 3, 4, 4] = false ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 2, 3, 4, 6] = false ∧
    validRpoSchedule stride8LoopBody stride8LoopCutpoints
      [0, 1, 2, 5, 3, 4] = false ∧
    validRpoSchedule stride8LoopBody [] [0, 1, 2, 3, 4, 5] = false ∧
    validRpoSchedule stride8LoopBody
      (stride8LoopCutpoints ++ stride8LoopCutpoints) [0, 1, 2, 3, 4, 5] =
      false ∧
    validRpoSchedule stride8LoopBody [(6, [])] [0, 1, 2, 3, 4, 5] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AiPcc
