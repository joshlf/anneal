/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.ParametricCore.V2026Bridge

/-!
# End-to-End Fuel-Free Loop, Stage-Cut, and Sub-Byte Lens Canaries (`V2026_06_01`)

Every canary in this file executes real `Trusted.Rustc.V2026_06_01` `CapturedMir`
bodies and `Memory` values through the unmodified trusted operational semantics
(`MirSemantics.stepMirFn`, `PureMirExec.mirStep`, `MirFuelFree.MirWpConverges`,
`Trusted.VerificationResult.VerificationResult`, `decodeValueFromBytes`, Tree
Borrows `updateBorrowPermAtProj`) bridged via `Anneal.ParametricCore.V2026Bridge`.
-/

namespace Anneal.ParametricLoopInvAndSubLensTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.Lower (mirDefaultWP)
open Anneal.Rustc.V2026_06_01.SymbolicEval (mirNormalPost)
open Anneal.ParametricCore
open Anneal.ParametricCore.V2026Bridge

/-! ## 0. Shared Real `V2026_06_01` MIR AST Fixtures -/

private def u32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def u32PairLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr :=
      .scalarPair (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
    isUninhabited := false }

private def u8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def fatSliceLayout : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Rust `bool`: 1 byte, align 1, valid range `0..=1`. -/
private def boolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Rust `(u32, bool)` (the result type of `AddWithOverflow` / `SubWithOverflow`
on `u32`): size 8, align 4, fields at offsets `0` and `4`. -/
private def u32BoolPairLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr :=
      .scalarPair (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0,
    isUninhabited := false }

private def testLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [u32Layout, u32PairLayout, u8Layout, fatSliceLayout, boolLayout,
      u32BoolPairLayout] }

def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 2 }
def boolTy : Ty := { kind := .bool, layoutIdx := 4 }
private def u32BoolTy : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 5 }
private def pairU32Ty : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }
private def refMutSliceU8Ty : Ty := { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 3 }

private def u32C (n : Nat) : Operand :=
  .constant { ty := u32Ty, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

private def u8C (n : Nat) : Operand :=
  .constant { ty := u8Ty, val := .scalar (.int { bits := n, sizeBytes := 1 }) }

private def boolC (b : Bool) : Operand :=
  .constant { ty := boolTy, val := .scalar (.int { bits := if b then 1 else 0, sizeBytes := 1 }) }

private def pl (l : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := l, projection := proj }

private def mkSt (k : StatementKind) : Statement :=
  { kind := k, span := "ParametricLoopInvAndSubLensTests" }

private def mkBb (ss : List Statement) (t : TerminatorKind) : BasicBlockData :=
  { statements := ss, terminator := { kind := t, span := "ParametricLoopInvAndSubLensTests" },
    isCleanup := false }

private def decl (m : Mutability) (ty : Ty) : LocalDecl :=
  { mutability := m, ty := ty, debugName := none }

private def mkBody (name : String) (argCount : Nat) (ds : List LocalDecl)
    (bbs : List BasicBlockData) : CapturedMir :=
  { defPath := name
    phase := .runtimeOptimized
    role := .subject
    argCount := argCount
    localDecls := ds
    basicBlocks := bbs
    fnAbi := Anneal.PureMirExec.pureAdtMultiBlockBody.fnAbi
    layouts := testLayouts
    allocations := [] }

private theorem step_det_to {body : CapturedMir} {s : MachineState} (s' : MachineState)
    {stop : MachineState → Prop} {post : MirOutcome → Prop}
    (hStep : Anneal.PureMirExec.mirStep body s = .cont s')
    (hNext : wpUntilOk (ops := mirDetWpOps body) stop post s') :
    wpUntilOk (ops := mirDetWpOps body) stop post s := by
  refine wpUntil_step (ops := mirDetWpOps body) ?_
  change (mirDetStep body s).wp _ _ _
  rw [mirDetStep_step_iff.mpr hStep]
  exact hNext

private theorem step_det_done {body : CapturedMir} {s : MachineState} (out : MirOutcome)
    {stop : MachineState → Prop} {post : MirOutcome → Prop}
    (hDone : Anneal.PureMirExec.mirStep body s = .done out)
    (hPost : post out) :
    wpUntilOk (ops := mirDetWpOps body) stop post s := by
  refine wpUntil_step (ops := mirDetWpOps body) ?_
  change (mirDetStep body s).wp _ _ _
  rw [mirDetStep_done_iff.mpr hDone]
  exact hPost

private theorem wrapU32_of_lt {x : Nat} (h : x < 2 ^ 32) :
    wrapScalarBits x (scalarModulus 4) = x := by
  rw [Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## 1. Canary 1 — Fuel-Free Symbolic Loops over Real `V2026_06_01` `CapturedMir` -/

/-! ### 1A. Fuel-Free Symbolic `countDown` Accumulator Loop (`∀ n < 2^32`) -/

/-- Real multi-block `V2026_06_01` `CapturedMir`:
```rust
fn count_down(n: u32) -> u32 {
    let mut i: u32 = n;
    let mut acc: u32 = 0;
    while 0 < i {
        i = i - 1;
        acc = acc + 1;
    }
    acc
}
```
Locals: `_0: u32` (return), `_1: u32` (`n`), `_2: u32` (`i`), `_3: u32` (`acc`),
`_4: bool` (loop condition). -/
def countDownMirBody : CapturedMir :=
  mkBody "count_down" 1
    [decl .mut u32Ty, decl .not u32Ty, decl .mut u32Ty, decl .mut u32Ty, decl .mut boolTy]
    [mkBb
       [mkSt (.storageLive 2),
        mkSt (.assign (pl 2) (.use (.copy (pl 1)))),
        mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.use (u32C 0)))]
       (.goto 1),
     mkBb
       [mkSt (.storageLive 4),
        mkSt (.assign (pl 4) (.binaryOp .lt (u32C 0) (.copy (pl 2))))]
       (.switchInt (.copy (pl 4)) ⟨[(0, 3)], 2⟩),
     mkBb
       [mkSt (.storageDead 4),
        mkSt (.assign (pl 2) (.binaryOp .sub (.copy (pl 2)) (u32C 1))),
        mkSt (.assign (pl 3) (.binaryOp .add (.copy (pl 3)) (u32C 1)))]
       (.goto 1),
     mkBb
       [mkSt (.storageDead 4),
        mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
        mkSt (.storageDead 3),
        mkSt (.storageDead 2)]
       .return_]

private def countDownState (bb stmt : Nat)
    (l0 l1 l2 l3 l4 : LocalSlot) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [l0, l1, l2, l3, l4] }
    memory := {} }

private theorem countDown_entry_reach (n : Nat) :
    wpReach (ops := mirDetWpOps countDownMirBody)
      (· = countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead)
      (initMachineState countDownMirBody [.scalar ⟨n, 4⟩]) := by
  exact
    step_det_to (countDownState 0 1 .uninit (.init (.scalar ⟨n, 4⟩)) .uninit .dead .dead) rfl <|
    step_det_to (countDownState 0 2 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨n, 4⟩)) .dead .dead) rfl <|
    step_det_to (countDownState 0 3 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨n, 4⟩)) .uninit .dead) rfl <|
    step_det_to (countDownState 0 4 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) rfl <|
    step_det_to (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) rfl <|
    wpUntil_here (ops := mirDetWpOps countDownMirBody) rfl

private theorem countDown_step_iter (n i acc : Nat)
    (hSum : i + 1 + acc = n) (hLt : n < 2 ^ 32)
    (l4 : LocalSlot) (hL4 : l4 = .uninit ∨ l4 = .dead) :
    wpReach (ops := mirDetWpOps countDownMirBody)
      (· = countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨acc + 1, 4⟩)) .dead)
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) l4) := by
  have h1 : Anneal.PureMirExec.mirStep countDownMirBody
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) l4) =
      .cont (countDownState 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) .uninit) := by
    rcases hL4 with rfl | rfl <;> rfl
  have h5 : Anneal.PureMirExec.mirStep countDownMirBody
      (countDownState 2 1 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) .dead) =
      .cont (countDownState 2 2 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) .dead) := by
    change Anneal.PureMirExec.Step.cont (countDownState 2 2 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨wrapScalarBits i (scalarModulus 4), 4⟩))
      (.init (.scalar ⟨acc, 4⟩)) .dead) = _
    rw [wrapU32_of_lt (by omega)]
  have h6 : Anneal.PureMirExec.mirStep countDownMirBody
      (countDownState 2 2 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) .dead) =
      .cont (countDownState 2 3 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨acc + 1, 4⟩)) .dead) := by
    change Anneal.PureMirExec.Step.cont (countDownState 2 3 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨i, 4⟩))
      (.init (.scalar ⟨wrapScalarBits (acc + 1) (scalarModulus 4), 4⟩)) .dead) = _
    rw [wrapU32_of_lt (by omega)]
  exact
    step_det_to _ h1 <|
    step_det_to (countDownState 1 2 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) (.init (.scalar ⟨1, 1⟩))) rfl <|
    step_det_to (countDownState 2 0 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) (.init (.scalar ⟨1, 1⟩))) rfl <|
    step_det_to (countDownState 2 1 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨i + 1, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) .dead) rfl <|
    step_det_to _ h5 <|
    step_det_to _ h6 <|
    step_det_to (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨acc + 1, 4⟩)) .dead) rfl <|
    wpUntil_here (ops := mirDetWpOps countDownMirBody) rfl

private theorem countDown_exit_ok (n : Nat) (l4 : LocalSlot)
    (hL4 : l4 = .uninit ∨ l4 = .dead) :
    wpStateOk (ops := mirDetWpOps countDownMirBody)
      (mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {}))
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) l4) := by
  have h1 : Anneal.PureMirExec.mirStep countDownMirBody
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) l4) =
      .cont (countDownState 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) .uninit) := by
    rcases hL4 with rfl | rfl <;> rfl
  exact
    step_det_to _ h1 <|
    step_det_to (countDownState 1 2 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 1⟩))) rfl <|
    step_det_to (countDownState 3 0 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 1⟩))) rfl <|
    step_det_to (countDownState 3 1 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) .dead) rfl <|
    step_det_to (countDownState 3 2 (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) .dead) rfl <|
    step_det_to (countDownState 3 3 (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) .dead .dead) rfl <|
    step_det_to (countDownState 3 4 (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
      .dead .dead .dead) rfl <|
    step_det_done (.normal (.scalar ⟨n, 4⟩, {})) rfl ⟨rfl, rfl⟩

/-- **Canary 1A (Fuel-Free Symbolic `countDown`, `∀ n < 2^32`)**:
Proved via `ParametricCore.wpLoop_countdown` with ZERO hardcoded fuel for every
symbolic `n < 2^32`. -/
theorem canary1a_countDown_wpStateOk (n : Nat) (hLt : n < 2 ^ 32) :
    wpStateOk (ops := mirDetWpOps countDownMirBody)
      (mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {}))
      (initMachineState countDownMirBody [.scalar ⟨n, 4⟩]) := by
  let post : MirOutcome → Prop :=
    mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {})
  let Inv : Nat → MachineState → Prop := fun rem s =>
    ∃ acc l4, rem + acc = n ∧ (l4 = .uninit ∨ l4 = .dead) ∧
      s = countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨rem, 4⟩)) (.init (.scalar ⟨acc, 4⟩)) l4
  let exitP : MachineState → Prop := fun s =>
    ∃ l4, (l4 = .uninit ∨ l4 = .dead) ∧
      s = countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨n, 4⟩)) l4
  have hLoop : wpUntilOk (ops := mirDetWpOps countDownMirBody) exitP post
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) :=
    wpLoop_countdown (ops := mirDetWpOps countDownMirBody) (Inv := Inv) (exit := exitP)
      (onDone := post) (onFault := fun _ => False)
      (fun _ ⟨acc, l4, hSum, hL4, hEq⟩ => by
        have hAcc : acc = n := by omega
        subst hAcc
        exact ⟨l4, hL4, hEq⟩)
      (fun rem _ ⟨acc, l4, hSum, hL4, hEq⟩ => by
        subst hEq
        refine wpUntil_mono (ops := mirDetWpOps countDownMirBody)
          (fun _ hS' => Or.inl ⟨acc + 1, .dead, by omega, Or.inr rfl, hS'⟩)
          (fun _ hF => False.elim hF) (fun _ hF => False.elim hF) ?_
        exact countDown_step_iter n rem acc hSum hLt l4 hL4)
      n _ ⟨0, .dead, by omega, Or.inr rfl, rfl⟩
  have hFromHeader : wpStateOk (ops := mirDetWpOps countDownMirBody) post
      (countDownState 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) :=
    wpUntil_bind (ops := mirDetWpOps countDownMirBody) hLoop fun _ ⟨l4, hL4, hEq⟩ => by
      subst hEq
      exact countDown_exit_ok n l4 hL4
  exact wpUntil_bind (ops := mirDetWpOps countDownMirBody)
    (wpUntil_mono (ops := mirDetWpOps countDownMirBody) (fun _ h => h)
      (fun _ hF => False.elim hF) (fun _ hF => False.elim hF) (countDown_entry_reach n))
    (fun _ hEq => by subst hEq; exact hFromHeader)

/-- Fuel-free `MirWpConverges` for symbolic `countDownMirBody` (`∀ n < 2^32`). -/
theorem canary1a_countDown_mirWpConverges (n : Nat) (hLt : n < 2 ^ 32) :
    MirWpConverges countDownMirBody
      (initMachineState countDownMirBody [.scalar ⟨n, 4⟩])
      (mirNormalPost (fun ret _ => ret = .scalar ⟨n, 4⟩)) :=
  MirWpConverges.mono
    (fun out hOut => by
      cases out with
      | panic | abort => exact False.elim hOut
      | normal p => exact hOut.1)
    (mirWpConverges_of_wpStateOk (canary1a_countDown_wpStateOk n hLt))

/-- Coalgebraic total-correctness `DWP` for `countDownMirBody` (`∀ n < 2^32`),
transported through `mirStrictDetWpOps_refines_mirCoalWpOps` + `dwp_of_coalWpStateOk`. -/
theorem canary1a_countDown_dwp (n : Nat) (hLt : n < 2 ^ 32) :
    DWP mirDefaultWP
      (mirTree countDownMirBody (initMachineState countDownMirBody [.scalar ⟨n, 4⟩]))
      (fun out _ => mirNormalPost (fun ret _ => ret = .scalar ⟨n, 4⟩) out) PUnit.unit := by
  have hDet : wpStateOk (ops := mirDetWpOps countDownMirBody)
      (mirNormalPost (fun ret _ => ret = .scalar ⟨n, 4⟩))
      (initMachineState countDownMirBody [.scalar ⟨n, 4⟩]) :=
    wpOutcome_mono (ops := mirDetWpOps countDownMirBody)
      (fun out hOut => by
        cases out with
        | panic | abort => exact False.elim hOut
        | normal p => exact hOut.1)
      (fun _ h => h) (canary1a_countDown_wpStateOk n hLt)
  have hStrict := wpStateOk_mirDet_iff_strictDet.mp hDet
  have hCoal := wpOutcome_of_refines (mirStrictDetWpOps_refines_mirCoalWpOps countDownMirBody) hStrict
  exact dwp_of_coalWpStateOk hCoal

def countDownClaim : Claim where
  body := countDownMirBody
  callees := []
  pre args := ∃ n : Nat, n < 2 ^ 32 ∧ args = [.scalar ⟨n, 4⟩]
  post args ret := ∃ n : Nat, args = [.scalar ⟨n, 4⟩] ∧ ret = .scalar ⟨n, 4⟩

/-- **Trusted `VerificationResult` for symbolic `countDownMirBody` (`∀ n < 2^32`)**. -/
theorem canary1a_countDown_verificationResult : VerificationResult countDownClaim :=
  verifyMirNoPanic_of_wpStateOk countDownClaim fun args ⟨n, hLt, hArgs⟩ => by
    subst hArgs
    refine wpOutcome_mono (ops := mirDetWpOps countDownMirBody) ?_ (fun _ h => h)
      (canary1a_countDown_wpStateOk n hLt)
    intro out hOut
    cases out with
    | panic | abort => exact False.elim hOut
    | normal p => exact ⟨n, rfl, hOut.1⟩

def countDownTotalClaim : TotalClaim where
  body := countDownMirBody
  callees := []
  pre args mem := mem = {} ∧ ∃ n : Nat, n < 2 ^ 32 ∧ args = [.scalar ⟨n, 4⟩]
  post args mem ret mem' :=
    mem' = mem ∧ ∃ n : Nat, args = [.scalar ⟨n, 4⟩] ∧ ret = .scalar ⟨n, 4⟩

/-- **Trusted `TotalVerificationResult` for symbolic `countDownMirBody` (`∀ n < 2^32`)**. -/
theorem canary1a_countDown_totalVerificationResult :
    TotalVerificationResult countDownTotalClaim :=
  verifyTotalMir_of_wpStateOk countDownTotalClaim fun args mem ⟨hMem, n, hLt, hArgs⟩ => by
    subst hMem hArgs
    refine wpOutcome_mono (ops := mirDetWpOps countDownMirBody) ?_ (fun _ h => h)
      (canary1a_countDown_wpStateOk n hLt)
    intro out hOut
    cases out with
    | panic | abort => exact False.elim hOut
    | normal p => exact ⟨hOut.2, n, rfl, hOut.1⟩

/-- **Canary 1A (Deterministic → Coalgebraic `MirWpOps.Refines` + `DWP` + `DWLP`)**:
Lifts the fuel-free deterministic loop proof `canary1a_countDown_wpStateOk`
along the `MirWpOps.Refines` chain (`mirDetWpOps ↔ mirStrictDetWpOps ≤
mirNoCallCoalWpOps ≤ mirCoalWpOps`) into coalgebraic `MirWpConverges`, total
`DWP mirDefaultWP`, and partial `DWLP mirDefaultWP` (`wlpOutcome_of_wpOutcome`
+ `dwlp_of_coalWlpOutcome`) for ALL symbolic `n < 2^32`. -/
theorem canary1a_countDown_coalWp_refines_dwp_dwlp (n : Nat) (hLt : n < 2 ^ 32) :
    let post : MirOutcome → Prop :=
      mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {})
    let s0 := initMachineState countDownMirBody [.scalar ⟨n, 4⟩]
    wpStateOk (ops := mirNoCallCoalWpOps countDownMirBody) post s0 ∧
    wpStateOk (ops := mirCoalWpOps countDownMirBody) post s0 ∧
    MirWpConverges countDownMirBody s0 post ∧
    DWP mirDefaultWP (mirTree countDownMirBody s0) (fun out _ => post out) PUnit.unit ∧
    DWLP mirDefaultWP (mirTree countDownMirBody s0) (fun out _ => post out) PUnit.unit := by
  intro post s0
  have hStrict : wpStateOk (ops := mirStrictDetWpOps countDownMirBody) post s0 :=
    wpStateOk_mirDet_iff_strictDet.mp (canary1a_countDown_wpStateOk n hLt)
  have hNoCall : wpStateOk (ops := mirNoCallCoalWpOps countDownMirBody) post s0 :=
    wpOutcome_of_refines (mirStrictDetWpOps_refines_mirNoCallCoalWpOps countDownMirBody) hStrict
  have hCoal : wpStateOk (ops := mirCoalWpOps countDownMirBody) post s0 :=
    wpOutcome_of_refines (mirNoCallCoalWpOps_refines_mirCoalWpOps countDownMirBody) hNoCall
  exact ⟨hNoCall, hCoal,
    mirWpConverges_of_noCallCoalWpStateOk hNoCall,
    dwp_of_coalWpStateOk hCoal,
    dwlp_of_coalWlpOutcome (wlpOutcome_of_wpOutcome (ops := mirCoalWpOps countDownMirBody) hCoal)⟩

/-! ### 1B. Fuel-Free Symbolic Early-Return Loop (`wpLoop_early_return_rank`) -/

/-- Real multi-block `V2026_06_01` `CapturedMir` with genuine mid-loop early return:
```rust
fn find_or_zero(mut i: u32, target: u32) -> u32 {
    while i != 0 {
        if i == target { return i; }
        i = i - 1;
    }
    0
}
```
Locals: `_0: u32`, `_1: u32` (`i`), `_2: u32` (`target`), `_3: bool` (`i == target`). -/
def findTargetMirBody : CapturedMir :=
  mkBody "find_or_zero" 2
    [decl .mut u32Ty, decl .mut u32Ty, decl .not u32Ty, decl .mut boolTy]
    [mkBb [] (.switchInt (.copy (pl 1)) ⟨[(0, 3)], 1⟩),
     mkBb
       [mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.binaryOp .eq (.copy (pl 1)) (.copy (pl 2))))]
       (.switchInt (.copy (pl 3)) ⟨[(0, 2)], 4⟩),
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 1) (.binaryOp .sub (.copy (pl 1)) (u32C 1)))]
       (.goto 0),
     mkBb [mkSt (.assign (pl 0) (.use (u32C 0)))] .return_,
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 0) (.use (.copy (pl 1))))]
       .return_]

private def mirState4 (bb stmt : Nat)
    (l0 l1 l2 l3 : LocalSlot) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [l0, l1, l2, l3] }
    memory := {} }

private def findTargetSpec (n target : Nat) : Nat :=
  if 0 < target ∧ target ≤ n then target else 0

/-- **Canary 1B (Fuel-Free Symbolic Early-Return Loop, `∀ n target < 2^32`)**:
Discharged via `ParametricCore.wpLoop_early_return_rank` separating normal loop
exhaustion (`bb3`) from genuine mid-loop early return (`bb4`). -/
theorem canary1b_findTarget_wpStateOk (n target : Nat)
    (hN : n < 2 ^ 32) (_hT : target < 2 ^ 32) :
    wpStateOk (ops := mirDetWpOps findTargetMirBody)
      (mirNormalPost (fun ret mem' => ret = .scalar ⟨findTargetSpec n target, 4⟩ ∧ mem' = {}))
      (initMachineState findTargetMirBody [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩]) := by
  let post : MirOutcome → Prop :=
    mirNormalPost (fun ret mem' => ret = .scalar ⟨findTargetSpec n target, 4⟩ ∧ mem' = {})
  let Inv : Nat → MachineState → Prop := fun i s =>
    ∃ l3, i ≤ n ∧ (0 < target ∧ target ≤ n → target ≤ i) ∧
      (l3 = .uninit ∨ l3 = .dead) ∧
      s = mirState4 0 0 .uninit (.init (.scalar ⟨i, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) l3
  let normalExit : MachineState → Prop := fun s =>
    ¬ (0 < target ∧ target ≤ n) ∧
      ∃ l3, s = mirState4 3 0 .uninit (.init (.scalar ⟨0, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) l3
  let earlyClean : MachineState → Prop := fun s =>
    (0 < target ∧ target ≤ n) ∧
      s = mirState4 4 0 .uninit (.init (.scalar ⟨target, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨1, 1⟩))
  refine wpLoop_early_return_rank (ops := mirDetWpOps findTargetMirBody)
    (rank := fun i : Nat => i) (Inv := Inv) (normalExit := normalExit)
    (earlyClean := earlyClean) (onDone := post) (onFault := fun _ => False) ?_ ?_ ?_ n
    (initMachineState findTargetMirBody [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩])
    ⟨.dead, Nat.le_refl n, fun h => h.2, Or.inr rfl, rfl⟩
  · intro i s ⟨l3, hILe, hTargetIn, hL3, hEq⟩
    subst hEq
    cases i with
    | zero =>
      refine Or.inr (Or.inr ?_)
      have hNotIn : ¬ (0 < target ∧ target ≤ n) := by
        intro h; have := hTargetIn h; omega
      exact step_det_to (mirState4 3 0 .uninit (.init (.scalar ⟨0, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) l3) rfl
        (wpUntil_here (ops := mirDetWpOps findTargetMirBody) (Or.inl ⟨hNotIn, l3, rfl⟩))
    | succ k =>
      refine Or.inr (Or.inr ?_)
      have hSw : Anneal.PureMirExec.mirStep findTargetMirBody
          (mirState4 0 0 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) l3) =
          .cont (mirState4 1 0 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) l3) := rfl
      have hLive : Anneal.PureMirExec.mirStep findTargetMirBody
          (mirState4 1 0 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) l3) =
          .cont (mirState4 1 1 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) .uninit) := by
        rcases hL3 with rfl | rfl <;> rfl
      by_cases hHit : k + 1 = target
      · have hEqTrue : Nat.beq (k + 1) target = true := by
          rw [hHit]; exact Nat.beq_refl target
        have hCmp : Anneal.PureMirExec.mirStep findTargetMirBody
            (mirState4 1 1 .uninit (.init (.scalar ⟨k + 1, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) .uninit) =
            .cont (mirState4 1 2 .uninit (.init (.scalar ⟨k + 1, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨1, 1⟩))) := by
          change Anneal.PureMirExec.Step.cont (mirState4 1 2 .uninit
            (.init (.scalar ⟨k + 1, 4⟩)) (.init (.scalar ⟨target, 4⟩))
            (.init (.scalar (boolToScalar (Nat.beq (k + 1) target))))) = _
          rw [hEqTrue]; rfl
        have hIn : 0 < target ∧ target ≤ n := by omega
        exact
          step_det_to _ hSw <|
          step_det_to _ hLive <|
          step_det_to _ hCmp <|
          step_det_to (mirState4 4 0 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨1, 1⟩))) rfl <|
          wpUntil_here (ops := mirDetWpOps findTargetMirBody)
            (Or.inr (Or.inl ⟨hIn, by rw [hHit]⟩))
      · have hEqFalse : Nat.beq (k + 1) target = false := natBeq_false_of_not_eq hHit
        have hCmp : Anneal.PureMirExec.mirStep findTargetMirBody
            (mirState4 1 1 .uninit (.init (.scalar ⟨k + 1, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) .uninit) =
            .cont (mirState4 1 2 .uninit (.init (.scalar ⟨k + 1, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨0, 1⟩))) := by
          change Anneal.PureMirExec.Step.cont (mirState4 1 2 .uninit
            (.init (.scalar ⟨k + 1, 4⟩)) (.init (.scalar ⟨target, 4⟩))
            (.init (.scalar (boolToScalar (Nat.beq (k + 1) target))))) = _
          rw [hEqFalse]; rfl
        have hSubStep : Anneal.PureMirExec.mirStep findTargetMirBody
            (mirState4 2 1 .uninit (.init (.scalar ⟨k + 1, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) .dead) =
            .cont (mirState4 2 2 .uninit (.init (.scalar ⟨k, 4⟩))
              (.init (.scalar ⟨target, 4⟩)) .dead) := by
          change Anneal.PureMirExec.Step.cont (mirState4 2 2 .uninit
            (.init (.scalar ⟨wrapScalarBits k (scalarModulus 4), 4⟩))
            (.init (.scalar ⟨target, 4⟩)) .dead) = _
          rw [wrapU32_of_lt (by omega)]
        exact
          step_det_to _ hSw <|
          step_det_to _ hLive <|
          step_det_to _ hCmp <|
          step_det_to (mirState4 2 0 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨0, 1⟩))) rfl <|
          step_det_to (mirState4 2 1 .uninit (.init (.scalar ⟨k + 1, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) .dead) rfl <|
          step_det_to _ hSubStep <|
          step_det_to (mirState4 0 0 .uninit (.init (.scalar ⟨k, 4⟩))
            (.init (.scalar ⟨target, 4⟩)) .dead) rfl <|
          wpUntil_here (ops := mirDetWpOps findTargetMirBody)
            (Or.inr (Or.inr ⟨k, Nat.lt_succ_self k, .dead, by omega,
              fun h => by have := hTargetIn h; omega, Or.inr rfl, rfl⟩))
  · intro s ⟨hNotIn, l3, hEq⟩
    subst hEq
    have hSpec : findTargetSpec n target = 0 := by
      unfold findTargetSpec; rw [ite_eq_right hNotIn]
    exact
      step_det_to (mirState4 3 1 (.init (.scalar ⟨0, 4⟩)) (.init (.scalar ⟨0, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) l3) rfl <|
      step_det_done (.normal (.scalar ⟨0, 4⟩, {})) rfl ⟨by rw [hSpec], rfl⟩
  · intro s ⟨hIn, hEq⟩
    subst hEq
    have hSpec : findTargetSpec n target = target := by
      unfold findTargetSpec; rw [ite_eq_left hIn]
    exact
      step_det_to (mirState4 4 1 .uninit (.init (.scalar ⟨target, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) .dead) rfl <|
      step_det_to (mirState4 4 2 (.init (.scalar ⟨target, 4⟩))
        (.init (.scalar ⟨target, 4⟩)) (.init (.scalar ⟨target, 4⟩)) .dead) rfl <|
      step_det_done (.normal (.scalar ⟨target, 4⟩, {})) rfl ⟨by rw [hSpec], rfl⟩

theorem canary1b_findTarget_mirWpConverges (n target : Nat)
    (hN : n < 2 ^ 32) (hT : target < 2 ^ 32) :
    MirWpConverges findTargetMirBody
      (initMachineState findTargetMirBody [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩])
      (mirNormalPost (fun ret _ => ret = .scalar ⟨findTargetSpec n target, 4⟩)) :=
  MirWpConverges.mono
    (fun out hOut => by
      cases out with
      | panic | abort => exact False.elim hOut
      | normal p => exact hOut.1)
    (mirWpConverges_of_wpStateOk (canary1b_findTarget_wpStateOk n target hN hT))

def findTargetClaim : Claim where
  body := findTargetMirBody
  callees := []
  pre args := ∃ n target : Nat, n < 2 ^ 32 ∧ target < 2 ^ 32 ∧
    args = [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩]
  post args ret := ∃ n target : Nat,
    args = [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩] ∧
    ret = .scalar ⟨findTargetSpec n target, 4⟩

theorem canary1b_findTarget_verificationResult : VerificationResult findTargetClaim :=
  verifyMirNoPanic_of_wpStateOk findTargetClaim fun args ⟨n, target, hN, hT, hArgs⟩ => by
    subst hArgs
    refine wpOutcome_mono (ops := mirDetWpOps findTargetMirBody) ?_ (fun _ h => h)
      (canary1b_findTarget_wpStateOk n target hN hT)
    intro out hOut
    cases out with
    | panic | abort => exact False.elim hOut
    | normal p => exact ⟨n, target, rfl, hOut.1⟩

def findTargetTotalClaim : TotalClaim where
  body := findTargetMirBody
  callees := []
  pre args mem := mem = {} ∧ ∃ n target : Nat, n < 2 ^ 32 ∧ target < 2 ^ 32 ∧
    args = [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩]
  post args mem ret mem' := mem' = mem ∧ ∃ n target : Nat,
    args = [.scalar ⟨n, 4⟩, .scalar ⟨target, 4⟩] ∧
    ret = .scalar ⟨findTargetSpec n target, 4⟩

/-- **Trusted `TotalVerificationResult` for symbolic early-return
`findTargetMirBody` (`∀ n, target < 2^32`)**, proving termination + exact
return value + memory preservation without any fuel parameter. -/
theorem canary1b_findTarget_totalVerificationResult :
    TotalVerificationResult findTargetTotalClaim :=
  verifyTotalMir_of_wpStateOk findTargetTotalClaim
    fun args mem ⟨hMem, n, target, hN, hT, hArgs⟩ => by
      subst hMem hArgs
      refine wpOutcome_mono (ops := mirDetWpOps findTargetMirBody) ?_ (fun _ h => h)
        (canary1b_findTarget_wpStateOk n target hN hT)
      intro out hOut
      cases out with
      | panic | abort => exact False.elim hOut
      | normal p => exact ⟨hOut.2, n, target, rfl, hOut.1⟩

/-! ### 1C. Fuel-Free Symbolic Upward-Counting Loop (`wpLoop_nat`) -/

/-- Real multi-block `V2026_06_01` `CapturedMir` counting upward (`for i in 0..n`):
```rust
fn count_up(n: u32) -> u32 {
    let mut i: u32 = 0;
    while i < n { i = i + 1; }
    i
}
```
Locals: `_0: u32`, `_1: u32` (`n`), `_2: u32` (`i`), `_3: bool` (`i < n`). -/
def countUpMirBody : CapturedMir :=
  mkBody "count_up" 1
    [decl .mut u32Ty, decl .not u32Ty, decl .mut u32Ty, decl .mut boolTy]
    [mkBb
       [mkSt (.storageLive 2),
        mkSt (.assign (pl 2) (.use (u32C 0)))]
       (.goto 1),
     mkBb
       [mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.binaryOp .lt (.copy (pl 2)) (.copy (pl 1))))]
       (.switchInt (.copy (pl 3)) ⟨[(0, 3)], 2⟩),
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 2) (.binaryOp .add (.copy (pl 2)) (u32C 1)))]
       (.goto 1),
     mkBb
       [mkSt (.storageDead 3),
        mkSt (.assign (pl 0) (.use (.copy (pl 2)))),
        mkSt (.storageDead 2)]
       .return_]

/-- **Canary 1C (Fuel-Free Symbolic Upward Loop, `∀ n < 2^32`)**:
Discharged via `ParametricCore.wpLoop_nat` climbing `0 → 1 → ... → n`. -/
theorem canary1c_countUp_wpStateOk (n : Nat) (hLt : n < 2 ^ 32) :
    wpStateOk (ops := mirDetWpOps countUpMirBody)
      (mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {}))
      (initMachineState countUpMirBody [.scalar ⟨n, 4⟩]) := by
  let post : MirOutcome → Prop :=
    mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {})
  let Inv : Nat → MachineState → Prop := fun i s =>
    ∃ l3, (l3 = .uninit ∨ l3 = .dead) ∧
      s = mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨i, 4⟩)) l3
  let exitP : MachineState → Prop := fun s =>
    ∃ l3, (l3 = .uninit ∨ l3 = .dead) ∧
      s = mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
        (.init (.scalar ⟨n, 4⟩)) l3
  have hLoop : wpUntilOk (ops := mirDetWpOps countUpMirBody) exitP post
      (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) :=
    wpLoop_nat (ops := mirDetWpOps countUpMirBody) (Inv := Inv) (exit := exitP)
      (onDone := post) (onFault := fun _ => False) (hi := n)
      (fun _ ⟨l3, hL3, hEq⟩ => ⟨l3, hL3, hEq⟩)
      (fun i s hILt ⟨l3, hL3, hEq⟩ => by
        subst hEq
        have hLive : Anneal.PureMirExec.mirStep countUpMirBody
            (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i, 4⟩)) l3) =
            .cont (mirState4 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i, 4⟩)) .uninit) := by
          rcases hL3 with rfl | rfl <;> rfl
        have hNotLe : Nat.ble n i = false := natBle_false_of_not_le (by omega)
        have hCmp : Anneal.PureMirExec.mirStep countUpMirBody
            (mirState4 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i, 4⟩)) .uninit) =
            .cont (mirState4 1 2 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨1, 1⟩))) := by
          change Anneal.PureMirExec.Step.cont (mirState4 1 2 .uninit
            (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨i, 4⟩))
            (.init (.scalar (boolToScalar (Bool.not (Nat.ble n i)))))) = _
          rw [hNotLe]; rfl
        have hInc : Anneal.PureMirExec.mirStep countUpMirBody
            (mirState4 2 1 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i, 4⟩)) .dead) =
            .cont (mirState4 2 2 .uninit (.init (.scalar ⟨n, 4⟩))
              (.init (.scalar ⟨i + 1, 4⟩)) .dead) := by
          change Anneal.PureMirExec.Step.cont (mirState4 2 2 .uninit
            (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨wrapScalarBits (i + 1) (scalarModulus 4), 4⟩)) .dead) = _
          rw [wrapU32_of_lt (by omega)]
        exact
          step_det_to _ hLive <|
          step_det_to _ hCmp <|
          step_det_to (mirState4 2 0 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨i, 4⟩)) (.init (.scalar ⟨1, 1⟩))) rfl <|
          step_det_to (mirState4 2 1 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨i, 4⟩)) .dead) rfl <|
          step_det_to _ hInc <|
          step_det_to (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨i + 1, 4⟩)) .dead) rfl <|
          wpUntil_here (ops := mirDetWpOps countUpMirBody) (Or.inr ⟨.dead, Or.inr rfl, rfl⟩))
      0 (Nat.zero_le n) _ ⟨.dead, Or.inr rfl, rfl⟩
  have hFromHeader : wpStateOk (ops := mirDetWpOps countUpMirBody) post
      (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 4⟩)) .dead) :=
    wpUntil_bind (ops := mirDetWpOps countUpMirBody) hLoop fun _ ⟨l3, hL3, hEq⟩ => by
      subst hEq
      have hLive : Anneal.PureMirExec.mirStep countUpMirBody
          (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨n, 4⟩)) l3) =
          .cont (mirState4 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨n, 4⟩)) .uninit) := by
        rcases hL3 with rfl | rfl <;> rfl
      have hLeSelf : Nat.ble n n = true := Nat.ble_eq_true_of_le (Nat.le_refl n)
      have hCmp : Anneal.PureMirExec.mirStep countUpMirBody
          (mirState4 1 1 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨n, 4⟩)) .uninit) =
          .cont (mirState4 1 2 .uninit (.init (.scalar ⟨n, 4⟩))
            (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 1⟩))) := by
        change Anneal.PureMirExec.Step.cont (mirState4 1 2 .uninit
          (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
          (.init (.scalar (boolToScalar (Bool.not (Nat.ble n n)))))) = _
        rw [hLeSelf]; rfl
      exact
        step_det_to _ hLive <|
        step_det_to _ hCmp <|
        step_det_to (mirState4 3 0 .uninit (.init (.scalar ⟨n, 4⟩))
          (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨0, 1⟩))) rfl <|
        step_det_to (mirState4 3 1 .uninit (.init (.scalar ⟨n, 4⟩))
          (.init (.scalar ⟨n, 4⟩)) .dead) rfl <|
        step_det_to (mirState4 3 2 (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
          (.init (.scalar ⟨n, 4⟩)) .dead) rfl <|
        step_det_to (mirState4 3 3 (.init (.scalar ⟨n, 4⟩)) (.init (.scalar ⟨n, 4⟩))
          .dead .dead) rfl <|
        step_det_done (.normal (.scalar ⟨n, 4⟩, {})) rfl ⟨rfl, rfl⟩
  exact
    step_det_to (mirState4 0 1 .uninit (.init (.scalar ⟨n, 4⟩)) .uninit .dead) rfl <|
    step_det_to (mirState4 0 2 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) .dead) rfl <|
    step_det_to (mirState4 1 0 .uninit (.init (.scalar ⟨n, 4⟩))
      (.init (.scalar ⟨0, 4⟩)) .dead) rfl <|
    hFromHeader

theorem canary1c_countUp_mirWpConverges (n : Nat) (hLt : n < 2 ^ 32) :
    MirWpConverges countUpMirBody
      (initMachineState countUpMirBody [.scalar ⟨n, 4⟩])
      (mirNormalPost (fun ret _ => ret = .scalar ⟨n, 4⟩)) :=
  MirWpConverges.mono
    (fun out hOut => by
      cases out with
      | panic | abort => exact False.elim hOut
      | normal p => exact hOut.1)
    (mirWpConverges_of_wpStateOk (canary1c_countUp_wpStateOk n hLt))

/-! ### 1D. Fuel-Free Symbolic `countDown` with Debug-Mode Checked Arithmetic

Rustc with `overflow-checks = on` (debug profile) lowers `i -= 1` and
`acc += 1` to `SubWithOverflow` / `AddWithOverflow` producing a `(u32, bool)`
pair followed by an `Assert` terminator on the overflow flag. Canary 1A uses the
release-mode wrapping `Sub` / `Add`; this canary proves, for ALL `n < 2^32`
with ZERO fuel, that neither overflow assertion can fire, so the debug-mode
body never panics and returns `n`. -/

/-- Real multi-block debug-mode `V2026_06_01` `CapturedMir`:
```rust
fn count_down_checked(n: u32) -> u32 {
    let mut i: u32 = n;
    let mut acc: u32 = 0;
    while 0 < i {
        i -= 1;   // SubWithOverflow + assert(!overflow)
        acc += 1; // AddWithOverflow + assert(!overflow)
    }
    acc
}
```
Locals: `_0: u32`, `_1: u32` (`n`), `_2: u32` (`i`), `_3: u32` (`acc`),
`_4: bool`, `_5: (u32, bool)`, `_6: (u32, bool)`. -/
def countDownCheckedMirBody : CapturedMir :=
  mkBody "count_down_checked" 1
    [decl .mut u32Ty, decl .not u32Ty, decl .mut u32Ty, decl .mut u32Ty,
     decl .mut boolTy, decl .mut u32BoolTy, decl .mut u32BoolTy]
    [mkBb
       [mkSt (.storageLive 2),
        mkSt (.assign (pl 2) (.use (.copy (pl 1)))),
        mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.use (u32C 0)))]
       (.goto 1),
     mkBb
       [mkSt (.storageLive 4),
        mkSt (.assign (pl 4) (.binaryOp .lt (u32C 0) (.copy (pl 2))))]
       (.switchInt (.copy (pl 4)) ⟨[(0, 5)], 2⟩),
     mkBb
       [mkSt (.storageDead 4),
        mkSt (.storageLive 5),
        mkSt (.assign (pl 5) (.binaryOp .subWithOverflow (.copy (pl 2)) (u32C 1)))]
       (.assert (.copy (pl 5 [.field 1 boolTy])) false 3 .continue_),
     mkBb
       [mkSt (.assign (pl 2) (.use (.copy (pl 5 [.field 0 u32Ty])))),
        mkSt (.storageDead 5),
        mkSt (.storageLive 6),
        mkSt (.assign (pl 6) (.binaryOp .addWithOverflow (.copy (pl 3)) (u32C 1)))]
       (.assert (.copy (pl 6 [.field 1 boolTy])) false 4 .continue_),
     mkBb
       [mkSt (.assign (pl 3) (.use (.copy (pl 6 [.field 0 u32Ty])))),
        mkSt (.storageDead 6)]
       (.goto 1),
     mkBb
       [mkSt (.storageDead 4),
        mkSt (.assign (pl 0) (.use (.copy (pl 3)))),
        mkSt (.storageDead 3),
        mkSt (.storageDead 2)]
       .return_]

private def cdcState (bb stmt : Nat) (l0 l2 l3 l4 l5 l6 : LocalSlot) (n : Nat) :
    MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt,
               locals := [l0, .init (.scalar ⟨n, 4⟩), l2, l3, l4, l5, l6] }
    memory := {} }

private def u32S (v : Nat) : LocalSlot := .init (.scalar ⟨v, 4⟩)

private def ovfPair (v bit : Nat) : LocalSlot :=
  .init (.aggregate 0 [.scalar ⟨v, 4⟩, .scalar ⟨bit, 1⟩])

/-- One checked loop iteration from the header: `(i + 1, acc) ↦ (i, acc + 1)`,
discharging both overflow assertions symbolically. -/
private theorem countDownChecked_step_iter (n i acc : Nat)
    (hSum : i + 1 + acc = n) (hLt : n < 2 ^ 32) :
    wpReach (ops := mirDetWpOps countDownCheckedMirBody)
      (· = cdcState 1 0 .uninit (u32S i) (u32S (acc + 1)) .dead .dead .dead n)
      (cdcState 1 0 .uninit (u32S (i + 1)) (u32S acc) .dead .dead .dead n) := by
  have hSub : Anneal.PureMirExec.mirStep countDownCheckedMirBody
      (cdcState 2 2 .uninit (u32S (i + 1)) (u32S acc) .dead .uninit .dead n) =
      .cont (cdcState 2 3 .uninit (u32S (i + 1)) (u32S acc) .dead (ovfPair i 0) .dead n) := by
    change Anneal.PureMirExec.Step.cont (cdcState 2 3 .uninit (u32S (i + 1)) (u32S acc) .dead
      (ovfPair (wrapScalarBits i (scalarModulus 4)) 0) .dead n) = _
    rw [wrapU32_of_lt (by omega)]
  have hNoOvf : Nat.ble (scalarModulus 4) (acc + 1) = false := by
    rw [Scalars.scalarModulus_eq_two_pow]
    exact natBle_false_of_not_le (by omega)
  have hAdd : Anneal.PureMirExec.mirStep countDownCheckedMirBody
      (cdcState 3 3 .uninit (u32S i) (u32S acc) .dead .dead .uninit n) =
      .cont (cdcState 3 4 .uninit (u32S i) (u32S acc) .dead .dead
        (ovfPair (acc + 1) 0) n) := by
    change Anneal.PureMirExec.Step.cont (cdcState 3 4 .uninit (u32S i) (u32S acc) .dead .dead
      (.init (.aggregate 0 [.scalar ⟨wrapScalarBits (acc + 1) (scalarModulus 4), 4⟩,
        .scalar ⟨match Nat.ble (scalarModulus 4) (acc + 1) with | true => 1 | false => 0, 1⟩]))
      n) = _
    rw [wrapU32_of_lt (by omega), hNoOvf]
    rfl
  exact
    step_det_to (cdcState 1 1 .uninit (u32S (i + 1)) (u32S acc) .uninit .dead .dead n) rfl <|
    step_det_to (cdcState 1 2 .uninit (u32S (i + 1)) (u32S acc)
      (.init (.scalar ⟨1, 1⟩)) .dead .dead n) rfl <|
    step_det_to (cdcState 2 0 .uninit (u32S (i + 1)) (u32S acc)
      (.init (.scalar ⟨1, 1⟩)) .dead .dead n) rfl <|
    step_det_to (cdcState 2 1 .uninit (u32S (i + 1)) (u32S acc) .dead .dead .dead n) rfl <|
    step_det_to (cdcState 2 2 .uninit (u32S (i + 1)) (u32S acc) .dead .uninit .dead n) rfl <|
    step_det_to _ hSub <|
    step_det_to (cdcState 3 0 .uninit (u32S (i + 1)) (u32S acc) .dead (ovfPair i 0) .dead n)
      rfl <|
    step_det_to (cdcState 3 1 .uninit (u32S i) (u32S acc) .dead (ovfPair i 0) .dead n) rfl <|
    step_det_to (cdcState 3 2 .uninit (u32S i) (u32S acc) .dead .dead .dead n) rfl <|
    step_det_to (cdcState 3 3 .uninit (u32S i) (u32S acc) .dead .dead .uninit n) rfl <|
    step_det_to _ hAdd <|
    step_det_to (cdcState 4 0 .uninit (u32S i) (u32S acc) .dead .dead
      (ovfPair (acc + 1) 0) n) rfl <|
    step_det_to (cdcState 4 1 .uninit (u32S i) (u32S (acc + 1)) .dead .dead
      (ovfPair (acc + 1) 0) n) rfl <|
    step_det_to (cdcState 4 2 .uninit (u32S i) (u32S (acc + 1)) .dead .dead .dead n) rfl <|
    step_det_to (cdcState 1 0 .uninit (u32S i) (u32S (acc + 1)) .dead .dead .dead n) rfl <|
    wpUntil_here (ops := mirDetWpOps countDownCheckedMirBody) rfl

/-- **Canary 1D (Fuel-Free Symbolic Debug-Mode `countDown`, `∀ n < 2^32`)**:
both `SubWithOverflow` and `AddWithOverflow` assertions are discharged inside
the `wpLoop_countdown` invariant (`rem + acc = n`), so the body never panics. -/
theorem canary1d_countDownChecked_wpStateOk (n : Nat) (hLt : n < 2 ^ 32) :
    wpStateOk (ops := mirDetWpOps countDownCheckedMirBody)
      (mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {}))
      (initMachineState countDownCheckedMirBody [.scalar ⟨n, 4⟩]) := by
  let post : MirOutcome → Prop :=
    mirNormalPost (fun ret mem' => ret = .scalar ⟨n, 4⟩ ∧ mem' = {})
  let Inv : Nat → MachineState → Prop := fun rem s =>
    ∃ acc, rem + acc = n ∧
      s = cdcState 1 0 .uninit (u32S rem) (u32S acc) .dead .dead .dead n
  let exitP : MachineState → Prop := fun s =>
    s = cdcState 1 0 .uninit (u32S 0) (u32S n) .dead .dead .dead n
  have hLoop : wpUntilOk (ops := mirDetWpOps countDownCheckedMirBody) exitP post
      (cdcState 1 0 .uninit (u32S n) (u32S 0) .dead .dead .dead n) :=
    wpLoop_countdown (ops := mirDetWpOps countDownCheckedMirBody) (Inv := Inv) (exit := exitP)
      (onDone := post) (onFault := fun _ => False)
      (fun _ ⟨acc, hSum, hEq⟩ => by
        have hAcc : acc = n := by omega
        subst hAcc
        exact hEq)
      (fun rem _ ⟨acc, hSum, hEq⟩ => by
        subst hEq
        refine wpUntil_mono (ops := mirDetWpOps countDownCheckedMirBody)
          (fun _ hS' => Or.inl ⟨acc + 1, by omega, hS'⟩)
          (fun _ hF => False.elim hF) (fun _ hF => False.elim hF) ?_
        exact countDownChecked_step_iter n rem acc hSum hLt)
      n _ ⟨0, by omega, rfl⟩
  have hFromHeader : wpStateOk (ops := mirDetWpOps countDownCheckedMirBody) post
      (cdcState 1 0 .uninit (u32S n) (u32S 0) .dead .dead .dead n) :=
    wpUntil_bind (ops := mirDetWpOps countDownCheckedMirBody) hLoop fun _ hEq => by
      subst hEq
      exact
        step_det_to (cdcState 1 1 .uninit (u32S 0) (u32S n) .uninit .dead .dead n) rfl <|
        step_det_to (cdcState 1 2 .uninit (u32S 0) (u32S n)
          (.init (.scalar ⟨0, 1⟩)) .dead .dead n) rfl <|
        step_det_to (cdcState 5 0 .uninit (u32S 0) (u32S n)
          (.init (.scalar ⟨0, 1⟩)) .dead .dead n) rfl <|
        step_det_to (cdcState 5 1 .uninit (u32S 0) (u32S n) .dead .dead .dead n) rfl <|
        step_det_to (cdcState 5 2 (u32S n) (u32S 0) (u32S n) .dead .dead .dead n) rfl <|
        step_det_to (cdcState 5 3 (u32S n) (u32S 0) .dead .dead .dead .dead n) rfl <|
        step_det_to (cdcState 5 4 (u32S n) .dead .dead .dead .dead .dead n) rfl <|
        step_det_done (.normal (.scalar ⟨n, 4⟩, {})) rfl ⟨rfl, rfl⟩
  exact
    step_det_to (cdcState 0 1 .uninit .uninit .dead .dead .dead .dead n) rfl <|
    step_det_to (cdcState 0 2 .uninit (u32S n) .dead .dead .dead .dead n) rfl <|
    step_det_to (cdcState 0 3 .uninit (u32S n) .uninit .dead .dead .dead n) rfl <|
    step_det_to (cdcState 0 4 .uninit (u32S n) (u32S 0) .dead .dead .dead n) rfl <|
    step_det_to (cdcState 1 0 .uninit (u32S n) (u32S 0) .dead .dead .dead n) rfl <|
    hFromHeader

/-- Fuel-free `MirWpConverges` for debug-mode `countDownCheckedMirBody`. -/
theorem canary1d_countDownChecked_mirWpConverges (n : Nat) (hLt : n < 2 ^ 32) :
    MirWpConverges countDownCheckedMirBody
      (initMachineState countDownCheckedMirBody [.scalar ⟨n, 4⟩])
      (mirNormalPost (fun ret _ => ret = .scalar ⟨n, 4⟩)) :=
  MirWpConverges.mono
    (fun out hOut => by
      cases out with
      | panic | abort => exact False.elim hOut
      | normal p => exact hOut.1)
    (mirWpConverges_of_wpStateOk (canary1d_countDownChecked_wpStateOk n hLt))

def countDownCheckedClaim : Claim where
  body := countDownCheckedMirBody
  callees := []
  pre args := ∃ n : Nat, n < 2 ^ 32 ∧ args = [.scalar ⟨n, 4⟩]
  post args ret := ∃ n : Nat, args = [.scalar ⟨n, 4⟩] ∧ ret = .scalar ⟨n, 4⟩

/-- **Trusted no-panic `VerificationResult` for debug-mode `countDownCheckedMirBody`**:
the overflow `Assert`s are provably unreachable for every `n < 2^32`. -/
theorem canary1d_countDownChecked_verificationResult :
    VerificationResult countDownCheckedClaim :=
  verifyMirNoPanic_of_wpStateOk countDownCheckedClaim fun args ⟨n, hLt, hArgs⟩ => by
    subst hArgs
    refine wpOutcome_mono (ops := mirDetWpOps countDownCheckedMirBody) ?_ (fun _ h => h)
      (canary1d_countDownChecked_wpStateOk n hLt)
    intro out hOut
    cases out with
    | panic | abort => exact False.elim hOut
    | normal p => exact ⟨n, rfl, hOut.1⟩

def countDownCheckedTotalClaim : TotalClaim where
  body := countDownCheckedMirBody
  callees := []
  pre args mem := ∃ n : Nat, n < 2 ^ 32 ∧ args = [.scalar ⟨n, 4⟩] ∧ mem = {}
  post args _ ret mem' := ∃ n : Nat, args = [.scalar ⟨n, 4⟩] ∧ ret = .scalar ⟨n, 4⟩ ∧ mem' = {}

/-- **Trusted `TotalVerificationResult` (fuel-free termination + no-panic) for
debug-mode `countDownCheckedMirBody`**, discharging both `SubWithOverflow` and
`AddWithOverflow` guards for every `n < 2^32`. -/
theorem canary1d_countDownChecked_totalVerificationResult :
    TotalVerificationResult countDownCheckedTotalClaim :=
  verifyTotalMir_of_wpStateOk countDownCheckedTotalClaim fun args mem ⟨n, hLt, hArgs, hMem⟩ => by
    subst hArgs hMem
    refine wpOutcome_mono (ops := mirDetWpOps countDownCheckedMirBody) ?_ (fun _ h => h)
      (canary1d_countDownChecked_wpStateOk n hLt)
    intro out hOut
    cases out with
    | panic | abort => exact False.elim hOut
    | normal p => exact ⟨n, rfl, hOut.1, hOut.2⟩

/-- Non-vacuity of the debug-mode `SubWithOverflow` guard: if `_5` ever carried
a set overflow flag, the real `Assert` terminator in `bb2` would `.panic`. -/
theorem canary1d_overflowAssert_live (n i acc : Nat) :
    Anneal.PureMirExec.mirStep countDownCheckedMirBody
      (cdcState 2 3 .uninit (u32S i) (u32S acc) .dead (ovfPair (2 ^ 32 - 1) 1) .dead n) =
      .done .panic := rfl

/-- Non-vacuity of the debug-mode `AddWithOverflow` guard: if `_6` ever carried
a set overflow flag, the real `Assert` terminator in `bb3` would `.panic`. -/
theorem canary1d_addOverflowAssert_live (n i acc : Nat) :
    Anneal.PureMirExec.mirStep countDownCheckedMirBody
      (cdcState 3 4 .uninit (u32S i) (u32S acc) .dead .dead (ovfPair 0 1) n) =
      .done .panic := rfl

/-! ## 2. Canary 2 — 2-Stage Diamond CFG `StageCut` + `BlockTree` + Frame + `PureLift` -/

/-- Real 7-block 2-stage diamond `V2026_06_01` `CapturedMir`:
```rust
fn two_stage_diamond(c1: bool, c2: bool, x: u32, z: u32) -> (u32, u32) {
    // Stage 1: bb0 -> (bb1 | bb2) -> bb3 [cutpoint]
    let mut acc: u32 = if c1 { x + 10 } else { x + 20 };
    // Stage 2: bb3 -> (bb4 | bb5) -> bb6 [return]
    acc = if c2 { acc + 1 } else { acc + 2 };
    (acc, z) // _4 (z) is completely untouched across both stages
}
```
Locals: `_0: (u32, u32)`, `_1: bool (c1)`, `_2: bool (c2)`, `_3: u32 (x)`,
`_4: u32 (z — framed)`, `_5: u32 (acc)`. -/
def diamond2StageMirBody : CapturedMir :=
  mkBody "two_stage_diamond" 4
    [decl .mut pairU32Ty, decl .not boolTy, decl .not boolTy,
     decl .not u32Ty, decl .not u32Ty, decl .mut u32Ty]
    [mkBb [] (.switchInt (.copy (pl 1)) ⟨[(0, 2)], 1⟩),
     mkBb
       [mkSt (.storageLive 5),
        mkSt (.assign (pl 5) (.binaryOp .add (.copy (pl 3)) (u32C 10)))]
       (.goto 3),
     mkBb
       [mkSt (.storageLive 5),
        mkSt (.assign (pl 5) (.binaryOp .add (.copy (pl 3)) (u32C 20)))]
       (.goto 3),
     mkBb [] (.switchInt (.copy (pl 2)) ⟨[(0, 5)], 4⟩),
     mkBb
       [mkSt (.assign (pl 5) (.binaryOp .add (.copy (pl 5)) (u32C 1)))]
       (.goto 6),
     mkBb
       [mkSt (.assign (pl 5) (.binaryOp .add (.copy (pl 5)) (u32C 2)))]
       (.goto 6),
     mkBb
       [mkSt (.assign (pl 0) (.aggregate .tuple [.copy (pl 5), .copy (pl 4)])),
        mkSt (.storageDead 5)]
       .return_]

def diamondBlockTree : BlockTree BasicBlockData :=
  BlockTree.ofList diamond2StageMirBody.basicBlocks

def diamondChunk8Tree : Chunk8BlockTree BasicBlockData :=
  Chunk8BlockTree.ofList diamond2StageMirBody.basicBlocks

theorem diamondBlockTree_valid :
    ValidBlockTree diamond2StageMirBody.basicBlocks diamondBlockTree :=
  validBlockTree_basicBlocks diamond2StageMirBody

theorem diamondChunk8Tree_valid :
    ValidChunk8BlockTree diamond2StageMirBody.basicBlocks diamondChunk8Tree :=
  validChunk8BlockTree_basicBlocks diamond2StageMirBody

/-- Unconditional basic-block lookup agreement for both `BlockTree` and
`Chunk8BlockTree` on `diamond2StageMirBody`, across all in-bounds and OOB indices. -/
theorem canary2_blockTree_lookup_all (idx : Nat) :
    diamondBlockTree.lookup? idx = Trusted.Sequence.get? diamond2StageMirBody.basicBlocks idx ∧
    diamondChunk8Tree.lookup? idx = Trusted.Sequence.get? diamond2StageMirBody.basicBlocks idx :=
  ⟨blockTree_ofList_basicBlocks_lookup? diamond2StageMirBody idx,
   chunk8BlockTree_ofList_basicBlocks_lookup? diamond2StageMirBody idx⟩

private def cutAtBb3 : MaskTree :=
  MaskTree.ofList [false, false, false, true, false, false, false]

private def cutAtBb6 : MaskTree :=
  MaskTree.ofList [false, false, false, false, false, false, true]

private def isScalarSlot : LocalSlot → Bool
  | .init (.scalar _) => true
  | _ => false

private def isU32Slot : LocalSlot → Bool
  | .init (.scalar ⟨_, 4⟩) => true
  | _ => false

private def stage1Region (s : MachineState) : Bool :=
  Nat.blt s.frame.blockIdx 3 &&
    match s.frame.locals with
    | [_, l1, _, l3, _, _] => isScalarSlot l1 && isU32Slot l3 && s.memory.activeCallee.isNone
    | _ => false

private def stage2Region (s : MachineState) : Bool :=
  Nat.ble 3 s.frame.blockIdx && Nat.blt s.frame.blockIdx 6 &&
    match s.frame.locals with
    | [_, _, l2, _, _, l5] => isScalarSlot l2 && isU32Slot l5 && s.memory.activeCallee.isNone
    | _ => false

private def diamondState (bb stmt : Nat)
    (l0 l1 l2 l3 l4 l5 : LocalSlot) : MachineState :=
  { frame := { blockIdx := bb, stmtIdx := stmt, locals := [l0, l1, l2, l3, l4, l5] }
    memory := {} }

private def boolScalar (b : Bool) : Value :=
  .scalar ⟨if b then 1 else 0, 1⟩

private def stage1Delta (c1 : Bool) : Nat := if c1 then 10 else 20
private def stage2Delta (c2 : Bool) : Nat := if c2 then 1 else 2

/-- Frame predicate for untouched local `_4` (`z`) and empty memory, proved once
for Stage 1 and Stage 2 without expanding branches. -/
private def diamondFrameZ (z : LocalSlot) (s : MachineState) : Prop :=
  listGet? s.frame.locals 4 = some z ∧ s.memory = {}

/-- Executing `diamond2StageMirBody` anywhere in Stage 1 (`bb ∈ {0, 1, 2}`)
with clean memory preserves untouched local `_4` (`z`) and `memory = {}`. -/
private theorem diamond_stage1_stepFrame (z : LocalSlot) :
    (mirDetWpOps diamond2StageMirBody).StepFrameOn
      (fun s => stage1Region s = true) (diamondFrameZ z) := by
  intro s P Q R hReg ⟨hLoc4, hMem⟩ hStep
  change (mirDetStep diamond2StageMirBody s).wp _ _ _ at hStep ⊢
  cases hSt : mirDetStep diamond2StageMirBody s with
  | done o => rw [hSt] at hStep; exact hStep
  | fault f => rw [hSt] at hStep; exact hStep
  | step s' =>
    rw [hSt] at hStep
    refine ⟨hStep, ?_⟩
    have hMir := mirDetStep_step_iff.mp hSt
    unfold stage1Region at hReg
    have hLt3 : s.frame.blockIdx < 3 :=
      Nat.lt_of_succ_le (Nat.le_of_ble_eq_true (boolAnd_left hReg))
    have hLocOk := boolAnd_right hReg
    rcases s with ⟨⟨bb, stmt, locs⟩, mem⟩
    dsimp only at hMem hLt3 hLocOk hLoc4 hMir
    subst hMem
    match locs, hLocOk with
    | [l0, l1, l2, l3, l4, l5], hLocOk =>
      have hL1Sc : isScalarSlot l1 = true := boolAnd_left (boolAnd_left hLocOk)
      have hL3U32 : isU32Slot l3 = true := boolAnd_right (boolAnd_left hLocOk)
      cases l1 with
      | uninit | dead => cases hL1Sc
      | init v1 =>
        cases v1 with
        | unit | ptr _ _ | aggregate _ _ | uninit => cases hL1Sc
        | scalar sc1 =>
          cases l3 with
          | uninit | dead => cases hL3U32
          | init v3 =>
            cases v3 with
            | unit | ptr _ _ | aggregate _ _ | uninit => cases hL3U32
            | scalar sc3 =>
              rcases sc3 with ⟨bits3, sz3⟩
              cases sz3 with
              | zero => cases hL3U32
              | succ k =>
                cases k with
                | zero => cases hL3U32
                | succ k =>
                  cases k with
                  | zero => cases hL3U32
                  | succ k =>
                    cases k with
                    | zero => cases hL3U32
                    | succ k =>
                      cases k with
                      | succ _ => cases hL3U32
                      | zero =>
                        match bb, hLt3 with
                        | 0, _ =>
                          cases stmt with
                          | succ _ => cases hMir
                          | zero =>
                            cases hEq0 : Nat.beq sc1.bits 0 with
                            | true =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState (match Nat.beq sc1.bits 0 with | true => 2 | false => 1) 0
                                  l0 (.init (.scalar sc1)) l2 (.init (.scalar ⟨bits3, 4⟩)) l4 l5) = _ at hMir
                              rw [hEq0] at hMir; injection hMir with hEq; subst hEq
                              exact ⟨hLoc4, rfl⟩
                            | false =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState (match Nat.beq sc1.bits 0 with | true => 2 | false => 1) 0
                                  l0 (.init (.scalar sc1)) l2 (.init (.scalar ⟨bits3, 4⟩)) l4 l5) = _ at hMir
                              rw [hEq0] at hMir; injection hMir with hEq; subst hEq
                              exact ⟨hLoc4, rfl⟩
                        | 1, _ =>
                          match stmt with
                          | 0 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 1 =>
                            cases l5 with
                            | dead => cases hMir
                            | uninit | init _ =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState 1 2 l0 (.init (.scalar sc1)) l2
                                  (.init (.scalar ⟨bits3, 4⟩)) l4
                                  (.init (.scalar ⟨wrapScalarBits (bits3 + 10) (scalarModulus 4), 4⟩))) = _ at hMir
                              injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 2 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | _ + 3 => cases hMir
                        | 2, _ =>
                          match stmt with
                          | 0 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 1 =>
                            cases l5 with
                            | dead => cases hMir
                            | uninit | init _ =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState 2 2 l0 (.init (.scalar sc1)) l2
                                  (.init (.scalar ⟨bits3, 4⟩)) l4
                                  (.init (.scalar ⟨wrapScalarBits (bits3 + 20) (scalarModulus 4), 4⟩))) = _ at hMir
                              injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 2 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | _ + 3 => cases hMir

/-- Executing `diamond2StageMirBody` anywhere in Stage 2 (`bb ∈ {3, 4, 5}`)
with clean memory preserves untouched local `_4` (`z`) and `memory = {}`. -/
private theorem diamond_stage2_stepFrame (z : LocalSlot) :
    (mirDetWpOps diamond2StageMirBody).StepFrameOn
      (fun s => stage2Region s = true) (diamondFrameZ z) := by
  intro s P Q R hReg ⟨hLoc4, hMem⟩ hStep
  change (mirDetStep diamond2StageMirBody s).wp _ _ _ at hStep ⊢
  cases hSt : mirDetStep diamond2StageMirBody s with
  | done o => rw [hSt] at hStep; exact hStep
  | fault f => rw [hSt] at hStep; exact hStep
  | step s' =>
    rw [hSt] at hStep
    refine ⟨hStep, ?_⟩
    have hMir := mirDetStep_step_iff.mp hSt
    unfold stage2Region at hReg
    have hB := boolAnd_left hReg
    have hGe3 : 3 ≤ s.frame.blockIdx := Nat.le_of_ble_eq_true (boolAnd_left hB)
    have hLt6 : s.frame.blockIdx < 6 :=
      Nat.lt_of_succ_le (Nat.le_of_ble_eq_true (boolAnd_right hB))
    have hLocOk := boolAnd_right hReg
    rcases s with ⟨⟨bb, stmt, locs⟩, mem⟩
    dsimp only at hMem hGe3 hLt6 hLocOk hLoc4 hMir
    subst hMem
    match locs, hLocOk with
    | [l0, l1, l2, l3, l4, l5], hLocOk =>
      have hL2Sc : isScalarSlot l2 = true := boolAnd_left (boolAnd_left hLocOk)
      have hL5U32 : isU32Slot l5 = true := boolAnd_right (boolAnd_left hLocOk)
      cases l2 with
      | uninit | dead => cases hL2Sc
      | init v2 =>
        cases v2 with
        | unit | ptr _ _ | aggregate _ _ | uninit => cases hL2Sc
        | scalar sc2 =>
          cases l5 with
          | uninit | dead => cases hL5U32
          | init v5 =>
            cases v5 with
            | unit | ptr _ _ | aggregate _ _ | uninit => cases hL5U32
            | scalar sc5 =>
              rcases sc5 with ⟨bits5, sz5⟩
              cases sz5 with
              | zero => cases hL5U32
              | succ k =>
                cases k with
                | zero => cases hL5U32
                | succ k =>
                  cases k with
                  | zero => cases hL5U32
                  | succ k =>
                    cases k with
                    | zero => cases hL5U32
                    | succ k =>
                      cases k with
                      | succ _ => cases hL5U32
                      | zero =>
                        match bb, hGe3, hLt6 with
                        | 3, _, _ =>
                          cases stmt with
                          | succ _ => cases hMir
                          | zero =>
                            cases hEq0 : Nat.beq sc2.bits 0 with
                            | true =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState (match Nat.beq sc2.bits 0 with | true => 5 | false => 4) 0
                                  l0 l1 (.init (.scalar sc2)) l3 l4 (.init (.scalar ⟨bits5, 4⟩))) = _ at hMir
                              rw [hEq0] at hMir; injection hMir with hEq; subst hEq
                              exact ⟨hLoc4, rfl⟩
                            | false =>
                              change Anneal.PureMirExec.Step.cont
                                (diamondState (match Nat.beq sc2.bits 0 with | true => 5 | false => 4) 0
                                  l0 l1 (.init (.scalar sc2)) l3 l4 (.init (.scalar ⟨bits5, 4⟩))) = _ at hMir
                              rw [hEq0] at hMir; injection hMir with hEq; subst hEq
                              exact ⟨hLoc4, rfl⟩
                        | 4, _, _ =>
                          match stmt with
                          | 0 =>
                            change Anneal.PureMirExec.Step.cont
                              (diamondState 4 1 l0 l1 (.init (.scalar sc2)) l3 l4
                                (.init (.scalar ⟨wrapScalarBits (bits5 + 1) (scalarModulus 4), 4⟩))) = _ at hMir
                            injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 1 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | _ + 2 => cases hMir
                        | 5, _, _ =>
                          match stmt with
                          | 0 =>
                            change Anneal.PureMirExec.Step.cont
                              (diamondState 5 1 l0 l1 (.init (.scalar sc2)) l3 l4
                                (.init (.scalar ⟨wrapScalarBits (bits5 + 2) (scalarModulus 4), 4⟩))) = _ at hMir
                            injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | 1 => injection hMir with hEq; subst hEq; exact ⟨hLoc4, rfl⟩
                          | _ + 2 => cases hMir

/-- **Stage 1 opaque `StepStageCut` (`bb0 ↝ bb3`)** via `ValidBlockTree`
(`evalBlockTreeToCut`), proved with only 2 branch cases (`c1 = true | false`)
for arbitrary symbolic `x`, `l2`, `l4`. -/
theorem canary2_stage1_stepStageCut (c1 : Bool) (x : Nat) (hX : x + 20 < 2 ^ 32)
    (l2 l4 : LocalSlot) :
    StepStageCut (mirDetStep diamond2StageMirBody) 4
      (diamondState 0 0 .uninit (.init (boolScalar c1)) l2 (.init (.scalar ⟨x, 4⟩)) l4 .dead)
      (diamondState 3 0 .uninit (.init (boolScalar c1)) l2 (.init (.scalar ⟨x, 4⟩)) l4
        (.init (.scalar ⟨x + stage1Delta c1, 4⟩))) := by
  refine stepStageCut_of_validBlockTreeToCut diamondBlockTree_valid (cuts := cutAtBb3) ?_
  cases c1 with
  | false =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar false)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 20) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl
  | true =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar true)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 10) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl

/-- **Stage 1 opaque `StepStageCut` via `ValidChunk8BlockTree`**
(`V2026Bridge.stepStageCut_of_validChunk8BlockTreeToCut`), exercising the
8-way chunked basic-block lookup accelerator on `diamond2StageMirBody`. -/
theorem canary2_stage1_chunk8BlockTree_stepStageCut (c1 : Bool) (x : Nat)
    (hX : x + 20 < 2 ^ 32) (l2 l4 : LocalSlot) :
    StepStageCut (mirDetStep diamond2StageMirBody) 4
      (diamondState 0 0 .uninit (.init (boolScalar c1)) l2 (.init (.scalar ⟨x, 4⟩)) l4 .dead)
      (diamondState 3 0 .uninit (.init (boolScalar c1)) l2 (.init (.scalar ⟨x, 4⟩)) l4
        (.init (.scalar ⟨x + stage1Delta c1, 4⟩))) := by
  refine stepStageCut_of_validChunk8BlockTreeToCut diamondChunk8Tree_valid (cuts := cutAtBb3) ?_
  cases c1 with
  | false =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar false)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 20) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl
  | true =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar true)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 10) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl

/-- **Stage 1 region-guarded `StageCut` (`bb0 ↝ bb3`, ignoring `_4 = z`)** proved
directly from `ValidBlockTree` via `wpReach_within_of_validBlockTreeToCut`. -/
theorem canary2_stage1_within (c1 : Bool) (x : Nat) (hX : x + 20 < 2 ^ 32)
    (l2 : LocalSlot) :
    StageCut (ops := (mirDetWpOps diamond2StageMirBody).within (fun s => stage1Region s = true))
      (fun s => ∃ l4, s = diamondState 0 0 .uninit (.init (boolScalar c1)) l2
        (.init (.scalar ⟨x, 4⟩)) l4 .dead)
      (fun s => ∃ l4, s = diamondState 3 0 .uninit (.init (boolScalar c1)) l2
        (.init (.scalar ⟨x, 4⟩)) l4 (.init (.scalar ⟨x + stage1Delta c1, 4⟩)))
      (fun _ => False) (fun _ => False) :=
  StageCut.intro (ops := (mirDetWpOps diamond2StageMirBody).within (fun s => stage1Region s = true))
    fun s ⟨l4, hEq⟩ => by
  subst hEq
  refine wpUntil_mono_stop (ops := (mirDetWpOps diamond2StageMirBody).within
      (fun s => stage1Region s = true))
    (fun s' hS' => ⟨l4, hS'⟩) ?_
  refine wpReach_within_of_validBlockTreeToCut diamondBlockTree_valid
    (region := stage1Region) (cuts := cutAtBb3) (fuel := 4) ?_
  cases c1 with
  | false =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar false)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 20) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl
  | true =>
    change CutRun.cut (diamondState 3 0 .uninit (.init (boolScalar true)) l2
      (.init (.scalar ⟨x, 4⟩)) l4
      (.init (.scalar ⟨wrapScalarBits (x + 10) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl

/-- **Stage 2 opaque `StepStageCut` (`bb3 ↝ bb6`)** via `ValidBlockTree`
(`evalBlockTreeFromCut`), proved with only 2 branch cases (`c2 = true | false`)
for arbitrary symbolic `acc`, `l1`, `l3`, `l4`. -/
theorem canary2_stage2_stepStageCut (c2 : Bool) (acc : Nat) (hAcc : acc + 2 < 2 ^ 32)
    (l1 l3 l4 : LocalSlot) :
    StepStageCut (mirDetStep diamond2StageMirBody) 3
      (diamondState 3 0 .uninit l1 (.init (boolScalar c2)) l3 l4 (.init (.scalar ⟨acc, 4⟩)))
      (diamondState 6 0 .uninit l1 (.init (boolScalar c2)) l3 l4
        (.init (.scalar ⟨acc + stage2Delta c2, 4⟩))) := by
  refine stepStageCut_of_validBlockTreeFromCut diamondBlockTree_valid (cuts := cutAtBb6)
    (fuel := 2) ?_
  cases c2 with
  | false =>
    change CutRun.cut (diamondState 6 0 .uninit l1 (.init (boolScalar false)) l3 l4
      (.init (.scalar ⟨wrapScalarBits (acc + 2) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl
  | true =>
    change CutRun.cut (diamondState 6 0 .uninit l1 (.init (boolScalar true)) l3 l4
      (.init (.scalar ⟨wrapScalarBits (acc + 1) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl

/-- **Stage 2 region-guarded `StageCut` (`bb3 ↝ bb6`, ignoring `_4 = z`)** proved
directly from `ValidBlockTree` via `wpReach_within_of_validBlockTreeFromCut`. -/
theorem canary2_stage2_within (c2 : Bool) (acc : Nat) (hAcc : acc + 2 < 2 ^ 32)
    (l1 l3 : LocalSlot) :
    StageCut (ops := (mirDetWpOps diamond2StageMirBody).within (fun s => stage2Region s = true))
      (fun s => ∃ l4, s = diamondState 3 0 .uninit l1 (.init (boolScalar c2)) l3 l4
        (.init (.scalar ⟨acc, 4⟩)))
      (fun s => ∃ l4, s = diamondState 6 0 .uninit l1 (.init (boolScalar c2)) l3 l4
        (.init (.scalar ⟨acc + stage2Delta c2, 4⟩)))
      (fun _ => False) (fun _ => False) :=
  StageCut.intro (ops := (mirDetWpOps diamond2StageMirBody).within (fun s => stage2Region s = true))
    fun s ⟨l4, hEq⟩ => by
  subst hEq
  refine wpUntil_mono_stop (ops := (mirDetWpOps diamond2StageMirBody).within
      (fun s => stage2Region s = true))
    (fun s' hS' => ⟨l4, hS'⟩) ?_
  refine wpReach_within_of_validBlockTreeFromCut diamondBlockTree_valid
    (region := stage2Region) (cuts := cutAtBb6) (fuel := 2) ?_
  cases c2 with
  | false =>
    change CutRun.cut (diamondState 6 0 .uninit l1 (.init (boolScalar false)) l3 l4
      (.init (.scalar ⟨wrapScalarBits (acc + 2) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl
  | true =>
    change CutRun.cut (diamondState 6 0 .uninit l1 (.init (boolScalar true)) l3 l4
      (.init (.scalar ⟨wrapScalarBits (acc + 1) (scalarModulus 4), 4⟩))) = _
    rw [wrapU32_of_lt (by omega)]; rfl

/-- **Canary 2 (Modular 2-Stage Composition + Frame Preservation)**:
Composes framed Stage 1 + Stage 2 via `stageCut_frame` and `stageCut_compose`
with zero `2 × 2` path blowup, preserving untouched `_4 = z`, and discharges
`MirWpConverges` for all symbolic `(c1, c2, x, z)`. -/
theorem canary2_diamond_mirWpConverges (c1 c2 : Bool) (x z : Nat)
    (hX : x + 22 < 2 ^ 32) :
    MirWpConverges diamond2StageMirBody
      (initMachineState diamond2StageMirBody
        [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩])
      (mirNormalPost (fun ret _ =>
        ret = .aggregate 0
          [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩])) := by
  let zSlot : LocalSlot := .init (.scalar ⟨z, 4⟩)
  have hStage1Framed :=
    stageCut_frame (ops := mirDetWpOps diamond2StageMirBody) (diamond_stage1_stepFrame zSlot)
      (canary2_stage1_within c1 x (by omega) (.init (boolScalar c2)))
  have hStage2Framed :=
    stageCut_frame (ops := mirDetWpOps diamond2StageMirBody) (diamond_stage2_stepFrame zSlot)
      (canary2_stage2_within c2 (x + stage1Delta c1)
        (by cases c1 with
          | false => change x + 20 + 2 < 2 ^ 32; omega
          | true => change x + 10 + 2 < 2 ^ 32; omega)
        (.init (boolScalar c1)) (.init (.scalar ⟨x, 4⟩)))
  let post : MirOutcome → Prop :=
    mirNormalPost (fun ret _ =>
      ret = .aggregate 0
        [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩])
  have hComposed :=
    stageCut_weaken (ops := mirDetWpOps diamond2StageMirBody) (onDone' := post)
      (fun _ h => h) (fun _ h => h)
      (fun _ hF => False.elim hF) (fun _ h => h)
      (stageCut_compose (ops := mirDetWpOps diamond2StageMirBody) hStage1Framed hStage2Framed)
  refine mirWpConverges_of_stageCut hComposed ?_ ⟨⟨zSlot, rfl⟩, rfl, rfl⟩
  intro s ⟨⟨l4, hEq⟩, hLoc4, _⟩
  subst hEq
  change some l4 = some zSlot at hLoc4
  injection hLoc4 with hL4
  subst hL4
  refine mirWpConverges_of_wpStateOk ?_
  exact
    step_det_to (diamondState 6 1
      (.init (.aggregate 0 [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
      (.init (boolScalar c1)) (.init (boolScalar c2)) (.init (.scalar ⟨x, 4⟩))
      zSlot (.init (.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩))) rfl <|
    step_det_to (diamondState 6 2
      (.init (.aggregate 0 [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
      (.init (boolScalar c1)) (.init (boolScalar c2)) (.init (.scalar ⟨x, 4⟩))
      zSlot .dead) rfl <|
    step_det_done (.normal (.aggregate 0
      [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩], {})) rfl rfl

/-- **Canary 2 (`PureLift` `StepPath` & `mirOperationalAdapter` bridge)**:
Composes the opaque `StepStageCut`s for Stage 1 and Stage 2 via `StepStageCut.trans`
and transports directly to `PureLift.MirLiftCoreInterop.StepPath` and
`mirOperationalAdapter.executesTo` in 2 lines. -/
theorem canary2_diamond_pureLift_stepPath (c1 c2 : Bool) (x z : Nat)
    (hX : x + 22 < 2 ^ 32) :
    ∃ k, k ≤ 7 ∧
      Anneal.PureLift.MirLiftCoreInterop.StepPath (Anneal.PureMirExec.mirStep diamond2StageMirBody)
        (initMachineState diamond2StageMirBody
          [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩])
        k
        (diamondState 6 0 .uninit (.init (boolScalar c1)) (.init (boolScalar c2))
          (.init (.scalar ⟨x, 4⟩)) (.init (.scalar ⟨z, 4⟩))
          (.init (.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩))) := by
  have hCut12 :=
    (canary2_stage1_stepStageCut c1 x (by omega) (.init (boolScalar c2))
      (.init (.scalar ⟨z, 4⟩))).trans
    (canary2_stage2_stepStageCut c2 (x + stage1Delta c1)
      (by cases c1 with
        | false => change x + 20 + 2 < 2 ^ 32; omega
        | true => change x + 10 + 2 < 2 ^ 32; omega)
      (.init (boolScalar c1)) (.init (.scalar ⟨x, 4⟩)) (.init (.scalar ⟨z, 4⟩)))
  exact stepPath_of_stepStageCut hCut12

/-- **Canary 2 (`mirOperationalAdapter.ExecutesTo` bridge)**:
Lifts the composed 2-stage `StepStageCut` directly into
`PureLift.V2026_06_01Bridge.mirOperationalAdapter`. -/
theorem canary2_diamond_mirOperationalAdapter_executesTo (c1 c2 : Bool) (x z : Nat)
    (hX : x + 22 < 2 ^ 32) :
    ∃ k, k ≤ 7 ∧
      (Anneal.PureLift.V2026_06_01Bridge.mirOperationalAdapter (fun lid => lid + 1)
          diamond2StageMirBody []).ExecutesTo
        (initMachineState diamond2StageMirBody
          [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩])
        k
        (diamondState 6 0 .uninit (.init (boolScalar c1)) (.init (boolScalar c2))
          (.init (.scalar ⟨x, 4⟩)) (.init (.scalar ⟨z, 4⟩))
          (.init (.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩))) := by
  have hCut12 :=
    (canary2_stage1_stepStageCut c1 x (by omega) (.init (boolScalar c2))
      (.init (.scalar ⟨z, 4⟩))).trans
    (canary2_stage2_stepStageCut c2 (x + stage1Delta c1)
      (by cases c1 with
        | false => change x + 20 + 2 < 2 ^ 32; omega
        | true => change x + 10 + 2 < 2 ^ 32; omega)
      (.init (boolScalar c1)) (.init (.scalar ⟨x, 4⟩)) (.init (.scalar ⟨z, 4⟩)))
  exact mirOperationalAdapter_executesTo_of_stepStageCut (fun lid => lid + 1)
    diamond2StageMirBody [] [] hCut12

def diamond2StageClaim : Claim where
  body := diamond2StageMirBody
  callees := []
  pre args := ∃ (c1 c2 : Bool) (x z : Nat), x + 22 < 2 ^ 32 ∧
    args = [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩]
  post args ret := ∃ (c1 c2 : Bool) (x z : Nat),
    args = [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩] ∧
    ret = .aggregate 0
      [.scalar ⟨x + stage1Delta c1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]

theorem canary2_diamond_verificationResult : VerificationResult diamond2StageClaim :=
  verifyMirNoPanic_of_wpConverges diamond2StageClaim fun args ⟨c1, c2, x, z, hX, hArgs⟩ => by
    subst hArgs
    exact MirWpConverges.mono
      (fun out hOut => by
        cases out with
        | panic | abort => exact False.elim hOut
        | normal p => exact ⟨c1, c2, x, z, rfl, hOut⟩)
      (canary2_diamond_mirWpConverges c1 c2 x z hX)

/-- `PureLift` `FlowPlan` lifting Stage 2 (`bb3 -> (bb4|bb5) -> bb6`) of
`diamond2StageMirBody`: locals `0..4` correspond to MIR `_1.._5` (`c1, c2, x, z, acc`). -/
def diamondStage2PurePlan : Anneal.PureLift.FlowPlan Anneal.PureLift.StdVal :=
  .branch (.use (.localSub 1 []))
    (.act (.assign (.localSub 4 [])
      (.unary (fun v => match v with | .nat n => some (.nat (n + 1)) | _ => none)
        (.localSub 4 []))))
    (.act (.assign (.localSub 4 [])
      (.unary (fun v => match v with | .nat n => some (.nat (n + 2)) | _ => none)
        (.localSub 4 []))))

/-- **Canary 2 (End-to-End `ParametricCore.StageCut` + `PureLift` Composition)**:
Composes framed Stage 1 (`bb0 ↝ bb3`, sealed behind `@[irreducible] StageCut`
with `_4 = z` framed via `stageCut_frame`) directly with Stage 2 (`bb3 ↝ bb6`)
certified via real `PureLift` (`FlowPlan`, `evalFnValue`, `mirStateRel`,
`MirReturnRel`, `LiftedMirPost`) through `V2026Bridge.mirWpConverges_stageCut_then_pureLift`
for ALL symbolic `(c1 c2 : Bool)` and `(x z : Nat)` (`x + 22 < 2^32`, `z < 2^32`). -/
theorem canary2_diamond_stageCut_then_pureLift (c1 c2 : Bool) (x z : Nat)
    (hX : x + 22 < 2 ^ 32) (hZ : z < 2 ^ 32) :
    let acc1 := x + stage1Delta c1
    let post : Anneal.PureLift.FuncOut Anneal.PureLift.StdVal → Prop :=
      fun out => out.ret = .pair (.nat (acc1 + stage2Delta c2)) (.nat z)
    MirWpConverges diamond2StageMirBody
      (initMachineState diamond2StageMirBody
        [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩])
      (fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost (fun lid => lid + 1) post o []) := by
  intro acc1 post
  let params : List (Anneal.PureLift.ParamInput Anneal.PureLift.StdVal) :=
    [⟨.byVal, .bool c1⟩, ⟨.byVal, .bool c2⟩, ⟨.byVal, .nat x⟩,
     ⟨.byVal, .nat z⟩, ⟨.byVal, .nat acc1⟩]
  let retExpr : Anneal.PureLift.RvalOp Anneal.PureLift.StdVal :=
    .binary (fun a b => some (.pair a b)) (.localSub 4 []) (.localSub 3 [])
  let tagOf : Anneal.PureLift.LoanId → Nat := fun lid => lid + 1
  let postMir : MirOutcome → Prop :=
    fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost tagOf post o []
  let zSlot : LocalSlot := .init (.scalar ⟨z, 4⟩)
  let sEntry := initMachineState diamond2StageMirBody
    [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩]
  let sCut := diamondState 3 0 .uninit (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot (.init (.scalar ⟨acc1, 4⟩))
  let sBb6_0 := diamondState 6 0 .uninit (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot
    (.init (.scalar ⟨acc1 + stage2Delta c2, 4⟩))
  let sBb6_1 := diamondState 6 1
    (.init (.aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
    (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot
    (.init (.scalar ⟨acc1 + stage2Delta c2, 4⟩))
  let sBb6_2 := diamondState 6 2
    (.init (.aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
    (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot .dead
  -- Stage 1 framed behind `@[irreducible] StageCut` (zero touching of `_4 = z`)
  have hStage1Framed :=
    stageCut_frame (ops := mirDetWpOps diamond2StageMirBody) (diamond_stage1_stepFrame zSlot)
      (canary2_stage1_within c1 x (by omega) (.init (boolScalar c2)))
  have hStage1Exact :
      StageCut (ops := mirDetWpOps diamond2StageMirBody)
        (· = sEntry) (· = sCut) postMir (fun _ => False) :=
    stageCut_weaken (ops := mirDetWpOps diamond2StageMirBody) (onDone' := postMir)
      (fun _ hEq => by subst hEq; exact ⟨⟨zSlot, rfl⟩, rfl, rfl⟩)
      (fun _ ⟨⟨l4, hEq⟩, hLoc4, _⟩ => by
        subst hEq
        change some l4 = some zSlot at hLoc4
        injection hLoc4 with hL4Eq
        subst hL4Eq; rfl)
      (fun _ hF => False.elim hF) (fun _ h => h) hStage1Framed
  -- PureLift evaluation of Stage 2 from cutpoint `bb3`
  have hEvalPure :
      Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params diamondStage2PurePlan retExpr =
        .ok ⟨.pair (.nat (acc1 + stage2Delta c2)) (.nat z), []⟩ := by
    cases c2 <;> rfl
  have hSpec : Anneal.PureLift.HoldsFnSpec
      (Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params diamondStage2PurePlan retExpr)
      post := by
    rw [hEvalPure]; rfl
  let stCut : Anneal.PureLift.SymState Anneal.PureLift.StdVal :=
    ⟨[⟨.bool c1, .unborrowed⟩, ⟨.bool c2, .unborrowed⟩, ⟨.nat x, .unborrowed⟩,
      ⟨.nat z, .unborrowed⟩, ⟨.nat acc1, .unborrowed⟩], [], [], [], [], 0⟩
  have hCutInit : ∀ mc, mc = sCut →
      ∃ st0,
        Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 ∧
        Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf [] st0 mc := by
    intro mc hMc; subst hMc
    refine ⟨stCut, rfl, ⟨trivial, trivial⟩,
      Anneal.PureLift.V2026_06_01Bridge.mirLocalsRel_of_localsRefine ?_⟩
    have hX4 : x < 256 ^ 4 := by omega
    have hZ4 : z < 256 ^ 4 := by omega
    have hAcc1 : acc1 < 256 ^ 4 := by
      cases c1 with
      | false => change x + 20 < 256 ^ 4; omega
      | true => change x + 10 < 256 ^ 4; omega
    exact ⟨fun _ => ⟨_, rfl, .bool c1⟩, fun _ => ⟨_, rfl, .bool c2⟩,
      fun _ => ⟨_, rfl, .nat hX4⟩, fun _ => ⟨_, rfl, .nat hZ4⟩,
      fun _ => ⟨_, rfl, .nat hAcc1⟩, trivial⟩
  have hCutSim : ∀ mc st0 out, mc = sCut →
      Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 →
      Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf [] st0 mc →
      Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params diamondStage2PurePlan retExpr =
        .ok out →
      ∃ mFinal,
        DetStageCut (mirDetStep diamond2StageMirBody) mc mFinal ∧
        Anneal.PureLift.V2026_06_01Bridge.MirReturnRel tagOf diamond2StageMirBody out mFinal [] := by
    intro mc st0 out hMc _ _ hEv
    subst hMc
    rw [hEvalPure] at hEv; injection hEv with hOut; subst hOut
    have hAcc1Lt : acc1 + 2 < 2 ^ 32 := by
      cases c1 with
      | false => change x + 20 + 2 < 2 ^ 32; omega
      | true => change x + 10 + 2 < 2 ^ 32; omega
    have hStepToBb6_0 : StepStageCut (mirDetStep diamond2StageMirBody) 3 sCut sBb6_0 :=
      canary2_stage2_stepStageCut c2 acc1 hAcc1Lt
        (.init (boolScalar c1)) (.init (.scalar ⟨x, 4⟩)) (.init (.scalar ⟨z, 4⟩))
    have hStepToBb6_2 : StepStageCut (mirDetStep diamond2StageMirBody) 5 sCut sBb6_2 :=
      hStepToBb6_0.trans
        (StepStageCut.step
          (mirDetStep_step_iff.mpr (rfl : Anneal.PureMirExec.mirStep diamond2StageMirBody sBb6_0 = .cont sBb6_1))
          (StepStageCut.step
            (mirDetStep_step_iff.mpr (rfl : Anneal.PureMirExec.mirStep diamond2StageMirBody sBb6_1 = .cont sBb6_2))
            (StepStageCut.refl _ 0 sBb6_2)))
    refine ⟨sBb6_2, DetStageCut.of_stepStageCut hStepToBb6_2,
      .aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩], {}, rfl, ?_, rfl⟩
    have hFinalLt : acc1 + stage2Delta c2 < 256 ^ 4 := by
      cases c2 with
      | false => change acc1 + 2 < 256 ^ 4; omega
      | true => change acc1 + 1 < 256 ^ 4; omega
    have hZ4 : z < 256 ^ 4 := by omega
    exact .pair (.nat hFinalLt) (.nat hZ4)
  exact mirWpConverges_stageCut_then_pureLift tagOf diamond2StageMirBody [] params
    diamondStage2PurePlan retExpr post (· = sEntry) (· = sCut) []
    hStage1Exact hSpec hCutInit hCutSim rfl

/-- `PureLift` `FlowPlan` lifting Stage 1 (`bb0 -> (bb1|bb2) -> bb3`) of
`diamond2StageMirBody`: locals `0..4` correspond to MIR `_1.._5` (`c1, c2, x, z, acc`). -/
def diamondStage1PurePlan : Anneal.PureLift.FlowPlan Anneal.PureLift.StdVal :=
  .branch (.use (.localSub 0 []))
    (.act (.assign (.localSub 4 [])
      (.unary (fun v => match v with | .nat n => some (.nat (n + 10)) | _ => none)
        (.localSub 2 []))))
    (.act (.assign (.localSub 4 [])
      (.unary (fun v => match v with | .nat n => some (.nat (n + 20)) | _ => none)
        (.localSub 2 []))))

/-- Full 2-stage sequential `PureLift` `FlowPlan` for `diamond2StageMirBody`,
composing Stage 1 and Stage 2 in `2 + 2` additive style. -/
def diamondFullPurePlan : Anneal.PureLift.FlowPlan Anneal.PureLift.StdVal :=
  .seq diamondStage1PurePlan diamondStage2PurePlan

/-- **Canary 2 (Full 2-Stage `PureLift` via `V2026Bridge.mir_pure_lift_sound_of_stepStageCut`)**:
Directly exercises `V2026Bridge.mir_pure_lift_sound_of_stepStageCut` from real
`initMachineState diamond2StageMirBody [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩]`
across BOTH stages using `StepStageCut.trans` (ZERO `2 × 2` path explosion on
both the live MIR simulation AND the `PureLift` evaluation!) for ALL symbolic
`(c1 c2 : Bool)` and `(x z : Nat)` (`x + 22 < 2^32`, `z < 2^32`). -/
theorem canary2_diamond_full_pureLift_sound (c1 c2 : Bool) (x z : Nat)
    (hX : x + 22 < 2 ^ 32) (hZ : z < 2 ^ 32) :
    let acc1 := x + stage1Delta c1
    let post : Anneal.PureLift.FuncOut Anneal.PureLift.StdVal → Prop :=
      fun out => out.ret = .pair (.nat (acc1 + stage2Delta c2)) (.nat z)
    MirWpConverges diamond2StageMirBody
      (initMachineState diamond2StageMirBody
        [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩])
      (fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost (fun lid => lid + 1) post o []) := by
  intro acc1 post
  let params : List (Anneal.PureLift.ParamInput Anneal.PureLift.StdVal) :=
    [⟨.byVal, .bool c1⟩, ⟨.byVal, .bool c2⟩, ⟨.byVal, .nat x⟩, ⟨.byVal, .nat z⟩]
  let retExpr : Anneal.PureLift.RvalOp Anneal.PureLift.StdVal :=
    .binary (fun a b => some (.pair a b)) (.localSub 4 []) (.localSub 3 [])
  let tagOf : Anneal.PureLift.LoanId → Nat := fun lid => lid + 1
  let m0 := initMachineState diamond2StageMirBody
    [boolScalar c1, boolScalar c2, .scalar ⟨x, 4⟩, .scalar ⟨z, 4⟩]
  let st0 : Anneal.PureLift.SymState Anneal.PureLift.StdVal :=
    ⟨[⟨.bool c1, .unborrowed⟩, ⟨.bool c2, .unborrowed⟩, ⟨.nat x, .unborrowed⟩,
      ⟨.nat z, .unborrowed⟩], [], [], [], [], 0⟩
  let st1 : Anneal.PureLift.SymState Anneal.PureLift.StdVal :=
    ⟨[⟨.bool c1, .unborrowed⟩, ⟨.bool c2, .unborrowed⟩, ⟨.nat x, .unborrowed⟩,
      ⟨.nat z, .unborrowed⟩, ⟨.nat acc1, .unborrowed⟩], [], [], [], [], 0⟩
  let st2 : Anneal.PureLift.SymState Anneal.PureLift.StdVal :=
    ⟨[⟨.bool c1, .unborrowed⟩, ⟨.bool c2, .unborrowed⟩, ⟨.nat x, .unborrowed⟩,
      ⟨.nat z, .unborrowed⟩, ⟨.nat (acc1 + stage2Delta c2), .unborrowed⟩], [], [], [], [], 0⟩
  -- Additive 2 + 2 PureLift evaluation (never `cases c1 <;> cases c2`!)
  have hStage1Pure :
      Anneal.PureLift.evalPlan Anneal.PureLift.stdValAlg diamondStage1PurePlan st0 =
        .ok (.continuing st1) := by
    cases c1 <;> rfl
  have hStage2Pure :
      Anneal.PureLift.evalPlan Anneal.PureLift.stdValAlg diamondStage2PurePlan st1 =
        .ok (.continuing st2) := by
    cases c2 <;> rfl
  have hEvalFull :
      Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params diamondFullPurePlan retExpr =
        .ok ⟨.pair (.nat (acc1 + stage2Delta c2)) (.nat z), []⟩ := by
    unfold Anneal.PureLift.evalFnValue diamondFullPurePlan
    have hInit0 : Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 := rfl
    rw [hInit0]
    dsimp only
    rw [Anneal.PureLift.evalPlan_seq Anneal.PureLift.stdValAlg
      diamondStage1PurePlan diamondStage2PurePlan st0 (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [hStage1Pure]
    dsimp only
    rw [hStage2Pure]
    rfl
  have hInit : ∃ st,
      Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st ∧
      Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf [] st m0 := by
    refine ⟨st0, rfl, ⟨trivial, trivial⟩,
      Anneal.PureLift.V2026_06_01Bridge.mirLocalsRel_of_localsRefine ?_⟩
    have hX4 : x < 256 ^ 4 := by omega
    have hZ4 : z < 256 ^ 4 := by omega
    exact ⟨fun _ => ⟨_, rfl, .bool c1⟩, fun _ => ⟨_, rfl, .bool c2⟩,
      fun _ => ⟨_, rfl, .nat hX4⟩, fun _ => ⟨_, rfl, .nat hZ4⟩, trivial⟩
  have hSpec : Anneal.PureLift.HoldsFnSpec
      (Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params diamondFullPurePlan retExpr)
      post := by
    rw [hEvalFull]; rfl
  refine mir_pure_lift_sound_of_stepStageCut tagOf diamond2StageMirBody [] params
    diamondFullPurePlan retExpr post m0 [] hInit hSpec ?_
  intro _ out _ _ hEv
  rw [hEvalFull] at hEv; injection hEv with hOut; subst hOut
  have hAcc1Lt : acc1 + 2 < 2 ^ 32 := by
    cases c1 with
    | false => change x + 20 + 2 < 2 ^ 32; omega
    | true => change x + 10 + 2 < 2 ^ 32; omega
  let zSlot : LocalSlot := .init (.scalar ⟨z, 4⟩)
  let sBb6_0 := diamondState 6 0 .uninit (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot (.init (.scalar ⟨acc1 + stage2Delta c2, 4⟩))
  let sBb6_1 := diamondState 6 1
    (.init (.aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
    (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot (.init (.scalar ⟨acc1 + stage2Delta c2, 4⟩))
  let sBb6_2 := diamondState 6 2
    (.init (.aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩]))
    (.init (boolScalar c1)) (.init (boolScalar c2))
    (.init (.scalar ⟨x, 4⟩)) zSlot .dead
  have hCut12 : StepStageCut (mirDetStep diamond2StageMirBody) 7 m0 sBb6_0 :=
    (canary2_stage1_stepStageCut c1 x (by omega) (.init (boolScalar c2)) zSlot).trans
      (canary2_stage2_stepStageCut c2 acc1 hAcc1Lt
        (.init (boolScalar c1)) (.init (.scalar ⟨x, 4⟩)) zSlot)
  have hCutFinal : StepStageCut (mirDetStep diamond2StageMirBody) 9 m0 sBb6_2 :=
    hCut12.trans
      (StepStageCut.step
        (mirDetStep_step_iff.mpr (rfl : Anneal.PureMirExec.mirStep diamond2StageMirBody sBb6_0 = .cont sBb6_1))
        (StepStageCut.step
          (mirDetStep_step_iff.mpr (rfl : Anneal.PureMirExec.mirStep diamond2StageMirBody sBb6_1 = .cont sBb6_2))
          (StepStageCut.refl _ 0 sBb6_2)))
  refine ⟨9, sBb6_2, hCutFinal,
    .aggregate 0 [.scalar ⟨acc1 + stage2Delta c2, 4⟩, .scalar ⟨z, 4⟩], {}, rfl, ?_, rfl⟩
  have hFinalLt : acc1 + stage2Delta c2 < 256 ^ 4 := by
    cases c2 with
    | false => change acc1 + 2 < 256 ^ 4; omega
    | true => change acc1 + 1 < 256 ^ 4; omega
  have hZ4 : z < 256 ^ 4 := by omega
  exact .pair (.nat hFinalLt) (.nat hZ4)

/-! ## 3. Canary 3 — Disjoint `ByteSubLens`, `AlignedSubLens`, Tree Borrows & Certified `MutSummaryChain` -/

/-! ### 3A. `Memory.globals` (`CapturedAllocation`), `AlignedSubLens`, `SliceCodec.paddedPair`, `decodeValueFromBytes`, `TypedAt`, Tree Borrows & Fail-Closed Rejections -/

/-- `SliceCodec` for a `u32` inside `Memory.globals` (`Option UInt8` bytes). -/
abbrev globalU32Codec : SliceCodec (Option UInt8) UInt32 4 :=
  SliceCodec.uint32 optUInt8ByteCodec

/-- `SliceCodec` for a `bool` inside `Memory.globals` (`Option UInt8` bytes). -/
abbrev globalBoolCodec : SliceCodec (Option UInt8) Bool 1 :=
  SliceCodec.bool optUInt8ByteCodec

/-- `SliceCodec` for a Rust-aligned 8-byte `(bool, [u8; 3], u32)` padded pair
inside `Memory.globals` (`1 + 3 + 4 = 8` bytes). -/
abbrev globalPaddedPairCodec : SliceCodec (Option UInt8) (Bool × UInt32) 8 :=
  SliceCodec.paddedPair 3 (some 0) globalBoolCodec globalU32Codec

/-- Disjoint aligned sub-lenses on mutable global allocation `allocId = 7`
(`align = 8`, 20 bytes):
* `[0..4)` header `u32` (align `2^2 = 4`),
* `[8..16)` padded `(bool, u32)` payload (align `2^3 = 8`),
* `[16..20)` untouched sibling `u32` (align `2^2 = 4`). -/
def hdrAligned : AlignedSubLens Nat := ⟨⟨7, 0, 4⟩, 2⟩
def payloadAligned : AlignedSubLens Nat := ⟨⟨7, 8, 8⟩, 3⟩
def siblingAligned : AlignedSubLens Nat := ⟨⟨7, 16, 4⟩, 2⟩

/-- Misaligned, out-of-bounds, and immutable lenses for fail-closed rejections. -/
def misalignedU32Lens : AlignedSubLens Nat := ⟨⟨7, 2, 4⟩, 2⟩
def misalignedU64Lens : AlignedSubLens Nat := ⟨⟨7, 4, 8⟩, 3⟩
def oobGlobalLens : ByteSubLens Nat := ⟨7, 18, 4⟩
def immutableGlobalLens : ByteSubLens Nat := ⟨8, 0, 4⟩

/-- Live frozen Tree Borrows entry keyed on `targetLocal = 7`, `[16..20)`.

Note on key spaces: `V2026_06_01` `BorrowEntry`s are keyed by
`(targetFrameDepth, targetLocal)` -- the trusted semantics does NOT attach Tree
Borrows state to `Memory.globals` allocations. This entry therefore lives in
the same numeric key space as global `allocId = 7` only through the
`Anneal.Memory.BorrowEntry.toByteRangePerm` view; Canary 3A uses it solely to
exercise the key-agnostic range non-interference lemma
(`borrowEntry_operational_non_interference_of_separated`) and to show that
global-allocation writes leave `Memory.borrows` bit-for-bit unchanged. Genuine
deref-write Tree Borrows interaction (`invalidateDerefWriteBorrows` over
`&mut [u8]` tags on a caller local) is exercised by Canary 3B. -/
def siblingGlobalBorrow : BorrowEntry :=
  { tag := 11, targetLocal := 7, targetProjection := [], perm := .frozen,
    rangeOffset := 16, rangeLen := 4, targetFrameDepth := 0 }

/-- Construct a real `V2026_06_01` `Memory` containing:
* mutable `CapturedAllocation` `allocId = 7` (`align = 8`, 20 bytes holding
  symbolic `initHdr`, `initFlag`, `initVal`, and `siblingVal`),
* immutable `CapturedAllocation` `allocId = 8` (`align = 4`, `mutability = .not`),
* live Tree Borrows entry `siblingGlobalBorrow`. -/
def mkCanaryGlobalMem (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal : UInt32) :
    Memory :=
  let pad4 : List (Option UInt8) := [some 0, some 0, some 0, some 0]
  let bytes20 : List (Option UInt8) :=
    globalU32Codec.enc initHdr ++ pad4 ++
    globalPaddedPairCodec.enc (initFlag, initVal) ++
    globalU32Codec.enc siblingVal
  { globals :=
      [{ allocId := 7, bytes := bytes20, relocations := [],
         align := { bytes := 8 }, mutability := .mut },
       { allocId := 8, bytes := [some 1, some 2, some 3, some 4], relocations := [],
         align := { bytes := 4 }, mutability := .not }]
    borrows := [siblingGlobalBorrow]
    nextAllocId := 9
    nextTag := 12 }

private theorem globalU32_enc_len (v : UInt32) :
    (globalU32Codec.enc v).length = 4 :=
  globalU32Codec.enc_length v

private theorem globalPaddedPair_enc_len (p : Bool × UInt32) :
    (globalPaddedPairCodec.enc p).length = 8 :=
  globalPaddedPairCodec.enc_length p

private theorem mkCanaryGlobalMem_lookup7 (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    lookupGlobalAlloc (mkCanaryGlobalMem initHdr initFlag initVal siblingVal).globals 7 =
      some { allocId := 7,
             bytes := globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
               globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal,
             relocations := [], align := { bytes := 8 }, mutability := .mut } := rfl

private theorem mkCanaryGlobalMem_lookup8 (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    lookupGlobalAlloc (mkCanaryGlobalMem initHdr initFlag initVal siblingVal).globals 8 =
      some { allocId := 8, bytes := [some 1, some 2, some 3, some 4],
             relocations := [], align := { bytes := 4 }, mutability := .not } := rfl

private theorem mkCanaryGlobalMem_hdr_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    hdrAligned.lens.getVal globalU32Codec
      (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) = some initHdr := by
  have hL1 := globalU32_enc_len initHdr
  have hL2 := globalPaddedPair_enc_len (initFlag, initVal)
  have hL3 := globalU32_enc_len siblingVal
  have hGet : hdrAligned.lens.get (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) =
      some (globalU32Codec.enc initHdr) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match Nat.ble 4
      (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length with
      | true => some (((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
          globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 0).take 4)
      | false => none) = some (globalU32Codec.enc initHdr)
    have hTot : (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length = 20 := by
      simp [hL1, hL2, hL3]
    rw [hTot]
    have hTake : ((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 0).take 4 =
        globalU32Codec.enc initHdr := by
      rw [List.drop_zero, List.append_assoc, List.append_assoc,
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hTake]
  exact ByteSubLens.getVal_of rfl hGet (globalU32Codec.dec_enc initHdr)

private theorem mkCanaryGlobalMem_payload_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    payloadAligned.lens.getVal globalPaddedPairCodec
      (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) = some (initFlag, initVal) := by
  have hL1 := globalU32_enc_len initHdr
  have hL2 := globalPaddedPair_enc_len (initFlag, initVal)
  have hL3 := globalU32_enc_len siblingVal
  have hGet : payloadAligned.lens.get (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) =
      some (globalPaddedPairCodec.enc (initFlag, initVal)) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match Nat.ble 16
      (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length with
      | true => some (((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
          globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 8).take 8)
      | false => none) = some (globalPaddedPairCodec.enc (initFlag, initVal))
    have hTot : (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length = 20 := by
      simp [hL1, hL2, hL3]
    rw [hTot]
    have hPreLen : (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0]).length = 8 := by
      simp [hL1]
    have hSlice : ((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 8).take 8 =
        globalPaddedPairCodec.enc (initFlag, initVal) := by
      rw [List.append_assoc (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0]),
        List.drop_left' hPreLen,
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hSlice]
  exact ByteSubLens.getVal_of rfl hGet (globalPaddedPairCodec.dec_enc (initFlag, initVal))

private theorem mkCanaryGlobalMem_sibling_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    siblingAligned.lens.getVal globalU32Codec
      (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) = some siblingVal := by
  have hL1 := globalU32_enc_len initHdr
  have hL2 := globalPaddedPair_enc_len (initFlag, initVal)
  have hL3 := globalU32_enc_len siblingVal
  have hGet : siblingAligned.lens.get (mkCanaryGlobalMem initHdr initFlag initVal siblingVal) =
      some (globalU32Codec.enc siblingVal) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match Nat.ble 20
      (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length with
      | true => some (((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
          globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 16).take 4)
      | false => none) = some (globalU32Codec.enc siblingVal)
    have hTot : (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).length = 20 := by
      simp [hL1, hL2, hL3]
    rw [hTot]
    have hPreLen : (globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal)).length = 16 := by
      simp [hL1, hL2]
    have hSlice : ((globalU32Codec.enc initHdr ++ [some 0, some 0, some 0, some 0] ++
        globalPaddedPairCodec.enc (initFlag, initVal) ++ globalU32Codec.enc siblingVal).drop 16).take 4 =
        globalU32Codec.enc siblingVal := by
      rw [List.drop_left' hPreLen, List.take_of_length_le (by omega)]
    rw [hSlice]
  exact ByteSubLens.getVal_of rfl hGet (globalU32Codec.dec_enc siblingVal)

/-- Unified mutation argument for the 2-call global summary chain. -/
inductive GlobalMutArg : Type where
  | setU32 (v : UInt32) : GlobalMutArg
  | setPaddedPair (b : Bool) (v : UInt32) : GlobalMutArg

/-- Summary 1: overwrite a `u32` sub-slice via `MutSummary.ofSliceCodec`,
returning the old `u32`. -/
def globalSetU32Sum : MutSummary (Option UInt8) GlobalMutArg UInt32 :=
  MutSummary.ofSliceCodec globalU32Codec fun old arg =>
    match arg with
    | .setU32 v => some (v, old)
    | _ => none

/-- Summary 2: overwrite an 8-byte padded `(bool, u32)` sub-slice via
`MutSummary.ofSliceCodec`, returning the old `u32` payload. -/
def globalSetPaddedPairSum : MutSummary (Option UInt8) GlobalMutArg UInt32 :=
  MutSummary.ofSliceCodec globalPaddedPairCodec fun old arg =>
    match arg with
    | .setPaddedPair b v => some ((b, v), old.2)
    | _ => none

/-- **Canary 3A (Global `CapturedAllocation`, `AlignedSubLens`, `SliceCodec.paddedPair`,
`decodeValueFromBytes`, `WritePreserves`, Tree Borrows, and Fail-Closed Rejections)**:
For ALL symbolic `(initHdr, initFlag, initVal, siblingVal, newHdr, newFlag, newVal)`:
1. Executes the 2-call `execMutSummaryChain` updating `hdr` and `payload`.
2. Proves exact post-values via BOTH `AlignedSubLens.getVal` AND trusted
   `decodeValueFromBytes` (`u32` header, `bool` flag, `u32` payload, `u32` sibling).
3. Proves untouched sibling preservation via `AlignedSubLens.get_execMutSummaryChain_disjoint`
   and `execMutSummaryChain_frame_disjoint` (ZERO raw byte-list destructuring!).
4. Proves `Memory.borrows`, `CapturedAllocation.align`, `CapturedAllocation.mutability`,
   and `memGlobalsAlignedAt` invariance via `WritePreserves`.
5. Proves range-level Tree Borrows non-interference on `siblingGlobalBorrow`
   (keyed on `targetLocal = 7`; see its docstring for the key-space caveat).
6. Proves fail-closed rejection of misaligned, out-of-bounds, and immutable lenses. -/
theorem canary3a_globalAlloc_aligned_chain_and_framing
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newHdr : UInt32)
    (newFlag : Bool) (newVal : UInt32) :
    let m0 := mkCanaryGlobalMem initHdr initFlag initVal siblingVal
    let calls : List (MutSummaryCall (Option UInt8) Nat GlobalMutArg UInt32) :=
      [⟨globalSetU32Sum, hdrAligned.lens, .setU32 newHdr⟩,
       ⟨globalSetPaddedPairSum, payloadAligned.lens, .setPaddedPair newFlag newVal⟩]
    ∃ m2,
      execMutSummaryChain calls m0 = some (m2, [initHdr, initVal]) ∧
      -- 1. Exact aligned post-state values via `AlignedSubLens.getVal`
      hdrAligned.getVal memGlobalsAlignedAt globalU32Codec m2 = some newHdr ∧
      payloadAligned.getVal memGlobalsAlignedAt globalPaddedPairCodec m2 = some (newFlag, newVal) ∧
      -- 2. Untouched sibling preserved via `AlignedSubLens.get_execMutSummaryChain_disjoint`
      siblingAligned.getVal memGlobalsAlignedAt globalU32Codec m2 = some siblingVal ∧
      -- 3. Trusted `decodeValueFromBytes` agreement on post-state `CapturedAllocation`
      (∃ alloc2, lookupGlobalAlloc m2.globals 7 = some alloc2 ∧
        (∃ bs, globalAllocSliceToAbstractBytes alloc2 0 4 = some bs ∧
          decodeValueFromBytes defaultCodecFuel testLayouts u32Ty bs =
            some (.scalar ⟨newHdr.toNat, 4⟩)) ∧
        (∃ bs, globalAllocSliceToAbstractBytes alloc2 8 1 = some bs ∧
          decodeValueFromBytes defaultCodecFuel testLayouts boolTy bs =
            some (.scalar ⟨if newFlag then 1 else 0, 1⟩)) ∧
        (∃ bs, globalAllocSliceToAbstractBytes alloc2 12 4 = some bs ∧
          decodeValueFromBytes defaultCodecFuel testLayouts u32Ty bs =
            some (.scalar ⟨newVal.toNat, 4⟩)) ∧
        (∃ bs, globalAllocSliceToAbstractBytes alloc2 16 4 = some bs ∧
          decodeValueFromBytes defaultCodecFuel testLayouts u32Ty bs =
            some (.scalar ⟨siblingVal.toNat, 4⟩))) ∧
      -- 4. `WritePreserves` invariance of `borrows` and allocation metadata
      m2.borrows = m0.borrows ∧
      (lookupGlobalAlloc m2.globals 7).map (fun a => a.align) = some { bytes := 8 } ∧
      (lookupGlobalAlloc m2.globals 7).map (fun a => a.mutability) = some .mut ∧
      -- 5. Range-level Tree Borrows non-interference (`targetLocal = 7` key space)
      (updateBorrowPermAtProj siblingGlobalBorrow 7 none [] 0 4 0 = siblingGlobalBorrow ∧
       updateBorrowPermAtProj siblingGlobalBorrow 7 none [] 8 8 0 = siblingGlobalBorrow) ∧
      -- 6. Fail-closed rejections: misaligned, OOB, immutable
      misalignedU32Lens.get memGlobalsAlignedAt m2 = none ∧
      misalignedU32Lens.set memGlobalsAlignedAt m2 (globalU32Codec.enc newHdr) = none ∧
      misalignedU64Lens.get memGlobalsAlignedAt m2 = none ∧
      oobGlobalLens.get m2 = none ∧
      oobGlobalLens.set m2 (globalU32Codec.enc newHdr) = none ∧
      immutableGlobalLens.get m2 = none ∧
      immutableGlobalLens.set m2 (globalU32Codec.enc newHdr) = none := by
  intro m0 calls
  have hHdr0 : hdrAligned.lens.getVal globalU32Codec m0 = some initHdr :=
    mkCanaryGlobalMem_hdr_getVal initHdr initFlag initVal siblingVal
  have hPay0 : payloadAligned.lens.getVal globalPaddedPairCodec m0 = some (initFlag, initVal) :=
    mkCanaryGlobalMem_payload_getVal initHdr initFlag initVal siblingVal
  have hSib0 : siblingAligned.lens.getVal globalU32Codec m0 = some siblingVal :=
    mkCanaryGlobalMem_sibling_getVal initHdr initFlag initVal siblingVal
  -- Execute call 1 (`hdr`) via `execMutSummary_ofSliceCodec_of`
  rcases execMutSummary_ofSliceCodec_of (sc := globalU32Codec)
      (fn := fun old arg => match arg with | GlobalMutArg.setU32 v => some (v, old) | _ => none)
      (arg := GlobalMutArg.setU32 newHdr)
      hHdr0 (v' := newHdr) (ret := initHdr) rfl with ⟨m1, hCall1, _, hHdr1_get⟩
  -- Disjointness proofs (pure offset arithmetic, zero byte destructuring)
  have hDisjHdrPay : ByteSubLens.Disjoint Memory hdrAligned.lens payloadAligned.lens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  have hDisjHdrSib : ByteSubLens.Disjoint Memory hdrAligned.lens siblingAligned.lens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  have hDisjPaySib : ByteSubLens.Disjoint Memory payloadAligned.lens siblingAligned.lens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  -- Frame `payload` across call 1 using `execMutSummary_frame_disjoint`
  have hPay1 : payloadAligned.lens.getVal globalPaddedPairCodec m1 = some (initFlag, initVal) := by
    have hEq := execMutSummary_frame_disjoint (Mem := Memory) hDisjHdrPay hCall1
    unfold ByteSubLens.getVal at hPay0 ⊢
    rw [hEq]
    exact hPay0
  -- Execute call 2 (`payload`) via `execMutSummary_ofSliceCodec_of`
  rcases execMutSummary_ofSliceCodec_of (sc := globalPaddedPairCodec)
      (fn := fun old arg => match arg with | GlobalMutArg.setPaddedPair b v => some ((b, v), old.2) | _ => none)
      (arg := GlobalMutArg.setPaddedPair newFlag newVal)
      hPay1 (v' := (newFlag, newVal)) (ret := initVal) rfl with ⟨m2, hCall2, _, hPay2_get⟩
  -- Assemble chain witness
  have hChain : execMutSummaryChain calls m0 = some (m2, [initHdr, initVal]) :=
    execMutSummaryChain_cons_of hCall1
      (execMutSummaryChain_cons_of hCall2 (execMutSummaryChain_nil m2))
  -- Frame `hdr` across call 2 via `execMutSummary_frame_disjoint`
  have hHdr2_get : hdrAligned.lens.getVal globalU32Codec m2 = some newHdr := by
    have hEq := execMutSummary_frame_disjoint (Mem := Memory) hDisjHdrPay.symm hCall2
    unfold ByteSubLens.getVal at hHdr1_get ⊢
    rw [hEq]
    exact hHdr1_get
  -- Alignment checks preserved across the entire chain via `WritePreserves`
  have hHdrOk0 : hdrAligned.ok memGlobalsAlignedAt m0 = true := by
    unfold AlignedSubLens.ok memGlobalsAlignedAt tableAlignedAt
    dsimp only [hdrAligned, m0]
    rw [← lookupGlobalAlloc_eq_tableFind, mkCanaryGlobalMem_lookup7]; dsimp only; decide
  have hPayOk0 : payloadAligned.ok memGlobalsAlignedAt m0 = true := by
    unfold AlignedSubLens.ok memGlobalsAlignedAt tableAlignedAt
    dsimp only [payloadAligned, m0]
    rw [← lookupGlobalAlloc_eq_tableFind, mkCanaryGlobalMem_lookup7]; dsimp only; decide
  have hSibOk0 : siblingAligned.ok memGlobalsAlignedAt m0 = true := by
    unfold AlignedSubLens.ok memGlobalsAlignedAt tableAlignedAt
    dsimp only [siblingAligned, m0]
    rw [← lookupGlobalAlloc_eq_tableFind, mkCanaryGlobalMem_lookup7]; dsimp only; decide
  have hHdrOk2 : hdrAligned.ok memGlobalsAlignedAt m2 = true :=
    (execMutSummaryChain_preserves (memGlobals_writePreserves_alignedAt 7 0 2) calls hChain).trans hHdrOk0
  have hPayOk2 : payloadAligned.ok memGlobalsAlignedAt m2 = true :=
    (execMutSummaryChain_preserves (memGlobals_writePreserves_alignedAt 7 8 3) calls hChain).trans hPayOk0
  have hSibOk2 : siblingAligned.ok memGlobalsAlignedAt m2 = true :=
    (execMutSummaryChain_preserves (memGlobals_writePreserves_alignedAt 7 16 2) calls hChain).trans hSibOk0
  -- Sibling framed across the entire chain via `AlignedSubLens.get_execMutSummaryChain_disjoint`
  have hAllDisjSib : AllCallsDisjoint Memory siblingAligned.lens calls :=
    ⟨hDisjHdrSib, hDisjPaySib, trivial⟩
  have hSibAlignedGetEq :
      siblingAligned.get memGlobalsAlignedAt m2 = siblingAligned.get memGlobalsAlignedAt m0 :=
    AlignedSubLens.get_execMutSummaryChain_disjoint memGlobals_writePreserves_alignedAt
      siblingAligned calls hAllDisjSib hChain
  have hSib2_get : siblingAligned.lens.getVal globalU32Codec m2 = some siblingVal := by
    have hEq := execMutSummaryChain_frame_disjoint siblingAligned.lens calls hAllDisjSib hChain
    unfold ByteSubLens.getVal at hSib0 ⊢
    rw [hEq]
    exact hSib0
  -- Metadata preservation via `WritePreserves`
  have hBorrows : m2.borrows = m0.borrows :=
    execMutSummaryChain_preserves memGlobals_writePreserves_borrows calls hChain
  have hAlignPres : (lookupGlobalAlloc m2.globals 7).map (fun a => a.align) = some { bytes := 8 } := by
    rw [execMutSummaryChain_preserves (memGlobals_writePreserves_align 7) calls hChain,
      mkCanaryGlobalMem_lookup7]; rfl
  have hMutPres : (lookupGlobalAlloc m2.globals 7).map (fun a => a.mutability) = some .mut := by
    rw [execMutSummaryChain_preserves (memGlobals_writePreserves_mutability 7) calls hChain,
      mkCanaryGlobalMem_lookup7]; rfl
  -- Extract post-state `alloc2` for `decodeValueFromBytes` bridges (no external
  -- `relocations = []` assumption needed; `capturedAllocView.writable` enforces it!)
  have hAlloc2 : ∃ alloc2, lookupGlobalAlloc m2.globals 7 = some alloc2 := by
    cases hF : lookupGlobalAlloc m2.globals 7 with
    | none => rw [hF] at hMutPres; cases hMutPres
    | some a => exact ⟨a, rfl⟩
  rcases hAlloc2 with ⟨alloc2, hFind2⟩
  -- Zoom into `payloadAligned.lens` (`bool` at +0, `u32` at +4) without raw byte destructuring
  have hPayZoom := ByteSubLens.getVal_paddedPair (by decide) (by decide) hPay2_get
  have hFlag2_get : (payloadAligned.lens.zoom 0 1).getVal globalBoolCodec m2 = some newFlag :=
    hPayZoom.1
  have hVal2_get : (payloadAligned.lens.zoom 4 4).getVal globalU32Codec m2 = some newVal :=
    hPayZoom.2
  -- Immutable alloc 8 preserved across writes to alloc 7
  have hFind8 : ∃ a8, lookupGlobalAlloc m2.globals 8 = some a8 ∧ a8.mutability = .not := by
    have hMut8 := execMutSummaryChain_preserves (memGlobals_writePreserves_mutability 8) calls hChain
    rw [mkCanaryGlobalMem_lookup8] at hMut8
    cases hF8 : lookupGlobalAlloc m2.globals 8 with
    | none => rw [hF8] at hMut8; cases hMut8
    | some a8 =>
      rw [hF8] at hMut8; injection hMut8 with hImm
      exact ⟨a8, rfl, hImm⟩
  rcases hFind8 with ⟨a8, hFind8', hImm8⟩
  -- Alignment rejections (preserved from `m0`)
  have hMisU32 : memGlobalsAlignedAt m2 7 2 2 = false := by
    rw [execMutSummaryChain_preserves (memGlobals_writePreserves_alignedAt 7 2 2) calls hChain]
    unfold memGlobalsAlignedAt tableAlignedAt
    dsimp only [m0]
    rw [← lookupGlobalAlloc_eq_tableFind, mkCanaryGlobalMem_lookup7]; dsimp only; decide
  have hMisU64 : memGlobalsAlignedAt m2 7 4 3 = false := by
    rw [execMutSummaryChain_preserves (memGlobals_writePreserves_alignedAt 7 4 3) calls hChain]
    unfold memGlobalsAlignedAt tableAlignedAt
    dsimp only [m0]
    rw [← lookupGlobalAlloc_eq_tableFind, mkCanaryGlobalMem_lookup7]; dsimp only; decide
  -- OOB rejection on 20-byte alloc 7 (`offset = 18, len = 4 → 22 > 20`)
  have hAllocLen2 : alloc2.bytes.length = 20 := by
    have hLenPres : memGlobalsByteStoreOps.WritePreserves
        (fun m : Memory => (lookupGlobalAlloc m.globals 7).map (fun a => a.bytes.length)) := by
      intro m m' addr off bs hW
      rcases ofTable_write_inv hW with ⟨t', hTW, hM'⟩
      rcases tableWrite_inv hTW with ⟨a, hF, _, hB, hRep⟩
      rw [hM', hRep]
      dsimp only
      rw [lookupGlobalAlloc_eq_tableFind, lookupGlobalAlloc_eq_tableFind]
      have hId : a.allocId = addr := tableFind_allocId hF
      let aNew := capturedAllocView.setBytes a (listSplice (capturedAllocView.bytes a) off bs)
      cases hEq7 : Nat.beq a.allocId 7 with
      | false =>
        have hNe : Nat.beq (capturedAllocView.allocId aNew) 7 = false := hEq7
        rw [tableFind_replace_ne (aNew := aNew) hNe]
      | true =>
        have hA7 : a.allocId = 7 := Nat.eq_of_beq_eq_true hEq7
        have hFindA : tableFind capturedAllocView (capturedAllocView.allocId a) m.globals = some a := by
          change tableFind capturedAllocView a.allocId m.globals = some a
          rw [hId]; exact hF
        have hRep : tableFind capturedAllocView a.allocId
            (tableReplace capturedAllocView aNew m.globals) = some aNew :=
          tableFind_replace_same (aNew := aNew) hFindA rfl
        have hFindA' : tableFind capturedAllocView a.allocId m.globals = some a := hFindA
        rw [← hA7, hRep, hFindA']
        dsimp only [aNew, capturedAllocView, Option.map]
        exact congrArg some (listSplice_length a.bytes off bs hB)
    have hL := execMutSummaryChain_preserves hLenPres calls hChain
    rw [hFind2, mkCanaryGlobalMem_lookup7] at hL
    dsimp only [Option.map] at hL
    injection hL with hEq
  have hOobGet : oobGlobalLens.get m2 = none := by
    rw [ByteSubLens.get_of_pos m2 (by decide)]
    change tableRead capturedAllocView m2.globals 7 18 4 = none
    unfold tableRead
    rw [← lookupGlobalAlloc_eq_tableFind, hFind2]
    dsimp only [capturedAllocView]
    rw [hAllocLen2]
    change (match (match alloc2.mutability with
        | .mut => alloc2.relocations.isEmpty | .not => false) && false with
      | true => _ | false => none) = none
    rw [Bool.and_false]
  have hOobSet : oobGlobalLens.set m2 (globalU32Codec.enc newHdr) = none := by
    rw [ByteSubLens.set_of_pos m2 (by decide) (globalU32_enc_len newHdr)]
    dsimp only [ByteStoreOps.writeBytes?, ByteStoreOps.ofTable, oobGlobalLens]
    unfold tableWrite
    rw [← lookupGlobalAlloc_eq_tableFind, hFind2]
    dsimp only [capturedAllocView]
    rw [globalU32_enc_len newHdr, hAllocLen2]
    cases alloc2.mutability <;> cases alloc2.relocations.isEmpty <;> rfl
  -- Operational Tree Borrows non-interference on `siblingGlobalBorrow`
  have hTbHdr := (borrowEntry_operational_non_interference_of_separated
    siblingGlobalBorrow [] hdrAligned.lens [] rfl rfl (Or.inr (Or.inr (by decide)))).2
  have hTbPay := (borrowEntry_operational_non_interference_of_separated
    siblingGlobalBorrow [] payloadAligned.lens [] rfl rfl (Or.inr (Or.inr (by decide)))).2
  refine ⟨m2, hChain,
    (ByteSubLens.getValIf_of_ok globalU32Codec hdrAligned.lens hHdrOk2).trans hHdr2_get,
    (ByteSubLens.getValIf_of_ok globalPaddedPairCodec payloadAligned.lens hPayOk2).trans hPay2_get,
    (ByteSubLens.getValIf_of_ok globalU32Codec siblingAligned.lens hSibOk2).trans hSib2_get,
    ⟨alloc2, hFind2,
      decodeValueFromBytes_u32_of_getVal testLayouts hFind2 hHdr2_get,
      decodeValueFromBytes_bool_of_getVal testLayouts hFind2 hFlag2_get boolTy.layoutIdx,
      decodeValueFromBytes_u32_of_getVal testLayouts hFind2 hVal2_get,
      decodeValueFromBytes_u32_of_getVal testLayouts hFind2 hSib2_get⟩,
    hBorrows, hAlignPres, hMutPres, ⟨hTbHdr, hTbPay⟩,
    AlignedSubLens.get_none_of_unaligned misalignedU32Lens hMisU32,
    AlignedSubLens.set_none_of_unaligned misalignedU32Lens _ hMisU32,
    AlignedSubLens.get_none_of_unaligned misalignedU64Lens hMisU64,
    hOobGet, hOobSet,
    memGlobals_get_none_of_immutable hFind8' hImm8,
    memGlobals_set_none_of_immutable hFind8' hImm8⟩

/-- Mutable 16-byte global `allocId = 9` whose bytes `[0..8)` hold a pointer to
global `allocId = 7` (one relocation at offset 0) and whose bytes `[8..16)` are
plain integers. -/
def provGlobalAlloc : CapturedAllocation :=
  { allocId := 9, bytes := List.replicate 16 (some 0),
    relocations := [(0, { allocId := 7, offsetBytes := 0 })],
    align := { bytes := 8 }, mutability := .mut }

def provGlobalMem : Memory := { globals := [provGlobalAlloc] }

/-- **Canary 3A (Provenance-Aware vs Raw `AbstractByte` Edge, Fail-Closed)**:
1. Trusted `globalAllocSliceToAbstractBytes` tags the pointer bytes `[0..4)` with
   provenance `some (7, _)`, but leaves `[8..12)` provenance-free.
2. Even so, the raw `Option UInt8` lens view refuses to read or write ANY window
   of the relocation-carrying allocation (including the provenance-free one), so
   no lens read can strip provenance and no lens write can leave a stale
   relocation table that desynchronises the view from trusted semantics. -/
theorem canary3a_provenance_failClosed :
    (∃ bs, globalAllocSliceToAbstractBytes provGlobalAlloc 0 4 = some bs ∧
      bs.all (fun b => match b with | .init _ (some (7, _)) => true | _ => false) = true) ∧
    globalAllocSliceToAbstractBytes provGlobalAlloc 8 4 =
      some (List.replicate 4 (.init 0 none)) ∧
    (⟨9, 0, 4⟩ : ByteSubLens Nat).get provGlobalMem = none ∧
    (⟨9, 8, 4⟩ : ByteSubLens Nat).get provGlobalMem = none ∧
    (⟨9, 0, 8⟩ : ByteSubLens Nat).set provGlobalMem (List.replicate 8 (some 0)) = none ∧
    (⟨9, 8, 4⟩ : ByteSubLens Nat).set provGlobalMem (globalU32Codec.enc 5) = none :=
  ⟨⟨_, rfl, rfl⟩, rfl,
    memGlobals_get_none_of_relocated rfl (List.cons_ne_nil _ _),
    memGlobals_get_none_of_relocated rfl (List.cons_ne_nil _ _),
    memGlobals_set_none_of_relocated rfl (List.cons_ne_nil _ _),
    memGlobals_set_none_of_relocated rfl (List.cons_ne_nil _ _)⟩

/-- **Canary 3A (`SepLogicLenses.TypedAt`, `MirTypedByteCodec`, & `encodeValueToBytes` bridge)**:
Connects `ByteSubLens.getVal` and `ByteSubLens.setVal` on `ByteMem`
(`List AbstractByte`) directly to `SepLogicLenses.TypedAt`,
`PureLift.V2026_06_01Bridge.MirTypedByteCodec`, trusted `decodeValueFromBytes`,
and trusted `encodeValueToBytes` for any symbolic `v v' : { n : Nat // n < 256 ^ 4 }`. -/
theorem canary3a_byteMem_typedAt_and_mirTypedByteCodec
    (v v' : { n : Nat // n < 256 ^ 4 }) (suffix : Anneal.SepLogicLenses.ByteMem) :
    let mCodec := Anneal.PureLift.V2026_06_01Bridge.u32MirCodec testLayouts
    let bm : Anneal.SepLogicLenses.ByteMem := mCodec.codec.encode v ++ suffix
    let L : ByteSubLens Unit := ⟨(), 0, 4⟩
    Anneal.SepLogicLenses.TypedAt mCodec.codec 0 v bm ∧
    (∃ bs, L.get bm = some bs ∧
      decodeValueFromBytes defaultCodecFuel testLayouts u32Ty bs =
        some (.scalar ⟨v.val, 4⟩)) ∧
    (∃ bm', L.setVal (sliceCodecOfMirTypedByteCodec mCodec) bm v' = some bm' ∧
      Anneal.SepLogicLenses.TypedAt mCodec.codec 0 v' bm' ∧
      L.get bm' = encodeValueToBytes defaultCodecFuel testLayouts u32Ty (.scalar ⟨v'.val, 4⟩)) ∧
    encodeValueToBytes defaultCodecFuel testLayouts u32Ty (.scalar ⟨(UInt32.ofNat v.val).toNat, 4⟩) =
      some (((SliceCodec.uint32 optUInt8ByteCodec).enc (UInt32.ofNat v.val)).map
        optUInt8ToAbstractByte) := by
  intro mCodec bm L
  have hEncLen : (mCodec.codec.encode v).length = 4 := mCodec.codec.encode_len v
  have hTyped : Anneal.SepLogicLenses.TypedAt mCodec.codec 0 v bm := by
    rw [Anneal.SepLogicLenses.typedAt_iff]
    refine ⟨by simp [bm, hEncLen], ?_⟩
    have hSlice : (bm.drop 0).take 4 = mCodec.codec.encode v := by
      rw [List.drop_zero, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [hSlice]
    exact mCodec.codec.decode_encode v
  have hGetVal :
      L.getVal (sliceCodecOfMirTypedByteCodec mCodec) bm = some v :=
    (byteMem_getVal_iff_typedAt mCodec.codec (by decide) bm L rfl v).mpr hTyped
  rcases ByteSubLens.getVal_inv hGetVal with ⟨_, _, hGetRaw, _⟩
  rcases ByteSubLens.set_isSome_of_get ((sliceCodecOfMirTypedByteCodec mCodec).enc v') hGetRaw
    ((sliceCodecOfMirTypedByteCodec mCodec).enc_length v') with ⟨bm', hSet⟩
  have hPostSet := byteMem_setVal_mirTypedByteCodec_typedAt mCodec (by decide) bm bm' L rfl v' hSet
  exact ⟨hTyped,
    (byteMem_getVal_mirTypedByteCodec_iff_decode mCodec bm L rfl v).mp hGetVal,
    ⟨bm', hSet, hPostSet.1, hPostSet.2⟩,
    encodeValueToBytes_u32_eq_sliceCodec testLayouts (UInt32.ofNat v.val)⟩

/-- **Canary 3A (`ByteMem` Provenance Non-Laundering + `SliceTypedAt` Bridge)**:
Audits BOTH `abstractByteCodec` and `MirTypedByteCodec` on `byteMemByteStoreOps`
for ALL symbolic `(ptrLo : UInt32)`, `(prov : Nat × Nat)`, and
`(oldVal newVal e0 e1 : { n : Nat // n < 256 ^ 4 })`:
1. On a 12-byte `ByteMem` holding an 8-byte pointer `[0..8)` tagged with
   provenance `some prov` followed by a provenance-free `u32` at `[8..12)`:
   - Strict `SliceCodec.uint32 abstractByteCodec` **fails closed (`= none`)** on
     the provenance-carrying pointer window `[0..4)` (so it can NEVER strip
     provenance or launder `init b (some p) ↦ init b none`), while succeeding
     and round-tripping (`Exact`) on the provenance-free window `[8..12)`.
   - Writing `[8..12)` through `sliceCodecOfMirTypedByteCodec (u32MirCodec testLayouts)`
     writes strictly provenance-free bytes (`provenanceFree = true`, never
     forging `none → some p`) AND preserves `[0..8)`'s `.init b (some prov)`
     bytes bit-for-bit via `byteMem_setVal_mirTypedByteCodec_provenanceFree`.
   - Reading `[0..4)` through `u32MirCodec` matches trusted `decodeValueFromBytes`
     at `u32` (which intentionally drops provenance on integer loads per Rust
     semantics).
2. On a live 2-element `SepLogicLenses.SliceTypedAt` buffer `[e0, e1]`,
   `V2026Bridge.byteMem_getVal_of_sliceTypedAt` zooms cleanly to both element `0`
   and element `1`. -/
theorem canary3a_byteMem_provenance_and_sliceTypedAt
    (ptrLo : UInt32) (prov : Nat × Nat)
    (oldVal newVal e0 e1 : { n : Nat // n < 256 ^ 4 }) :
    let mCodec := Anneal.PureLift.V2026_06_01Bridge.u32MirCodec testLayouts
    let ptrBytes : List AbstractByte := encodeLittleEndianBytes ptrLo.toNat 8 (some prov)
    let bm : Anneal.SepLogicLenses.ByteMem := ptrBytes ++ mCodec.codec.encode oldVal
    let ptrLens8 : ByteSubLens Unit := ⟨(), 0, 8⟩
    let ptrLens4 : ByteSubLens Unit := ⟨(), 0, 4⟩
    let intLens : ByteSubLens Unit := ⟨(), 8, 4⟩
    let strictU32 := SliceCodec.uint32 abstractByteCodec
    -- 1. Strict `abstractByteCodec` fails closed on provenance-carrying bytes
    ptrLens4.getVal strictU32 bm = none ∧
    -- 2. Strict `abstractByteCodec` succeeds on provenance-free `[8..12)`
    intLens.getVal strictU32 bm = some (UInt32.ofNat oldVal.val) ∧
    -- 3. `MirTypedByteCodec` write on `[8..12)` is provenance-free & frames `[0..8)` provenance
    (∃ bm',
      intLens.setVal (sliceCodecOfMirTypedByteCodec mCodec) bm newVal = some bm' ∧
      (∃ bs, intLens.get bm' = some bs ∧
        Anneal.PureLift.MirLiftCoreInterop.provenanceFree bs = true) ∧
      ptrLens8.get bm' = some ptrBytes) ∧
    -- 4. `MirTypedByteCodec` read on `[0..4)` agrees with trusted `decodeValueFromBytes .u32`
    (∃ x : { n : Nat // n < 256 ^ 4 },
      ptrLens4.getVal (sliceCodecOfMirTypedByteCodec mCodec) bm = some x ∧
      ∃ bs, ptrLens4.get bm = some bs ∧
        decodeValueFromBytes defaultCodecFuel testLayouts u32Ty bs =
          some (.scalar ⟨x.val, 4⟩)) ∧
    -- 5. `SliceTypedAt` zoom bridge (`byteMem_getVal_of_sliceTypedAt`)
    (let sliceBm : Anneal.SepLogicLenses.ByteMem :=
       mCodec.codec.encode e0 ++ mCodec.codec.encode e1
     let sliceLens : ByteSubLens Unit := ⟨(), 0, 2 * 4⟩
     (sliceLens.zoom (0 * 4) 4).getVal (sliceCodecOfByteLensCodec mCodec.codec) sliceBm = some e0 ∧
     (sliceLens.zoom (1 * 4) 4).getVal (sliceCodecOfByteLensCodec mCodec.codec) sliceBm = some e1) := by
  intro mCodec ptrBytes bm ptrLens8 ptrLens4 intLens strictU32
  have hPtrLen : ptrBytes.length = 8 := rfl
  have hOldLen : (mCodec.codec.encode oldVal).length = 4 := mCodec.codec.encode_len oldVal
  have hBmLen : bm.length = 12 := by simp [bm, hPtrLen, hOldLen]
  -- 1. `ptrLens4.getVal strictU32 bm = none` because byte 0 carries `some prov`
  have hPtr4Get : ptrLens4.get bm = some (encodeLittleEndianBytes ptrLo.toNat 4 (some prov)) := by
    rw [ByteSubLens.get_of_pos bm (by decide)]
    dsimp only [ByteStoreOps.readBytes?, ptrLens4]
    rw [hBmLen]
    rfl
  have hStrictFail : ptrLens4.getVal strictU32 bm = none := by
    unfold ByteSubLens.getVal
    rw [hPtr4Get]
    rfl
  -- 2. `intLens.getVal strictU32 bm = some (UInt32.ofNat oldVal.val)`
  have hIntGet : intLens.get bm = some (mCodec.codec.encode oldVal) := by
    rw [ByteSubLens.get_of_pos bm (by decide)]
    dsimp only [ByteStoreOps.readBytes?, intLens]
    rw [hBmLen]
    change some ((bm.drop 8).take 4) = some (mCodec.codec.encode oldVal)
    have hSlice : (bm.drop 8).take 4 = mCodec.codec.encode oldVal := by
      dsimp only [bm]
      rw [List.drop_left' hPtrLen, List.take_of_length_le (by omega)]
    rw [hSlice]
  have hOldValEncEq : mCodec.codec.encode oldVal = strictU32.enc (UInt32.ofNat oldVal.val) := by
    have hLt : oldVal.val < 2 ^ 32 := oldVal.property
    have hMod : (UInt32.ofNat oldVal.val).toNat = oldVal.val := Nat.mod_eq_of_lt hLt
    show encodeLittleEndianBytes oldVal.val 4 none =
      [abstractByteCodec.enc (BitVec.ofNat 8 (UInt32.ofNat oldVal.val).toNat),
       abstractByteCodec.enc (BitVec.ofNat 8 ((UInt32.ofNat oldVal.val).toNat / 256)),
       abstractByteCodec.enc (BitVec.ofNat 8 ((UInt32.ofNat oldVal.val).toNat / 256 / 256)),
       abstractByteCodec.enc (BitVec.ofNat 8 ((UInt32.ofNat oldVal.val).toNat / 256 / 256 / 256))]
    rw [hMod]
    rfl
  have hStrictOk : intLens.getVal strictU32 bm = some (UInt32.ofNat oldVal.val) := by
    refine ByteSubLens.getVal_of rfl hIntGet ?_
    rw [hOldValEncEq]
    exact strictU32.dec_enc (UInt32.ofNat oldVal.val)
  -- 3. `MirTypedByteCodec` write on `[8..12)` + provenance-free + `[0..8)` framing
  have hPtr8Get : ptrLens8.get bm = some ptrBytes := by
    rw [ByteSubLens.get_of_pos bm (by decide)]
    dsimp only [ByteStoreOps.readBytes?, ptrLens8]
    rw [hBmLen]
    change some ((bm.drop 0).take 8) = some ptrBytes
    have hSlice : (bm.drop 0).take 8 = ptrBytes := by
      dsimp only [bm]
      rw [List.drop_zero, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [hSlice]
  rcases ByteSubLens.set_isSome_of_get ((sliceCodecOfMirTypedByteCodec mCodec).enc newVal)
      hIntGet ((sliceCodecOfMirTypedByteCodec mCodec).enc_length newVal) with ⟨bm', hSet⟩
  have hProvFree := byteMem_setVal_mirTypedByteCodec_provenanceFree mCodec hSet
  have hDisj : ByteSubLens.Disjoint Anneal.SepLogicLenses.ByteMem intLens ptrLens8 :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inr (by decide)))
  have hPtr8Pres : ptrLens8.get bm' = some ptrBytes :=
    (hProvFree.2 ptrLens8 hDisj).trans hPtr8Get
  -- 4. Trusted `decodeValueFromBytes .u32` agreement on `[0..4)`
  have hPtr4Val : ptrLens4.getVal (sliceCodecOfMirTypedByteCodec mCodec) bm =
      some ⟨ptrLo.toNat, ptrLo.toBitVec.isLt⟩ := by
    refine ByteSubLens.getVal_of rfl hPtr4Get ?_
    rw [sliceCodecOfMirTypedByteCodec,
      sliceCodecOfByteLensCodec_dec_of_length mCodec.codec rfl]
    change (match decodeLittleEndianBytes (encodeLittleEndianBytes ptrLo.toNat 4 (some prov)) with
      | some (v, _) =>
        if h : v < 256 ^ 4 then some (⟨v, h⟩ : { n : Nat // n < 256 ^ 4 }) else none
      | none => none) = some (⟨ptrLo.toNat, ptrLo.toBitVec.isLt⟩ : { n : Nat // n < 256 ^ 4 })
    have hDecLe := Anneal.SepLogicLenses.ByteLensCodec.decodeLE_encodeLE 4 ptrLo.toNat (some prov)
      ptrLo.toBitVec.isLt
    cases hD : decodeLittleEndianBytes (encodeLittleEndianBytes ptrLo.toNat 4 (some prov)) with
    | none => rw [hD] at hDecLe; cases hDecLe
    | some pair =>
      rcases pair with ⟨w, rp⟩
      rw [hD] at hDecLe
      have hW : w = ptrLo.toNat := Option.some.inj hDecLe
      subst hW
      dsimp only
      have hLt256 : ptrLo.toNat < 256 ^ 4 := ptrLo.toBitVec.isLt
      rw [dite_eq_left hLt256]
  have hPtr4Trusted :=
    (byteMem_getVal_mirTypedByteCodec_iff_decode mCodec bm ptrLens4 rfl
      ⟨ptrLo.toNat, ptrLo.toBitVec.isLt⟩).mp hPtr4Val
  -- 5. `SliceTypedAt` zoom bridge on `[e0, e1]`
  let sliceBm : Anneal.SepLogicLenses.ByteMem :=
    mCodec.codec.encode e0 ++ mCodec.codec.encode e1
  have hE0Len : (mCodec.codec.encode e0).length = 4 := mCodec.codec.encode_len e0
  have hE1Len : (mCodec.codec.encode e1).length = 4 := mCodec.codec.encode_len e1
  have hSliceTyped :
      Anneal.SepLogicLenses.SliceTypedAt mCodec.codec
        (Anneal.SepLogicLenses.WidePtrVal.mk ⟨7, 0⟩ 2) [e0, e1] sliceBm := by
    refine ⟨rfl, by simp [sliceBm, hE0Len, hE1Len], ?_⟩
    intro i hi
    match i, hi with
    | 0, _ =>
      rw [Anneal.SepLogicLenses.typedAt_iff]
      refine ⟨by simp [sliceBm, hE0Len, hE1Len], ?_⟩
      have hSl : (sliceBm.drop 0).take 4 = mCodec.codec.encode e0 := by
        dsimp only [sliceBm]
        rw [List.drop_zero, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
      rw [hSl]; exact mCodec.codec.decode_encode e0
    | 1, _ =>
      rw [Anneal.SepLogicLenses.typedAt_iff]
      refine ⟨by simp [sliceBm, hE0Len, hE1Len], ?_⟩
      have hSl : (sliceBm.drop 4).take 4 = mCodec.codec.encode e1 := by
        dsimp only [sliceBm]
        rw [List.drop_left' hE0Len, List.take_of_length_le (by omega)]
      rw [hSl]; exact mCodec.codec.decode_encode e1
  exact ⟨hStrictFail, hStrictOk,
    ⟨bm', hSet, hProvFree.1, hPtr8Pres⟩,
    ⟨⟨ptrLo.toNat, ptrLo.toBitVec.isLt⟩, hPtr4Val, hPtr4Trusted⟩,
    ⟨byteMem_getVal_of_sliceTypedAt (by decide) hSliceTyped (i := 0) (by simp),
     byteMem_getVal_of_sliceTypedAt (by decide) hSliceTyped (i := 1) (by simp)⟩⟩

/-! ### 3B. Real Mutating `V2026_06_01` `CapturedMir` Callees Behind `@[irreducible] MutSummaryOutcomeCut` + Multi-Call `execMutSummaryChain` → `MirWpConverges` -/

/-- Real `V2026_06_01` `CapturedMir` callee 1: serializes symbolic `val : u32`
into 4 little-endian bytes and writes them through `&mut [u8]` fat pointer `_1`
into the caller's `[u8; N]` buffer in `Memory.callerLocals`, returning `val`.
```rust
fn write_u32_le(buf: &mut [u8], val: u32) -> u32 {
    let b0 = val as u8;
    let b1 = (val >> 8) as u8;
    let b2 = (val >> 16) as u8;
    let b3 = (val >> 24) as u8;
    (*buf) = [b0, b1, b2, b3];
    val
}
```
Locals: `_0.._9` (`10` locals; caller referent slots live at index `≥ 12`). -/
def writeU32SliceBody : CapturedMir :=
  mkBody "write_u32_le" 2
    [decl .mut u32Ty, decl .not refMutSliceU8Ty, decl .not u32Ty,
     decl .mut u8Ty, decl .mut u32Ty, decl .mut u8Ty,
     decl .mut u32Ty, decl .mut u8Ty, decl .mut u32Ty, decl .mut u8Ty]
    [mkBb
       [mkSt (.storageLive 3),
        mkSt (.assign (pl 3) (.cast .intToInt (.copy (pl 2)) u8Ty)),
        mkSt (.storageLive 4),
        mkSt (.assign (pl 4) (.binaryOp .shr (.copy (pl 2)) (u32C 8))),
        mkSt (.storageLive 5),
        mkSt (.assign (pl 5) (.cast .intToInt (.copy (pl 4)) u8Ty)),
        mkSt (.storageLive 6),
        mkSt (.assign (pl 6) (.binaryOp .shr (.copy (pl 2)) (u32C 16))),
        mkSt (.storageLive 7),
        mkSt (.assign (pl 7) (.cast .intToInt (.copy (pl 6)) u8Ty)),
        mkSt (.storageLive 8),
        mkSt (.assign (pl 8) (.binaryOp .shr (.copy (pl 2)) (u32C 24))),
        mkSt (.storageLive 9),
        mkSt (.assign (pl 9) (.cast .intToInt (.copy (pl 8)) u8Ty)),
        mkSt (.assign (pl 1 [.deref])
          (.aggregate (.array u8Ty)
            [.copy (pl 3), .copy (pl 5), .copy (pl 7), .copy (pl 9)])),
        mkSt (.assign (pl 0) (.use (.copy (pl 2))))]
       .return_]

/-- Real `V2026_06_01` `CapturedMir` callee 2: serializes a Rust-aligned 8-byte
padded pair `(flag: bool, [0u8; 3], val: u32)` into `&mut [u8]` slice `_1`
in `Memory.callerLocals`, returning `val`.
Locals: `_0.._11` (`12` locals; caller referent slots live at index `≥ 12`). -/
def writePaddedPairSliceBody : CapturedMir :=
  mkBody "write_padded_pair" 3
    [decl .mut u32Ty, decl .not refMutSliceU8Ty, decl .not boolTy, decl .not u32Ty,
     decl .mut u8Ty, decl .mut u8Ty, decl .mut u32Ty, decl .mut u8Ty,
     decl .mut u32Ty, decl .mut u8Ty, decl .mut u32Ty, decl .mut u8Ty]
    [mkBb
       [mkSt (.storageLive 4),
        mkSt (.assign (pl 4) (.cast .intToInt (.copy (pl 2)) u8Ty)),
        mkSt (.storageLive 5),
        mkSt (.assign (pl 5) (.cast .intToInt (.copy (pl 3)) u8Ty)),
        mkSt (.storageLive 6),
        mkSt (.assign (pl 6) (.binaryOp .shr (.copy (pl 3)) (u32C 8))),
        mkSt (.storageLive 7),
        mkSt (.assign (pl 7) (.cast .intToInt (.copy (pl 6)) u8Ty)),
        mkSt (.storageLive 8),
        mkSt (.assign (pl 8) (.binaryOp .shr (.copy (pl 3)) (u32C 16))),
        mkSt (.storageLive 9),
        mkSt (.assign (pl 9) (.cast .intToInt (.copy (pl 8)) u8Ty)),
        mkSt (.storageLive 10),
        mkSt (.assign (pl 10) (.binaryOp .shr (.copy (pl 3)) (u32C 24))),
        mkSt (.storageLive 11),
        mkSt (.assign (pl 11) (.cast .intToInt (.copy (pl 10)) u8Ty)),
        mkSt (.assign (pl 1 [.deref])
          (.aggregate (.array u8Ty)
            [.copy (pl 4), u8C 0, u8C 0, u8C 0,
             .copy (pl 5), .copy (pl 7), .copy (pl 9), .copy (pl 11)])),
        mkSt (.assign (pl 0) (.use (.copy (pl 3))))]
       .return_]

/-- Real panicking `V2026_06_01` `CapturedMir` callee: executes
`assert!(false)` and terminates with `.panic`. -/
def panickingSliceBody : CapturedMir :=
  mkBody "panicking_slice_writer" 2
    [decl .mut u32Ty, decl .not refMutSliceU8Ty, decl .not u32Ty]
    [mkBb [] (.assert (boolC false) true 0 .continue_)]

/-- Address of a caller-owned `[u8; N]` referent slot in `Memory.callerLocals`
eligible for real `&mut [u8]` slice callee calls (`localIdx ≥ 12`). -/
structure SliceCallAddr : Type where
  localIdx : Nat
  deriving DecidableEq, Repr

private def isUniquePerm : TreeBorrowPerm → Bool
  | .unique => true
  | _ => false

private theorem perm_eq_unique_of_isUniquePerm {p : TreeBorrowPerm}
    (h : isUniquePerm p = true) : p = .unique := by
  cases p <;> first | rfl | cases h

/-- Decidable check that a `BorrowEntry` is a flat, root-level, caller-owned
(`targetLocal ≥ 12`), positive-range entry on frame depth `0`. -/
private def borrowFlatRoot (e : BorrowEntry) : Bool :=
  Nat.beq e.targetFrameDepth 0 && e.targetProjection.isEmpty &&
    e.parentTag.isNone && Nat.ble 12 e.targetLocal && Nat.blt 0 e.rangeLen

/-- Decidable non-overlap check between two distinct `BorrowEntry`s:
distinct tags and either distinct `targetLocal` or disjoint byte ranges. -/
private def borrowsDisjointPair (e₁ e₂ : BorrowEntry) : Bool :=
  Bool.not (Nat.beq e₁.tag e₂.tag) &&
    (Bool.not (Nat.beq e₁.targetLocal e₂.targetLocal) ||
      Nat.ble (e₁.rangeOffset + e₁.rangeLen) e₂.rangeOffset ||
      Nat.ble (e₂.rangeOffset + e₂.rangeLen) e₁.rangeOffset)

/-- Decidable well-formedness of a live Tree Borrows table: every entry is a
flat caller-owned root borrow, and every pair of distinct list entries has
distinct tags and non-overlapping byte ranges (so tags are unique and every
disjoint slice write preserves the entire borrow table). -/
private def borrowsTableDisjoint : List BorrowEntry → Bool
  | [] => true
  | e :: rest =>
    borrowFlatRoot e && rest.all (fun e₂ => borrowsDisjointPair e e₂) &&
      borrowsTableDisjoint rest

/-- Find a live `.unique` borrow entry in `bs` covering `[off, off + len)` on
`localIdx`. -/
private def findCoveringUniqueBorrow (bs : List BorrowEntry) (localIdx off len : Nat) :
    Option BorrowEntry :=
  bs.find? fun e =>
    isUniquePerm e.perm && Nat.beq e.targetLocal localIdx &&
      borrowFlatRoot e && Nat.ble e.rangeOffset off &&
      Nat.ble (off + len) (e.rangeOffset + e.rangeLen)

/-- Pure decidable ABI readiness guard on raw `V2026_06_01.MirSemantics.Memory`:
checks only non-byte metadata (`activeCallee`, `callStack`, `activeProtectors`,
`callees`, `borrows`, and `localIdx ≥ 12`), invariant across all `callerLocals`
byte writes. -/
private def sliceCallAbiReady (m : Memory) (a : SliceCallAddr) (off len : Nat) : Bool :=
  m.activeCallee.isNone && m.callStack.isEmpty && m.activeProtectors.isEmpty &&
    m.callees.isEmpty && Nat.ble 12 a.localIdx && borrowsTableDisjoint m.borrows &&
    (findCoveringUniqueBorrow m.borrows a.localIdx off len).isSome

private theorem sliceCallAbiReady_mono_sub {m : Memory} {a : SliceCallAddr}
    {off len rel k : Nat} (hLe : rel + k ≤ len)
    (hReady : sliceCallAbiReady m a off len = true) :
    sliceCallAbiReady m a (off + rel) k = true := by
  unfold sliceCallAbiReady at hReady ⊢
  have hPre := boolAnd_left hReady
  have hFind := boolAnd_right hReady
  rw [hPre]
  cases hF : findCoveringUniqueBorrow m.borrows a.localIdx off len with
  | none => rw [hF] at hFind; cases hFind
  | some e =>
    unfold findCoveringUniqueBorrow at hF ⊢
    rcases List.find?_eq_some_iff_append.mp hF with ⟨hPred, _, _, hApp, _⟩
    have hSub :
        (isUniquePerm e.perm && Nat.beq e.targetLocal a.localIdx &&
          borrowFlatRoot e && Nat.ble e.rangeOffset (off + rel) &&
          Nat.ble (off + rel + k) (e.rangeOffset + e.rangeLen)) = true := by
      have h1 := boolAnd_left hPred
      have hEnd := Nat.le_of_ble_eq_true (boolAnd_right hPred)
      have h2 := boolAnd_left h1
      have hStart := Nat.le_of_ble_eq_true (boolAnd_right h1)
      rw [h2, Nat.ble_eq_true_of_le (by omega), Nat.ble_eq_true_of_le (by omega)]
      rfl
    have hMem : e ∈ m.borrows := by rw [hApp]; exact List.mem_append_right _ (List.Mem.head _)
    cases hF' : List.find? (fun e =>
        isUniquePerm e.perm && Nat.beq e.targetLocal a.localIdx &&
          borrowFlatRoot e && Nat.ble e.rangeOffset (off + rel) &&
          Nat.ble (off + rel + k) (e.rangeOffset + e.rangeLen)) m.borrows with
    | some _ => rfl
    | none =>
      have hFalse := List.find?_eq_none.mp hF' e hMem
      exact absurd hSub hFalse

/-- Raw `Memory` `ByteStoreOps` for ABI-ready caller-owned `[u8; N]` slices,
delegating all byte storage directly to `V2026Bridge.memCallerByteStoreOps`. -/
local instance sliceCallByteStoreOps : ByteStoreOps Memory SliceCallAddr UInt8 where
  readBytes? m a off len :=
    match sliceCallAbiReady m a off len with
    | false => none
    | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len
  writeBytes? m a off bs :=
    match sliceCallAbiReady m a off bs.length with
    | false => none
    | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs
  addrDisjoint a₁ off₁ len₁ a₂ off₂ len₂ :=
    a₁ ≠ a₂ ∨ off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁

private theorem sliceCallAbiReady_of_memCallerWrite {m m' : Memory} {idx off : Nat}
    {bs : List UInt8} (hW : memCallerByteStoreOps.writeBytes? m ⟨idx⟩ off bs = some m')
    (a : SliceCallAddr) (o l : Nat) :
    sliceCallAbiReady m' a o l = sliceCallAbiReady m a o l := by
  have hSame : m'.activeCallee = m.activeCallee ∧ m'.callStack = m.callStack ∧
      m'.activeProtectors = m.activeProtectors ∧ m'.callees = m.callees ∧
      m'.borrows = m.borrows := by
    dsimp [ByteStoreOps.writeBytes?] at hW
    cases hG : listGet? m.callerLocals idx with
    | none => simp only [hG] at hW; cases hW
    | some slot =>
      simp only [hG] at hW
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at hW; cases hW
      | some bytes =>
        simp only [hS] at hW
        cases hB : Nat.ble (off + bs.length) bytes.length with
        | false => simp only [hB] at hW; cases hW
        | true =>
          simp only [hB] at hW
          cases hSet : listSet? m.callerLocals idx (u8BytesToSlot (listSplice bytes off bs)) with
          | none => simp only [hSet] at hW; cases hW
          | some cl' =>
            simp only [hSet] at hW; injection hW with hEq; subst hEq
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold sliceCallAbiReady
  rw [hSame.1, hSame.2.1, hSame.2.2.1, hSame.2.2.2.1, hSame.2.2.2.2]

local instance sliceCallLawfulByteStoreOps :
    LawfulByteStoreOps Memory SliceCallAddr UInt8 where
  read_len := by
    intro m a off len bs h
    change (match sliceCallAbiReady m a off len with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len) = some bs at h
    cases hR : sliceCallAbiReady m a off len with
    | false => rw [hR] at h; cases h
    | true => rw [hR] at h; exact memCallerLawfulByteStoreOps.read_len h
  read_sub := by
    intro m a off len rel k bs h hLe
    change (match sliceCallAbiReady m a off len with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len) = some bs at h
    change (match sliceCallAbiReady m a (off + rel) k with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ (off + rel) k) = _
    cases hR : sliceCallAbiReady m a off len with
    | false => rw [hR] at h; cases h
    | true =>
      rw [hR] at h
      rw [sliceCallAbiReady_mono_sub hLe hR]
      exact memCallerLawfulByteStoreOps.read_sub h hLe
  write_sub := by
    intro m a off len rel old sub h hLe
    change (match sliceCallAbiReady m a off len with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len) = some old at h
    change (match sliceCallAbiReady m a (off + rel) sub.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ (off + rel) sub) =
      (match sliceCallAbiReady m a off (listSplice old rel sub).length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off (listSplice old rel sub))
    cases hR : sliceCallAbiReady m a off len with
    | false => rw [hR] at h; cases h
    | true =>
      rw [hR] at h
      have hOldLen : old.length = len := memCallerLawfulByteStoreOps.read_len h
      have hSpLen : (listSplice old rel sub).length = len :=
        (listSplice_length old rel sub (by omega)).trans hOldLen
      rw [sliceCallAbiReady_mono_sub hLe hR, hSpLen, hR]
      exact memCallerLawfulByteStoreOps.write_sub h hLe
  read_write_same := by
    intro m m' a off bs hW
    change (match sliceCallAbiReady m a off bs.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs) = some m' at hW
    change (match sliceCallAbiReady m' a off bs.length with
      | false => none | true => memCallerByteStoreOps.readBytes? m' ⟨a.localIdx⟩ off bs.length) = _
    cases hR : sliceCallAbiReady m a off bs.length with
    | false => rw [hR] at hW; cases hW
    | true =>
      rw [hR] at hW
      rw [sliceCallAbiReady_of_memCallerWrite hW, hR]
      exact memCallerLawfulByteStoreOps.read_write_same hW
  write_read_same := by
    intro m a off len bs h
    change (match sliceCallAbiReady m a off len with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len) = some bs at h
    change (match sliceCallAbiReady m a off bs.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs) = _
    cases hR : sliceCallAbiReady m a off len with
    | false => rw [hR] at h; cases h
    | true =>
      rw [hR] at h
      have hLen : bs.length = len := memCallerLawfulByteStoreOps.read_len h
      rw [hLen, hR]
      exact memCallerLawfulByteStoreOps.write_read_same h
  write_of_read := by
    intro m a off len old bs h hLen
    change (match sliceCallAbiReady m a off len with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a.localIdx⟩ off len) = some old at h
    cases hR : sliceCallAbiReady m a off len with
    | false => rw [hR] at h; cases h
    | true =>
      rw [hR] at h
      rcases memCallerLawfulByteStoreOps.write_of_read (bs := bs) h hLen with ⟨m', hW⟩
      refine ⟨m', ?_⟩
      change (match sliceCallAbiReady m a off bs.length with
        | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs) = some m'
      rw [hLen, hR]; exact hW
  write_write_same := by
    intro m m₁ a off bs₁ bs₂ hW hLen
    change (match sliceCallAbiReady m a off bs₁.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs₁) = some m₁ at hW
    change (match sliceCallAbiReady m₁ a off bs₂.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m₁ ⟨a.localIdx⟩ off bs₂) =
      (match sliceCallAbiReady m a off bs₂.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs₂)
    cases hR : sliceCallAbiReady m a off bs₁.length with
    | false => rw [hR] at hW; cases hW
    | true =>
      rw [hR] at hW
      rw [sliceCallAbiReady_of_memCallerWrite hW, hLen, hR]
      exact memCallerLawfulByteStoreOps.write_write_same hW hLen
  read_write_disjoint := by
    intro m m' a₁ off₁ bs₁ a₂ off₂ len₂ hDisj hW
    change (match sliceCallAbiReady m a₁ off₁ bs₁.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a₁.localIdx⟩ off₁ bs₁) = some m' at hW
    change (match sliceCallAbiReady m' a₂ off₂ len₂ with
      | false => none | true => memCallerByteStoreOps.readBytes? m' ⟨a₂.localIdx⟩ off₂ len₂) =
      (match sliceCallAbiReady m a₂ off₂ len₂ with
      | false => none | true => memCallerByteStoreOps.readBytes? m ⟨a₂.localIdx⟩ off₂ len₂)
    cases hR₁ : sliceCallAbiReady m a₁ off₁ bs₁.length with
    | false => rw [hR₁] at hW; cases hW
    | true =>
      rw [hR₁] at hW
      rw [sliceCallAbiReady_of_memCallerWrite hW]
      cases hR₂ : sliceCallAbiReady m a₂ off₂ len₂ with
      | false => rfl
      | true =>
        have hDisj' : memCallerByteStoreOps.addrDisjoint ⟨a₁.localIdx⟩ off₁ bs₁.length
            ⟨a₂.localIdx⟩ off₂ len₂ := by
          rcases hDisj with hNe | hR
          · exact Or.inl (fun hEq => hNe (by cases a₁; cases a₂; injection hEq with h; subst h; rfl))
          · exact Or.inr hR
        exact memCallerLawfulByteStoreOps.read_write_disjoint hDisj' hW
  write_write_comm := by
    intro m m₁ m₂ a₁ off₁ bs₁ a₂ off₂ bs₂ hDisj hW₁ hW₂
    change (match sliceCallAbiReady m a₁ off₁ bs₁.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a₁.localIdx⟩ off₁ bs₁) = some m₁ at hW₁
    change (match sliceCallAbiReady m a₂ off₂ bs₂.length with
      | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a₂.localIdx⟩ off₂ bs₂) = some m₂ at hW₂
    cases hR₁ : sliceCallAbiReady m a₁ off₁ bs₁.length with
    | false => rw [hR₁] at hW₁; cases hW₁
    | true =>
      rw [hR₁] at hW₁
      cases hR₂ : sliceCallAbiReady m a₂ off₂ bs₂.length with
      | false => rw [hR₂] at hW₂; cases hW₂
      | true =>
        rw [hR₂] at hW₂
        have hDisj' : memCallerByteStoreOps.addrDisjoint ⟨a₁.localIdx⟩ off₁ bs₁.length
            ⟨a₂.localIdx⟩ off₂ bs₂.length := by
          rcases hDisj with hNe | hR
          · exact Or.inl (fun hEq => hNe (by cases a₁; cases a₂; injection hEq with h; subst h; rfl))
          · exact Or.inr hR
        rcases memCallerLawfulByteStoreOps.write_write_comm hDisj' hW₁ hW₂ with ⟨m₃, h12, h21⟩
        refine ⟨m₃, ?_, ?_⟩
        · change (match sliceCallAbiReady m₁ a₂ off₂ bs₂.length with
            | false => none | true => memCallerByteStoreOps.writeBytes? m₁ ⟨a₂.localIdx⟩ off₂ bs₂) = some m₃
          rw [sliceCallAbiReady_of_memCallerWrite hW₁, hR₂]; exact h12
        · change (match sliceCallAbiReady m₂ a₁ off₁ bs₁.length with
            | false => none | true => memCallerByteStoreOps.writeBytes? m₂ ⟨a₁.localIdx⟩ off₁ bs₁) = some m₃
          rw [sliceCallAbiReady_of_memCallerWrite hW₂, hR₁]; exact h21
  addrDisjoint_of_separated := fun h => h
  addrDisjoint_symm := by
    intro a₁ a₂ o₁ l₁ o₂ l₂ h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  addrDisjoint_mono_sub := by
    intro a₁ a₂ o₁ l₁ o₂ l₂ o₁' l₁' o₂' l₂' h1 h2 h3 h4 hD
    rcases hD with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

private theorem sliceCall_writePreserves_borrows :
    sliceCallByteStoreOps.WritePreserves (fun m : Memory => m.borrows) := by
  intro m m' a off bs hW
  change (match sliceCallAbiReady m a off bs.length with
    | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs) = some m' at hW
  cases hR : sliceCallAbiReady m a off bs.length with
  | false => rw [hR] at hW; cases hW
  | true => rw [hR] at hW; exact memCaller_writePreserves_borrows m m' ⟨a.localIdx⟩ off bs hW

private theorem sliceCall_writePreserves_globals :
    sliceCallByteStoreOps.WritePreserves (fun m : Memory => m.globals) := by
  intro m m' a off bs hW
  change (match sliceCallAbiReady m a off bs.length with
    | false => none | true => memCallerByteStoreOps.writeBytes? m ⟨a.localIdx⟩ off bs) = some m' at hW
  cases hR : sliceCallAbiReady m a off bs.length with
  | false => rw [hR] at hW; cases hW
  | true => rw [hR] at hW; exact memCaller_writePreserves_globals m m' ⟨a.localIdx⟩ off bs hW

/-! #### Pure helper lemmas bridging trusted `MirSemantics` slice writes & Tree Borrows to `listSplice` -/

private theorem u8BytesToValues_length :
    ∀ bs : List UInt8, (u8BytesToValues bs).length = bs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (u8BytesToValues_length rest)

private theorem takeValues_u8BytesToValues :
    ∀ (n : Nat) (bs : List UInt8),
      takeValues n (u8BytesToValues bs) = u8BytesToValues (bs.take n)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: rest => congrArg (Value.scalar ⟨b.toNat, 1⟩ :: ·) (takeValues_u8BytesToValues n rest)

private theorem dropValues_u8BytesToValues :
    ∀ (n : Nat) (bs : List UInt8),
      dropValues n (u8BytesToValues bs) = u8BytesToValues (bs.drop n)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: rest => dropValues_u8BytesToValues n rest

private theorem appendValueList_u8BytesToValues :
    ∀ (xs ys : List UInt8),
      appendValueList (u8BytesToValues xs) (u8BytesToValues ys) = u8BytesToValues (xs ++ ys)
  | [], _ => rfl
  | b :: rest, ys =>
    congrArg (Value.scalar ⟨b.toNat, 1⟩ :: ·) (appendValueList_u8BytesToValues rest ys)

private theorem replaceSubslice_u8BytesToValues (bytes bs : List UInt8) (off : Nat)
    (hBound : off + bs.length ≤ bytes.length) :
    replaceSubslice (u8BytesToValues bytes) off (off + bs.length) false (u8BytesToValues bs) =
      some (u8BytesToValues (listSplice bytes off bs)) := by
  unfold replaceSubslice
  dsimp only
  have hLenBytes : Trusted.Sequence.length (u8BytesToValues bytes) = bytes.length :=
    u8BytesToValues_length bytes
  have hLenBs : Trusted.Sequence.length (u8BytesToValues bs) = bs.length :=
    u8BytesToValues_length bs
  have hSub : (off + bs.length).sub off = bs.length := Nat.add_sub_cancel_left off bs.length
  rw [hLenBytes, Nat.ble_eq_true_of_le hBound, Nat.ble_eq_true_of_le (Nat.le_add_right off bs.length),
    hSub, hLenBs, Nat.beq_refl]
  dsimp only
  rw [takeValues_u8BytesToValues, dropValues_u8BytesToValues,
    appendValueList_u8BytesToValues, appendValueList_u8BytesToValues, ← List.append_assoc]
  rfl

private theorem exactByteDivAux_one :
    ∀ (k acc : Nat), exactByteDivAux k k 1 acc = some (acc + k)
  | 0, acc => by unfold exactByteDivAux; simp
  | k + 1, acc => by
    unfold exactByteDivAux
    change exactByteDivAux k k 1 (acc + 1) = some (acc + (k + 1))
    rw [exactByteDivAux_one k (acc + 1)]
    congr 1; omega

private theorem byteOffsetToElemIdx?_one (off : Nat) :
    byteOffsetToElemIdx? off 1 = some off := by
  cases off with
  | zero => rfl
  | succ k =>
    unfold byteOffsetToElemIdx?
    change exactByteDivAux (k + 1) (k + 1) 1 0 = some (k + 1)
    rw [exactByteDivAux_one (k + 1) 0, Nat.zero_add]

private theorem valueListContainsUninit_u8BytesToValues :
    ∀ (bs : List UInt8), valueListContainsUninit (u8BytesToValues bs) = false
  | [] => rfl
  | _ :: rest => valueListContainsUninit_u8BytesToValues rest

private theorem writeSliceFatPtr_u8_whole (frameLocals : List LocalSlot)
    (bytes bs : List UInt8) (tag off : Nat)
    (hPos : 0 < bs.length) (hBound : off + bs.length ≤ bytes.length) :
    writeSliceFatPtrTargetValue frameLocals (.aggregate 0 (u8BytesToValues bytes)) []
      ⟨tag, off⟩ 8 ⟨bs.length, 8⟩ [] (.aggregate 0 (u8BytesToValues bs)) =
      .ok (.aggregate 0 (u8BytesToValues (listSplice bytes off bs))) := by
  cases bytes with
  | nil =>
    have hZ : ([] : List UInt8).length = 0 := rfl
    rw [hZ] at hBound; omega
  | cons b0 rest =>
    unfold writeSliceFatPtrTargetValue
    have hRead : readSliceBackingAggregate? frameLocals (.aggregate 0 (u8BytesToValues (b0 :: rest)))
        [] bs.length = some ([], 0, u8BytesToValues (b0 :: rest)) := by
      unfold readSliceBackingAggregate?
      dsimp only [normalizeSubsliceProjections, stripTransparentProjections,
        splitLastConstantIndex?, readProjectedValue, valueContainsUninit]
      rw [valueListContainsUninit_u8BytesToValues (b0 :: rest)]; rfl
    have hStride : inferElemListByteStride (u8BytesToValues (b0 :: rest)) = 1 := rfl
    dsimp only
    rw [hRead]
    dsimp only
    rw [hStride, byteOffsetToElemIdx?_one]
    dsimp only
    have hAdd0 : off.add 0 = off := Nat.add_zero off
    have hLen : Trusted.Sequence.length (u8BytesToValues (b0 :: rest)) = (b0 :: rest).length :=
      u8BytesToValues_length (b0 :: rest)
    have hBle : (off.add bs.length).ble (b0 :: rest).length = true :=
      Nat.ble_eq_true_of_le hBound
    rw [hAdd0, hLen, hBle]
    change (match replaceSubslice (u8BytesToValues (b0 :: rest)) off (off + bs.length) false
        (u8BytesToValues bs) with
      | some elems' => ProjWriteResult.ok (.aggregate 0 elems')
      | none => ProjWriteResult.ub) = _
    rw [replaceSubslice_u8BytesToValues (b0 :: rest) bs off hBound]

private theorem writeSliceFatPtr_u8_oob (frameLocals : List LocalSlot)
    (b0 : UInt8) (rest : List UInt8) (newElems : List Value) (tag off : Nat)
    (hOob : (b0 :: rest).length < off + newElems.length) :
    writeSliceFatPtrTargetValue frameLocals (.aggregate 0 (u8BytesToValues (b0 :: rest))) []
      ⟨tag, off⟩ 8 ⟨newElems.length, 8⟩ [] (.aggregate 0 newElems) = .ub := by
  unfold writeSliceFatPtrTargetValue
  have hRead : readSliceBackingAggregate? frameLocals (.aggregate 0 (u8BytesToValues (b0 :: rest)))
      [] newElems.length = some ([], 0, u8BytesToValues (b0 :: rest)) := by
    unfold readSliceBackingAggregate?
    dsimp only [normalizeSubsliceProjections, stripTransparentProjections,
      splitLastConstantIndex?, readProjectedValue, valueContainsUninit]
    rw [valueListContainsUninit_u8BytesToValues (b0 :: rest)]; rfl
  have hStride : inferElemListByteStride (u8BytesToValues (b0 :: rest)) = 1 := rfl
  dsimp only
  rw [hRead]
  dsimp only
  rw [hStride, byteOffsetToElemIdx?_one]
  dsimp only
  have hAdd0 : off.add 0 = off := Nat.add_zero off
  have hLen : Trusted.Sequence.length (u8BytesToValues (b0 :: rest)) = (b0 :: rest).length :=
    u8BytesToValues_length (b0 :: rest)
  have hBle : (off.add newElems.length).ble (b0 :: rest).length = false := by
    change Nat.ble (off + newElems.length) (b0 :: rest).length = false
    exact natBle_false_of_not_le (by omega)
  rw [hAdd0, hLen, hBle]
  rfl

private theorem borrowsDisjointPair_symm {e₁ e₂ : BorrowEntry}
    (h : borrowsDisjointPair e₁ e₂ = true) :
    borrowsDisjointPair e₂ e₁ = true := by
  unfold borrowsDisjointPair at h ⊢
  have hNe := boolAnd_left h
  have hDisj := boolAnd_right h
  have hTagNe : e₁.tag ≠ e₂.tag := by
    intro hEq; rw [hEq, Nat.beq_refl] at hNe; cases hNe
  have hNe' : Bool.not (Nat.beq e₂.tag e₁.tag) = true := by
    rw [natBeq_false_of_not_eq (Ne.symm hTagNe)]; rfl
  rw [hNe']
  cases hLoc : Nat.beq e₁.targetLocal e₂.targetLocal with
  | false =>
    have hLocNe : e₁.targetLocal ≠ e₂.targetLocal := by
      intro hEq; rw [hEq, Nat.beq_refl] at hLoc; cases hLoc
    rw [natBeq_false_of_not_eq (Ne.symm hLocNe)]; rfl
  | true =>
    have hLocEq : e₁.targetLocal = e₂.targetLocal := Nat.eq_of_beq_eq_true hLoc
    rw [hLoc, Bool.not_true, Bool.false_or] at hDisj
    rw [hLocEq, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.true_and]
    cases h1 : Nat.ble (e₁.rangeOffset + e₁.rangeLen) e₂.rangeOffset with
    | true =>
      rw [Bool.or_true]
    | false =>
      rw [h1, Bool.false_or] at hDisj
      rw [hDisj]; rfl

private theorem borrowsTableDisjoint_props :
    ∀ {bs : List BorrowEntry}, borrowsTableDisjoint bs = true →
      (∀ e, e ∈ bs → borrowFlatRoot e = true) ∧
      (∀ e₁ e₂, e₁ ∈ bs → e₂ ∈ bs → e₁ = e₂ ∨ borrowsDisjointPair e₁ e₂ = true)
  | [], _ => And.intro (fun _ h => nomatch h) (fun _ _ h _ => nomatch h)
  | hd :: tl, h => by
    unfold borrowsTableDisjoint at h
    have hHead := boolAnd_left h
    have hTail := boolAnd_right h
    have hRootHd := boolAnd_left hHead
    have hAllHd := List.all_eq_true.mp (boolAnd_right hHead)
    rcases borrowsTableDisjoint_props hTail with ⟨hFlatTl, hPairTl⟩
    refine ⟨?_, ?_⟩
    · intro e hMem
      cases hMem with
      | head => exact hRootHd
      | tail _ hIn => exact hFlatTl e hIn
    · intro e₁ e₂ h₁ h₂
      cases h₁ with
      | head =>
        cases h₂ with
        | head => exact Or.inl rfl
        | tail _ hIn₂ => exact Or.inr (hAllHd e₂ hIn₂)
      | tail _ hIn₁ =>
        cases h₂ with
        | head => exact Or.inr (borrowsDisjointPair_symm (hAllHd e₁ hIn₁))
        | tail _ hIn₂ => exact hPairTl e₁ e₂ hIn₁ hIn₂

private theorem lookupBorrow_of_disjoint :
    ∀ {bs : List BorrowEntry} {w : BorrowEntry},
      borrowsTableDisjoint bs = true → w ∈ bs → lookupBorrow bs w.tag = some w
  | [], _, _, h => nomatch h
  | hd :: tl, w, hDisj, hMem => by
    unfold lookupBorrow
    rcases borrowsTableDisjoint_props hDisj with ⟨_, hPair⟩
    cases hMem with
    | head => rw [Nat.beq_refl]
    | tail _ hIn =>
      have hHead := boolAnd_left hDisj
      have hTail := boolAnd_right hDisj
      have hP := List.all_eq_true.mp (boolAnd_right hHead) w hIn
      have hTagNe : Nat.beq hd.tag w.tag = false := by
        have hNot := boolAnd_left hP
        cases hB : Nat.beq hd.tag w.tag with
        | false => rfl
        | true => rw [hB] at hNot; cases hNot
      rw [hTagNe]
      exact lookupBorrow_of_disjoint hTail hIn

private theorem borrowFlatRoot_unpack {e : BorrowEntry} (h : borrowFlatRoot e = true) :
    e.targetFrameDepth = 0 ∧ e.targetProjection = [] ∧ e.parentTag = none ∧
      12 ≤ e.targetLocal ∧ 0 < e.rangeLen := by
  unfold borrowFlatRoot at h
  have h4 := boolAnd_left h
  have hLen := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true (boolAnd_right h))
  have h3 := boolAnd_left h4
  have hLoc := Nat.le_of_ble_eq_true (boolAnd_right h4)
  have h2 := boolAnd_left h3
  have hPar : e.parentTag = none := by
    have hP := boolAnd_right h3
    cases hEq : e.parentTag with | none => rfl | some _ => rw [hEq] at hP; cases hP
  have hDepth := Nat.eq_of_beq_eq_true (boolAnd_left h2)
  have hProj : e.targetProjection = [] := by
    have hP := boolAnd_right h2
    cases hEq : e.targetProjection with | nil => rfl | cons _ _ => rw [hEq] at hP; cases hP
  exact ⟨hDepth, hProj, hPar, hLoc, hLen⟩

private theorem invalidateConflictingBorrows_of_lt12 :
    ∀ {bs : List BorrowEntry} (dstLocal : Nat),
      dstLocal < 12 → (∀ e, e ∈ bs → borrowFlatRoot e = true) →
      invalidateConflictingBorrows bs dstLocal none 0 = bs
  | [], _, _, _ => rfl
  | hd :: tl, dstLocal, hLt, hFlat => by
    unfold invalidateConflictingBorrows updateBorrowPerm
    rcases borrowFlatRoot_unpack (hFlat hd (List.Mem.head _)) with ⟨_, _, _, hGe12, _⟩
    have hNe : Nat.beq hd.targetLocal dstLocal = false :=
      natBeq_false_of_not_eq (Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hGe12))
    rw [hNe, Bool.and_false]
    exact congrArg (hd :: ·)
      (invalidateConflictingBorrows_of_lt12 dstLocal hLt (fun e h => hFlat e (List.Mem.tail _ h)))

private theorem disableLocalBorrows_of_lt12 :
    ∀ {bs : List BorrowEntry} (dstLocal : Nat),
      dstLocal < 12 → (∀ e, e ∈ bs → borrowFlatRoot e = true) →
      disableLocalBorrows bs dstLocal 0 = bs
  | [], _, _, _ => rfl
  | hd :: tl, dstLocal, hLt, hFlat => by
    unfold disableLocalBorrows
    rcases borrowFlatRoot_unpack (hFlat hd (List.Mem.head _)) with ⟨_, _, _, hGe12, _⟩
    have hNe : Nat.beq hd.targetLocal dstLocal = false :=
      natBeq_false_of_not_eq (Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hGe12))
    rw [hNe, Bool.and_false]
    exact congrArg (hd :: ·)
      (disableLocalBorrows_of_lt12 dstLocal hLt (fun e h => hFlat e (List.Mem.tail _ h)))

private theorem disableFrameBorrows_of_le12 :
    ∀ {bs : List BorrowEntry} (nLocals : Nat),
      nLocals ≤ 12 → (∀ e, e ∈ bs → borrowFlatRoot e = true) →
      disableFrameBorrows bs 0 nLocals = bs
  | [], _, _, _ => rfl
  | hd :: tl, nLocals, hLe, hFlat => by
    unfold disableFrameBorrows
    rcases borrowFlatRoot_unpack (hFlat hd (List.Mem.head _)) with ⟨_, _, _, hGe12, _⟩
    have hBlt : Nat.blt hd.targetLocal nLocals = false := by
      unfold Nat.blt
      exact Bool.eq_false_iff.mpr fun hT =>
        Nat.not_le.mpr (Nat.lt_succ_of_le (Nat.le_trans hLe hGe12)) (Nat.le_of_ble_eq_true hT)
    rw [hBlt, Bool.and_false]
    exact congrArg (hd :: ·)
      (disableFrameBorrows_of_le12 nLocals hLe (fun e h => hFlat e (List.Mem.tail _ h)))

private theorem updateBorrowPermAtProj_self_unique (e : BorrowEntry)
    (writeProj : List ProjectionElem) (hPerm : e.perm = .unique) :
    updateBorrowPermAtProj e e.targetLocal (some e.tag) writeProj e.rangeOffset e.rangeLen
      e.targetFrameDepth = e := by
  unfold updateBorrowPermAtProj
  rw [Nat.beq_refl, Nat.beq_refl]
  dsimp only [treeBorrowWriterRelatedness]
  rw [Nat.beq_refl]
  dsimp only [treeBorrowNodeAccess, treeBorrowPermTransition, applyTreeBorrowTransition]
  cases e; dsimp only at hPerm; subst hPerm; rfl

private theorem updateBorrowPermAtProj_disjoint_pair {e w : BorrowEntry}
    (writeProj : List ProjectionElem)
    (hRootE : borrowFlatRoot e = true) (hRootW : borrowFlatRoot w = true)
    (hPair : borrowsDisjointPair e w = true) :
    updateBorrowPermAtProj e w.targetLocal (some w.tag) writeProj w.rangeOffset w.rangeLen 0 = e := by
  rcases borrowFlatRoot_unpack hRootE with ⟨hDepthE, hProjE, _, _, hLenE⟩
  rcases borrowFlatRoot_unpack hRootW with ⟨_, _, _, _, hLenW⟩
  unfold borrowsDisjointPair at hPair
  have hTagNot := boolAnd_left hPair
  have hRange := boolAnd_right hPair
  have hTagFalse : Nat.beq e.tag w.tag = false := by
    cases hB : Nat.beq e.tag w.tag with
    | false => rfl
    | true => rw [hB] at hTagNot; cases hTagNot
  unfold updateBorrowPermAtProj
  rw [hDepthE, Nat.beq_refl]
  cases hLoc : Nat.beq e.targetLocal w.targetLocal with
  | false => rfl
  | true =>
    dsimp only [treeBorrowWriterRelatedness]
    rw [hTagFalse]
    dsimp only [borrowEntryOverlapsWrite]
    rw [hLoc, Bool.not_true, Bool.false_or] at hRange
    rw [hProjE]
    have hSep : (byteRangePermLens (Anneal.Memory.BorrowEntry.toByteRangePerm e)).Separated
        ⟨w.targetLocal, w.rangeOffset, w.rangeLen⟩ := by
      cases h1 : Nat.ble (e.rangeOffset + e.rangeLen) w.rangeOffset with
      | true => exact Or.inr (Or.inl (Nat.le_of_ble_eq_true h1))
      | false =>
        rw [h1, Bool.false_or] at hRange
        exact Or.inr (Or.inr (Nat.le_of_ble_eq_true hRange))
    have hNoOv := byteRangeOverlapsWrite_false_of_separated
      (Anneal.Memory.BorrowEntry.toByteRangePerm e)
      ⟨w.targetLocal, w.rangeOffset, w.rangeLen⟩ hSep
    unfold Anneal.Memory.byteRangeOverlapsWrite at hNoOv
    dsimp only [Anneal.Memory.BorrowEntry.toByteRangePerm] at hNoOv
    rw [hLoc, Bool.true_and] at hNoOv
    have hEnz : Nat.beq e.rangeLen 0 = false := natBeq_false_of_not_eq (by omega)
    have hWnz : Nat.beq w.rangeLen 0 = false := natBeq_false_of_not_eq (by omega)
    rw [hEnz, hWnz]
    change (match byteRangesOverlapBool e.rangeOffset e.rangeLen w.rangeOffset w.rangeLen with
      | false => e | true => _) = e
    rw [hNoOv]

private theorem isBorrowDescendantOrSelf_flat {bs : List BorrowEntry}
    (hDisj : borrowsTableDisjoint bs = true)
    {w : BorrowEntry} (hW : w ∈ bs) (t : Nat) :
    isBorrowDescendantOrSelf bs w.tag t = Nat.beq w.tag t := by
  cases bs with
  | nil => cases hW
  | cons hd tl =>
    unfold isBorrowDescendantOrSelf
    change isBorrowDescendantOrSelfAux (tl.length + 1) (hd :: tl) w.tag t = Nat.beq w.tag t
    unfold isBorrowDescendantOrSelfAux
    cases hEq : Nat.beq w.tag t with
    | true => rfl
    | false =>
      rw [lookupBorrow_of_disjoint hDisj hW]
      dsimp only
      rcases borrowFlatRoot_unpack ((borrowsTableDisjoint_props hDisj).1 w hW) with ⟨_, _, hPar, _, _⟩
      rw [hPar]

private theorem invalidateTreeBorrowsAtProj_disjoint {all bs : List BorrowEntry}
    (hDisj : borrowsTableDisjoint all = true)
    (hSub : ∀ e, e ∈ bs → e ∈ all)
    {w : BorrowEntry} (hW : w ∈ all) (hPermW : w.perm = .unique)
    (writeProj : List ProjectionElem) :
    invalidateTreeBorrowsAtProj all bs w.targetLocal (some w.tag) writeProj
      w.rangeOffset w.rangeLen 0 = bs := by
  rcases borrowsTableDisjoint_props hDisj with ⟨hFlat, hPair⟩
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    unfold invalidateTreeBorrowsAtProj
    have hHdIn : hd ∈ all := hSub hd (List.Mem.head _)
    have hHdEq : updateBorrowPermTreeAtProj all hd w.targetLocal (some w.tag) writeProj
        w.rangeOffset w.rangeLen 0 = hd := by
      unfold updateBorrowPermTreeAtProj resolveTreeBorrowWriterTag
      dsimp only
      rw [isBorrowDescendantOrSelf_flat hDisj hW hd.tag]
      rcases hPair hd w hHdIn hW with rfl | hDisjPair
      · rw [Nat.beq_refl]; dsimp only
        rcases borrowFlatRoot_unpack (hFlat hd hHdIn) with ⟨hDepth, _, _, _, _⟩
        rw [← hDepth]
        exact updateBorrowPermAtProj_self_unique hd writeProj hPermW
      · have hTagNot := boolAnd_left (borrowsDisjointPair_symm hDisjPair)
        have hTagFalse : Nat.beq w.tag hd.tag = false := by
          cases hB : Nat.beq w.tag hd.tag with
          | false => rfl
          | true => rw [hB] at hTagNot; cases hTagNot
        rw [hTagFalse]; dsimp only
        exact updateBorrowPermAtProj_disjoint_pair writeProj (hFlat hd hHdIn) (hFlat w hW) hDisjPair
    rw [hHdEq, ih (fun e h => hSub e (List.Mem.tail _ h))]

private theorem invalidateDerefWriteBorrows_u8_unchanged
    (frameLocals callerLocals : List LocalSlot) (bs : List BorrowEntry)
    (w : BorrowEntry) (off len : Nat)
    (hFrame : Trusted.Sequence.get? frameLocals 1 =
      some (.init (.aggregate 0 [.ptr ⟨w.tag, off⟩ 8, .scalar ⟨len, 8⟩])))
    (hDisj : borrowsTableDisjoint bs = true)
    (hW : w ∈ bs) (hPermW : w.perm = .unique) :
    invalidateDerefWriteBorrows frameLocals bs (pl 1 [.deref]) [] callerLocals [] = bs := by
  have hFlat := (borrowsTableDisjoint_props hDisj).1
  have hLook : lookupBorrow bs w.tag = some w := lookupBorrow_of_disjoint hDisj hW
  rcases borrowFlatRoot_unpack (hFlat w hW) with ⟨hDepthW, hProjW, _, _, hLenPos⟩
  have hLenNz : Nat.beq w.rangeLen 0 = false := natBeq_false_of_not_eq (by omega)
  have hExt : extractDerefPtrVal?
      (.aggregate 0 [.ptr ⟨w.tag, off⟩ 8, .scalar ⟨len, 8⟩]) = some ⟨w.tag, off⟩ := rfl
  cases bs with
  | nil => cases hW
  | cons b1 rest =>
    cases rest with
    | nil =>
      cases hW with
      | head =>
        unfold invalidateDerefWriteBorrows
        dsimp only [pl]
        rw [hFrame]
        dsimp only
        rw [hExt]
        dsimp only [lookupBorrow, ProvenancePtr.tag]
        rw [Nat.beq_refl]
        dsimp only
        rw [hDepthW]
        cases hProjRes : resolveDerefWriteFullProj frameLocals frameLocals
            (.aggregate 0 [.ptr ⟨w.tag, off⟩ 8, .scalar ⟨len, 8⟩]) w [] callerLocals with
        | nil =>
          dsimp only
          rw [hLenNz]
          dsimp only [invalidateConflictingBorrowsAtProj]
          rw [← hDepthW, updateBorrowPermAtProj_self_unique w [] hPermW]
        | cons pHead pTail =>
          dsimp only [invalidateConflictingBorrowsAtProj]
          rw [← hDepthW, updateBorrowPermAtProj_self_unique w (pHead :: pTail) hPermW]
      | tail _ h => cases h
    | cons b2 rest' =>
      unfold invalidateDerefWriteBorrows
      dsimp only [pl]
      rw [hFrame]
      dsimp only
      rw [hExt]
      dsimp only [ProvenancePtr.tag]
      rw [hLook]
      dsimp only
      rw [hDepthW]
      exact invalidateTreeBorrowsAtProj_disjoint hDisj (fun _ h => h) hW hPermW _

private theorem u32_le_bytes_match (v : UInt32) :
    let b0 := wrapScalarBits v.toNat (scalarModulus 1)
    let s1 := wrapScalarBits (shiftRightUnsignedBits v.toNat 8) (scalarModulus 4)
    let b1 := wrapScalarBits s1 (scalarModulus 1)
    let s2 := wrapScalarBits (shiftRightUnsignedBits v.toNat 16) (scalarModulus 4)
    let b2 := wrapScalarBits s2 (scalarModulus 1)
    let s3 := wrapScalarBits (shiftRightUnsignedBits v.toNat 24) (scalarModulus 4)
    let b3 := wrapScalarBits s3 (scalarModulus 1)
    [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩, Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩] =
      u8BytesToValues ((SliceCodec.uint32 ByteCodec.uint8).enc v) := by
  intro b0 s1 b1 s2 b2 s3 b3
  have hLt : v.toNat < 2 ^ 32 := v.toBitVec.isLt
  have hb0 : b0 = v.toNat % 256 := by
    dsimp only [b0]; rw [Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow]
  have hs1 : s1 = v.toNat / 256 := by
    dsimp only [s1]
    rw [Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow,
      Scalars.shiftRightUnsignedBits_eq_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hb1 : b1 = (v.toNat / 256) % 256 := by
    dsimp only [b1]; rw [hs1, Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow]
  have hs2 : s2 = v.toNat / 65536 := by
    dsimp only [s2]
    rw [Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow,
      Scalars.shiftRightUnsignedBits_eq_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hb2 : b2 = (v.toNat / 65536) % 256 := by
    dsimp only [b2]; rw [hs2, Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow]
  have hs3 : s3 = v.toNat / 16777216 := by
    dsimp only [s3]
    rw [Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow,
      Scalars.shiftRightUnsignedBits_eq_shiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hb3 : b3 = (v.toNat / 16777216) % 256 := by
    dsimp only [b3]; rw [hs3, Scalars.wrapScalarBits_eq_mod_modulus, Scalars.scalarModulus_eq_two_pow]
  rw [hb0, hb1, hb2, hb3]
  show [Value.scalar ⟨v.toNat % 256, 1⟩, Value.scalar ⟨(v.toNat / 256) % 256, 1⟩,
    Value.scalar ⟨(v.toNat / 65536) % 256, 1⟩, Value.scalar ⟨(v.toNat / 16777216) % 256, 1⟩] =
    [Value.scalar ⟨(UInt8.ofBitVec (BitVec.ofNat 8 v.toNat)).toNat, 1⟩,
     Value.scalar ⟨(UInt8.ofBitVec (BitVec.ofNat 8 (v.toNat / 256))).toNat, 1⟩,
     Value.scalar ⟨(UInt8.ofBitVec (BitVec.ofNat 8 (v.toNat / 256 / 256))).toNat, 1⟩,
     Value.scalar ⟨(UInt8.ofBitVec (BitVec.ofNat 8 (v.toNat / 256 / 256 / 256))).toNat, 1⟩]
  have hDiv3 : v.toNat / 256 / 256 / 256 = v.toNat / 16777216 := by omega
  have hDiv2 : v.toNat / 256 / 256 = v.toNat / 65536 := by omega
  rw [hDiv3, hDiv2]
  rfl

/-- Shared argument type for the real-callee `execMutSummaryChain`. -/
inductive SliceCalleeArg : Type where
  | u32Arg (v : UInt32) : SliceCalleeArg
  | paddedPairArg (b : Bool) (v : UInt32) : SliceCalleeArg

/-- Partial `Value → Option UInt32` extractor for `mirNormalOutcomeExtract`. -/
def ofU32Value : Value → Option UInt32
  | .scalar ⟨bits, 4⟩ => if bits < 2 ^ 32 then some (UInt32.ofNat bits) else none
  | _ => none

private theorem ofU32Value_u32 (v : UInt32) :
    ofU32Value (.scalar ⟨v.toNat, 4⟩) = some v := by
  unfold ofU32Value
  have hLt : v.toNat < 2 ^ 32 := v.toBitVec.isLt
  change (if v.toNat < 2 ^ 32 then some (UInt32.ofNat v.toNat) else none) = some v
  rw [ite_eq_left hLt]
  exact congrArg some UInt32.ofNat_toNat

/-- Live entry state for `writeU32SliceBody`: passes `m` completely unmodified
into `Trusted.VerificationResult.initMachineStateWithMemoryAndCallees`, with
`_1` holding the `&mut [u8]` fat pointer from `findCoveringUniqueBorrow`. -/
def writeU32Entry (L : ByteSubLens SliceCallAddr) (m : Memory) (arg : SliceCalleeArg) :
    MachineState :=
  let tag := match findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len with
    | some e => e.tag
    | none => 0
  let v := match arg with | .u32Arg v => v | .paddedPairArg _ v => v
  Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
    writeU32SliceBody
    [.aggregate 0 [.ptr ⟨tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩], .scalar ⟨v.toNat, 4⟩]
    m []

/-- Live entry state for `writePaddedPairSliceBody`: passes `m` completely
unmodified into `Trusted.VerificationResult.initMachineStateWithMemoryAndCallees`. -/
def writePaddedPairEntry (L : ByteSubLens SliceCallAddr) (m : Memory) (arg : SliceCalleeArg) :
    MachineState :=
  let tag := match findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len with
    | some e => e.tag
    | none => 0
  let (b, v) := match arg with | .u32Arg v => (false, v) | .paddedPairArg b v => (b, v)
  Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
    writePaddedPairSliceBody
    [.aggregate 0 [.ptr ⟨tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩],
     boolScalar b, .scalar ⟨v.toNat, 4⟩]
    m []

/-- Live entry state for `panickingSliceBody`. -/
def panickingEntry (L : ByteSubLens SliceCallAddr) (m : Memory) (arg : SliceCalleeArg) :
    MachineState :=
  let tag := match findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len with
    | some e => e.tag
    | none => 0
  let v := match arg with | .u32Arg v => v | .paddedPairArg _ v => v
  Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
    panickingSliceBody
    [.aggregate 0 [.ptr ⟨tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩], .scalar ⟨v.toNat, 4⟩]
    m []

abbrev rawU32Codec : SliceCodec UInt8 UInt32 4 := SliceCodec.uint32 ByteCodec.uint8
abbrev rawBoolCodec : SliceCodec UInt8 Bool 1 := SliceCodec.bool ByteCodec.uint8
abbrev rawPaddedPairCodec : SliceCodec UInt8 (Bool × UInt32) 8 :=
  SliceCodec.paddedPair 3 (0 : UInt8) rawBoolCodec rawU32Codec

def writeU32SliceSum : MutSummary UInt8 SliceCalleeArg UInt32 :=
  MutSummary.ofSliceCodec rawU32Codec fun _ arg =>
    match arg with
    | .u32Arg v => some (v, v)
    | _ => none

def writePaddedPairSliceSum : MutSummary UInt8 SliceCalleeArg UInt32 :=
  MutSummary.ofSliceCodec rawPaddedPairCodec fun _ arg =>
    match arg with
    | .paddedPairArg b v => some ((b, v), v)
    | _ => none

private theorem sliceCall_get_inv {L : ByteSubLens SliceCallAddr} {m : Memory}
    {old : List UInt8} (hGet : L.get m = some old) :
    0 < L.len ∧ m.activeCallee = none ∧ m.callStack = [] ∧
      m.activeProtectors = [] ∧ m.callees = [] ∧
      12 ≤ L.addr.localIdx ∧ borrowsTableDisjoint m.borrows = true ∧
      (∃ e, findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len = some e ∧
        e ∈ m.borrows ∧ e.perm = .unique ∧ e.targetLocal = L.addr.localIdx ∧
        borrowFlatRoot e = true) ∧
      (∃ slot bytes, listGet? m.callerLocals L.addr.localIdx = some slot ∧
        slotAsU8Bytes? slot = some bytes ∧ L.offset + L.len ≤ bytes.length) := by
  rcases ByteSubLens.get_inv hGet with ⟨hPos, hRead⟩
  change (match sliceCallAbiReady m L.addr L.offset L.len with
    | false => none | true => memCallerByteStoreOps.readBytes? m ⟨L.addr.localIdx⟩ L.offset L.len) =
    some old at hRead
  cases hReady : sliceCallAbiReady m L.addr L.offset L.len with
  | false => rw [hReady] at hRead; cases hRead
  | true =>
    rw [hReady] at hRead
    unfold sliceCallAbiReady at hReady
    have h6 := boolAnd_left hReady
    have hFindSome := boolAnd_right hReady
    have h5 := boolAnd_left h6
    have hDisj := boolAnd_right h6
    have h4 := boolAnd_left h5
    have hIdx12 := Nat.le_of_ble_eq_true (boolAnd_right h5)
    have h3 := boolAnd_left h4
    have hCalEmp := boolAnd_right h4
    have h2 := boolAnd_left h3
    have hPrEmp := boolAnd_right h3
    have hAcNone := boolAnd_left h2
    have hCsEmp := boolAnd_right h2
    have hAc : m.activeCallee = none := by
      cases h : m.activeCallee with | none => rfl | some _ => rw [h] at hAcNone; cases hAcNone
    have hCs : m.callStack = [] := by
      cases h : m.callStack with | nil => rfl | cons _ _ => rw [h] at hCsEmp; cases hCsEmp
    have hPr : m.activeProtectors = [] := by
      cases h : m.activeProtectors with | nil => rfl | cons _ _ => rw [h] at hPrEmp; cases hPrEmp
    have hCa : m.callees = [] := by
      cases h : m.callees with | nil => rfl | cons _ _ => rw [h] at hCalEmp; cases hCalEmp
    have hBorrow : ∃ e, findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len = some e ∧
        e ∈ m.borrows ∧ e.perm = .unique ∧ e.targetLocal = L.addr.localIdx ∧
        borrowFlatRoot e = true := by
      cases hF : findCoveringUniqueBorrow m.borrows L.addr.localIdx L.offset L.len with
      | none => rw [hF] at hFindSome; cases hFindSome
      | some e =>
        unfold findCoveringUniqueBorrow at hF
        rcases List.find?_eq_some_iff_append.mp hF with ⟨hP, _, _, hApp, _⟩
        have hMem : e ∈ m.borrows := by rw [hApp]; exact List.mem_append_right _ (List.Mem.head _)
        have hP3 := boolAnd_left (boolAnd_left hP)
        have hRoot := boolAnd_right hP3
        have hP2 := boolAnd_left hP3
        have hLoc := Nat.eq_of_beq_eq_true (boolAnd_right hP2)
        have hPerm := perm_eq_unique_of_isUniquePerm (boolAnd_left hP2)
        exact ⟨e, rfl, hMem, hPerm, hLoc, hRoot⟩
    dsimp [ByteStoreOps.readBytes?] at hRead
    cases hG : listGet? m.callerLocals L.addr.localIdx with
    | none => simp only [hG] at hRead; cases hRead
    | some slot =>
      simp only [hG] at hRead
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at hRead; cases hRead
      | some bytes =>
        simp only [hS] at hRead
        cases hB : Nat.ble (L.offset + L.len) bytes.length with
        | false => simp only [hB] at hRead; cases hRead
        | true =>
          exact ⟨hPos, hAc, hCs, hPr, hCa, hIdx12, hDisj, hBorrow,
            slot, bytes, rfl, hS, Nat.le_of_ble_eq_true hB⟩

/-- Reusable lemma for executing `StatementKind.assign (pl 1 [.deref]) (aggregate array bs)`
into `m.callerLocals` through a `&mut [u8]` fat pointer in `_1`, bridging
directly to `listSet? m.callerLocals idx (u8BytesToSlot (listSplice bytes off bs))`. -/
private theorem evalCallerSliceAssign_ok
    {m : Memory} {frameLocals : List LocalSlot} {e : BorrowEntry}
    {off : Nat} {slot : LocalSlot} {bytes bs : List UInt8} {cl' : List LocalSlot}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (hFrame1 : Trusted.Sequence.get? frameLocals 1 =
      some (.init (.aggregate 0 [.ptr ⟨e.tag, off⟩ 8, .scalar ⟨bs.length, 8⟩])))
    (hFrameLen : frameLocals.length ≤ 12)
    (hCs : m.callStack = []) (hPr : m.activeProtectors = [])
    (hDisj : borrowsTableDisjoint m.borrows = true)
    (hMemE : e ∈ m.borrows) (hPermE : e.perm = .unique)
    (hGetSlot : listGet? m.callerLocals e.targetLocal = some slot)
    (hSlotBytes : slotAsU8Bytes? slot = some bytes)
    (hPos : 0 < bs.length) (hBound : off + bs.length ≤ bytes.length)
    (hSetCl : listSet? m.callerLocals e.targetLocal (u8BytesToSlot (listSplice bytes off bs)) =
      some cl') :
    evalPlaceWrite frameLocals m.borrows (pl 1 [.deref])
        (.aggregate 0 (u8BytesToValues bs)) m.activeProtectors localDecls layouts m.callStack = .ub ∧
    m.callerLocals ≠ [] ∧
    evalCallerPlaceWrite frameLocals m.callerLocals m.borrows (pl 1 [.deref])
        (.aggregate 0 (u8BytesToValues bs)) m.activeProtectors = .ok cl' ∧
    derefWriteTreeUB frameLocals m.borrows (pl 1 [.deref]) = false ∧
    invalidateDerefWriteBorrows frameLocals m.borrows (pl 1 [.deref]) [] m.callerLocals = m.borrows := by
  have hFlat := (borrowsTableDisjoint_props hDisj).1
  rcases borrowFlatRoot_unpack (hFlat e hMemE) with ⟨hDepthE, hProjE, _, hLoc12, _⟩
  have hLook : lookupBorrow m.borrows e.tag = some e := lookupBorrow_of_disjoint hDisj hMemE
  have hActiveNone : activeFrameSlot? frameLocals [] 0 e.targetLocal = none := by
    unfold activeFrameSlot?
    unfold Trusted.Sequence.length
    change Trusted.Sequence.get? frameLocals e.targetLocal = none
    unfold Trusted.Sequence.get?
    exact List.getElem?_eq_none (Nat.le_trans hFrameLen hLoc12)
  have hPlaceUb : evalPlaceWrite frameLocals m.borrows (pl 1 [.deref])
      (.aggregate 0 (u8BytesToValues bs)) m.activeProtectors localDecls layouts m.callStack = .ub := by
    rw [hPr, hCs]
    unfold evalPlaceWrite writePlaceValue
    dsimp only [pl]
    rw [hFrame1]
    change (match
        Bool.and
          (checkDerefAlign localDecls layouts _ off)
          (validateValueForTy? layouts _ (.aggregate 0 (u8BytesToValues bs))) with
      | false => PlaceWriteResult.ub
      | true =>
        match lookupBorrow m.borrows e.tag with
        | some entry =>
          match entry.perm with
          | .frozen => PlaceWriteResult.ub
          | .disabled => PlaceWriteResult.ub
          | _ =>
            match activeFrameSlot? frameLocals [] entry.targetFrameDepth entry.targetLocal with
            | some (.init _) => _
            | _ => PlaceWriteResult.ub
        | none => PlaceWriteResult.ub) = PlaceWriteResult.ub
    cases Bool.and (checkDerefAlign localDecls layouts _ off)
        (validateValueForTy? layouts _ (.aggregate 0 (u8BytesToValues bs))) with
    | false => rfl
    | true =>
      dsimp only
      rw [hLook]
      dsimp only
      rw [hPermE, hDepthE]
      dsimp only
      rw [hActiveNone]
  have hSlotEq : slot = u8BytesToSlot bytes := (u8BytesToSlot_of_slotAsU8Bytes? hSlotBytes).symm
  have hGetSeq : Trusted.Sequence.get? m.callerLocals e.targetLocal = some (u8BytesToSlot bytes) := by
    rw [sequenceGet?_eq_listGet?, hGetSlot, hSlotEq]
  have hSetSeq : Trusted.Sequence.set? m.callerLocals e.targetLocal
      (u8BytesToSlot (listSplice bytes off bs)) = some cl' := by
    rcases listSet?_lt_and_eq hSetCl with ⟨hLt, hEqCl⟩
    unfold Trusted.Sequence.set?
    rw [ite_eq_left hLt, hEqCl]
  have hCallerNe : m.callerLocals ≠ [] := by
    intro hNil; rw [hNil] at hGetSlot; cases hGetSlot
  have hCallerWrite : evalCallerPlaceWrite frameLocals m.callerLocals m.borrows (pl 1 [.deref])
      (.aggregate 0 (u8BytesToValues bs)) m.activeProtectors = .ok cl' := by
    have hAlignTrue : checkDerefAlign [] emptyLayoutTable none off = true := by
      unfold checkDerefAlign; cases Nat.beq off 0 <;> rfl
    rw [hPr]
    unfold evalCallerPlaceWrite writeCallerPlaceValue
    dsimp only [pl]
    rw [hFrame1]
    change (match Bool.and (checkDerefAlign [] emptyLayoutTable none off) true with
      | false => PlaceWriteResult.ub
      | true =>
        match lookupBorrow m.borrows e.tag with
        | some entry =>
          match entry.perm with
          | .frozen => PlaceWriteResult.ub
          | .disabled => PlaceWriteResult.ub
          | _ =>
            match activeFrameSlot? frameLocals [] entry.targetFrameDepth entry.targetLocal with
            | some _ => PlaceWriteResult.ub
            | none =>
              match Trusted.Sequence.get? m.callerLocals entry.targetLocal with
              | some (.init curVal) =>
                match checkTargetPlaceAlign
                    (foreignFrameDeclsAndLayouts [] emptyLayoutTable entry.targetFrameDepth entry.targetLocal).1
                    emptyLayoutTable none entry ⟨e.tag, off⟩ (some curVal)
                    (foreignFrameDeclsAndLayouts [] emptyLayoutTable entry.targetFrameDepth entry.targetLocal).2 [] with
                | false => PlaceWriteResult.ub
                | true =>
                  match writeSliceFatPtrTargetValue frameLocals curVal entry.targetProjection
                      ⟨e.tag, off⟩ 8 ⟨bs.length, 8⟩ [] (.aggregate 0 (u8BytesToValues bs)) with
                  | .ok nextVal =>
                    match Trusted.Sequence.set? m.callerLocals entry.targetLocal (.init nextVal) with
                    | some nextLocals => PlaceWriteResult.ok nextLocals
                    | none => PlaceWriteResult.ub
                  | .ub => PlaceWriteResult.ub
                  | .unsupported => PlaceWriteResult.unsupported
              | _ => PlaceWriteResult.ub
        | none => PlaceWriteResult.ub) = PlaceWriteResult.ok cl'
    rw [hAlignTrue, Bool.and_self]
    dsimp only
    rw [hLook]
    dsimp only
    rw [hPermE, hDepthE]
    dsimp only
    rw [hActiveNone, hGetSeq]
    dsimp only [u8BytesToSlot, foreignFrameDeclsAndLayouts, checkTargetPlaceAlign]
    rw [hProjE, writeSliceFatPtr_u8_whole frameLocals bytes bs e.tag off hPos hBound]
    dsimp only
    dsimp only [u8BytesToSlot] at hSetSeq
    rw [hSetSeq]
  have hTreeUb : derefWriteTreeUB frameLocals m.borrows (pl 1 [.deref]) = false := by
    unfold derefWriteTreeUB
    cases m.borrows with
    | nil => rfl
    | cons _ rest =>
      cases rest with
      | nil => rfl
      | cons _ _ =>
        dsimp only [pl]
        rw [hFrame1]
  have hBorInv : invalidateDerefWriteBorrows frameLocals m.borrows (pl 1 [.deref]) []
      m.callerLocals = m.borrows :=
    invalidateDerefWriteBorrows_u8_unchanged frameLocals m.callerLocals m.borrows e off bs.length
      hFrame1 hDisj hMemE hPermE
  exact ⟨hPlaceUb, hCallerNe, hCallerWrite, hTreeUb, hBorInv⟩

private def writeU32St10 (fatVal : Value) (v : UInt32) (stmt : Nat) (mem : Memory)
    (l0 l3 l4 l5 l6 l7 l8 l9 : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := stmt,
               locals := [l0, .init fatVal, .init (.scalar ⟨v.toNat, 4⟩),
                          l3, l4, l5, l6, l7, l8, l9] }
    memory := mem }

private def writeU32Stmt14State (fatVal : Value) (v : UInt32) (m : Memory) : MachineState :=
  let b0 := wrapScalarBits v.toNat (scalarModulus 1)
  let s1 := wrapScalarBits (shiftRightUnsignedBits v.toNat 8) (scalarModulus 4)
  let b1 := wrapScalarBits s1 (scalarModulus 1)
  let s2 := wrapScalarBits (shiftRightUnsignedBits v.toNat 16) (scalarModulus 4)
  let b2 := wrapScalarBits s2 (scalarModulus 1)
  let s3 := wrapScalarBits (shiftRightUnsignedBits v.toNat 24) (scalarModulus 4)
  let b3 := wrapScalarBits s3 (scalarModulus 1)
  writeU32St10 fatVal v 14 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
    (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
    (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))

/-- Shared 14-step prefix of `writeU32SliceBody` (statements `0..13`: `shr` + `cast`
to `u8`) sealed as a `StepStageCut` for ANY fat-pointer argument `fatVal`, ANY
symbolic `v : UInt32`, and ANY flat-caller-borrow `m : Memory`. Reused by BOTH
`writeU32Slice_mutSummaryOutcomeCut` (valid `.unique` writes) AND the symbolic
entry-to-UB refutation canaries (frozen borrow & OOB slice). -/
private theorem writeU32Slice_entry_to_stmt14 (fatVal : Value) (v : UInt32) (m : Memory)
    (hAc : m.activeCallee = none) (hCs : m.callStack = [])
    (hPr : m.activeProtectors = []) (hCa : m.callees = [])
    (hFlat : ∀ e ∈ m.borrows, borrowFlatRoot e = true) :
    StepStageCut (mirDetStep writeU32SliceBody) 14
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees writeU32SliceBody
        [fatVal, .scalar ⟨v.toNat, 4⟩] m [])
      (writeU32Stmt14State fatVal v m) := by
  rcases m with ⟨mNextAlloc, mGlobals, mBorrows, mNextTag, mCallees, mTraitImpls,
    mCallStack, mActiveCallee, mActiveProtectors, mNextProtector, mCallerLocals,
    mFnPtrs, mExposed⟩
  dsimp only at hAc hCs hPr hCa hFlat ⊢
  subst hAc hCs hPr hCa
  let m : Memory :=
    { nextAllocId := mNextAlloc, globals := mGlobals, borrows := mBorrows,
      nextTag := mNextTag, callees := [], traitImpls := mTraitImpls,
      callStack := [], activeCallee := none, activeProtectors := [],
      nextProtector := mNextProtector, callerLocals := mCallerLocals,
      fnPtrs := mFnPtrs, exposedAllocIds := mExposed }
  let b0 := wrapScalarBits v.toNat (scalarModulus 1)
  let s1 := wrapScalarBits (shiftRightUnsignedBits v.toNat 8) (scalarModulus 4)
  let b1 := wrapScalarBits s1 (scalarModulus 1)
  let s2 := wrapScalarBits (shiftRightUnsignedBits v.toNat 16) (scalarModulus 4)
  let b2 := wrapScalarBits s2 (scalarModulus 1)
  let s3 := wrapScalarBits (shiftRightUnsignedBits v.toNat 24) (scalarModulus 4)
  let b3 := wrapScalarBits s3 (scalarModulus 1)
  have hBorEq : ∀ k < 12, invalidateConflictingBorrows mBorrows k none 0 = mBorrows :=
    fun k hk => invalidateConflictingBorrows_of_lt12 k hk hFlat
  have hDisEq : ∀ k < 12, disableLocalBorrows mBorrows k 0 = mBorrows :=
    fun k hk => disableLocalBorrows_of_lt12 k hk hFlat
  have hs0 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 0 m .uninit .dead .dead .dead .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 1 m .uninit .uninit .dead .dead .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 1
      { m with borrows := disableLocalBorrows mBorrows 3 0 }
      .uninit .uninit .dead .dead .dead .dead .dead .dead) = _
    rw [hDisEq 3 (by decide)]
  have hs1 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 1 m .uninit .uninit .dead .dead .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 2 m .uninit (.init (.scalar ⟨b0, 1⟩)) .dead .dead .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 2
      { m with borrows := invalidateConflictingBorrows mBorrows 3 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) .dead .dead .dead .dead .dead .dead) = _
    rw [hBorEq 3 (by decide)]
  have hs2 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 2 m .uninit (.init (.scalar ⟨b0, 1⟩)) .dead .dead .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 3 m .uninit (.init (.scalar ⟨b0, 1⟩)) .uninit .dead .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 3
      { m with borrows := disableLocalBorrows mBorrows 4 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) .uninit .dead .dead .dead .dead .dead) = _
    rw [hDisEq 4 (by decide)]
  have hs3 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 3 m .uninit (.init (.scalar ⟨b0, 1⟩)) .uninit .dead .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 4 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        .dead .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 4
      { m with borrows := invalidateConflictingBorrows mBorrows 4 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      .dead .dead .dead .dead .dead) = _
    rw [hBorEq 4 (by decide)]
  have hs4 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 4 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        .dead .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 5 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        .uninit .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 5
      { m with borrows := disableLocalBorrows mBorrows 5 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      .uninit .dead .dead .dead .dead) = _
    rw [hDisEq 5 (by decide)]
  have hs5 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 5 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        .uninit .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 6 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 6
      { m with borrows := invalidateConflictingBorrows mBorrows 5 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) = _
    rw [hBorEq 5 (by decide)]
  have hs6 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 6 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 7 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 7
      { m with borrows := disableLocalBorrows mBorrows 6 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) = _
    rw [hDisEq 6 (by decide)]
  have hs7 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 7 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 8 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 8
      { m with borrows := invalidateConflictingBorrows mBorrows 6 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) = _
    rw [hBorEq 6 (by decide)]
  have hs8 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 8 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) =
      .cont (writeU32St10 fatVal v 9 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 9
      { m with borrows := disableLocalBorrows mBorrows 7 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) = _
    rw [hDisEq 7 (by decide)]
  have hs9 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 9 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) =
      .cont (writeU32St10 fatVal v 10 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) .dead .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 10
      { m with borrows := invalidateConflictingBorrows mBorrows 7 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
      (.init (.scalar ⟨b2, 1⟩)) .dead .dead) = _
    rw [hBorEq 7 (by decide)]
  have hs10 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 10 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) .dead .dead) =
      .cont (writeU32St10 fatVal v 11 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 11
      { m with borrows := disableLocalBorrows mBorrows 8 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
      (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) = _
    rw [hDisEq 8 (by decide)]
  have hs11 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 11 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) =
      .cont (writeU32St10 fatVal v 12 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .dead) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 12
      { m with borrows := invalidateConflictingBorrows mBorrows 8 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
      (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .dead) = _
    rw [hBorEq 8 (by decide)]
  have hs12 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 12 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .dead) =
      .cont (writeU32St10 fatVal v 13 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .uninit) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 13
      { m with borrows := disableLocalBorrows mBorrows 9 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
      (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .uninit) = _
    rw [hDisEq 9 (by decide)]
  have hs13 : Anneal.PureMirExec.mirStep writeU32SliceBody
      (writeU32St10 fatVal v 13 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .uninit) =
      .cont (writeU32St10 fatVal v 14 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
        (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
        (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
    change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 14
      { m with borrows := invalidateConflictingBorrows mBorrows 9 none 0 }
      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
      (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) = _
    rw [hBorEq 9 (by decide)]
  have hInitEq :
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees writeU32SliceBody
        [fatVal, .scalar ⟨v.toNat, 4⟩] m [] =
      writeU32St10 fatVal v 0 m .uninit .dead .dead .dead .dead .dead .dead .dead := rfl
  rw [hInitEq]
  exact
    StepStageCut.step (mirDetStep_step_iff.mpr hs0) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs1) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs2) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs3) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs4) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs5) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs6) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs7) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs8) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs9) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs10) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs11) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs12) <|
    StepStageCut.step (mirDetStep_step_iff.mpr hs13) <|
    StepStageCut.refl _ 0 _

/-- **Sealed `@[irreducible] MutSummaryOutcomeCut` for real `writeU32SliceBody`**:
Proved once, universally for ALL `L : ByteSubLens SliceCallAddr`, ALL raw
`m : Memory`, and ALL symbolic `arg : SliceCalleeArg` directly over unmodified
`V2026_06_01.MirSemantics.stepMirFn`. -/
theorem writeU32Slice_mutSummaryOutcomeCut :
    MutSummaryOutcomeCut (wops := mirDetWpOps writeU32SliceBody)
      writeU32Entry (mirNormalOutcomeExtract ofU32Value) writeU32SliceSum := by
  refine seal_mutSummaryOutcomeCut (wops := mirDetWpOps writeU32SliceBody) ?_
  intro L m arg old new ret hLen hGet hSum
  cases arg with
  | paddedPairArg _ _ =>
    unfold writeU32SliceSum MutSummary.ofSliceCodec at hSum
    dsimp only at hSum
    cases hD : rawU32Codec.dec old with
    | none => rw [hD] at hSum; cases hSum
    | some _ => rw [hD] at hSum; cases hSum
  | u32Arg v =>
    unfold writeU32SliceSum MutSummary.ofSliceCodec at hSum
    dsimp only at hSum
    cases hD : rawU32Codec.dec old with
    | none => rw [hD] at hSum; cases hSum
    | some _ =>
      rw [hD] at hSum
      injection hSum with hPair
      injection hPair with hNew hRet
      subst hNew hRet
      have hL4 : L.len = 4 := hLen
      have hEncLen : (rawU32Codec.enc v).length = 4 := rawU32Codec.enc_length v
      rcases ByteSubLens.set_isSome_of_get (rawU32Codec.enc v) hGet
        (hEncLen.trans hL4.symm) with ⟨m', hSet⟩
      refine ⟨m', hSet, ?_⟩
      rcases sliceCall_get_inv hGet with
        ⟨_, hAc, hCs, hPr, hCa, hIdx12, hDisj,
         ⟨e, hFindE, hMemE, hPermE, hLocE, hRootE⟩,
         ⟨slot, bytes, hGetSlot, hSlotBytes, hBound⟩⟩
      have hFlat := (borrowsTableDisjoint_props hDisj).1
      have hM'Eq : ∃ cl', listSet? m.callerLocals L.addr.localIdx
          (u8BytesToSlot (listSplice bytes L.offset (rawU32Codec.enc v))) = some cl' ∧
          m' = { m with callerLocals := cl' } := by
        rw [ByteSubLens.set_of_pos m (by omega) (hEncLen.trans hL4.symm)] at hSet
        change (match sliceCallAbiReady m L.addr L.offset (rawU32Codec.enc v).length with
          | false => none
          | true => memCallerByteStoreOps.writeBytes? m ⟨L.addr.localIdx⟩ L.offset
              (rawU32Codec.enc v)) = some m' at hSet
        cases hR : sliceCallAbiReady m L.addr L.offset (rawU32Codec.enc v).length with
        | false => rw [hR] at hSet; cases hSet
        | true =>
          rw [hR] at hSet
          dsimp [ByteStoreOps.writeBytes?] at hSet
          simp only [hGetSlot, hSlotBytes, hEncLen] at hSet
          rw [hL4] at hBound
          rw [Nat.ble_eq_true_of_le (by omega)] at hSet
          cases hSetL : listSet? m.callerLocals L.addr.localIdx
              (u8BytesToSlot (listSplice bytes L.offset (rawU32Codec.enc v))) with
          | none => simp only [hSetL] at hSet; cases hSet
          | some cl' =>
            simp only [hSetL] at hSet
            injection hSet with hEq
            exact ⟨cl', rfl, hEq.symm⟩
      rcases hM'Eq with ⟨cl', hSetCl, hM'⟩
      rcases m with ⟨mNextAlloc, mGlobals, mBorrows, mNextTag, mCallees, mTraitImpls,
        mCallStack, mActiveCallee, mActiveProtectors, mNextProtector, mCallerLocals,
        mFnPtrs, mExposed⟩
      dsimp only at hAc hCs hPr hCa hDisj hFindE hMemE hGetSlot hBound hFlat hSetCl hM' ⊢
      subst hAc hCs hPr hCa
      let m : Memory :=
        { nextAllocId := mNextAlloc, globals := mGlobals, borrows := mBorrows,
          nextTag := mNextTag, callees := [], traitImpls := mTraitImpls,
          callStack := [], activeCallee := none, activeProtectors := [],
          nextProtector := mNextProtector, callerLocals := mCallerLocals,
          fnPtrs := mFnPtrs, exposedAllocIds := mExposed }
      subst hM'
      let fatVal : Value := .aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨4, 8⟩]
      let b0 := wrapScalarBits v.toNat (scalarModulus 1)
      let s1 := wrapScalarBits (shiftRightUnsignedBits v.toNat 8) (scalarModulus 4)
      let b1 := wrapScalarBits s1 (scalarModulus 1)
      let s2 := wrapScalarBits (shiftRightUnsignedBits v.toNat 16) (scalarModulus 4)
      let b2 := wrapScalarBits s2 (scalarModulus 1)
      let s3 := wrapScalarBits (shiftRightUnsignedBits v.toNat 24) (scalarModulus 4)
      let b3 := wrapScalarBits s3 (scalarModulus 1)
      have hEntryEq : writeU32Entry L m (.u32Arg v) =
          Trusted.VerificationResult.initMachineStateWithMemoryAndCallees writeU32SliceBody
            [fatVal, .scalar ⟨v.toNat, 4⟩] m [] := by
        unfold writeU32Entry
        dsimp only [m]
        rw [hFindE, hL4]
      rw [hEntryEq]
      have hBorEq : ∀ k < 12, invalidateConflictingBorrows mBorrows k none 0 = mBorrows :=
        fun k hk => invalidateConflictingBorrows_of_lt12 k hk hFlat
      have hPrefix :=
        (writeU32Slice_entry_to_stmt14 fatVal v m rfl rfl rfl rfl hFlat).to_wpReach
          (tag := fun ms => some ms.frame.blockIdx)
      -- Step 14: live `&mut [u8]` slice write into `m.callerLocals` → `{ m with callerLocals := cl' }`!
      have hs14 : Anneal.PureMirExec.mirStep writeU32SliceBody
          (writeU32St10 fatVal v 14 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .cont (writeU32St10 fatVal v 15 { m with callerLocals := cl' }
            .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
        let locs14 := (writeU32St10 fatVal v 14 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
          (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
          (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))).frame.locals
        have hArrEq : [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
            Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩] =
            u8BytesToValues (rawU32Codec.enc v) := u32_le_bytes_match v
        have hFrame1 : Trusted.Sequence.get? locs14 1 =
            some (.init (.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8,
              .scalar ⟨(rawU32Codec.enc v).length, 8⟩])) := by
          rw [hEncLen]; rfl
        have hCaller := evalCallerSliceAssign_ok
          (m := m) (frameLocals := locs14) (e := e) (off := L.offset)
          (slot := slot) (bytes := bytes) (bs := rawU32Codec.enc v) (cl' := cl')
          (localDecls := writeU32SliceBody.localDecls) (layouts := writeU32SliceBody.layouts)
          hFrame1 (Nat.le_of_ble_eq_true (rfl : Nat.ble 10 12 = true)) rfl rfl hDisj hMemE hPermE
          (by rw [hLocE]; exact hGetSlot) hSlotBytes (by omega)
          (by rw [hEncLen, ← hL4]; exact hBound) (by rw [hLocE]; exact hSetCl)
        have hStep14 : stepMirFn writeU32SliceBody
            (writeU32St10 fatVal v 14 m .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
            MirStepNode.step (writeU32St10 fatVal v 15 { m with callerLocals := cl' }
              .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
          change (match evalPlaceWrite locs14 m.borrows (pl 1 [.deref])
              (.aggregate 0 [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
                             Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩])
              m.activeProtectors writeU32SliceBody.localDecls writeU32SliceBody.layouts m.callStack with
            | .ok _ => _
            | .ub =>
              match mCallerLocals with
              | [] => MirStepNode.fail .ub
              | _ :: _ =>
                match evalCallerPlaceWrite locs14 m.callerLocals m.borrows (pl 1 [.deref])
                    (.aggregate 0 [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
                                   Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩])
                    m.activeProtectors with
                | .ok callerLocals' =>
                  match derefWriteTreeUB locs14 m.borrows (pl 1 [.deref]) with
                  | true => MirStepNode.fail .ub
                  | false =>
                    MirStepNode.step (writeU32St10 fatVal v 15
                      { m with callerLocals := callerLocals',
                               borrows := invalidateDerefWriteBorrows locs14 m.borrows (pl 1 [.deref])
                                 [] m.callerLocals }
                      .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
                      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
                      (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩)))
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
            | .unsupported => MirStepNode.unsupported) = _
          rw [hArrEq, hCaller.1]
          cases hCl : mCallerLocals with
          | nil => exact False.elim (hCaller.2.1 hCl)
          | cons _ _ =>
            dsimp only
            rw [hCaller.2.2.1, hCaller.2.2.2.1, hCaller.2.2.2.2]
        unfold Anneal.PureMirExec.mirStep
        rw [hStep14]; rfl
      -- Step 15: `_0 = _2`, Step 16: `.return_` → `.normal (.scalar ⟨v.toNat, 4⟩, { m with callerLocals := cl' })`
      have hs15 : Anneal.PureMirExec.mirStep writeU32SliceBody
          (writeU32St10 fatVal v 15 { m with callerLocals := cl' }
            .uninit (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .cont (writeU32St10 fatVal v 16 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
        change Anneal.PureMirExec.Step.cont (writeU32St10 fatVal v 16
          { m with callerLocals := cl', borrows := invalidateConflictingBorrows mBorrows 0 none 0 }
          (.init (.scalar ⟨v.toNat, 4⟩))
          (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
          (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
          (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) = _
        rw [hBorEq 0 (by decide)]
      have hs16 : Anneal.PureMirExec.mirStep writeU32SliceBody
          (writeU32St10 fatVal v 16 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .done (.normal (.scalar ⟨v.toNat, 4⟩, { m with callerLocals := cl' })) := by
        have hStep16 : stepMirFn writeU32SliceBody
            (writeU32St10 fatVal v 16 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
            MirStepNode.retNormal (Value.scalar ⟨v.toNat, 4⟩) { m with callerLocals := cl' } := by
          change evalTerminator
            (writeU32St10 fatVal v 16 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩)))
            (mkBb [] .return_).terminator (some writeU32SliceBody) = _
          unfold evalTerminator Trusted.Sequence.length
          simp only [mkBb, writeU32St10, m, Trusted.Sequence.get?, List.getElem?_cons_zero,
            List.length_nil, List.length_cons, hasFrameDeallocProtectorConflict,
            disableFrameBorrows_of_le12 10 (by decide) hFlat]
        unfold Anneal.PureMirExec.mirStep
        rw [hStep16]; rfl
      refine wpUntil_bind (ops := mirDetWpOps writeU32SliceBody)
        (wpUntil_mono (ops := mirDetWpOps writeU32SliceBody)
          (fun _ h => h) (fun _ hF => False.elim hF) (fun _ h => h) hPrefix) fun s14 hS14 => ?_
      subst hS14
      exact
        step_det_to _ hs14 <| step_det_to _ hs15 <|
        step_det_done (.normal (.scalar ⟨v.toNat, 4⟩, { m with callerLocals := cl' })) hs16
          (by dsimp [mirNormalOutcomeExtract]; rw [ofU32Value_u32]; rfl)

/-- **Sealed `@[irreducible] MutSummaryOutcomeCut` for real `writePaddedPairSliceBody`**:
Proved once, universally for ALL `L : ByteSubLens SliceCallAddr`, ALL raw
`m : Memory`, and ALL symbolic `arg : SliceCalleeArg` directly over unmodified
`V2026_06_01.MirSemantics.stepMirFn`. -/
theorem writePaddedPairSlice_mutSummaryOutcomeCut :
    MutSummaryOutcomeCut (wops := mirDetWpOps writePaddedPairSliceBody)
      writePaddedPairEntry (mirNormalOutcomeExtract ofU32Value) writePaddedPairSliceSum := by
  refine seal_mutSummaryOutcomeCut (wops := mirDetWpOps writePaddedPairSliceBody) ?_
  intro L m arg old new ret hLen hGet hSum
  cases arg with
  | u32Arg _ =>
    unfold writePaddedPairSliceSum MutSummary.ofSliceCodec at hSum
    dsimp only at hSum
    cases hD : rawPaddedPairCodec.dec old with
    | none => rw [hD] at hSum; cases hSum
    | some _ => rw [hD] at hSum; cases hSum
  | paddedPairArg flag v =>
    unfold writePaddedPairSliceSum MutSummary.ofSliceCodec at hSum
    dsimp only at hSum
    cases hD : rawPaddedPairCodec.dec old with
    | none => rw [hD] at hSum; cases hSum
    | some _ =>
      rw [hD] at hSum
      injection hSum with hPair
      injection hPair with hNew hRet
      subst hNew hRet
      have hL8 : L.len = 8 := hLen
      have hEncLen : (rawPaddedPairCodec.enc (flag, v)).length = 8 :=
        rawPaddedPairCodec.enc_length (flag, v)
      rcases ByteSubLens.set_isSome_of_get (rawPaddedPairCodec.enc (flag, v)) hGet
        (hEncLen.trans hL8.symm) with ⟨m', hSet⟩
      refine ⟨m', hSet, ?_⟩
      rcases sliceCall_get_inv hGet with
        ⟨_, hAc, hCs, hPr, hCa, hIdx12, hDisj,
         ⟨e, hFindE, hMemE, hPermE, hLocE, hRootE⟩,
         ⟨slot, bytes, hGetSlot, hSlotBytes, hBound⟩⟩
      have hFlat := (borrowsTableDisjoint_props hDisj).1
      have hM'Eq : ∃ cl', listSet? m.callerLocals L.addr.localIdx
          (u8BytesToSlot (listSplice bytes L.offset (rawPaddedPairCodec.enc (flag, v)))) = some cl' ∧
          m' = { m with callerLocals := cl' } := by
        rw [ByteSubLens.set_of_pos m (by omega) (hEncLen.trans hL8.symm)] at hSet
        change (match sliceCallAbiReady m L.addr L.offset (rawPaddedPairCodec.enc (flag, v)).length with
          | false => none
          | true => memCallerByteStoreOps.writeBytes? m ⟨L.addr.localIdx⟩ L.offset
              (rawPaddedPairCodec.enc (flag, v))) = some m' at hSet
        cases hR : sliceCallAbiReady m L.addr L.offset (rawPaddedPairCodec.enc (flag, v)).length with
        | false => rw [hR] at hSet; cases hSet
        | true =>
          rw [hR] at hSet
          dsimp [ByteStoreOps.writeBytes?] at hSet
          simp only [hGetSlot, hSlotBytes, hEncLen] at hSet
          rw [hL8] at hBound
          rw [Nat.ble_eq_true_of_le (by omega)] at hSet
          cases hSetL : listSet? m.callerLocals L.addr.localIdx
              (u8BytesToSlot (listSplice bytes L.offset (rawPaddedPairCodec.enc (flag, v)))) with
          | none => simp only [hSetL] at hSet; cases hSet
          | some cl' =>
            simp only [hSetL] at hSet
            injection hSet with hEq
            exact ⟨cl', rfl, hEq.symm⟩
      rcases hM'Eq with ⟨cl', hSetCl, hM'⟩
      rcases m with ⟨mNextAlloc, mGlobals, mBorrows, mNextTag, mCallees, mTraitImpls,
        mCallStack, mActiveCallee, mActiveProtectors, mNextProtector, mCallerLocals,
        mFnPtrs, mExposed⟩
      dsimp only at hAc hCs hPr hCa hDisj hFindE hMemE hGetSlot hBound hFlat hSetCl hM' ⊢
      subst hAc hCs hPr hCa
      let m : Memory :=
        { nextAllocId := mNextAlloc, globals := mGlobals, borrows := mBorrows,
          nextTag := mNextTag, callees := [], traitImpls := mTraitImpls,
          callStack := [], activeCallee := none, activeProtectors := [],
          nextProtector := mNextProtector, callerLocals := mCallerLocals,
          fnPtrs := mFnPtrs, exposedAllocIds := mExposed }
      subst hM'
      let fatVal : Value := .aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨8, 8⟩]
      let bf := wrapScalarBits (if flag then 1 else 0) (scalarModulus 1)
      let b0 := wrapScalarBits v.toNat (scalarModulus 1)
      let s1 := wrapScalarBits (shiftRightUnsignedBits v.toNat 8) (scalarModulus 4)
      let b1 := wrapScalarBits s1 (scalarModulus 1)
      let s2 := wrapScalarBits (shiftRightUnsignedBits v.toNat 16) (scalarModulus 4)
      let b2 := wrapScalarBits s2 (scalarModulus 1)
      let s3 := wrapScalarBits (shiftRightUnsignedBits v.toNat 24) (scalarModulus 4)
      let b3 := wrapScalarBits s3 (scalarModulus 1)
      let mkSt12 (stmt : Nat) (mem : Memory)
          (l0 l4 l5 l6 l7 l8 l9 l10 l11 : LocalSlot) : MachineState :=
        { frame := { blockIdx := 0, stmtIdx := stmt,
                     locals := [l0, .init fatVal, .init (boolScalar flag),
                                .init (.scalar ⟨v.toNat, 4⟩),
                                l4, l5, l6, l7, l8, l9, l10, l11] }
          memory := mem }
      have hEntryEq : writePaddedPairEntry L m (.paddedPairArg flag v) =
          mkSt12 0 m .uninit .dead .dead .dead .dead .dead .dead .dead .dead := by
        unfold writePaddedPairEntry Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        dsimp only [m]
        rw [hFindE, hL8]; rfl
      rw [hEntryEq]
      have hBorEq : ∀ k < 12, invalidateConflictingBorrows mBorrows k none 0 = mBorrows :=
        fun k hk => invalidateConflictingBorrows_of_lt12 k hk hFlat
      have hDisEq : ∀ k < 12, disableLocalBorrows mBorrows k 0 = mBorrows :=
        fun k hk => disableLocalBorrows_of_lt12 k hk hFlat
      have hs0 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 0 m .uninit .dead .dead .dead .dead .dead .dead .dead .dead) =
          .cont (mkSt12 1 m .uninit .uninit .dead .dead .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 1
          { m with borrows := disableLocalBorrows mBorrows 4 0 }
          .uninit .uninit .dead .dead .dead .dead .dead .dead .dead) = _
        rw [hDisEq 4 (by decide)]
      have hs1 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 1 m .uninit .uninit .dead .dead .dead .dead .dead .dead .dead) =
          .cont (mkSt12 2 m .uninit (.init (.scalar ⟨bf, 1⟩))
            .dead .dead .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 2
          { m with borrows := invalidateConflictingBorrows mBorrows 4 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) .dead .dead .dead .dead .dead .dead .dead) = _
        rw [hBorEq 4 (by decide)]
      have hs2 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 2 m .uninit (.init (.scalar ⟨bf, 1⟩))
            .dead .dead .dead .dead .dead .dead .dead) =
          .cont (mkSt12 3 m .uninit (.init (.scalar ⟨bf, 1⟩))
            .uninit .dead .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 3
          { m with borrows := disableLocalBorrows mBorrows 5 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) .uninit .dead .dead .dead .dead .dead .dead) = _
        rw [hDisEq 5 (by decide)]
      have hs3 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 3 m .uninit (.init (.scalar ⟨bf, 1⟩))
            .uninit .dead .dead .dead .dead .dead .dead) =
          .cont (mkSt12 4 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) .dead .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 4
          { m with borrows := invalidateConflictingBorrows mBorrows 5 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          .dead .dead .dead .dead .dead .dead) = _
        rw [hBorEq 5 (by decide)]
      have hs4 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 4 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) .dead .dead .dead .dead .dead .dead) =
          .cont (mkSt12 5 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) .uninit .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 5
          { m with borrows := disableLocalBorrows mBorrows 6 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          .uninit .dead .dead .dead .dead .dead) = _
        rw [hDisEq 6 (by decide)]
      have hs5 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 5 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) .uninit .dead .dead .dead .dead .dead) =
          .cont (mkSt12 6 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            .dead .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 6
          { m with borrows := invalidateConflictingBorrows mBorrows 6 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) .dead .dead .dead .dead .dead) = _
        rw [hBorEq 6 (by decide)]
      have hs6 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 6 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            .dead .dead .dead .dead .dead) =
          .cont (mkSt12 7 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            .uninit .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 7
          { m with borrows := disableLocalBorrows mBorrows 7 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) .uninit .dead .dead .dead .dead) = _
        rw [hDisEq 7 (by decide)]
      have hs7 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 7 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            .uninit .dead .dead .dead .dead) =
          .cont (mkSt12 8 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 8
          { m with borrows := invalidateConflictingBorrows mBorrows 7 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) = _
        rw [hBorEq 7 (by decide)]
      have hs8 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 8 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) .dead .dead .dead .dead) =
          .cont (mkSt12 9 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 9
          { m with borrows := disableLocalBorrows mBorrows 8 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) = _
        rw [hDisEq 8 (by decide)]
      have hs9 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 9 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) .uninit .dead .dead .dead) =
          .cont (mkSt12 10 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 10
          { m with borrows := invalidateConflictingBorrows mBorrows 8 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) = _
        rw [hBorEq 8 (by decide)]
      have hs10 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 10 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .dead .dead .dead) =
          .cont (mkSt12 11 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 11
          { m with borrows := disableLocalBorrows mBorrows 9 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) = _
        rw [hDisEq 9 (by decide)]
      have hs11 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 11 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩)) .uninit .dead .dead) =
          .cont (mkSt12 12 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) .dead .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 12
          { m with borrows := invalidateConflictingBorrows mBorrows 9 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) (.init (.scalar ⟨b2, 1⟩)) .dead .dead) = _
        rw [hBorEq 9 (by decide)]
      have hs12 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 12 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) .dead .dead) =
          .cont (mkSt12 13 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 13
          { m with borrows := disableLocalBorrows mBorrows 10 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) = _
        rw [hDisEq 10 (by decide)]
      have hs13 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 13 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) .uninit .dead) =
          .cont (mkSt12 14 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .dead) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 14
          { m with borrows := invalidateConflictingBorrows mBorrows 10 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) (.init (.scalar ⟨b2, 1⟩))
          (.init (.scalar ⟨s3, 4⟩)) .dead) = _
        rw [hBorEq 10 (by decide)]
      have hs14 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 14 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .dead) =
          .cont (mkSt12 15 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .uninit) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 15
          { m with borrows := disableLocalBorrows mBorrows 11 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) (.init (.scalar ⟨b2, 1⟩))
          (.init (.scalar ⟨s3, 4⟩)) .uninit) = _
        rw [hDisEq 11 (by decide)]
      have hs15 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 15 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) .uninit) =
          .cont (mkSt12 16 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 16
          { m with borrows := invalidateConflictingBorrows mBorrows 11 none 0 }
          .uninit (.init (.scalar ⟨bf, 1⟩)) (.init (.scalar ⟨b0, 1⟩))
          (.init (.scalar ⟨s1, 4⟩)) (.init (.scalar ⟨b1, 1⟩))
          (.init (.scalar ⟨s2, 4⟩)) (.init (.scalar ⟨b2, 1⟩))
          (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) = _
        rw [hBorEq 11 (by decide)]
      have hs16 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 16 m .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .cont (mkSt12 17 { m with callerLocals := cl' } .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
        let locs16 := (mkSt12 16 m .uninit (.init (.scalar ⟨bf, 1⟩))
          (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
          (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
          (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))).frame.locals
        have hArrEq : [Value.scalar ⟨bf, 1⟩, Value.scalar ⟨0, 1⟩, Value.scalar ⟨0, 1⟩, Value.scalar ⟨0, 1⟩,
            Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩, Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩] =
            u8BytesToValues (rawPaddedPairCodec.enc (flag, v)) := by
          have hU32 := u32_le_bytes_match v
          have hFlagVal : Value.scalar ⟨bf, 1⟩ = Value.scalar ⟨(if flag then 1 else 0), 1⟩ := by
            cases flag <;> rfl
          rw [hFlagVal]
          cases flag with
          | false =>
            show Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ ::
              Value.scalar ⟨0, 1⟩ :: [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
              Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩] =
              Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ ::
              Value.scalar ⟨0, 1⟩ :: u8BytesToValues (rawU32Codec.enc v)
            rw [hU32]
          | true =>
            show Value.scalar ⟨1, 1⟩ :: Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ ::
              Value.scalar ⟨0, 1⟩ :: [Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
              Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩] =
              Value.scalar ⟨1, 1⟩ :: Value.scalar ⟨0, 1⟩ :: Value.scalar ⟨0, 1⟩ ::
              Value.scalar ⟨0, 1⟩ :: u8BytesToValues (rawU32Codec.enc v)
            rw [hU32]
        have hFrame1 : Trusted.Sequence.get? locs16 1 =
            some (.init (.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8,
              .scalar ⟨(rawPaddedPairCodec.enc (flag, v)).length, 8⟩])) := by
          rw [hEncLen]; rfl
        have hCaller := evalCallerSliceAssign_ok
          (m := m) (frameLocals := locs16) (e := e) (off := L.offset)
          (slot := slot) (bytes := bytes) (bs := rawPaddedPairCodec.enc (flag, v)) (cl' := cl')
          (localDecls := writePaddedPairSliceBody.localDecls)
          (layouts := writePaddedPairSliceBody.layouts)
          hFrame1 (Nat.le_of_ble_eq_true (rfl : Nat.ble 12 12 = true)) rfl rfl hDisj hMemE hPermE
          (by rw [hLocE]; exact hGetSlot) hSlotBytes (by omega)
          (by rw [hEncLen, ← hL8]; exact hBound) (by rw [hLocE]; exact hSetCl)
        have hStep16 : stepMirFn writePaddedPairSliceBody
            (mkSt12 16 m .uninit (.init (.scalar ⟨bf, 1⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
            MirStepNode.step (mkSt12 17 { m with callerLocals := cl' } .uninit (.init (.scalar ⟨bf, 1⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
          change (match evalPlaceWrite locs16 m.borrows (pl 1 [.deref])
              (.aggregate 0 [Value.scalar ⟨bf, 1⟩, Value.scalar ⟨0, 1⟩, Value.scalar ⟨0, 1⟩,
                             Value.scalar ⟨0, 1⟩, Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
                             Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩])
              m.activeProtectors writePaddedPairSliceBody.localDecls
              writePaddedPairSliceBody.layouts m.callStack with
            | .ok _ => _
            | .ub =>
              match mCallerLocals with
              | [] => MirStepNode.fail .ub
              | _ :: _ =>
                match evalCallerPlaceWrite locs16 m.callerLocals m.borrows (pl 1 [.deref])
                    (.aggregate 0 [Value.scalar ⟨bf, 1⟩, Value.scalar ⟨0, 1⟩, Value.scalar ⟨0, 1⟩,
                                   Value.scalar ⟨0, 1⟩, Value.scalar ⟨b0, 1⟩, Value.scalar ⟨b1, 1⟩,
                                   Value.scalar ⟨b2, 1⟩, Value.scalar ⟨b3, 1⟩])
                    m.activeProtectors with
                | .ok callerLocals' =>
                  match derefWriteTreeUB locs16 m.borrows (pl 1 [.deref]) with
                  | true => MirStepNode.fail .ub
                  | false =>
                    MirStepNode.step (mkSt12 17
                      { m with callerLocals := callerLocals',
                               borrows := invalidateDerefWriteBorrows locs16 m.borrows (pl 1 [.deref])
                                 [] m.callerLocals }
                      .uninit (.init (.scalar ⟨bf, 1⟩))
                      (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
                      (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
                      (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩)))
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
            | .unsupported => MirStepNode.unsupported) = _
          rw [hArrEq, hCaller.1]
          cases hCl : mCallerLocals with
          | nil => exact False.elim (hCaller.2.1 hCl)
          | cons _ _ =>
            dsimp only
            rw [hCaller.2.2.1, hCaller.2.2.2.1, hCaller.2.2.2.2]
        unfold Anneal.PureMirExec.mirStep
        rw [hStep16]; rfl
      have hs17 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 17 { m with callerLocals := cl' } .uninit (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .cont (mkSt12 18 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
            (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) := by
        change Anneal.PureMirExec.Step.cont (mkSt12 18
          { m with callerLocals := cl', borrows := invalidateConflictingBorrows mBorrows 0 none 0 }
          (.init (.scalar ⟨v.toNat, 4⟩)) (.init (.scalar ⟨bf, 1⟩))
          (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
          (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
          (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) = _
        rw [hBorEq 0 (by decide)]
      have hs18 : Anneal.PureMirExec.mirStep writePaddedPairSliceBody
          (mkSt12 18 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
            (.init (.scalar ⟨bf, 1⟩))
            (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
            (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
            (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
          .done (.normal (.scalar ⟨v.toNat, 4⟩, { m with callerLocals := cl' })) := by
        have hStep18 : stepMirFn writePaddedPairSliceBody
            (mkSt12 18 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
              (.init (.scalar ⟨bf, 1⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩))) =
            MirStepNode.retNormal (Value.scalar ⟨v.toNat, 4⟩) { m with callerLocals := cl' } := by
          change evalTerminator
            (mkSt12 18 { m with callerLocals := cl' } (.init (.scalar ⟨v.toNat, 4⟩))
              (.init (.scalar ⟨bf, 1⟩))
              (.init (.scalar ⟨b0, 1⟩)) (.init (.scalar ⟨s1, 4⟩))
              (.init (.scalar ⟨b1, 1⟩)) (.init (.scalar ⟨s2, 4⟩))
              (.init (.scalar ⟨b2, 1⟩)) (.init (.scalar ⟨s3, 4⟩)) (.init (.scalar ⟨b3, 1⟩)))
            (mkBb [] .return_).terminator (some writePaddedPairSliceBody) = _
          unfold evalTerminator Trusted.Sequence.length
          simp only [mkBb, mkSt12, m, Trusted.Sequence.get?, List.getElem?_cons_zero,
            List.length_nil, List.length_cons, hasFrameDeallocProtectorConflict,
            disableFrameBorrows_of_le12 12 (by decide) hFlat]
        unfold Anneal.PureMirExec.mirStep
        rw [hStep18]; rfl
      exact
        step_det_to _ hs0 <| step_det_to _ hs1 <| step_det_to _ hs2 <|
        step_det_to _ hs3 <| step_det_to _ hs4 <| step_det_to _ hs5 <|
        step_det_to _ hs6 <| step_det_to _ hs7 <| step_det_to _ hs8 <|
        step_det_to _ hs9 <| step_det_to _ hs10 <| step_det_to _ hs11 <|
        step_det_to _ hs12 <| step_det_to _ hs13 <| step_det_to _ hs14 <|
        step_det_to _ hs15 <| step_det_to _ hs16 <| step_det_to _ hs17 <|
        step_det_done (.normal (.scalar ⟨v.toNat, 4⟩, { m with callerLocals := cl' })) hs18
          (by dsimp [mirNormalOutcomeExtract]; rw [ofU32Value_u32]; rfl)

/-- Disjoint `&mut [u8]` slice lenses inside caller buffer `callerLocals[12]`:
* `[0..4)` header `u32`,
* `[4..12)` 8-byte padded `(bool, [u8; 3], u32)` payload,
* `[12..16)` untouched sibling `u32`. -/
def calleeHdrLens : ByteSubLens SliceCallAddr := ⟨⟨12⟩, 0, 4⟩
def calleePayLens : ByteSubLens SliceCallAddr := ⟨⟨12⟩, 4, 8⟩
def calleeSibLens : ByteSubLens SliceCallAddr := ⟨⟨12⟩, 12, 4⟩

/-- Live `V2026_06_01` `Memory` carrying:
* a 16-byte caller-owned `[u8; 16]` referent in `callerLocals[12]` holding
  symbolic `(initHdr, initFlag, initVal, siblingVal)`,
* 4 live pairwise-disjoint Tree Borrows entries (`tag 1` for `[0..4)`, `tag 2`
  for `[4..12)`, `tag 3` for `[12..16)`, and frozen `tag 4` on `callerLocals[13]`),
* live global allocations from `mkCanaryGlobalMem`. -/
def mkCanaryCalleeMem (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal : UInt32) :
    Memory :=
  let buf16 : List UInt8 :=
    rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal) ++
      rawU32Codec.enc siblingVal
  { globals := (mkCanaryGlobalMem initHdr initFlag initVal siblingVal).globals
    borrows :=
      [{ tag := 1, targetLocal := 12, targetProjection := [], perm := .unique,
         rangeOffset := 0, rangeLen := 4, targetFrameDepth := 0 },
       { tag := 2, targetLocal := 12, targetProjection := [], perm := .unique,
         rangeOffset := 4, rangeLen := 8, targetFrameDepth := 0 },
       { tag := 3, targetLocal := 12, targetProjection := [], perm := .unique,
         rangeOffset := 12, rangeLen := 4, targetFrameDepth := 0 },
       { tag := 4, targetLocal := 13, targetProjection := [], perm := .frozen,
         rangeOffset := 0, rangeLen := 4, targetFrameDepth := 0 }]
    callerLocals := List.replicate 12 LocalSlot.dead ++
      [u8BytesToSlot buf16, u8BytesToSlot (rawU32Codec.enc siblingVal)]
    nextAllocId := 9
    nextTag := 5 }

private theorem mkCanaryCalleeMem_get12 (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    listGet? (mkCanaryCalleeMem initHdr initFlag initVal siblingVal).callerLocals 12 =
      some (u8BytesToSlot (rawU32Codec.enc initHdr ++
        rawPaddedPairCodec.enc (initFlag, initVal) ++ rawU32Codec.enc siblingVal)) := rfl

private theorem mkCanaryCalleeMem_hdr_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    calleeHdrLens.getVal rawU32Codec
      (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) = some initHdr := by
  have hL1 := rawU32Codec.enc_length initHdr
  have hL2 := rawPaddedPairCodec.enc_length (initFlag, initVal)
  have hL3 := rawU32Codec.enc_length siblingVal
  have hReady : sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal)
      ⟨12⟩ 0 4 = true := by
    unfold sliceCallAbiReady; dsimp only [mkCanaryCalleeMem]; decide
  have hGet : calleeHdrLens.get (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) =
      some (rawU32Codec.enc initHdr) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 0 4 with
      | false => none
      | true => memCallerByteStoreOps.readBytes? (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 0 4) = _
    rw [hReady]
    dsimp [ByteStoreOps.readBytes?]
    rw [mkCanaryCalleeMem_get12]; dsimp only
    rw [slotAsU8Bytes?_u8BytesToSlot]; dsimp only
    have hTot : (rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal) ++
        rawU32Codec.enc siblingVal).length = 16 := by simp [hL1, hL2, hL3]
    rw [hTot]; dsimp only
    rw [List.drop_zero, List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  exact ByteSubLens.getVal_of rfl hGet (rawU32Codec.dec_enc initHdr)

private theorem mkCanaryCalleeMem_pay_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    calleePayLens.getVal rawPaddedPairCodec
      (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) = some (initFlag, initVal) := by
  have hL1 := rawU32Codec.enc_length initHdr
  have hL2 := rawPaddedPairCodec.enc_length (initFlag, initVal)
  have hL3 := rawU32Codec.enc_length siblingVal
  have hReady : sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal)
      ⟨12⟩ 4 8 = true := by
    unfold sliceCallAbiReady; dsimp only [mkCanaryCalleeMem]; decide
  have hGet : calleePayLens.get (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) =
      some (rawPaddedPairCodec.enc (initFlag, initVal)) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 4 8 with
      | false => none
      | true => memCallerByteStoreOps.readBytes? (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 4 8) = _
    rw [hReady]
    dsimp [ByteStoreOps.readBytes?]
    rw [mkCanaryCalleeMem_get12]; dsimp only
    rw [slotAsU8Bytes?_u8BytesToSlot]; dsimp only
    have hTot : (rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal) ++
        rawU32Codec.enc siblingVal).length = 16 := by simp [hL1, hL2, hL3]
    rw [hTot]; dsimp only
    rw [List.append_assoc, List.drop_left' hL1,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact ByteSubLens.getVal_of rfl hGet (rawPaddedPairCodec.dec_enc (initFlag, initVal))

private theorem mkCanaryCalleeMem_sib_getVal (initHdr : UInt32) (initFlag : Bool)
    (initVal siblingVal : UInt32) :
    calleeSibLens.getVal rawU32Codec
      (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) = some siblingVal := by
  have hL1 := rawU32Codec.enc_length initHdr
  have hL2 := rawPaddedPairCodec.enc_length (initFlag, initVal)
  have hL3 := rawU32Codec.enc_length siblingVal
  have hReady : sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal)
      ⟨12⟩ 12 4 = true := by
    unfold sliceCallAbiReady; dsimp only [mkCanaryCalleeMem]; decide
  have hGet : calleeSibLens.get (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) =
      some (rawU32Codec.enc siblingVal) := by
    rw [ByteSubLens.get_of_pos _ (by decide)]
    change (match sliceCallAbiReady (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 12 4 with
      | false => none
      | true => memCallerByteStoreOps.readBytes? (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) ⟨12⟩ 12 4) = _
    rw [hReady]
    dsimp [ByteStoreOps.readBytes?]
    rw [mkCanaryCalleeMem_get12]; dsimp only
    rw [slotAsU8Bytes?_u8BytesToSlot]; dsimp only
    have hTot : (rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal) ++
        rawU32Codec.enc siblingVal).length = 16 := by simp [hL1, hL2, hL3]
    rw [hTot]; dsimp only
    have hPre : (rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal)).length = 12 := by
      simp [hL1, hL2]
    rw [List.drop_left' hPre, List.take_of_length_le (by omega)]
  exact ByteSubLens.getVal_of rfl hGet (rawU32Codec.dec_enc siblingVal)

/-- **Canary 3B (Real Mutating `V2026_06_01` Callees Sealed Behind
`@[irreducible] MutSummaryOutcomeCut` + Multi-Call `execMutSummaryChain` →
`MirOutcomeChainConverges` / `MirWpConverges` + Zero-Destructuring Framing)**:
For ALL symbolic `(initHdr, initFlag, initVal, siblingVal, newHdr, newFlag, newVal)`:
1. Seals BOTH real `V2026_06_01` callees (`writeU32SliceBody`, `writePaddedPairSliceBody`)
   behind `@[irreducible] MutSummaryOutcomeCut` and runs them via
   `mirOutcomeChainConverges_of_execMutSummaryChain`.
2. Delivers live `MirWpConverges` for EVERY callee execution in the chain
   (`MirOutcomeChainConverges ofU32Value specs m0 m2 [newHdr, newVal]`).
3. Proves exact post-values on `[0..4)` (`newHdr`) and `[4..12)` (`(newFlag, newVal)`).
4. Proves untouched sibling `[12..16)` (`siblingVal`) is preserved via
   `execMutSummaryChain_frame_disjoint` (ZERO raw byte-list destructuring!).
5. Proves `Memory.borrows` and `Memory.globals` invariance via `WritePreserves`. -/
theorem canary3b_realCallees_execMutSummaryChain_and_framing
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newHdr : UInt32)
    (newFlag : Bool) (newVal : UInt32) :
    let m0 := mkCanaryCalleeMem initHdr initFlag initVal siblingVal
    let specs : List (CapturedMir × (ByteSubLens SliceCallAddr → Memory → SliceCalleeArg → MachineState) ×
        MutSummaryCall UInt8 SliceCallAddr SliceCalleeArg UInt32) :=
      [(writeU32SliceBody, writeU32Entry, ⟨writeU32SliceSum, calleeHdrLens, .u32Arg newHdr⟩),
       (writePaddedPairSliceBody, writePaddedPairEntry,
         ⟨writePaddedPairSliceSum, calleePayLens, .paddedPairArg newFlag newVal⟩)]
    ∃ m2,
      execMutSummaryChain (specs.map (fun s => s.2.2)) m0 = some (m2, [newHdr, newVal]) ∧
      MirOutcomeChainConverges ofU32Value specs m0 m2 [newHdr, newVal] ∧
      calleeHdrLens.getVal rawU32Codec m2 = some newHdr ∧
      calleePayLens.getVal rawPaddedPairCodec m2 = some (newFlag, newVal) ∧
      calleeSibLens.getVal rawU32Codec m2 = some siblingVal ∧
      m2.borrows = m0.borrows ∧
      m2.globals = m0.globals := by
  intro m0 specs
  have hHdr0 := mkCanaryCalleeMem_hdr_getVal initHdr initFlag initVal siblingVal
  have hPay0 := mkCanaryCalleeMem_pay_getVal initHdr initFlag initVal siblingVal
  have hSib0 := mkCanaryCalleeMem_sib_getVal initHdr initFlag initVal siblingVal
  rcases execMutSummary_ofSliceCodec_of (sc := rawU32Codec)
      (fn := fun _ arg => match arg with | SliceCalleeArg.u32Arg v => some (v, v) | _ => none)
      (arg := SliceCalleeArg.u32Arg newHdr)
      hHdr0 (v' := newHdr) (ret := newHdr) rfl with ⟨m1, hCall1, _, hHdr1_get⟩
  have hDisjHdrPay : ByteSubLens.Disjoint Memory calleeHdrLens calleePayLens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  have hDisjHdrSib : ByteSubLens.Disjoint Memory calleeHdrLens calleeSibLens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  have hDisjPaySib : ByteSubLens.Disjoint Memory calleePayLens calleeSibLens :=
    ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by decide)))
  have hPay1 : calleePayLens.getVal rawPaddedPairCodec m1 = some (initFlag, initVal) := by
    have hEq := execMutSummary_frame_disjoint (Mem := Memory) hDisjHdrPay hCall1
    unfold ByteSubLens.getVal at hPay0 ⊢; rw [hEq]; exact hPay0
  rcases execMutSummary_ofSliceCodec_of (sc := rawPaddedPairCodec)
      (fn := fun _ arg => match arg with | SliceCalleeArg.paddedPairArg b v => some ((b, v), v) | _ => none)
      (arg := SliceCalleeArg.paddedPairArg newFlag newVal)
      hPay1 (v' := (newFlag, newVal)) (ret := newVal) rfl with ⟨m2, hCall2, _, hPay2_get⟩
  have hChain : execMutSummaryChain (specs.map (fun s => s.2.2)) m0 = some (m2, [newHdr, newVal]) :=
    execMutSummaryChain_cons_of hCall1
      (execMutSummaryChain_cons_of hCall2 (execMutSummaryChain_nil m2))
  have hCuts : ∀ item, item ∈ specs →
      MutSummaryOutcomeCut (wops := mirDetWpOps item.1) item.2.1
        (mirNormalOutcomeExtract ofU32Value) item.2.2.sum := by
    intro item hMem
    dsimp only [specs] at hMem
    cases hMem with
    | head => exact writeU32Slice_mutSummaryOutcomeCut
    | tail _ hMem2 =>
      cases hMem2 with
      | head => exact writePaddedPairSlice_mutSummaryOutcomeCut
      | tail _ hEmpty => cases hEmpty
  rcases mirOutcomeChainConverges_of_execMutSummaryChain specs hCuts hChain with ⟨hConv, hFrameAll⟩
  have hHdr2 : calleeHdrLens.getVal rawU32Codec m2 = some newHdr := by
    have hEq := execMutSummary_frame_disjoint (Mem := Memory) hDisjHdrPay.symm hCall2
    unfold ByteSubLens.getVal at hHdr1_get ⊢; rw [hEq]; exact hHdr1_get
  have hAllDisjSib : AllCallsDisjoint Memory calleeSibLens (specs.map (fun s => s.2.2)) :=
    ⟨hDisjHdrSib, hDisjPaySib, trivial⟩
  have hSib2 : calleeSibLens.getVal rawU32Codec m2 = some siblingVal := by
    have hEq := hFrameAll calleeSibLens hAllDisjSib
    unfold ByteSubLens.getVal at hSib0 ⊢; rw [hEq]; exact hSib0
  exact ⟨m2, hChain, hConv, hHdr2, hPay2_get, hSib2,
    execMutSummaryChain_preserves sliceCall_writePreserves_borrows (specs.map (fun s => s.2.2)) hChain,
    execMutSummaryChain_preserves sliceCall_writePreserves_globals (specs.map (fun s => s.2.2)) hChain⟩

/-- **Canary 3B (Fail-Closed Rejection of a Real Panicking `V2026_06_01` Callee)**:
`panickingSliceBody` terminates with `.panic` under `stepMirFn`, so
`not_mutSummaryOutcomeCut_of_nonNormal` proves it CANNOT satisfy
`MutSummaryOutcomeCut` under `mirNormalOutcomeExtract`. -/
theorem canary3b_panickingCallee_rejected :
    ¬ MutSummaryOutcomeCut (wops := mirDetWpOps panickingSliceBody)
        panickingEntry (mirNormalOutcomeExtract ofU32Value) writeU32SliceSum := by
  let m0 := mkCanaryCalleeMem 1 false 2 3
  have hHdr0 := mkCanaryCalleeMem_hdr_getVal 1 false 2 3
  rcases execMutSummary_ofSliceCodec_of (sc := rawU32Codec)
      (fn := fun _ arg => match arg with | SliceCalleeArg.u32Arg v => some (v, v) | _ => none)
      (arg := SliceCalleeArg.u32Arg 99)
      hHdr0 (v' := 99) (ret := 99) rfl with ⟨m1, hExec, _, _⟩
  have hPanicRun : wpStateOk (ops := mirDetWpOps panickingSliceBody) (· = .panic)
      (panickingEntry calleeHdrLens m0 (.u32Arg 99)) :=
    step_det_done .panic rfl rfl
  exact not_mutSummaryOutcomeCut_of_nonNormal hExec rfl hPanicRun

/-- Alignment oracle for caller-frame `[u8; N]` referent slices (`SliceCallAddr`):
requires `2^k ∣ off` (modelling 4-byte-aligned caller buffer bases, independent of
byte contents so write-invariant across all `sliceCallByteStoreOps` writes).

Caveat: this is a caller-side packing DISCIPLINE, not a Rust layout fact. A Rust
`[u8; N]` has ABI alignment 1, and `V2026_06_01` `callerLocals` slots carry no
layout/address metadata, so the trusted semantics never faults on an "unaligned"
`&mut [u8]` write. Fail-closed rejection here is enforced only by the
`AlignedSubLens` view, not by `stepMirFn`. -/
def sliceCallAlignedAt (_m : Memory) (_a : SliceCallAddr) (off k : Nat) : Bool :=
  Nat.beq (off % (2 ^ k)) 0

theorem sliceCall_writePreserves_alignedAt (a : SliceCallAddr) (off k : Nat) :
    sliceCallByteStoreOps.WritePreserves (fun m : Memory => sliceCallAlignedAt m a off k) :=
  fun _ _ _ _ _ _ => rfl

/-- Aligned 4-byte lenses (`alignLog2 = 2`) and fail-closed misaligned, OOB, and
frozen-borrow lenses over `SliceCallAddr`. -/
def calleeHdrAligned : AlignedSubLens SliceCallAddr := ⟨calleeHdrLens, 2⟩
def calleePayAligned : AlignedSubLens SliceCallAddr := ⟨calleePayLens, 2⟩
def calleeSibAligned : AlignedSubLens SliceCallAddr := ⟨calleeSibLens, 2⟩
def calleeMisalignedU32 : AlignedSubLens SliceCallAddr := ⟨⟨⟨12⟩, 2, 4⟩, 2⟩
def calleeOobLens : ByteSubLens SliceCallAddr := ⟨⟨12⟩, 14, 4⟩
def calleeFrozenLens : ByteSubLens SliceCallAddr := ⟨⟨13⟩, 0, 4⟩

/-- **Canary 3B (`AlignedSubLens` framing + fail-closed misaligned, OOB, and
frozen-borrow rejection on `SliceCallAddr`)**:
For ALL symbolic `(initHdr, initFlag, initVal, siblingVal, newHdr, newFlag, newVal)`:
1. Alignment-checked post-reads (`AlignedSubLens.getVal`) succeed on header,
   payload, and untouched sibling (via `AlignedSubLens.get_execMutSummaryChain_disjoint`).
2. Misaligned `SliceCallAddr` (`offset = 2`, `alignLog2 = 2`) fails closed (`= none`)
   on both `get` and `set`.
3. Out-of-bounds `SliceCallAddr` (`offset = 14, len = 4` on 16-byte buffer) fails
   closed (`= none`) on both `get` and `set`.
4. Frozen-borrow `SliceCallAddr` (`callerLocals[13]`, live initialized 4-byte
   buffer covered only by `.frozen` `tag 4`) fails closed (`= none`) on `get` and `set`. -/
theorem canary3b_sliceCall_aligned_and_failClosed
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newHdr : UInt32)
    (newFlag : Bool) (newVal : UInt32) :
    let m0 := mkCanaryCalleeMem initHdr initFlag initVal siblingVal
    let calls : List (MutSummaryCall UInt8 SliceCallAddr SliceCalleeArg UInt32) :=
      [⟨writeU32SliceSum, calleeHdrLens, .u32Arg newHdr⟩,
       ⟨writePaddedPairSliceSum, calleePayLens, .paddedPairArg newFlag newVal⟩]
    ∃ m2,
      execMutSummaryChain calls m0 = some (m2, [newHdr, newVal]) ∧
      calleeHdrAligned.getVal sliceCallAlignedAt rawU32Codec m2 = some newHdr ∧
      calleePayAligned.getVal sliceCallAlignedAt rawPaddedPairCodec m2 = some (newFlag, newVal) ∧
      calleeSibAligned.getVal sliceCallAlignedAt rawU32Codec m2 = some siblingVal ∧
      calleeMisalignedU32.get sliceCallAlignedAt m2 = none ∧
      calleeMisalignedU32.set sliceCallAlignedAt m2 (rawU32Codec.enc newHdr) = none ∧
      calleeOobLens.get m2 = none ∧
      calleeOobLens.set m2 (rawU32Codec.enc newHdr) = none ∧
      calleeFrozenLens.get m2 = none ∧
      calleeFrozenLens.set m2 (rawU32Codec.enc newHdr) = none := by
  intro m0 calls
  rcases canary3b_realCallees_execMutSummaryChain_and_framing
      initHdr initFlag initVal siblingVal newHdr newFlag newVal with
    ⟨m2, hChain, _, hHdr2, hPay2, _, hBor2, _⟩
  have hAllDisjSib : AllCallsDisjoint Memory calleeSibLens calls := by
    dsimp only [calls]
    exact ⟨ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by dsimp only; decide))),
     ByteSubLens.disjoint_of_separated (Or.inr (Or.inl (by dsimp only; decide))), trivial⟩
  have hSibAlignedEq :
      calleeSibAligned.get sliceCallAlignedAt m2 =
      calleeSibAligned.get sliceCallAlignedAt m0 :=
    AlignedSubLens.get_execMutSummaryChain_disjoint
      (fun a off k => sliceCall_writePreserves_alignedAt a off k)
      calleeSibAligned calls hAllDisjSib hChain
  have hSib2Aligned :
      calleeSibAligned.getVal sliceCallAlignedAt rawU32Codec m2 = some siblingVal := by
    have hGet2 : calleeSibLens.get m2 = calleeSibLens.get m0 :=
      execMutSummaryChain_frame_disjoint calleeSibLens calls hAllDisjSib hChain
    exact (ByteSubLens.getValIf_of_ok rawU32Codec calleeSibLens rfl).trans
      (by unfold ByteSubLens.getVal; rw [hGet2]; exact mkCanaryCalleeMem_sib_getVal initHdr initFlag initVal siblingVal)
  have hNotReadyOob : sliceCallAbiReady m2 ⟨12⟩ 14 4 = false := by
    unfold sliceCallAbiReady
    rw [hBor2]
    have hFindNone : (findCoveringUniqueBorrow m0.borrows 12 14 4).isSome = false := by
      dsimp only [m0, mkCanaryCalleeMem]; decide
    rw [hFindNone, Bool.and_false]
  have hNotReadyFrozen : sliceCallAbiReady m2 ⟨13⟩ 0 4 = false := by
    unfold sliceCallAbiReady
    rw [hBor2]
    have hFindNone : (findCoveringUniqueBorrow m0.borrows 13 0 4).isSome = false := by
      dsimp only [m0, mkCanaryCalleeMem]; decide
    rw [hFindNone, Bool.and_false]
  have hOobGet : calleeOobLens.get m2 = none := by
    rw [ByteSubLens.get_of_pos m2 (by decide)]
    change (match sliceCallAbiReady m2 ⟨12⟩ 14 4 with | false => none | true => _) = none
    rw [hNotReadyOob]
  have hOobSet : calleeOobLens.set m2 (rawU32Codec.enc newHdr) = none := by
    rw [ByteSubLens.set_of_pos m2 (by decide) (rawU32Codec.enc_length newHdr)]
    change (match sliceCallAbiReady m2 ⟨12⟩ 14 (rawU32Codec.enc newHdr).length with
      | false => none | true => _) = none
    rw [rawU32Codec.enc_length newHdr, hNotReadyOob]
  have hFrozenGet : calleeFrozenLens.get m2 = none := by
    rw [ByteSubLens.get_of_pos m2 (by decide)]
    change (match sliceCallAbiReady m2 ⟨13⟩ 0 4 with | false => none | true => _) = none
    rw [hNotReadyFrozen]
  have hFrozenSet : calleeFrozenLens.set m2 (rawU32Codec.enc newHdr) = none := by
    rw [ByteSubLens.set_of_pos m2 (by decide) (rawU32Codec.enc_length newHdr)]
    change (match sliceCallAbiReady m2 ⟨13⟩ 0 (rawU32Codec.enc newHdr).length with
      | false => none | true => _) = none
    rw [rawU32Codec.enc_length newHdr, hNotReadyFrozen]
  have _ := hSibAlignedEq
  exact ⟨m2, hChain,
    (ByteSubLens.getValIf_of_ok rawU32Codec calleeHdrLens rfl).trans hHdr2,
    (ByteSubLens.getValIf_of_ok rawPaddedPairCodec calleePayLens rfl).trans hPay2,
    hSib2Aligned,
    AlignedSubLens.get_none_of_unaligned calleeMisalignedU32 rfl,
    AlignedSubLens.set_none_of_unaligned calleeMisalignedU32 _ rfl,
    hOobGet, hOobSet, hFrozenGet, hFrozenSet⟩

private theorem mkCanaryCalleeMem_borrows_flat
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal : UInt32) :
    ∀ e ∈ (mkCanaryCalleeMem initHdr initFlag initVal siblingVal).borrows,
      borrowFlatRoot e = true := by
  intro e hMem
  simp only [mkCanaryCalleeMem, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl <;> rfl

/-- **Symbolic Entry-to-UB Live Tree Borrows Non-Vacuity on Unmodified
`V2026_06_01.MirSemantics`**:
Starting from real `initMachineStateWithMemoryAndCallees writeU32SliceBody` with
frozen borrow `tag 4` targeting the live initialized 4-byte buffer in
`callerLocals[13]`, for ALL symbolic `(initHdr, initFlag, initVal, siblingVal, newVal)`:
1. Real MIR execution steps 14 times (`StepStageCut`) to statement 14 (`(*_1) = [b0..b3]`).
2. At statement 14, unmodified `stepMirFn writeU32SliceBody` emits `MirStepNode.fail .ub`
   strictly because `tag 4` has `perm = .frozen`.
3. Consequently, `MirWpConverges writeU32SliceBody st0 post` AND
   `wpStateOk (ops := mirDetWpOps writeU32SliceBody) post st0` are uninhabited for
   EVERY `post` (via `V2026Bridge.not_mirWpConverges_of_stepStageCut_fault`). -/
theorem canary3b_frozenBorrow_derefWrite_ub
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newVal : UInt32) :
    let m0 := mkCanaryCalleeMem initHdr initFlag initVal siblingVal
    let fatFrozen : Value := .aggregate 0 [.ptr ⟨4, 0⟩ 8, .scalar ⟨4, 8⟩]
    let st0 := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees writeU32SliceBody
      [fatFrozen, .scalar ⟨newVal.toNat, 4⟩] m0 []
    (∃ st14,
      StepStageCut (mirDetStep writeU32SliceBody) 14 st0 st14 ∧
      stepMirFn writeU32SliceBody st14 = MirStepNode.fail .ub) ∧
    (∀ post, ¬ MirWpConverges writeU32SliceBody st0 post) ∧
    (∀ post, ¬ wpStateOk (ops := mirDetWpOps writeU32SliceBody) post st0) := by
  intro m0 fatFrozen st0
  have hCut14 :
      StepStageCut (mirDetStep writeU32SliceBody) 14 st0
        (writeU32Stmt14State fatFrozen newVal m0) :=
    writeU32Slice_entry_to_stmt14 fatFrozen newVal m0 rfl rfl rfl rfl
      (mkCanaryCalleeMem_borrows_flat initHdr initFlag initVal siblingVal)
  have hFail14 :
      stepMirFn writeU32SliceBody (writeU32Stmt14State fatFrozen newVal m0) =
        MirStepNode.fail .ub := rfl
  have hMirFault :
      Anneal.PureMirExec.mirStep writeU32SliceBody (writeU32Stmt14State fatFrozen newVal m0) =
        .fault := by
    unfold Anneal.PureMirExec.mirStep
    rw [hFail14]; rfl
  exact ⟨⟨writeU32Stmt14State fatFrozen newVal m0, hCut14, hFail14⟩,
    fun post => not_mirWpConverges_of_stepStageCut_fault hCut14 hFail14 post,
    fun post => not_wpStateOk_of_stepStageCut_fault hCut14 hMirFault post⟩

/-- **Symbolic Entry-to-UB Live Out-of-Bounds Slice Non-Vacuity on Unmodified
`V2026_06_01.MirSemantics`**:
Starting from real `initMachineStateWithMemoryAndCallees writeU32SliceBody` with
`.unique` borrow `tag 3` at an out-of-bounds offset (`offset = 14, len = 4` on
the 16-byte buffer in `callerLocals[12]`), for ALL symbolic
`(initHdr, initFlag, initVal, siblingVal, newVal)`:
1. Real MIR execution steps 14 times (`StepStageCut`) to statement 14 (`(*_1) = [b0..b3]`).
2. At statement 14, unmodified `stepMirFn writeU32SliceBody` emits `MirStepNode.fail .ub`
   inside `writeSliceFatPtrTargetValue` (bounds check `14 + 4 ≤ 16` fails).
3. Consequently, `MirWpConverges writeU32SliceBody st0 post` AND
   `wpStateOk (ops := mirDetWpOps writeU32SliceBody) post st0` are uninhabited for
   EVERY `post`. -/
theorem canary3b_oobSlice_derefWrite_ub
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newVal : UInt32) :
    let m0 := mkCanaryCalleeMem initHdr initFlag initVal siblingVal
    let fatOob : Value := .aggregate 0 [.ptr ⟨3, 14⟩ 8, .scalar ⟨4, 8⟩]
    let st0 := Trusted.VerificationResult.initMachineStateWithMemoryAndCallees writeU32SliceBody
      [fatOob, .scalar ⟨newVal.toNat, 4⟩] m0 []
    (∃ st14,
      StepStageCut (mirDetStep writeU32SliceBody) 14 st0 st14 ∧
      stepMirFn writeU32SliceBody st14 = MirStepNode.fail .ub) ∧
    (∀ post, ¬ MirWpConverges writeU32SliceBody st0 post) ∧
    (∀ post, ¬ wpStateOk (ops := mirDetWpOps writeU32SliceBody) post st0) := by
  intro m0 fatOob st0
  have hCut14 :
      StepStageCut (mirDetStep writeU32SliceBody) 14 st0
        (writeU32Stmt14State fatOob newVal m0) :=
    writeU32Slice_entry_to_stmt14 fatOob newVal m0 rfl rfl rfl rfl
      (mkCanaryCalleeMem_borrows_flat initHdr initFlag initVal siblingVal)
  have hFail14 :
      stepMirFn writeU32SliceBody (writeU32Stmt14State fatOob newVal m0) =
        MirStepNode.fail .ub := by
    let buf16 : List UInt8 :=
      rawU32Codec.enc initHdr ++ rawPaddedPairCodec.enc (initFlag, initVal) ++
        rawU32Codec.enc siblingVal
    have hL1 := rawU32Codec.enc_length initHdr
    have hL2 := rawPaddedPairCodec.enc_length (initFlag, initVal)
    have hL3 := rawU32Codec.enc_length siblingVal
    have hBufLen : buf16.length = 16 := by simp [buf16, hL1, hL2, hL3]
    cases hCons : buf16 with
    | nil => rw [hCons] at hBufLen; cases hBufLen
    | cons b0 rest =>
      rw [hCons] at hBufLen
      let st14 := writeU32Stmt14State fatOob newVal m0
      let newElems : List Value :=
        [Value.scalar ⟨wrapScalarBits newVal.toNat (scalarModulus 1), 1⟩,
         Value.scalar ⟨wrapScalarBits (wrapScalarBits (shiftRightUnsignedBits newVal.toNat 8) (scalarModulus 4)) (scalarModulus 1), 1⟩,
         Value.scalar ⟨wrapScalarBits (wrapScalarBits (shiftRightUnsignedBits newVal.toNat 16) (scalarModulus 4)) (scalarModulus 1), 1⟩,
         Value.scalar ⟨wrapScalarBits (wrapScalarBits (shiftRightUnsignedBits newVal.toNat 24) (scalarModulus 4)) (scalarModulus 1), 1⟩]
      have hNewLen : newElems.length = 4 := rfl
      have hOobWrite :
          writeSliceFatPtrTargetValue st14.frame.locals
            (.aggregate 0 (u8BytesToValues (b0 :: rest))) []
            ⟨3, 14⟩ 8 ⟨4, 8⟩ [] (.aggregate 0 newElems) = .ub :=
        writeSliceFatPtr_u8_oob st14.frame.locals b0 rest newElems 3 14 (by omega)
      change (match writeSliceFatPtrTargetValue st14.frame.locals
          (.aggregate 0 (u8BytesToValues buf16)) []
          ⟨3, 14⟩ 8 ⟨4, 8⟩ [] (.aggregate 0 newElems) with
        | .ok updated =>
          match Trusted.Sequence.set? m0.callerLocals 12 (.init updated) with
          | some cl' =>
            match derefWriteTreeUB st14.frame.locals m0.borrows (pl 1 [.deref]) with
            | true => MirStepNode.fail .ub
            | false =>
              MirStepNode.step { st14 with
                frame := { st14.frame with stmtIdx := 15 }
                memory := { m0 with
                  callerLocals := cl'
                  borrows := invalidateDerefWriteBorrows st14.frame.locals m0.borrows
                    (pl 1 [.deref]) [] m0.callerLocals } }
          | none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported) = MirStepNode.fail .ub
      rw [hCons, hOobWrite]
  have hMirFault :
      Anneal.PureMirExec.mirStep writeU32SliceBody (writeU32Stmt14State fatOob newVal m0) =
        .fault := by
    unfold Anneal.PureMirExec.mirStep
    rw [hFail14]; rfl
  exact ⟨⟨writeU32Stmt14State fatOob newVal m0, hCut14, hFail14⟩,
    fun post => not_mirWpConverges_of_stepStageCut_fault hCut14 hFail14 post,
    fun post => not_wpStateOk_of_stepStageCut_fault hCut14 hMirFault post⟩

/-- Raw caller-frame framing for any summary executed through
`sliceCallByteStoreOps`: every caller-local slot other than the lens target is
bit-for-bit unchanged. Unlike lens-level `get` framing (which only observes
regions covered by a live `.unique` borrow), this also covers frozen-borrow
slots such as `callerLocals[13]` and non-`[u8]` slots. -/
private theorem sliceCall_execMutSummary_other_local {Arg Ret : Type}
    {sum : MutSummary UInt8 Arg Ret} {L : ByteSubLens SliceCallAddr} {m m' : Memory}
    {arg : Arg} {ret : Ret} (h : execMutSummary sum L m arg = some (m', ret))
    {j : Nat} (hj : j ≠ L.addr.localIdx) :
    listGet? m'.callerLocals j = listGet? m.callerLocals j := by
  rcases execMutSummary_inv h with ⟨_, _, new, _, _, hSet⟩
  unfold ByteSubLens.set at hSet
  split at hSet
  · cases hSet
  · change (match sliceCallAbiReady m L.addr L.offset new.length with
      | false => none
      | true => memCallerByteStoreOps.writeBytes? m ⟨L.addr.localIdx⟩ L.offset new) =
        some m' at hSet
    split at hSet
    · cases hSet
    · exact memCaller_writeBytes_listGet?_ne hSet hj

/-- Raw intra-local AND inter-local byte-range framing for any summary executed
through `sliceCallByteStoreOps`: every disjoint `ByteSubLens CallerLocalAddr` on
raw `memCallerByteStoreOps` — including unborrowed or frozen-borrowed byte
windows inside the SAME caller local `L.addr.localIdx` — is bit-for-bit
unchanged. -/
private theorem sliceCall_execMutSummary_raw_disjoint {Arg Ret : Type}
    {sum : MutSummary UInt8 Arg Ret} {L : ByteSubLens SliceCallAddr} {m m' : Memory}
    {arg : Arg} {ret : Ret} (h : execMutSummary sum L m arg = some (m', ret))
    {other : ByteSubLens CallerLocalAddr}
    (hDisj : ByteSubLens.Disjoint Memory ⟨⟨L.addr.localIdx⟩, L.offset, L.len⟩ other) :
    other.get (ops := memCallerByteStoreOps) m' = other.get (ops := memCallerByteStoreOps) m := by
  rcases execMutSummary_inv h with ⟨_, _, new, _, _, hSet⟩
  unfold ByteSubLens.set at hSet
  split at hSet
  · cases hSet
  · rename_i hTrue
    change (match sliceCallAbiReady m L.addr L.offset new.length with
      | false => none
      | true => memCallerByteStoreOps.writeBytes? m ⟨L.addr.localIdx⟩ L.offset new) =
      some m' at hSet
    split at hSet
    · cases hSet
    · have hRawSet :
          (⟨⟨L.addr.localIdx⟩, L.offset, L.len⟩ : ByteSubLens CallerLocalAddr).set
            (ops := memCallerByteStoreOps) m new = some m' := by
        unfold ByteSubLens.set
        split
        · rename_i hFalse
          change (Nat.blt 0 L.len && new.length.beq L.len) = false at hFalse
          rw [hTrue] at hFalse
          cases hFalse
        · exact hSet
      exact ByteSubLens.get_set_disjoint (ops := memCallerByteStoreOps) hDisj hRawSet

/-- **Trusted `StatefulClaim` for real mutating callee `writeU32SliceBody`**,
requiring a live covering `.unique` borrow on any valid `ByteSubLens SliceCallAddr`
and guaranteeing exact return value, exact mutated `u32` bytes, raw intra-local
and inter-local byte-range framing (covering even unborrowed or frozen bytes
inside `L.addr.localIdx`), whole-slot framing of all other caller locals, and
ABI-ready disjoint-lens framing. -/
def writeU32SliceStatefulClaim : StatefulClaim where
  body := writeU32SliceBody
  callees := []
  pre args mem :=
    ∃ (L : ByteSubLens SliceCallAddr) (e : BorrowEntry) (oldVal newVal : UInt32),
      findCoveringUniqueBorrow mem.borrows L.addr.localIdx L.offset L.len = some e ∧
      L.getVal rawU32Codec mem = some oldVal ∧
      args = [.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩],
              .scalar ⟨newVal.toNat, 4⟩]
  post args mem ret mem' :=
    ∃ (L : ByteSubLens SliceCallAddr) (e : BorrowEntry) (newVal : UInt32),
      args = [.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩],
              .scalar ⟨newVal.toNat, 4⟩] ∧
      findCoveringUniqueBorrow mem.borrows L.addr.localIdx L.offset L.len = some e ∧
      ret = .scalar ⟨newVal.toNat, 4⟩ ∧
      L.getVal rawU32Codec mem' = some newVal ∧
      (∀ other : ByteSubLens CallerLocalAddr,
        ByteSubLens.Disjoint Memory ⟨⟨L.addr.localIdx⟩, L.offset, L.len⟩ other →
        other.get (ops := memCallerByteStoreOps) mem' =
          other.get (ops := memCallerByteStoreOps) mem) ∧
      (∀ j, j ≠ L.addr.localIdx → listGet? mem'.callerLocals j = listGet? mem.callerLocals j) ∧
      (∀ other : ByteSubLens SliceCallAddr, ByteSubLens.Disjoint Memory L other →
        other.get mem' = other.get mem) ∧
      mem'.borrows = mem.borrows ∧
      mem'.globals = mem.globals

private theorem ofU32Value_inv {rv : Value} {v : UInt32}
    (h : ofU32Value rv = some v) : rv = .scalar ⟨v.toNat, 4⟩ := by
  cases rv with
  | scalar sc =>
    cases sc with
    | mk bits sz =>
      cases sz with
      | zero => cases h
      | succ s1 =>
        cases s1 with
        | zero => cases h
        | succ s2 =>
          cases s2 with
          | zero => cases h
          | succ s3 =>
            cases s3 with
            | zero => cases h
            | succ s4 =>
              cases s4 with
              | succ _ => cases h
              | zero =>
                change (if bits < 2 ^ 32 then some (UInt32.ofNat bits) else none) = some v at h
                split at h
                · rename_i hLt
                  injection h with hEq
                  subst hEq
                  have hBits : (UInt32.ofNat bits).toNat = bits := by
                    simp [Nat.mod_eq_of_lt hLt]
                  rw [hBits]
                · cases h
  | _ => cases h

/-- **Trusted `StatefulVerificationResult` for real `writeU32SliceBody`**,
discharged directly from the sealed `@[irreducible] MutSummaryOutcomeCut` via
`V2026Bridge.verifyStatefulMirNoPanic_of_mutSummaryOutcomeCut` (zero re-stepping!). -/
theorem canary3b_writeU32Slice_statefulVerificationResult :
    StatefulVerificationResult writeU32SliceStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_mutSummaryOutcomeCut writeU32SliceStatefulClaim
    writeU32Slice_mutSummaryOutcomeCut ?_
  rintro args mem ⟨L, e, oldVal, newVal, hFind, hGet, hArgs⟩
  subst hArgs
  rcases execMutSummary_ofSliceCodec_of (sc := rawU32Codec)
      (fn := fun _ arg => match arg with | SliceCalleeArg.u32Arg v => some (v, v) | _ => none)
      (arg := SliceCalleeArg.u32Arg newVal)
      hGet (v' := newVal) (ret := newVal) rfl with ⟨m', hExec, _, hPostVal⟩
  refine ⟨L, .u32Arg newVal, m', newVal, ?_, hExec, ?_⟩
  · unfold writeU32Entry; rw [hFind]; rfl
  · intro rv hOfVal hFrame
    exact ⟨L, e, newVal, rfl, hFind, ofU32Value_inv hOfVal, hPostVal,
      fun _ hDisj => sliceCall_execMutSummary_raw_disjoint hExec hDisj,
      fun _ hj => sliceCall_execMutSummary_other_local hExec hj, hFrame,
      execMutSummary_preserves sliceCall_writePreserves_borrows hExec,
      execMutSummary_preserves sliceCall_writePreserves_globals hExec⟩

/-- Non-vacuity of `writeU32SliceStatefulClaim.pre`: the live canary memory
satisfies it for every symbolic buffer content and new value (`tag 1`, `[0..4)`),
so `canary3b_writeU32Slice_statefulVerificationResult` is not vacuous. -/
theorem canary3b_writeU32SliceStatefulClaim_pre_satisfiable
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal newVal : UInt32) :
    writeU32SliceStatefulClaim.pre
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨4, 8⟩], .scalar ⟨newVal.toNat, 4⟩]
      (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) :=
  ⟨calleeHdrLens,
    { tag := 1, targetLocal := 12, targetProjection := [], perm := .unique,
      rangeOffset := 0, rangeLen := 4, targetFrameDepth := 0 },
    initHdr, newVal, rfl, mkCanaryCalleeMem_hdr_getVal initHdr initFlag initVal siblingVal, rfl⟩

/-- **Trusted `StatefulClaim` for real mutating callee `writePaddedPairSliceBody`**,
with full raw intra-local and inter-local byte framing plus whole-slot and
ABI-ready disjoint-lens framing. -/
def writePaddedPairSliceStatefulClaim : StatefulClaim where
  body := writePaddedPairSliceBody
  callees := []
  pre args mem :=
    ∃ (L : ByteSubLens SliceCallAddr) (e : BorrowEntry) (oldPair : Bool × UInt32)
        (newFlag : Bool) (newVal : UInt32),
      findCoveringUniqueBorrow mem.borrows L.addr.localIdx L.offset L.len = some e ∧
      L.getVal rawPaddedPairCodec mem = some oldPair ∧
      args = [.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩],
              boolScalar newFlag, .scalar ⟨newVal.toNat, 4⟩]
  post args mem ret mem' :=
    ∃ (L : ByteSubLens SliceCallAddr) (e : BorrowEntry) (newFlag : Bool) (newVal : UInt32),
      args = [.aggregate 0 [.ptr ⟨e.tag, L.offset⟩ 8, .scalar ⟨L.len, 8⟩],
              boolScalar newFlag, .scalar ⟨newVal.toNat, 4⟩] ∧
      findCoveringUniqueBorrow mem.borrows L.addr.localIdx L.offset L.len = some e ∧
      ret = .scalar ⟨newVal.toNat, 4⟩ ∧
      L.getVal rawPaddedPairCodec mem' = some (newFlag, newVal) ∧
      (∀ other : ByteSubLens CallerLocalAddr,
        ByteSubLens.Disjoint Memory ⟨⟨L.addr.localIdx⟩, L.offset, L.len⟩ other →
        other.get (ops := memCallerByteStoreOps) mem' =
          other.get (ops := memCallerByteStoreOps) mem) ∧
      (∀ j, j ≠ L.addr.localIdx → listGet? mem'.callerLocals j = listGet? mem.callerLocals j) ∧
      (∀ other : ByteSubLens SliceCallAddr, ByteSubLens.Disjoint Memory L other →
        other.get mem' = other.get mem) ∧
      mem'.borrows = mem.borrows ∧
      mem'.globals = mem.globals

/-- **Trusted `StatefulVerificationResult` for real `writePaddedPairSliceBody`**,
discharged directly from `writePaddedPairSlice_mutSummaryOutcomeCut` via
`V2026Bridge.verifyStatefulMirNoPanic_of_mutSummaryOutcomeCut` (zero re-stepping!). -/
theorem canary3b_writePaddedPairSlice_statefulVerificationResult :
    StatefulVerificationResult writePaddedPairSliceStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_mutSummaryOutcomeCut writePaddedPairSliceStatefulClaim
    writePaddedPairSlice_mutSummaryOutcomeCut ?_
  rintro args mem ⟨L, e, oldPair, newFlag, newVal, hFind, hGet, hArgs⟩
  subst hArgs
  rcases execMutSummary_ofSliceCodec_of (sc := rawPaddedPairCodec)
      (fn := fun _ arg => match arg with | SliceCalleeArg.paddedPairArg b v => some ((b, v), v) | _ => none)
      (arg := SliceCalleeArg.paddedPairArg newFlag newVal)
      hGet (v' := (newFlag, newVal)) (ret := newVal) rfl with ⟨m', hExec, _, hPostVal⟩
  refine ⟨L, .paddedPairArg newFlag newVal, m', newVal, ?_, hExec, ?_⟩
  · unfold writePaddedPairEntry; rw [hFind]; rfl
  · intro rv hOfVal hFrame
    exact ⟨L, e, newFlag, newVal, rfl, hFind, ofU32Value_inv hOfVal, hPostVal,
      fun _ hDisj => sliceCall_execMutSummary_raw_disjoint hExec hDisj,
      fun _ hj => sliceCall_execMutSummary_other_local hExec hj, hFrame,
      execMutSummary_preserves sliceCall_writePreserves_borrows hExec,
      execMutSummary_preserves sliceCall_writePreserves_globals hExec⟩

/-- Non-vacuity of `writePaddedPairSliceStatefulClaim.pre` on the live canary
memory (`tag 2`, `[4..12)`). -/
theorem canary3b_writePaddedPairSliceStatefulClaim_pre_satisfiable
    (initHdr : UInt32) (initFlag : Bool) (initVal siblingVal : UInt32)
    (newFlag : Bool) (newVal : UInt32) :
    writePaddedPairSliceStatefulClaim.pre
      [.aggregate 0 [.ptr ⟨2, 4⟩ 8, .scalar ⟨8, 8⟩], boolScalar newFlag,
        .scalar ⟨newVal.toNat, 4⟩]
      (mkCanaryCalleeMem initHdr initFlag initVal siblingVal) :=
  ⟨calleePayLens,
    { tag := 2, targetLocal := 12, targetProjection := [], perm := .unique,
      rangeOffset := 4, rangeLen := 8, targetFrameDepth := 0 },
    (initFlag, initVal), newFlag, newVal, rfl,
    mkCanaryCalleeMem_pay_getVal initHdr initFlag initVal siblingVal, rfl⟩

/-! ## 4. Kernel Axiom Guardrails (`#guard_msgs` + `#print axioms`) -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_mirWpConverges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_mirWpConverges

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_dwp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_dwp

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_verificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_verificationResult

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_totalVerificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_totalVerificationResult

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1b_findTarget_mirWpConverges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1b_findTarget_mirWpConverges

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1b_findTarget_verificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1b_findTarget_verificationResult

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1c_countUp_mirWpConverges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary1c_countUp_mirWpConverges

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_blockTree_lookup_all' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary2_blockTree_lookup_all

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_mirWpConverges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary2_diamond_mirWpConverges

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_pureLift_stepPath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary2_diamond_pureLift_stepPath

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_mirOperationalAdapter_executesTo' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary2_diamond_mirOperationalAdapter_executesTo

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_verificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary2_diamond_verificationResult

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3a_globalAlloc_aligned_chain_and_framing' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3a_globalAlloc_aligned_chain_and_framing

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3a_byteMem_typedAt_and_mirTypedByteCodec' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3a_byteMem_typedAt_and_mirTypedByteCodec

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.writeU32Slice_mutSummaryOutcomeCut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms writeU32Slice_mutSummaryOutcomeCut

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.writePaddedPairSlice_mutSummaryOutcomeCut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms writePaddedPairSlice_mutSummaryOutcomeCut

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_realCallees_execMutSummaryChain_and_framing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_realCallees_execMutSummaryChain_and_framing

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_panickingCallee_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary3b_panickingCallee_rejected

/-! ### Additional guards: per-stage cuts, `BlockTree` validity, raw `wpStateOk`
loop lemmas, and the debug-mode checked-arithmetic Canary 1D. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_wpStateOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_wpStateOk

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1b_findTarget_wpStateOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1b_findTarget_wpStateOk

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1c_countUp_wpStateOk' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canary1c_countUp_wpStateOk

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_countDownChecked_wpStateOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1d_countDownChecked_wpStateOk

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_countDownChecked_mirWpConverges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1d_countDownChecked_mirWpConverges

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_countDownChecked_verificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1d_countDownChecked_verificationResult

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_overflowAssert_live' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary1d_overflowAssert_live

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.diamondBlockTree_valid' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms diamondBlockTree_valid

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.diamondChunk8Tree_valid' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms diamondChunk8Tree_valid

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_stage1_stepStageCut' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canary2_stage1_stepStageCut

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_stage1_within' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canary2_stage1_within

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_stage2_stepStageCut' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canary2_stage2_stepStageCut

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_stage2_within' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canary2_stage2_within

/-! ### Pass A1 guards: Canary 1D termination + add-overflow liveness, Canary 2
`StageCut` + `PureLift` composition, and Canary 3B alignment / fail-closed /
live UB / `StatefulVerificationResult` certificates. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_countDownChecked_totalVerificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1d_countDownChecked_totalVerificationResult

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1d_addOverflowAssert_live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary1d_addOverflowAssert_live

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_stageCut_then_pureLift' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary2_diamond_stageCut_then_pureLift

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.sliceCall_writePreserves_alignedAt' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms sliceCall_writePreserves_alignedAt

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_sliceCall_aligned_and_failClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_sliceCall_aligned_and_failClosed

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_frozenBorrow_derefWrite_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary3b_frozenBorrow_derefWrite_ub

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_oobSlice_derefWrite_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary3b_oobSlice_derefWrite_ub

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_writeU32Slice_statefulVerificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_writeU32Slice_statefulVerificationResult

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_writePaddedPairSlice_statefulVerificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_writePaddedPairSlice_statefulVerificationResult

/-! ### Pass B2 guards: `StatefulClaim` precondition non-vacuity. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_writeU32SliceStatefulClaim_pre_satisfiable' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_writeU32SliceStatefulClaim_pre_satisfiable

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3b_writePaddedPairSliceStatefulClaim_pre_satisfiable' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3b_writePaddedPairSliceStatefulClaim_pre_satisfiable

/-! ### Pass A2 guards: Canary 1B termination and Canary 2 full 2-stage
`PureLift` soundness via `mir_pure_lift_sound_of_stepStageCut`. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1b_findTarget_totalVerificationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1b_findTarget_totalVerificationResult

/-- info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_diamond_full_pureLift_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary2_diamond_full_pureLift_sound

/-! ### Pass B3 guards: provenance fail-closed edge. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3a_provenance_failClosed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary3a_provenance_failClosed

/-! ### Pass A3 guards: coalgebraic `Refines` + `DWLP`, `ValidChunk8BlockTree`
stage-cut, and `ByteMem` provenance non-laundering + `SliceTypedAt`. -/

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary1a_countDown_coalWp_refines_dwp_dwlp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary1a_countDown_coalWp_refines_dwp_dwlp

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary2_stage1_chunk8BlockTree_stepStageCut' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary2_stage1_chunk8BlockTree_stepStageCut

/--
info: 'Anneal.ParametricLoopInvAndSubLensTests.canary3a_byteMem_provenance_and_sliceTypedAt' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms canary3a_byteMem_provenance_and_sliceTypedAt

end Anneal.ParametricLoopInvAndSubLensTests
