-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.MirFuelFree

set_option maxRecDepth 2048
namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
# Tier 1 Pure MIR Execution & Alias Erasure (`Anneal.PureMirExec`)

This module implements Tier 1 local-value / alias erasure for pure Rust MIR
functions (`FF-2.1`), modeled on `Py/PureExec.lean`:

1. **Alias-Erased State (`PureState`) & `SlotState`**:
   Erases the 10-field `Memory` record (`nextAllocId`, `globals`, `borrows`,
   `nextTag`, `callees`, `callStack`, `activeCallee`, `activeProtectors`,
   `nextProtector`, `callerLocals`), retaining only the active basic-block
   index `bb : BasicBlockIdx`, statement index `stmtIdx : Nat`, and local value
   environment `env : List SlotState` where every initialized slot holds a pure
   `Value` (`SlotState.val v`).
2. **Frame Simulation (`MirFrameSim`)**:
   Relates `ps : PureState` to `ms : MachineState` at an arbitrary initial
   memory `mem₀ : Memory`, asserting exact agreement on `bb`, `stmtIdx`, and
   `env` together with `ms.memory = mem₀` (all 10 fields of `Memory`
   definitionally equal to `mem₀`, including when `mem₀.callees` is populated
   by `initMachineStateWithCallees` or `initMachineStateWithMemoryAndCallees`).
3. **Computable Syntactic Purity Checker (`checkPureMir : CapturedMir → Bool`)**:
   Verifies in $O(|\text{MIR}|)$ time (discharged by `decide` or `rfl`) that no
   statement, rvalue, operand, or terminator in `body` creates a local address
   (`Rvalue.ref`, `Rvalue.rawPtr`), dereferences a pointer
   (`ProjectionElem.deref`), reads indirect global memory, or mutates heap/borrow
   state, while permitting arbitrary value projections (`.field`, `.downcast`,
   `.index`, `.constantIndex`, `.subslice`, `.opaqueCast`), local statements
   (`storageLive`, `storageDead`, `assign`, `setDiscriminant`, `nop`, `deinit`,
   `placeMention`), and control-flow terminators (`return_`, `goto`,
   `switchInt`, `assert`, `drop`, `unreachable`).
4. **Once-and-for-All Alias-Erasure Soundness (`mirWpConverges_of_pureExec`)**:
   Proves that whenever `checkPureMir body = true` and
   `PureMirConverges body (initPureState body args) post`, the full stateful
   interaction tree converges (`MirWpConverges`) from
   `initMachineStateWithMemory body args mem₀` to
   `mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)` without ever
   destructuring the 10-field `Memory` record in user proofs.
-/

/-! ## 1. Alias-Erased State (`SlotState`, `PureState`) & Simulation (`MirFrameSim`) -/

/--
Alias-erased local slot state in `PureState` (`LocalSlot`: `.uninit`, `.init v`,
`.dead`), where every initialized slot holds a pure `Value` directly (never a
heap or borrow allocation address).
-/
abbrev SlotState : Type := LocalSlot

/-- Initialized value slot constructor (`LocalSlot.init`). -/
abbrev SlotState.val : Value → SlotState := LocalSlot.init

/-- Uninitialized slot constructor (`LocalSlot.uninit`). -/
abbrev SlotState.uninit : SlotState := LocalSlot.uninit

/-- Dead storage slot constructor (`LocalSlot.dead`). -/
abbrev SlotState.dead : SlotState := LocalSlot.dead

/-- Basic-block index accessor on `MachineState` (`ms.frame.blockIdx`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.bb
    (ms : MachineState) : BasicBlockIdx :=
  ms.frame.blockIdx

/-- Statement index accessor on `MachineState` (`ms.frame.stmtIdx`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.stmtIdx
    (ms : MachineState) : Nat :=
  ms.frame.stmtIdx

/-- Local slot environment accessor on `MachineState` (`ms.frame.locals`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.locals
    (ms : MachineState) : List LocalSlot :=
  ms.frame.locals

/--
Alias-erased execution state for Tier 1 pure MIR functions (`PureState`),
containing only the active basic-block index `bb`, statement index `stmtIdx`,
and local slot environment `env`.
-/
structure PureState : Type where
  /-- Active basic block index (`0` at function entry). -/
  bb : BasicBlockIdx
  /-- Active statement index within `bb` (`0` at basic block entry). -/
  stmtIdx : Nat := 0
  /-- Local slot environment (`_0` return slot followed by arguments and locals). -/
  env : List SlotState

/--
Default empty `Memory` state used as the canonical erased reference memory for
`PureState` evaluation (`emptyMemory`).
-/
abbrev dummyMem : Memory := emptyMemory

/--
Initialize `PureState` for `body` with argument values `args` at basic block `0`
and statement `0`.
-/
def initPureState (body : CapturedMir) (args : List Value) : PureState :=
  { bb := 0, stmtIdx := 0, env := initLocals body args }

/--
Embed `ps : PureState` into a full `MachineState` with memory `mem` (defaulting
to `emptyMemory`).
-/
def PureState.toMachineState
    (ps : PureState) (mem : Memory := emptyMemory) : MachineState :=
  { frame := { blockIdx := ps.bb, stmtIdx := ps.stmtIdx, locals := ps.env }
    memory := mem }

/--
Project the stack frame of `ms : MachineState` to `PureState`, erasing
`ms.memory`.
-/
def PureState.ofMachineState (ms : MachineState) : PureState :=
  { bb := ms.frame.blockIdx, stmtIdx := ms.frame.stmtIdx, env := ms.frame.locals }

@[simp]
theorem PureState.ofMachineState_toMachineState
    (ps : PureState) (mem : Memory) :
    PureState.ofMachineState (ps.toMachineState mem) = ps :=
  rfl

@[simp]
theorem PureState.toMachineState_ofMachineState
    (ms : MachineState) (mem : Memory) :
    (PureState.ofMachineState ms).toMachineState mem =
      { ms with memory := mem } :=
  rfl

@[simp]
theorem initPureState_toMachineState
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    (initPureState body args).toMachineState mem =
      initMachineStateWithMemory body args mem :=
  rfl

@[simp]
theorem initPureState_toMachineState_init
    (body : CapturedMir) (args : List Value) :
    (initPureState body args).toMachineState
        (initMachineState body args).memory =
      initMachineState body args :=
  rfl

@[simp]
theorem initPureState_toMachineState_withCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    (initPureState body args).toMachineState
        (initMachineStateWithCallees body args callees).memory =
      initMachineStateWithCallees body args callees :=
  rfl

@[simp]
theorem initPureState_toMachineState_withMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) :
    (initPureState body args).toMachineState
        (Memory.withDefaultCallees mem callees) =
      initMachineStateWithMemoryAndCallees body args mem callees :=
  rfl

/--
Frame simulation relation between alias-erased `ps : PureState` and full
`ms : MachineState` at initial memory `mem₀ : Memory`.

Asserts `ms.bb = ps.bb`, `ms.stmtIdx = ps.stmtIdx`, exact slot-by-slot local
environment correspondence (`ms.locals = ps.env`), and `ms.memory = mem₀` (all
10 fields of `Memory` definitionally equal to `mem₀`, including when
`mem₀.callees` is populated by `initMachineStateWithCallees` or
`initMachineStateWithMemoryAndCallees`).
-/
def MirFrameSim
    (_body : CapturedMir)
    (mem₀ : Memory)
    (ps : PureState)
    (ms : MachineState) : Prop :=
  ms.frame.blockIdx = ps.bb ∧
  ms.frame.stmtIdx = ps.stmtIdx ∧
  ms.frame.locals = ps.env ∧
  ms.memory = mem₀

/--
`MirFrameSim body mem₀ ps ms` holds if and only if `ms` is definitionally
`ps.toMachineState mem₀`.
-/
theorem mirFrameSim_iff_eq_toMachineState
    (body : CapturedMir) (mem₀ : Memory) (ps : PureState) (ms : MachineState) :
    MirFrameSim body mem₀ ps ms ↔ ms = ps.toMachineState mem₀ := by
  rcases ms with ⟨⟨bb, stmtIdx, locals⟩, memory⟩
  rcases ps with ⟨pbb, pstmtIdx, penv⟩
  simp [MirFrameSim, PureState.toMachineState, and_assoc]

@[simp]
theorem mirFrameSim_toMachineState
    (body : CapturedMir) (mem₀ : Memory) (ps : PureState) :
    MirFrameSim body mem₀ ps (ps.toMachineState mem₀) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithMemory body args mem₀` for arbitrary `mem₀ : Memory`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithMemory
    (body : CapturedMir) (args : List Value) (mem₀ : Memory) :
    MirFrameSim body mem₀
      (initPureState body args)
      (initMachineStateWithMemory body args mem₀) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineState body args`.
-/
@[simp]
theorem mirFrameSim_initMachineState
    (body : CapturedMir) (args : List Value) :
    MirFrameSim body (initMachineState body args).memory
      (initPureState body args)
      (initMachineState body args) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithCallees body args callees`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    MirFrameSim body (initMachineStateWithCallees body args callees).memory
      (initPureState body args)
      (initMachineStateWithCallees body args callees) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithMemoryAndCallees body args mem₀ callees`, preserving
`Memory.withDefaultCallees mem₀ callees`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem₀ : Memory)
    (callees : List CapturedMir) :
    MirFrameSim body (Memory.withDefaultCallees mem₀ callees)
      (initPureState body args)
      (initMachineStateWithMemoryAndCallees body args mem₀ callees) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Extract `ms.memory = mem₀` from `MirFrameSim`. -/
theorem MirFrameSim.memory_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.memory = mem₀ :=
  h.2.2.2

/-- Extract `ms.bb = ps.bb` from `MirFrameSim`. -/
theorem MirFrameSim.bb_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.bb = ps.bb :=
  h.1

/-- Extract `ms.stmtIdx = ps.stmtIdx` from `MirFrameSim`. -/
theorem MirFrameSim.stmtIdx_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.stmtIdx = ps.stmtIdx :=
  h.2.1

/-- Extract `ms.locals = ps.env` from `MirFrameSim`. -/
theorem MirFrameSim.locals_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.locals = ps.env :=
  h.2.2.1

/-! ## 2. Computable Syntactic Purity Checker (`checkPureMir`) -/

/--
Syntactic purity check on a `ConstValue`: accepts inline constants that do not
inspect global memory allocations (`mem.globals`), while rejecting `.indirect`
and pointer-backed `.slice` constants.
-/
def isPureConstValue : ConstValue → Bool
  | .zeroSized => true
  | .scalar _ => true
  | .slice (.int _) _ => true
  | .slice (.ptr _ _) _ => false
  | .indirect _ _ => false
  | .unevaluated _ => true

/--
Syntactic purity check on a `ProjectionElem`: allows arbitrary value projections
(`.field`, `.downcast`, `.index`, `.constantIndex`, `.subslice`, `.opaqueCast`)
while rejecting pointer dereferences (`.deref`).
-/
def isPureProjElem : ProjectionElem → Bool
  | .deref => false
  | .field _ _ => true
  | .index _ => true
  | .constantIndex .. => true
  | .subslice .. => true
  | .downcast _ _ => true
  | .opaqueCast _ => true
  | .unwrapUnsafeBinder _ => false

/-- Syntactic purity check on a `Place`: every projection element is pure. -/
def isPurePlace (p : Place) : Bool :=
  p.projection.all isPureProjElem

/--
Syntactic purity check on an `Operand`: `.copy` and `.move` access pure places,
and `.constant` carries a pure `ConstValue`.
-/
def isPureOperand : Operand → Bool
  | .copy p => isPurePlace p
  | .move p => isPurePlace p
  | .constant c => isPureConstValue c.val

/--
Syntactic purity check on an `Rvalue`: allows value operations on pure places
and operands while rejecting address/borrow creation (`.ref`, `.rawPtr`,
`.threadLocalRef`, `.shallowInitBox`).
-/
def isPureRvalue : Rvalue → Bool
  | .use op => isPureOperand op
  | .repeat op _ => isPureOperand op
  | .ref .. => false
  | .rawPtr .. => false
  | .threadLocalRef _ => false
  | .len p => isPurePlace p
  | .cast _ op _ => isPureOperand op
  | .binaryOp _ lhs rhs => isPureOperand lhs && isPureOperand rhs
  | .nullaryOp _ _ => true
  | .unaryOp _ op => isPureOperand op
  | .discriminant p => isPurePlace p
  | .aggregate _ ops => ops.all isPureOperand
  | .shallowInitBox _ _ => false
  | .copyForDeref p => isPurePlace p
  | .wrapUnsafeBinder op _ => isPureOperand op

/--
Syntactic purity check on a `StatementKind`: allows `.assign`,
`.setDiscriminant`, `.storageLive`, `.storageDead`, `.nop`, `.coverage`,
`.constEvalCounter`, `.placeMention`, `.deinit`, and `.intrinsic (.assume op)`
when all referenced places/operands are pure.
-/
def isPureStatement : StatementKind → Bool
  | .assign p r => isPurePlace p && isPureRvalue r
  | .setDiscriminant p _ => isPurePlace p
  | .storageLive _ => true
  | .storageDead _ => true
  | .nop => true
  | .coverage => true
  | .constEvalCounter => true
  | .placeMention p => isPurePlace p
  | .deinit p => isPurePlace p
  | .intrinsic (.assume op) => isPureOperand op
  | _ => false

/--
Syntactic purity check on a `TerminatorKind`: allows `.goto`, `.switchInt`,
`.return_`, `.assert`, `.drop`, and `.unreachable` when all referenced
places/operands are pure.
-/
def isPureTerminator : TerminatorKind → Bool
  | .goto _ => true
  | .switchInt discr _ => isPureOperand discr
  | .return_ => true
  | .assert cond _ _ _ => isPureOperand cond
  | .drop p _ _ => isPurePlace p
  | .unreachable => true
  | .unwindResume => true
  | .unwindTerminate => true
  | .inlineAsm .. => false
  | _ => false

/--
Computable $O(|\text{MIR}|)$ syntactic purity checker on a `CapturedMir` body,
discharged by `decide` or `rfl`.
-/
def checkPureMir (body : CapturedMir) : Bool :=
  body.basicBlocks.all (fun block =>
    block.statements.all (fun stmt => isPureStatement stmt.kind) &&
    isPureTerminator block.terminator.kind)

/-! ## 3. Pure Memory-Independence & Step Simulation Lemmas -/

/-- Look up an element of `xs` via `Trusted.Sequence.get?` preserves `List.all`. -/
theorem list_all_of_get?
    {α : Type} {p : α → Bool} {xs : List α} {idx : Nat} {x : α}
    (h_all : xs.all p = true)
    (h_get : get? xs idx = some x) :
    p x = true := by
  induction xs generalizing idx with
  | nil => cases h_get
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h_all
    cases idx with
    | zero =>
      cases h_get
      exact h_all.1
    | succ idx' =>
      exact ih h_all.2 h_get

/--
If `checkPureMir body = true`, every basic block in `body.basicBlocks` has pure
statements and a pure terminator.
-/
theorem checkPureMir_block
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h_pure : checkPureMir body = true)
    (h_bb : get? body.basicBlocks bbIdx = some bb) :
    bb.statements.all (fun stmt => isPureStatement stmt.kind) = true ∧
    isPureTerminator bb.terminator.kind = true := by
  have h := list_all_of_get? h_pure h_bb
  exact Bool.and_eq_true_iff.mp h

/--
Evaluating a pure `Operand` is completely independent of `borrows`, `globals`,
and `callerLocals`.
-/
theorem evalOperand_pure_eq
    (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (h_pure : isPureOperand op = true) :
    evalOperand locals op borrows globals layouts callerLocals =
      evalOperand locals op [] [] layouts [] := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val with
    | zeroSized => rfl
    | scalar sc => cases sc <;> rfl
    | slice sc lenMeta =>
      cases sc with
      | int _ => rfl
      | ptr _ _ => cases h_pure
    | indirect _ _ => cases h_pure
    | unevaluated _ => rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd tl =>
      simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
      cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd tl =>
      simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
      cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

/--
Evaluating a list of pure `Operand`s is completely independent of `borrows`,
`globals`, and `callerLocals`.
-/
theorem evalOperands_pure_eq
    (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (h_pure : ops.all isPureOperand = true) :
    evalOperands locals ops borrows globals layouts callerLocals =
      evalOperands locals ops [] [] layouts [] := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h_pure
    unfold evalOperands
    rw [evalOperand_pure_eq locals op borrows globals layouts callerLocals h_pure.1]
    cases evalOperand locals op [] [] layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [ih locals₁ h_pure.2]

/--
Writing to a pure `Place` via `writePlaceValue` is completely independent of
`borrows`.
-/
theorem writePlaceValue_pure_eq
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (dst : Place) (val : Value)
    (h_pure : isPurePlace dst = true) :
    writePlaceValue locals borrows dst val =
      writePlaceValue locals [] dst val := by
  rcases dst with ⟨loc, proj⟩
  cases proj with
  | nil => rfl
  | cons hd tl =>
    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

/-- Replace the `Memory` in an `RvalueEvalResult` with `mem`. -/
def RvalueEvalResult.withMem (mem : Memory) : RvalueEvalResult → RvalueEvalResult
  | .ok v locals' _ => .ok v locals' mem
  | .ub => .ub
  | .unsupported => .unsupported

@[simp]
theorem evalSignedDiv_eq_withMem
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals mem =
      RvalueEvalResult.withMem mem (evalSignedDiv a b sz locals emptyMemory) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz)) (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) <;> rfl

@[simp]
theorem evalSignedRem_eq_withMem
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals mem =
      RvalueEvalResult.withMem mem (evalSignedRem a b sz locals emptyMemory) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz)) (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalScalarBinOp_eq_withMem
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals mem isSigned =
      RvalueEvalResult.withMem mem
        (evalScalarBinOp op lhs rhs locals emptyMemory isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => rfl
  | false =>
    dsimp only
    cases op <;> dsimp only
    all_goals
      repeat' (first
        | rfl
        | exact evalSignedDiv_eq_withMem ..
        | exact evalSignedRem_eq_withMem ..
        | split)

theorem evalUnaryNot_eq_withMem
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals mem =
      RvalueEvalResult.withMem mem
        (evalUnaryNot sc optTy locals emptyMemory) := by
  unfold evalUnaryNot
  repeat' (first | rfl | split)

theorem evalByteCast_pure_eq_withMem
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureOperand op = true) :
    evalByteCast locals op targetTy mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalByteCast locals op targetTy emptyMemory localDecls layouts) := by
  unfold evalByteCast
  rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
  rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
  dsimp only
  try cases evalOperand locals op [] [] layouts []
  repeat' (first | rfl | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first | rfl | split)
  all_goals try rfl

/--
Evaluating a pure `Rvalue` at arbitrary `mem : Memory` produces the exact same
value and local-slot updates as evaluating at `emptyMemory`, leaving `mem`
completely unchanged.
-/
theorem evalRvalue_pure_eq_withMem
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureRvalue rv = true) :
    evalRvalue locals rv mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalRvalue locals rv emptyMemory localDecls layouts) := by
  cases rv with
  | use op =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] <;> rfl
  | «repeat» op count =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] <;> rfl
  | ref _ _ => cases h_pure
  | threadLocalRef _ => cases h_pure
  | rawPtr _ _ => cases h_pure
  | len p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals (.copy p) emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    repeat' (first | rfl | split)
  | cast ck op targetTy =>
    dsimp only [isPureRvalue] at h_pure
    cases ck with
    | transmute => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | subtype => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | _ =>
      dsimp only [evalRvalue]
      try rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      try cases evalOperand locals op [] [] layouts []
      repeat' (first | rfl | split)
      all_goals try dsimp (config := { zeta := true })
      repeat' (first | rfl | split)
      all_goals try rfl
  | binaryOp op lhs rhs =>
    simp only [isPureRvalue, Bool.and_eq_true] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals lhs mem.borrows mem.globals layouts mem.callerLocals h_pure.1]
    rw [evalOperand_pure_eq locals lhs emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure.1]
    cases evalOperand locals lhs [] [] layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      rw [evalOperand_pure_eq locals₁ rhs mem.borrows mem.globals layouts mem.callerLocals h_pure.2]
      rw [evalOperand_pure_eq locals₁ rhs emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure.2]
      cases evalOperand locals₁ rhs [] [] layouts [] with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhsSc =>
          cases rhsVal with
          | scalar rhsSc =>
            exact evalScalarBinOp_eq_withMem op lhsSc rhsSc locals₂ mem _
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar _ => cases op <;> rfl
          | _ => rfl
        | _ => rfl
  | nullaryOp _ _ => rfl
  | unaryOp uop op =>
    dsimp only [isPureRvalue] at h_pure
    cases uop with
    | not =>
      dsimp only [evalRvalue]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      cases evalOperand locals op [] [] layouts [] with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc => exact evalUnaryNot_eq_withMem sc _ locals' mem
        | _ => rfl
    | neg =>
      dsimp only [evalRvalue]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
    | ptrMetadata =>
      dsimp only [evalRvalue]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
  | discriminant p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals (.copy p) emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    repeat' (first | rfl | split)
  | aggregate kind ops =>
    dsimp only [isPureRvalue] at h_pure
    cases kind
    all_goals
      dsimp only [evalRvalue]
      try rw [evalOperands_pure_eq locals ops mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try rw [evalOperands_pure_eq locals ops emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
  | shallowInitBox _ _ => cases h_pure
  | copyForDeref p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals (.copy p) emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals (.copy p) [] [] layouts [] <;> rfl
  | wrapUnsafeBinder _ _ => rfl

/-- Replace the `Memory` in a normal `MirOutcome` with `mem`. -/
def MirOutcome.withMem (mem : Memory) : MirOutcome → MirOutcome
  | .normal retPair => .normal (retPair.1, mem)
  | .panic => .panic
  | .abort => .abort

/-- Replace the `Memory` in a `MirExecState` with `mem`. -/
def MirExecState.withMem (mem : Memory) : MirExecState → MirExecState
  | .running s => .running { s with memory := mem }
  | .halted out => .halted (MirOutcome.withMem mem out)
  | .faulted fk => .faulted fk

/--
Replace the `Memory` in a `MirStepNode` with `mem`, leaving `MirFailE` fault
nodes untouched so `MirStepNode.withMem mem (MirStepNode.fail fk)` is
definitionally equal (`rfl`) to `MirStepNode.fail fk`.
-/
def MirStepNode.withMem (mem : Memory) : MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.withMem mem out)
  | .tau st => .tau (MirExecState.withMem mem st)
  | .vis (.inl f) k => .vis (.inl f) k
  | .vis (.inr e) k => .vis (.inr e) (fun o => MirExecState.withMem mem (k o))

@[simp]
theorem MirStepNode.withMem_fail (mem : Memory) (fk : FailureKind) :
    MirStepNode.withMem mem (MirStepNode.fail fk) = MirStepNode.fail fk :=
  rfl

@[simp]
theorem MirStepNode.withMem_unsupported (mem : Memory) :
    MirStepNode.withMem mem MirStepNode.unsupported = MirStepNode.unsupported :=
  rfl

theorem memory_with_borrows_nil_eq {mem : Memory} (h : mem.borrows = []) :
    { mem with borrows := [] } = mem := by
  cases mem
  simp only at h
  subst h
  rfl

/--
Evaluating a pure `Statement` from `ps.toMachineState mem₀` under
`RootActiveMemory mem₀` produces the exact same transition as evaluating from
`ps.toMachineState emptyMemory` and restoring `mem₀`.
-/
theorem evalStmt_toMachineState_eq_withMem
    (ps : PureState) (mem₀ : Memory) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureStatement stmt.kind = true)
    (h_root : RootActiveMemory mem₀) :
    evalStmt (ps.toMachineState mem₀) stmt localDecls layouts =
      MirStepNode.withMem mem₀
        (evalStmt (ps.toMachineState emptyMemory) stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  rcases h_root with ⟨h_borrows, _, _, h_prot⟩
  cases kind with
  | nop => rfl
  | coverage => rfl
  | constEvalCounter => rfl
  | storageLive loc =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | storageDead loc =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | placeMention p =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | deinit p =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | intrinsic intr =>
    cases intr with
    | assume op =>
      dsimp only [isPureStatement] at h_pure
      unfold evalStmt
      dsimp only [PureState.toMachineState]
      rw [evalOperand_pure_eq ps.env op mem₀.borrows mem₀.globals layouts mem₀.callerLocals h_pure]
      rw [evalOperand_pure_eq ps.env op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
    | copyNonOverlapping _ _ _ => cases h_pure
  | retag _ _ => cases h_pure
  | backwardIncompatibleDropHint _ => cases h_pure
  | setDiscriminant p variantIdx =>
    dsimp only [isPureStatement] at h_pure
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    have h_op : isPureOperand (.copy p) = true := h_pure
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil =>
      dsimp only
      repeat' (first | rfl | split)
    | cons hd tl =>
      dsimp only
      rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
        mem₀.borrows mem₀.globals layouts mem₀.callerLocals h_op]
      rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
        emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_op]
      cases evalOperand ps.env (.copy { local_ := loc, projection := hd :: tl }) [] [] layouts [] with
      | ub => rfl
      | unsupported => rfl
      | ok v locals₁ =>
        cases v with
        | aggregate oldVar fields =>
          dsimp only
          rw [writePlaceValue_pure_eq locals₁ mem₀.borrows
            { local_ := loc, projection := hd :: tl }
            (.aggregate variantIdx fields) h_pure]
          rw [writePlaceValue_pure_eq locals₁ emptyMemory.borrows
            { local_ := loc, projection := hd :: tl }
            (.aggregate variantIdx fields) h_pure]
          cases writePlaceValue locals₁ []
            { local_ := loc, projection := hd :: tl }
            (.aggregate variantIdx fields) <;> rfl
        | _ => rfl
  | assign dst rv =>
    simp only [isPureStatement, Bool.and_eq_true] at h_pure
    rcases h_pure with ⟨h_dst, h_rv⟩
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    rw [evalRvalue_pure_eq_withMem ps.env rv mem₀ localDecls layouts h_rv]
    have h_emp := evalRvalue_pure_eq_withMem ps.env rv emptyMemory localDecls layouts h_rv
    cases h_res : evalRvalue ps.env rv emptyMemory localDecls layouts with
    | ub => rfl
    | unsupported => rfl
    | ok val locals₁ mem₁ =>
      have h_mem₁ : mem₁ = emptyMemory := by
        rw [h_res] at h_emp
        dsimp only [RvalueEvalResult.withMem] at h_emp
        injection h_emp
      subst h_mem₁
      dsimp only [RvalueEvalResult.withMem]
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        dsimp only
        cases get? locals₁ dstLoc with
        | none => rw [MirStepNode.withMem_fail]
        | some slot =>
          cases slot with
          | dead => rfl
          | uninit =>
            dsimp only
            cases set? locals₁ dstLoc (.init val) with
            | none => rw [MirStepNode.withMem_fail]
            | some locals₂ =>
              try rw [h_prot, h_borrows]
              try rfl
              dsimp only [emptyMemory, invalidateConflictingBorrows,
                MirStepNode.step, advanceStmt, MirStepNode.withMem,
                MirExecState.withMem]
              cases mem₀
              subst h_borrows
              subst h_prot
              rfl
          | init _ =>
            dsimp only
            cases set? locals₁ dstLoc (.init val) with
            | none => rw [MirStepNode.withMem_fail]
            | some locals₂ =>
              try rw [h_prot, h_borrows]
              try rfl
              dsimp only [emptyMemory, invalidateConflictingBorrows,
                MirStepNode.step, advanceStmt, MirStepNode.withMem,
                MirExecState.withMem]
              cases mem₀
              subst h_borrows
              subst h_prot
              rfl
      | cons hd tl =>
        simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_dst
        cases hd <;>
          try exact False.elim (Bool.false_ne_true h_dst.1)
        all_goals
          dsimp only
          cases get? locals₁ dstLoc with
          | none => rw [MirStepNode.withMem_fail]
          | some slot =>
            cases slot with
            | uninit => rfl
            | dead => rfl
            | init rootVal =>
              dsimp only
              cases writeProjectedValue locals₁ rootVal _ val with
              | ub => rfl
              | unsupported => rfl
              | ok rootVal' =>
                dsimp only
                cases set? locals₁ dstLoc (.init rootVal') with
                | none => rw [MirStepNode.withMem_fail]
                | some locals₂ =>
                  try rw [h_prot, h_borrows]
                  try rfl
                  dsimp only [emptyMemory, invalidateConflictingBorrowsAtProj,
                    MirStepNode.step, advanceStmt, MirStepNode.withMem,
                    MirExecState.withMem]
                  cases mem₀
                  subst h_borrows
                  subst h_prot
                  rfl

/--
Evaluating a pure `Terminator` from `ps.toMachineState mem₀` under
`RootActiveMemory mem₀` produces the exact same transition as evaluating from
`ps.toMachineState emptyMemory` and restoring `mem₀`.
-/
theorem evalTerminator_toMachineState_eq_withMem
    (ps : PureState) (mem₀ : Memory) (term : Terminator) (body : CapturedMir)
    (h_pure : isPureTerminator term.kind = true)
    (h_root : RootActiveMemory mem₀) :
    evalTerminator (ps.toMachineState mem₀) term (some body) =
      MirStepNode.withMem mem₀
        (evalTerminator (ps.toMachineState emptyMemory) term (some body)) := by
  rcases term with ⟨kind, span⟩
  rcases h_root with ⟨_, h_stack, _, _⟩
  cases kind with
  | goto target => rfl
  | unreachable => rfl
  | return_ =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    cases get? ps.env 0 with
    | none => rw [MirStepNode.withMem_fail]
    | some slot =>
      cases slot with
      | uninit => rfl
      | dead => rfl
      | init retVal =>
        dsimp only
        rw [h_stack]
        rfl
  | drop p target unwind =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | switchInt discr targets =>
    dsimp only [isPureTerminator] at h_pure
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [evalOperand_pure_eq ps.env discr mem₀.borrows mem₀.globals body.layouts mem₀.callerLocals h_pure]
    rw [evalOperand_pure_eq ps.env discr emptyMemory.borrows emptyMemory.globals body.layouts emptyMemory.callerLocals h_pure]
    cases evalOperand ps.env discr [] [] body.layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v <;> rfl
  | assert cond expected target unwind =>
    dsimp only [isPureTerminator] at h_pure
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [evalOperand_pure_eq ps.env cond mem₀.borrows mem₀.globals body.layouts mem₀.callerLocals h_pure]
    rw [evalOperand_pure_eq ps.env cond emptyMemory.borrows emptyMemory.globals body.layouts emptyMemory.callerLocals h_pure]
    cases evalOperand ps.env cond [] [] body.layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v with
      | scalar sc =>
        dsimp only
        cases Nat.beq sc.bits (match expected with | true => 1 | false => 0) with
        | true => rfl
        | false =>
          dsimp only [applyUnwindAction]
          cases unwind <;> rfl
      | _ => rfl
  | call _ _ _ _ _ => cases h_pure
  | tailCall _ _ => cases h_pure
  | unwindResume => rfl
  | unwindTerminate => rfl
  | inlineAsm => rfl

/--
One-step simulation theorem for `stepMirFn`: under `checkPureMir body = true`
and `RootActiveMemory mem₀`, stepping `ps.toMachineState mem₀` equals stepping
`ps.toMachineState emptyMemory` and restoring `mem₀` via
`MirStepNode.withMem mem₀`.
-/
theorem stepMirFn_toMachineState_eq_withMem
    {body : CapturedMir} {mem₀ : Memory} (ps : PureState)
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀) :
    stepMirFn body (ps.toMachineState mem₀) =
      MirStepNode.withMem mem₀ (stepMirFn body (ps.toMachineState emptyMemory)) := by
  have h_act : (ps.toMachineState mem₀).memory.activeCallee = none := h_root.2.2.1
  have h_emp_act : (ps.toMachineState emptyMemory).memory.activeCallee = none := rfl
  unfold stepMirFn
  rw [h_act, h_emp_act]
  dsimp only [Option.getD, PureState.toMachineState]
  cases body.phase with
  | other _ => rw [MirStepNode.withMem_unsupported]
  | _ =>
    all_goals
      dsimp only
      cases h_bb : Trusted.Sequence.get? body.basicBlocks (ps.bb : Nat) with
      | none => rw [MirStepNode.withMem_fail]
      | some bb =>
        dsimp only
        have ⟨h_stmts, h_term⟩ := checkPureMir_block h_pure h_bb
        cases h_stmt : get? bb.statements ps.stmtIdx with
        | some stmt =>
          have h_s := list_all_of_get? h_stmts h_stmt
          exact evalStmt_toMachineState_eq_withMem ps mem₀ stmt
            body.localDecls body.layouts h_s h_root
        | none =>
          dsimp only
          by_cases h_eq : (ps.stmtIdx == length bb.statements) = true
          · simp only [h_eq, ite_true]
            exact evalTerminator_toMachineState_eq_withMem ps mem₀ bb.terminator body h_term h_root
          · simp only [h_eq]
            rfl

/-! ## 4. Pure Execution Predicates (`wpPureMirExec`, `PureMirConverges`) & Soundness -/

/--
Pure operand evaluation on an alias-erased local slot environment `env`
(referencing no `Memory` state).
-/
def evalPureOperand
    (env : List SlotState)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable) : PlaceReadResult :=
  evalOperand env op [] [] layouts []

/--
Pure operand-list evaluation on an alias-erased local slot environment `env`
(referencing no `Memory` state).
-/
def evalPureOperands
    (env : List SlotState)
    (ops : List Operand)
    (layouts : LayoutTable := emptyLayoutTable) : OperandsEvalResult :=
  evalOperands env ops [] [] layouts []

/--
Pure place write on an alias-erased local slot environment `env` (referencing
no `BorrowEntry` table).
-/
def writePurePlaceValue
    (env : List SlotState)
    (dst : Place)
    (val : Value) : PlaceWriteResult :=
  writePlaceValue env [] dst val

/--
Fuel-bounded symbolic weakest precondition over alias-erased `PureState`
(`mirNormalPost`: requires normal return satisfying `post retVal` and forbids
UB, panics, and aborts).
-/
def wpPureMirExec
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (post : Value → Prop) : Prop :=
  wpMirExecSym fuel body (.running (ps.toMachineState emptyMemory))
    (mirNormalPost (fun retVal _ => post retVal))

/--
Fuel-bounded partial-correctness symbolic weakest precondition over `PureState`
(`mirSafePost`: forbids UB; if execution returns normally with `retVal`, then
`post retVal` holds).
-/
def wpPureMirSafeExec
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (post : Value → Prop) : Prop :=
  wpMirExecSym fuel body (.running (ps.toMachineState emptyMemory))
    (mirSafePost (fun retVal _ => post retVal))

/--
Fuel-bounded state-to-state symbolic stepper over `PureState`.
-/
def wpPureMirSteps
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  wpMirStepsSym fuel body (ps.toMachineState emptyMemory)
    (fun ms' => mid (PureState.ofMachineState ms'))
    (mirNormalPost (fun retVal _ => post retVal))

/--
Fuel-free total-correctness convergence over alias-erased `PureState`.
-/
def PureMirConverges
    (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  ∃ fuel : Nat, wpPureMirExec fuel body ps post

/--
Fuel-free partial-correctness (`mirSafePost`) convergence over alias-erased
`PureState`.
-/
def PureMirSafeConverges
    (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  ∃ fuel : Nat, wpPureMirSafeExec fuel body ps post

/--
Fuel-free intermediate state convergence over alias-erased `PureState`.
-/
def PureMirStepsConverges
    (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  ∃ fuel : Nat, wpPureMirSteps fuel body ps mid post

/-- Postcondition monotonicity for `PureMirConverges`. -/
theorem PureMirConverges.mono
    {body : CapturedMir} {ps : PureState} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirConverges body ps P) :
    PureMirConverges body ps Q := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Every `PureMirConverges` proof implies `PureMirSafeConverges`. -/
theorem PureMirSafeConverges.of_pureMirConverges
    {body : CapturedMir} {ps : PureState} {post : Value → Prop}
    (h : PureMirConverges body ps post) :
    PureMirSafeConverges body ps post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_mono_post (fun _ => mirNormalPost_imp_mirSafePost) h_wp⟩

/-- Postcondition monotonicity for `PureMirSafeConverges`. -/
theorem PureMirSafeConverges.mono
    {body : CapturedMir} {ps : PureState} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirSafeConverges body ps P) :
    PureMirSafeConverges body ps Q := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => trivial
  | abort => trivial

/-- Zero-step reflexivity for `PureMirStepsConverges`. -/
theorem PureMirStepsConverges.refl
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h : mid ps) :
    PureMirStepsConverges body ps mid post :=
  ⟨0, h⟩

/-- Root-active memory witness for `emptyMemory`. -/
@[simp]
theorem rootActiveMemory_emptyMemory : RootActiveMemory emptyMemory :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Fuel-free sequential composition (`PureMirConverges.bind`) over `PureState`. -/
theorem PureMirConverges.bind
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h₁ : PureMirStepsConverges body ps mid post)
    (h₂ : ∀ ps', mid ps' → PureMirConverges body ps' post)
    (h_pure : checkPureMir body = true) :
    PureMirConverges body ps post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  have h_steps :
      MirStepsConverges body (ps.toMachineState emptyMemory)
        (fun ms' =>
          mid (PureState.ofMachineState ms') ∧
          ms' = (PureState.ofMachineState ms').toMachineState emptyMemory)
        (mirNormalPost (fun retVal _ => post retVal)) := by
    suffices ∀ (f : Nat) (st : MirExecState),
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' => mid (PureState.ofMachineState s')
            | .halted out => mirNormalPost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirNormalPost (fun retVal _ => post retVal)) →
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' =>
              mid (PureState.ofMachineState s') ∧
              s' = (PureState.ofMachineState s').toMachineState emptyMemory
            | .halted out => mirNormalPost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirNormalPost (fun retVal _ => post retVal)) from
      ⟨f₁, this f₁ (.running (ps.toMachineState emptyMemory)) hf₁⟩
    intro f
    induction f with
    | zero =>
      intro st h_st
      cases st with
      | running s' => exact ⟨h_st, rfl⟩
      | halted out => exact h_st
      | faulted _ => exact False.elim h_st
    | succ f' ih =>
      intro st h_st
      cases st with
      | halted out =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        cases out with
        | normal retPair => exact h_st
        | panic => exact h_st
        | abort => exact h_st
      | faulted fk =>
        unfold wpMirExecStepsSym at h_st
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st
        exact False.elim h_st
      | running s =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
        have h_eq :=
          stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
            (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
        dsimp only [PureState.toMachineState_ofMachineState] at h_eq
        rw [h_eq] at h_st ⊢
        cases h_step : stepMirFn body { s with memory := emptyMemory } with
        | ret out =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact h_st
        | tau st' =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact ih st' h_st
        | vis i k =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          cases i with
          | inl _ => exact False.elim h_st
          | inr i2 => cases i2 with
            | inl _ => exact ih (k PUnit.unit) h_st
            | inr _ => exact False.elim h_st
  exact MirWpConverges.bind h_steps (fun ms' ⟨h_mid, h_eq⟩ => by
    rw [h_eq]
    exact h₂ (PureState.ofMachineState ms') h_mid)

/--
Core inductive simulation theorem lifting `wpMirExecSym` from `emptyMemory` to
any `mem₀ : Memory` satisfying `RootActiveMemory mem₀`.
-/
theorem wpMirExecSym_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecSym fuel body (MirExecState.withMem emptyMemory st)
        (mirNormalPost (fun retVal _ => post retVal))) :
    wpMirExecSym fuel body (MirExecState.withMem mem₀ st)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecSym at h_wp ⊢
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => trivial
        | abort => trivial
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            intro ans
            exact ih (k ans) (h_wp ans)

/--
Core inductive simulation theorem for `mirSafePost` lifting `wpMirExecSym` from
`emptyMemory` to any `mem₀ : Memory` satisfying `RootActiveMemory mem₀`.
-/
theorem wpMirExecSym_safe_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecSym fuel body (MirExecState.withMem emptyMemory st)
        (mirSafePost (fun retVal _ => post retVal))) :
    wpMirExecSym fuel body (MirExecState.withMem mem₀ st)
      (mirSafePost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecSym at h_wp ⊢
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => trivial
      | abort => trivial
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => trivial
        | abort => trivial
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            intro ans
            exact ih (k ans) (h_wp ans)

/--
Core inductive simulation theorem for call-forbidding `wpMirExecNoCallSym`
lifting from `emptyMemory` to `mem₀`.
-/
theorem wpMirExecNoCallSym_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecNoCallSym fuel body (MirExecState.withMem emptyMemory st)
        (mirNormalPost (fun retVal _ => post retVal))) :
    wpMirExecNoCallSym fuel body (MirExecState.withMem mem₀ st)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecNoCallSym at h_wp ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeNoCallWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeNoCallWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => exact False.elim h_wp
        | abort => exact False.elim h_wp
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp
            exact False.elim h_wp

/--
Simulation theorem from any intermediate `(ps, ms)` satisfying
`MirFrameSim body mem₀ ps ms`: `PureMirConverges body ps post` implies
`MirWpConverges body ms (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal))`.
-/
theorem mirWpConverges_of_pureExec_sim
    {body : CapturedMir} {ps : PureState} {ms : MachineState}
    {post : Value → Prop} {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_sim : MirFrameSim body mem₀ ps ms)
    (h_conv : PureMirConverges body ps post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body ms
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  have h_ms := (mirFrameSim_iff_eq_toMachineState body mem₀ ps ms).mp h_sim
  subst h_ms
  rcases h_conv with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_withMem_of_emptyMemory
    (.running (ps.toMachineState emptyMemory)) h_pure h_root h_wp⟩

/--
Once-and-for-All Tier 1 Alias-Erasure Theorem (`mirWpConverges_of_pureExec`):
Whenever `checkPureMir body = true` and
`PureMirConverges body (initPureState body args) post`, the full stateful
machine state `initMachineStateWithMemory body args mem₀` converges
(`MirWpConverges`) to `mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)`
for any root-active `mem₀ : Memory` (discharged automatically for concrete
initial memories and local `RootActiveMemory` hypotheses).
-/
theorem mirWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) :=
  mirWpConverges_of_pureExec_sim h_pure
    (mirFrameSim_initMachineStateWithMemory body args mem₀)
    h_conv
    h_root

/--
Specialization of `mirWpConverges_of_pureExec` to `initMachineState body args`
(where `RootActiveMemory` holds definitionally by `rfl`).
-/
theorem mirWpConverges_of_pureExec_init
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post) :
    MirWpConverges body (initMachineState body args)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = (initMachineState body args).memory ∧ post retVal)) :=
  mirWpConverges_of_pureExec h_pure h_conv (h_root := ⟨rfl, rfl, rfl, rfl⟩)

/--
Specialization of `mirWpConverges_of_pureExec` to
`initMachineStateWithCallees body args callees`, preserving the populated
callee table `callees` in `(initMachineStateWithCallees body args callees).memory`.
-/
theorem mirWpConverges_of_pureExec_withCallees
    {body : CapturedMir} {args : List Value} {callees : List CapturedMir}
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post) :
    MirWpConverges body (initMachineStateWithCallees body args callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = (initMachineStateWithCallees body args callees).memory ∧
          post retVal)) :=
  mirWpConverges_of_pureExec h_pure h_conv (h_root := ⟨rfl, rfl, rfl, rfl⟩)

/--
Specialization of `mirWpConverges_of_pureExec` to
`initMachineStateWithMemoryAndCallees body args mem₀ callees`, preserving
`Memory.withDefaultCallees mem₀ callees` across arbitrary `mem₀` and `callees`.
-/
theorem mirWpConverges_of_pureExec_withMemoryAndCallees
    {body : CapturedMir} {args : List Value} {mem₀ : Memory}
    {callees : List CapturedMir} {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body
      (initMachineStateWithMemoryAndCallees body args mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = Memory.withDefaultCallees mem₀ callees ∧ post retVal)) :=
  mirWpConverges_of_pureExec h_pure h_conv (h_root := ((rootActiveMemory_withDefaultCallees mem₀ callees).mpr h_root))

/--
Call-forbidding (`MirNoCallWpConverges`) alias-erasure theorem from
`PureMirConverges`.
-/
theorem mirNoCallWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirNoCallWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  have h_nc :
      wpMirExecNoCallSym fuel body
        (MirExecState.withMem emptyMemory
          (.running ((initPureState body args).toMachineState emptyMemory)))
        (mirNormalPost (fun retVal _ => post retVal)) := by
    suffices ∀ (f : Nat) (st : MirExecState),
        wpMirExecSym f body (MirExecState.withMem emptyMemory st)
          (mirNormalPost (fun retVal _ => post retVal)) →
        wpMirExecNoCallSym f body (MirExecState.withMem emptyMemory st)
          (mirNormalPost (fun retVal _ => post retVal)) from
      this fuel (.running ((initPureState body args).toMachineState emptyMemory)) h_wp
    intro f
    induction f with
    | zero =>
      intro st h_st
      exact False.elim h_st
    | succ f' ih =>
      intro st h_st
      unfold wpMirExecSym at h_st
      unfold wpMirExecNoCallSym
      rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_st
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      cases st with
      | halted out => exact h_st
      | faulted fk => exact False.elim h_st
      | running s =>
        dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
        have h_emp :=
          stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
            (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
        dsimp only [PureState.toMachineState_ofMachineState] at h_emp
        rw [h_emp] at h_st ⊢
        cases h_step : stepMirFn body { s with memory := emptyMemory } with
        | ret out =>
          rw [h_step] at h_st
          exact h_st
        | tau st' =>
          rw [h_step] at h_st
          exact ih st' h_st
        | vis i k =>
          rw [h_step] at h_st
          cases i with
          | inl _ => exact False.elim h_st
          | inr i2 => cases i2 with
            | inl _ => exact ih (k PUnit.unit) h_st
            | inr _ =>
              exfalso
              unfold stepMirFn at h_step
              dsimp only [emptyMemory, Option.getD] at h_step
              cases h_ph : body.phase with
              | other _ =>
                rw [h_ph] at h_step
                cases h_step
              | _ =>
                all_goals
                  rw [h_ph] at h_step
                  dsimp only at h_step
                cases h_bb : Trusted.Sequence.get? body.basicBlocks (s.frame.blockIdx : Nat) with
                | none =>
                  rw [h_bb] at h_step
                  cases h_step
                | some bb =>
                  rw [h_bb] at h_step
                  dsimp only at h_step
                  have ⟨h_stmts, h_term⟩ := checkPureMir_block h_pure h_bb
                  cases h_stmt : get? bb.statements (s.frame.stmtIdx : Nat) with
                  | some stmt =>
                    rw [h_stmt] at h_step
                    have h_s := list_all_of_get? h_stmts h_stmt
                    rcases stmt with ⟨skind, sspan⟩
                    cases skind
                    case intrinsic i =>
                      cases i <;> try exact False.elim (Bool.false_ne_true h_s)
                      all_goals
                        dsimp only [evalStmt] at h_step
                        repeat' (first | cases h_step | split at h_step)
                    all_goals
                      try exact False.elim (Bool.false_ne_true h_s)
                    all_goals
                      dsimp only [evalStmt] at h_step
                      repeat' (first | cases h_step | split at h_step)
                  | none =>
                    rw [h_stmt] at h_step
                    dsimp only at h_step
                    split at h_step
                    · rcases bb with ⟨_, ⟨tkind, tspan⟩, _⟩
                      cases tkind <;>
                        try exact False.elim (Bool.false_ne_true h_term)
                      all_goals
                        dsimp only [evalTerminator] at h_step
                        repeat' (first | cases h_step | split at h_step)
                    · cases h_step
  exact ⟨fuel, wpMirExecNoCallSym_withMem_of_emptyMemory
    (.running ((initPureState body args).toMachineState emptyMemory))
    h_pure h_root h_nc⟩

/--
Partial-correctness (`mirSafePost`) alias-erasure theorem from
`PureMirSafeConverges`.
-/
theorem mirSafeWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirSafeConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirSafePost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_safe_withMem_of_emptyMemory
    (.running ((initPureState body args).toMachineState emptyMemory))
    h_pure h_root h_wp⟩

/--
Intermediate state-to-state simulation lifting `PureMirStepsConverges` to
`MirStepsConverges` while preserving `MirFrameSim body mem₀ ps' ms'`.
-/
theorem mirStepsConverges_of_pureExec_sim
    {body : CapturedMir} {ps : PureState} {ms : MachineState}
    {mid : PureState → Prop} {post : Value → Prop} {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_sim : MirFrameSim body mem₀ ps ms)
    (h_steps : PureMirStepsConverges body ps mid post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirStepsConverges body ms
      (fun ms' =>
        ∃ ps' : PureState, mid ps' ∧ MirFrameSim body mem₀ ps' ms')
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  have h_ms := (mirFrameSim_iff_eq_toMachineState body mem₀ ps ms).mp h_sim
  subst h_ms
  rcases h_steps with ⟨fuel, h_wp⟩
  refine ⟨fuel, ?_⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym fuel body (MirExecState.withMem emptyMemory st)
        (fun
          | .running s' => mid (PureState.ofMachineState s')
          | .halted out => mirNormalPost (fun retVal _ => post retVal) out
          | .faulted _ => False)
        (mirNormalPost (fun retVal _ => post retVal)) →
      wpMirExecStepsSym fuel body (MirExecState.withMem mem₀ st)
        (fun
          | .running ms' =>
            ∃ ps' : PureState, mid ps' ∧ MirFrameSim body mem₀ ps' ms'
          | .halted out =>
            mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal) out
          | .faulted _ => False)
        (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) from
    this (.running (ps.toMachineState emptyMemory)) h_wp
  clear h_wp
  induction fuel with
  | zero =>
    intro st h_st
    cases st with
    | running s' =>
      exact ⟨PureState.ofMachineState s', h_st, ⟨rfl, rfl, rfl, rfl⟩⟩
    | halted out =>
      cases out with
      | normal retPair => exact ⟨rfl, h_st⟩
      | panic => exact False.elim h_st
      | abort => exact False.elim h_st
    | faulted _ => exact False.elim h_st
  | succ fuel' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeNoCallWP] at h_st ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_st⟩
      | panic => exact False.elim h_st
      | abort => exact False.elim h_st
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeNoCallWP] at h_st
      exact False.elim h_st
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_st
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_st
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_st⟩
        | panic => exact False.elim h_st
        | abort => exact False.elim h_st
      | tau st' =>
        rw [h_step] at h_st
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
        exact ih st' h_st
      | vis i k =>
        rw [h_step] at h_st
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st
          exact False.elim h_st
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
            exact ih (k PUnit.unit) h_st
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st
            exact False.elim h_st

/-! ## 5. Verification Gate Bridges (`VerificationResult`, `StatefulVerificationResult`, `TotalVerificationResult`) -/

/--
Discharge a stateless `VerificationResult c` from panic-forbidding pure
execution (`PureMirConverges`).
-/
theorem verifyMirNoPanic_of_pureExec
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c := by
  refine verifyMirNoPanic_of_wpConverges c (fun args h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec_init h_pure (h_wp args h_pre))

/--
Discharge a stateless `VerificationResult c` from partial-correctness pure
execution (`PureMirSafeConverges`).
-/
theorem verifyMirSafe_of_pureExec
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirSafeConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c := by
  refine verifyMirSafe_of_wpConverges c (fun args h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => trivial
      | abort => trivial)
    (mirSafeWpConverges_of_pureExec h_pure (h_wp args h_pre) ⟨rfl, rfl, rfl, rfl⟩)

/-- Primary alias for stateless pure verification (`verifyMirNoPanic_of_pureExec`). -/
abbrev verifyMir_of_pureExec := @verifyMirNoPanic_of_pureExec

/--
Discharge a stateful `StatefulVerificationResult c` from panic-forbidding pure
execution (`PureMirConverges`), automatically supplying `mem' = mem` alongside
`post retVal` without any manual `Memory` destructuring.
-/
theorem verifyStatefulMirNoPanic_of_pureExec
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConverges c.body (initPureState c.body args)
          (fun retVal => c.post args mem retVal mem)) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanic_of_wpConverges c (fun args mem h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases h_out with ⟨rfl, h_post⟩
        exact h_post
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec h_pure (h_wp args mem h_pre) (h_root args mem h_pre))

/--
Discharge a stateful `StatefulVerificationResult c` from partial-correctness
pure execution (`PureMirSafeConverges`).
-/
theorem verifyStatefulMirSafe_of_pureExec
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirSafeConverges c.body (initPureState c.body args)
          (fun retVal => c.post args mem retVal mem)) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirSafe_of_wpConverges c (fun args mem h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases h_out with ⟨rfl, h_post⟩
        exact h_post
      | panic => trivial
      | abort => trivial)
    (mirSafeWpConverges_of_pureExec h_pure (h_wp args mem h_pre) (h_root args mem h_pre))

/-- Primary alias for stateful pure verification (`verifyStatefulMirNoPanic_of_pureExec`). -/
abbrev verifyStatefulMir_of_pureExec := @verifyStatefulMirNoPanic_of_pureExec

/--
Discharge a total-correctness `TotalVerificationResult c` from pure execution
(`PureMirConverges`).
-/
theorem verifyTotalMir_of_pureExec
    (c : TotalClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConverges c.body (initPureState c.body args)
          (fun retVal => c.post args mem retVal mem)) :
    TotalVerificationResult c := by
  refine verifyTotalMir_of_wpConverges c (fun args mem h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases h_out with ⟨rfl, h_post⟩
        exact h_post
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec h_pure (h_wp args mem h_pre) (h_root args mem h_pre))

/--
Discharge `MirBoolPredicateHolds specBody args` from `PureMirConverges`.
-/
theorem mirBoolPredicateHolds_of_pureExec
    (specBody : CapturedMir) (args : List Value)
    (h_pure : checkPureMir specBody = true)
    (h_conv :
      PureMirConverges specBody (initPureState specBody args)
        (· = .scalar { bits := 1, sizeBytes := 1 })) :
    MirBoolPredicateHolds specBody args := by
  refine mirBoolPredicateHolds_of_wpConverges specBody args ?_
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec_init h_pure h_conv)

/--
Discharge `MirBoolPredicateHoldsWithCallees specBody callees args` from
`PureMirConverges`.
-/
theorem mirBoolPredicateHoldsWithCallees_of_pureExec
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_pure : checkPureMir specBody = true)
    (h_conv :
      PureMirConverges specBody (initPureState specBody args)
        (· = .scalar { bits := 1, sizeBytes := 1 })) :
    MirBoolPredicateHoldsWithCallees specBody callees args := by
  refine mirBoolPredicateHoldsWithCallees_of_wpConverges specBody callees args ?_
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec_withCallees h_pure h_conv)

/-! ## 6. Concrete Multi-Block Struct/Tuple/Enum Witness (`pureAdtMultiBlockBody`) -/

/-- Synthetic source span for `pureAdtMultiBlockBody`. -/
def pureAdtSpan : String := "PureMirExec.lean"

/-- `u32` type (`4` bytes). -/
def pureU32Ty : Ty :=
  { kind := .uint .u32, layoutIdx := 0 }

/-- Tuple type `(u32, u32)`. -/
def purePairTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }

/-- Two-variant enum/ADT type `Mode` (`variant 0 = KeepFirst`, `variant 1 = KeepSecond`). -/
def pureModeEnumTy : Ty :=
  { kind := .adt "demo::Mode" [], layoutIdx := 0 }

/--
Multi-block MIR function `pureAdtMultiBlockBody` operating on structs/tuples
and enums across 4 basic blocks (`bb0`, `bb1`, `bb2`, `bb3`):
- Incoming arguments:
  - `_1` (`purePairTy`): tuple/struct pair `(x, y)` of two `u32` scalars
  - `_2` (`pureModeEnumTy`): enum value with variant `0` or `1` and payload `[tag]`
- Locals:
  - `_0`: return slot (`u32`)
  - `_3`: temporary tuple `(x, y)` constructed via `Rvalue.aggregate .tuple`
    and projected at fields `0` and `1`
  - `_4`: discriminant of enum `_2` extracted via `Rvalue.discriminant`
- Control flow:
  - `bb0`: `StorageLive(_3)`, `StorageLive(_4)`, extract `x = _1.0` and
    `y = _1.1` into tuple `_3`, compute `_4 = discriminant(_2)`, and branch via
    `switchInt(_4)` to `bb1` (when variant == 0) or `bb2` (otherwise).
  - `bb1`: project `_0 = _3.0` and `goto bb3`.
  - `bb2`: project `_0 = _3.1` and `goto bb3`.
  - `bb3`: `StorageDead(_4)`, `StorageDead(_3)`, `return`.
-/
def pureAdtMultiBlockBody : CapturedMir where
  defPath := "demo::select_pair_by_mode"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := purePairTy, debugName := some "pair" },
    { mutability := .not, ty := pureModeEnumTy, debugName := some "mode" },
    { mutability := .mut, ty := purePairTy, debugName := some "tmp_pair" },
    { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := some "discr" }
  ]
  basicBlocks := [
    -- bb0: construct tuple _3 from (_1.0, _1.1), read discriminant(_2) into _4, switchInt
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 1, projection := [.field 0 pureU32Ty] },
              .copy { local_ := 1, projection := [.field 1 pureU32Ty] }
            ])
          span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.discriminant { local_ := 2, projection := [] })
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .switchInt
          (.copy { local_ := 4, projection := [] })
          { branches := [(0, 1)], otherwise := 2 }
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: variant 0 branch -> _0 = _3.0; goto bb3
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 0 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .goto 3, span := pureAdtSpan }
      isCleanup := false
    },
    -- bb2: non-zero variant branch -> _0 = _3.1; goto bb3
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 1 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .goto 3, span := pureAdtSpan }
      isCleanup := false
    },
    -- bb3: StorageDead(_4); StorageDead(_3); return
    { statements := [
        { kind := .storageDead 4, span := pureAdtSpan },
        { kind := .storageDead 3, span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32Layout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [u32Layout]
  }
  allocations := []

/--
`checkPureMir pureAdtMultiBlockBody = true` holds by `decide` / `rfl`.
-/
theorem checkPureMir_pureAdtMultiBlockBody :
    checkPureMir pureAdtMultiBlockBody = true := by
  decide

/--
Expected pure specification of `pureAdtMultiBlockBody` on scalar fields `x`, `y`
and enum variant index `variantIdx`.
-/
def pureAdtExpected (x y variantIdx : Nat) : Value :=
  .scalar { bits := if variantIdx == 0 then x else y, sizeBytes := 4 }

/--
Fuel-free pure execution convergence (`PureMirConverges`) for
`pureAdtMultiBlockBody` on `initPureState`, proved purely over `PureState`
without touching any `Memory` fields.
-/
theorem pureAdtMultiBlock_pureConverges
    (x y variantIdx : Nat) (payload : List Value) :
    PureMirConverges pureAdtMultiBlockBody
      (initPureState pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ])
      (· = pureAdtExpected x y variantIdx) := by
  refine ⟨12, ?_⟩
  cases variantIdx with
  | zero =>
    change Value.scalar { bits := x, sizeBytes := 4 } = pureAdtExpected x y 0
    rfl
  | succ n =>
    change Value.scalar { bits := y, sizeBytes := 4 } = pureAdtExpected x y (n + 1)
    rfl

/--
1-step stateful `MirWpConverges` proof for `pureAdtMultiBlockBody` at arbitrary
root-active `mem₀ : Memory`, discharged directly via `mirWpConverges_of_pureExec`
without ever mentioning `allocs`, `borrows`, or `provenanceMap`.
-/
theorem pureAdtMultiBlock_wpConverges
    (x y variantIdx : Nat) (payload : List Value)
    (mem₀ : Memory) (h_root : RootActiveMemory mem₀) :
    MirWpConverges pureAdtMultiBlockBody
      (initMachineStateWithMemory pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] mem₀)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = mem₀ ∧ retVal = pureAdtExpected x y variantIdx)) :=
  mirWpConverges_of_pureExec
    checkPureMir_pureAdtMultiBlockBody
    (pureAdtMultiBlock_pureConverges x y variantIdx payload)
    h_root

/--
1-step stateful `MirWpConverges` proof for `pureAdtMultiBlockBody` when
`mem₀.callees` is populated by `initMachineStateWithMemoryAndCallees`.
-/
theorem pureAdtMultiBlock_wpConverges_withCallees
    (x y variantIdx : Nat) (payload : List Value)
    (mem₀ : Memory) (callees : List CapturedMir)
    (h_root : RootActiveMemory mem₀) :
    MirWpConverges pureAdtMultiBlockBody
      (initMachineStateWithMemoryAndCallees pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = Memory.withDefaultCallees mem₀ callees ∧
          retVal = pureAdtExpected x y variantIdx)) :=
  mirWpConverges_of_pureExec_withMemoryAndCallees
    checkPureMir_pureAdtMultiBlockBody
    (pureAdtMultiBlock_pureConverges x y variantIdx payload)
    h_root

/--
Stateful claim for `pureAdtMultiBlockBody` requiring exact memory preservation
(`mem' = mem₀`) across arbitrary heap allocations and callee tables.
-/
def pureAdtMultiBlockStatefulClaim : StatefulClaim where
  body := pureAdtMultiBlockBody
  pre args mem₀ :=
    (∃ (x y variantIdx : Nat) (payload : List Value),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ]) ∧
    RootActiveMemory mem₀
  post args mem₀ retVal mem' :=
    mem' = mem₀ ∧
    ∀ (x y variantIdx : Nat) (payload : List Value),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] →
      retVal = pureAdtExpected x y variantIdx

/-- Non-vacuity witness for `pureAdtMultiBlockStatefulClaim.pre`. -/
theorem pureAdtMultiBlockStatefulClaim_nonVacuous :
    ∃ (args : List Value) (mem₀ : Memory),
      pureAdtMultiBlockStatefulClaim.pre args mem₀ :=
  ⟨[
      .aggregate 0 [
        .scalar { bits := 10, sizeBytes := 4 },
        .scalar { bits := 20, sizeBytes := 4 }
      ],
      .aggregate 1 []
    ],
    (initMachineStateWithCallees pureAdtMultiBlockBody [] [pureAdtMultiBlockBody]).memory,
    ⟨⟨10, 20, 1, [], rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

/--
Concrete `StatefulVerificationResult` discharge for `pureAdtMultiBlockStatefulClaim`
where the postcondition requires `mem' = mem₀`, proved via
`verifyStatefulMirNoPanic_of_pureExec` (`mirWpConverges_of_pureExec`) without
ever mentioning `allocs`, `borrows`, or `provenanceMap`.
-/
theorem verify_pureAdtMultiBlockStatefulClaim :
    StatefulVerificationResult pureAdtMultiBlockStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec
    pureAdtMultiBlockStatefulClaim
    checkPureMir_pureAdtMultiBlockBody
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, variantIdx, payload, rfl⟩
  exact PureMirConverges.mono
    (fun retVal h_ret =>
      ⟨rfl, fun x' y' v' p' h_eq => by
        injection h_eq with h_hd h_tl
        injection h_tl with h_snd _
        injection h_hd with _ h_fields
        injection h_fields with h_x h_rest
        injection h_rest with h_y _
        injection h_x with h_sc_x
        injection h_y with h_sc_y
        injection h_sc_x with h_bx _
        injection h_sc_y with h_by _
        injection h_snd with h_var _
        subst h_bx h_by h_var
        exact h_ret⟩)
    (pureAdtMultiBlock_pureConverges x y variantIdx payload)

end Anneal.PureMirExec
