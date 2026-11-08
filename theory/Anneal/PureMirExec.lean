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
      initMachineStateWithCallees body args callees := by
  cases callees <;> rfl

@[simp]
theorem initPureState_toMachineState_withMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) :
    (initPureState body args).toMachineState
        (MirFuelFree.Memory.withDefaultCallees mem callees) =
      MirFuelFree.initMachineStateWithMemoryAndCallees body args mem callees :=
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
      (initMachineStateWithCallees body args callees) := by
  cases callees <;> exact ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithMemoryAndCallees body args mem₀ callees`, preserving
`Memory.withDefaultCallees mem₀ callees`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem₀ : Memory)
    (callees : List CapturedMir) :
    MirFrameSim body (MirFuelFree.Memory.withDefaultCallees mem₀ callees)
      (initPureState body args)
      (MirFuelFree.initMachineStateWithMemoryAndCallees body args mem₀ callees) :=
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
Syntactic purity check on a `BinOp`: every operator except `BinOp.offset`,
whose pointer case (`evalPtrOffsetBinOp`) reads `mem.borrows` to bound the
offset.
-/
def isPureBinOp : BinOp → Bool
  | .offset => false
  | _ => true

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
  | .cast ck op _ => match ck with
    | .pointerCoercion _ => false
    | .fnPtrToPtr => false
    -- `ptrToPtr` reads `mem.borrows` and may push a fresh element borrow
    -- (`deriveStackElemThinPtr`), so it is not memory-independent.
    | .ptrToPtr => false
    | _ => isPureOperand op
  | .binaryOp op lhs rhs => isPureBinOp op && (isPureOperand lhs && isPureOperand rhs)
  | .nullaryOp _ _ => true
  | .unaryOp _ op => isPureOperand op
  | .discriminant p => isPurePlace p
  | .aggregate _ ops => ops.all isPureOperand
  | .shallowInitBox _ _ => false
  | .copyForDeref _p => false
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

/-- A pure projection path contains no `.deref`, so `splitLastDeref?` finds none. -/
theorem splitLastDeref?_eq_none_of_pure :
    ∀ (proj : List ProjectionElem), proj.all isPureProjElem = true →
      splitLastDeref? proj = none
  | [], _ => rfl
  | hd :: tl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitLastDeref?_eq_none_of_pure tl h.2
    cases hd <;> simp_all [isPureProjElem, splitLastDeref?]

/-- Reading a pure place is independent of `borrows`, `globals`, and `callerLocals`. -/
theorem evalPlaceRead_pure_eq
    (locals : List LocalSlot) (p : Place)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (h_pure : isPurePlace p = true) :
    evalPlaceRead locals p borrows globals layouts callerLocals localDecls =
      evalPlaceRead locals p [] [] layouts [] localDecls := by
  rcases p with ⟨loc, proj⟩
  cases proj with
  | nil => rfl
  | cons hd tl =>
    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

/-- `Rvalue.len` of a pure place is independent of `mem` and leaves it unchanged. -/
theorem evalPlaceLen_pure_eq_withMem
    (locals : List LocalSlot) (p : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPurePlace p = true) :
    evalPlaceLen locals p mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalPlaceLen locals p emptyMemory localDecls layouts) := by
  have h_split : splitLastDeref? p.projection = none :=
    splitLastDeref?_eq_none_of_pure p.projection h_pure
  unfold evalPlaceLen
  simp only [h_split]
  rw [evalPlaceRead_pure_eq locals p mem.borrows mem.globals layouts
      mem.callerLocals localDecls h_pure,
    evalPlaceRead_pure_eq locals p emptyMemory.borrows emptyMemory.globals
      layouts emptyMemory.callerLocals localDecls h_pure]
  repeat' (first | rfl | split)

/-- `evalPlaceDiscriminant` only threads `mem` through to its result. -/
theorem evalPlaceDiscriminant_eq_withMem
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (p : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals' mem p localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalPlaceDiscriminant val locals' emptyMemory p localDecls layouts) := by
  unfold evalPlaceDiscriminant
  dsimp only
  repeat' (first | rfl | split)

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
  | use op | wrapUnsafeBinder op _ =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases op with
      | constant _ => rfl
      | copy p | move p =>
        rcases p with ⟨loc, proj⟩
        cases proj with
        | nil => rfl
        | cons hd tl =>
          simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
          cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | «repeat» op count =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases op with
      | constant _ => rfl
      | copy p | move p =>
        rcases p with ⟨loc, proj⟩
        cases proj with
        | nil => rfl
        | cons hd tl =>
          simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
          cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | ref _ _ => cases h_pure
  | threadLocalRef _ => cases h_pure
  | rawPtr _ _ => cases h_pure
  | len p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    exact evalPlaceLen_pure_eq_withMem locals p mem localDecls layouts h_pure
  | cast ck op targetTy =>
    dsimp only [isPureRvalue] at h_pure
    cases ck with
    | pointerCoercion _ => cases h_pure
    | fnPtrToPtr => cases h_pure
    | ptrToPtr => cases h_pure
    | transmute => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | subtype => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | _ =>
      dsimp only [evalRvalue]
      try unfold evalReifyFnPointer
      try unfold evalFnPtrToPtr
      try rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try unfold evalReifyFnPointer
      try unfold evalFnPtrToPtr
      try rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      try cases evalOperand locals op [] [] layouts []
      repeat' (first | rfl | split)
      all_goals try dsimp (config := { zeta := true })
      repeat' (first | rfl | split)
      all_goals try rfl
  | binaryOp op lhs rhs =>
    simp only [isPureRvalue, Bool.and_eq_true] at h_pure
    obtain ⟨h_op, h_pure⟩ := h_pure
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
          | scalar _ => cases op <;> first | rfl | exact absurd h_op (by decide)
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
    repeat' (first | rfl | exact evalPlaceDiscriminant_eq_withMem .. | split)
  | aggregate kind ops =>
    dsimp only [isPureRvalue] at h_pure
    cases kind
    all_goals
      dsimp only [evalRvalue]
      try rw [evalOperands_pure_eq locals ops mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try rw [evalOperands_pure_eq locals ops emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
  | shallowInitBox _ _ => cases h_pure
  | copyForDeref _ => cases h_pure

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

private def evalAssignNonDeref
    (s : MachineState) (dstLoc : Local) (proj : List ProjectionElem)
    (val : Value) (locals₁ : List LocalSlot) (mem₁ : Memory) : MirStepNode :=
  match get? locals₁ dstLoc with
  | .some (.init rootVal) =>
    match writeProjectedValue locals₁ rootVal proj val with
    | .ok rootVal' =>
      match set? locals₁ dstLoc (.init rootVal') with
      | .some locals₂ =>
        let resolvedLocalProj :=
          match resolveBorrowProjectionElems locals₁ proj with
          | .some rp => rp
          | .none => proj
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrowsAtProj
              mem₁.borrows dstLoc .none resolvedLocalProj
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .some .uninit => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .none => MirStepNode.fail .ub

private def evalAssignDst
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory) : MirStepNode :=
  match dst.projection with
  | .nil =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deref :: restProj =>
    match evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors with
    | .ok locals₂ =>
      let borrows' := invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
      MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
    | .ub =>
      match mem₁.callerLocals with
      | .nil => MirStepNode.fail .ub
      | _ :: _ =>
        match
          evalCallerPlaceWrite
            locals₁ mem₁.callerLocals mem₁.borrows dst val mem₁.activeProtectors
        with
        | .ok callerLocals' =>
          let borrows' :=
            invalidateDerefWriteBorrows
              locals₁ mem₁.borrows dst restProj mem₁.callerLocals
          MirStepNode.step
            (advanceStmt s locals₁
              { mem₁ with borrows := borrows', callerLocals := callerLocals' })
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
    | .unsupported => MirStepNode.unsupported
  | hd :: tl =>
    evalAssignNonDeref s dst.local_ (hd :: tl) val locals₁ mem₁

private theorem evalStmt_assign_eq
    (s : MachineState) (dst : Place) (rv : Rvalue) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
      match evalRvalue s.frame.locals rv s.memory localDecls layouts with
      | .ok val locals₁ mem₁ => evalAssignDst s dst val locals₁ mem₁
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨dstLoc, dstProj⟩
    cases dstProj with
    | nil => rfl
    | cons hd tl => cases hd <;> rfl

private theorem evalAssignDst_nonDeref
    (s : MachineState) (dstLoc : Local) (hd : ProjectionElem)
    (tl : List ProjectionElem) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (h_nd : hd ≠ .deref) :
    evalAssignDst s ⟨dstLoc, hd :: tl⟩ val locals₁ mem₁ =
      evalAssignNonDeref s dstLoc (hd :: tl) val locals₁ mem₁ := by
  cases hd with
  | deref => exact False.elim (h_nd rfl)
  | _ => rfl

private theorem ne_deref_of_isPureProjElem
    {hd : ProjectionElem} (h : isPureProjElem hd = true) : hd ≠ .deref := by
  intro h_eq; subst h_eq; cases h

private def isOtherPhase : MirPhaseTag → Bool
  | .other _ => true
  | _ => false

private theorem stepMirFn_eq_ite (body : CapturedMir) (s : MachineState) :
    stepMirFn body s =
      let currentBody := s.memory.activeCallee.getD body
      if isOtherPhase currentBody.phase then
        MirStepNode.unsupported
      else
        match get? currentBody.basicBlocks s.frame.blockIdx with
        | none => MirStepNode.fail .ub
        | some bb =>
          match get? bb.statements s.frame.stmtIdx with
          | some stmt => evalStmt s stmt currentBody.localDecls currentBody.layouts
          | none =>
            if s.frame.stmtIdx == length bb.statements then
              evalTerminator s bb.terminator (some currentBody)
            else
              MirStepNode.fail .ub := by
  unfold stepMirFn
  dsimp only
  cases (s.memory.activeCallee.getD body).phase <;> rfl

private theorem isOtherPhase_eq_false {ph : MirPhaseTag}
    (h : ∀ tag, ph ≠ .other tag) : isOtherPhase ph = false := by
  cases ph with
  | other tag => exact False.elim (h tag rfl)
  | _ => rfl

private theorem isOtherPhase_eq_true_iff {ph : MirPhaseTag} :
    isOtherPhase ph = true → ∃ tag, ph = .other tag := by
  cases ph with
  | other tag => intro _; exact ⟨tag, rfl⟩
  | _ => intro h; cases h

/--
Evaluating a pure `Statement` from `ps.toMachineState mem₀` produces the exact
same transition as evaluating from `ps.toMachineState emptyMemory` and
restoring `mem₀`, provided `mem₀` has no live borrows and no active
function-entry protectors.

Pure statements read and write only the frame's locals; the only memory fields
they consult are the borrow table (invalidated on every local write) and the
protector stack (checked for protected-write conflicts). In particular, the
call stack and the active callee are irrelevant, so the lemma also applies to
callee frames and to caller frames resumed after a return.
-/
theorem evalStmt_toMachineState_eq_withMem_of_frameFree
    (ps : PureState) (mem₀ : Memory) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureStatement stmt.kind = true)
    (h_borrows : mem₀.borrows = [])
    (h_prot : mem₀.activeProtectors = []) :
    evalStmt (ps.toMachineState mem₀) stmt localDecls layouts =
      MirStepNode.withMem mem₀
        (evalStmt (ps.toMachineState emptyMemory) stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop => rfl
  | coverage => rfl
  | constEvalCounter => rfl
  | storageLive loc =>
    cases mem₀
    dsimp only at h_borrows h_prot
    subst h_borrows h_prot
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | storageDead loc =>
    cases mem₀
    dsimp only at h_borrows h_prot
    subst h_borrows h_prot
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
    rw [evalStmt_assign_eq, evalStmt_assign_eq]
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
        unfold evalAssignDst
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
        have h_nd := ne_deref_of_isPureProjElem h_dst.1
        rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd,
            evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd]
        unfold evalAssignNonDeref
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
        (evalStmt (ps.toMachineState emptyMemory) stmt localDecls layouts) :=
  evalStmt_toMachineState_eq_withMem_of_frameFree ps mem₀ stmt localDecls layouts
    h_pure h_root.1 h_root.2.2.2

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
        cases expected
        · dsimp only
          cases Nat.beq sc.bits 0 with
          | true => rfl
          | false =>
            dsimp only [applyUnwindAction]
            cases unwind <;> (try rw [h_stack]) <;> rfl
        · dsimp only
          cases Nat.beq sc.bits 1 with
          | true => rfl
          | false =>
            dsimp only [applyUnwindAction]
            cases unwind <;> (try rw [h_stack]) <;> rfl
      | _ => rfl
  | call _ _ _ _ _ => cases h_pure
  | tailCall _ _ => cases h_pure
  | unwindResume =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_stack]
    rfl
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
          post retVal)) := by
  have h := mirWpConverges_of_pureExec
    (mem₀ := (initMachineStateWithCallees body args callees).memory)
    h_pure h_conv (rootActiveMemory_initMachineStateWithCallees body args callees)
  rwa [← initMachineStateWithCallees_eq_withMemory] at h

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
      (MirFuelFree.initMachineStateWithMemoryAndCallees body args mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = MirFuelFree.Memory.withDefaultCallees mem₀ callees ∧ post retVal)) :=
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
The trusted callee-aware stateful initial state is `initMachineStateWithMemory`
over its own initial memory, which seeds `Memory.callees` and
`Memory.traitImpls` only when the callee table is non-empty.
-/
theorem trustedInitWithMemoryAndCallees_eq_withMemory
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) :
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees =
      initMachineStateWithMemory body args
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          body args mem callees).memory :=
  rfl

/--
Seeding the callee and trait-implementation tables preserves
`RootActiveMemory`: neither table is a root-activation field.
-/
theorem rootActiveMemory_trustedInitWithMemoryAndCallees
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {callees : List CapturedMir}
    (h_root : RootActiveMemory mem) :
    RootActiveMemory
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees).memory := by
  cases callees with
  | nil => exact h_root
  | cons _ _ => exact h_root

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
    (mirWpConverges_of_pureExec_withCallees h_pure (h_wp args h_pre))

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
  have h := mirSafeWpConverges_of_pureExec
    (mem₀ := (initMachineStateWithCallees c.body args c.callees).memory)
    h_pure (h_wp args h_pre)
    (rootActiveMemory_initMachineStateWithCallees c.body args c.callees)
  rw [← initMachineStateWithCallees_eq_withMemory] at h
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => trivial
      | abort => trivial)
    h

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
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
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
    (mirWpConverges_of_pureExec
      (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees).memory)
      h_pure (h_wp args mem h_pre)
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))

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
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
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
    (mirSafeWpConverges_of_pureExec
      (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees).memory)
      h_pure (h_wp args mem h_pre)
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))

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
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
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
    (mirWpConverges_of_pureExec
      (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees).memory)
      h_pure (h_wp args mem h_pre)
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))

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
    MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args := by
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

/--
Two-variant enum/ADT type `Mode` (`variant 0 = KeepFirst`, `variant 1 = KeepSecond`).

Its `layoutIdx` (`1`) has no entry in `pureAdtMultiBlockBody.layouts`, so
`evalPlaceDiscriminant` reads the raw variant index. Index `0` would alias
`u32Layout`, whose `.single 0` variants make every nonzero variant UB.
-/
def pureModeEnumTy : Ty :=
  { kind := .adt "demo::Mode" [], layoutIdx := 1 }

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
      (MirFuelFree.initMachineStateWithMemoryAndCallees pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = MirFuelFree.Memory.withDefaultCallees mem₀ callees ∧
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

/-! ## 7. Root-Active Callee Memory (`ActiveRootMemory`) & Stack-Suffix Simulation -/

/--
Memory frame relation between an initial root memory `mem₀` and the memory `mem`
observed when a root caller `body` returns across zero or more inlined
`s.memory.callees` calls or root `TerminatorKind.tailCall` transitions (`FF-2.2`).

Before any inlined call or tail call occurs, `mem = mem₀` (`mem.activeCallee =
mem₀.activeCallee`); once an inlined callee returns to `body` or `body` enters a
tail callee `activeBody`, `mem = { mem₀ with activeCallee := some activeBody }`,
leaving every other field of `mem₀` (`borrows`, `globals`, `callStack`,
`activeProtectors`, `callees`, `traitImpls`, `nextAllocId`, `nextTag`,
`nextProtector`, `callerLocals`, `fnPtrs`) untouched.
-/
def ActiveRootMemory (_body : CapturedMir) (mem₀ mem : Memory) : Prop :=
  mem = mem₀ ∨
  ∃ activeBody : CapturedMir, mem = { mem₀ with activeCallee := some activeBody }

@[simp]
theorem ActiveRootMemory.refl (body : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ mem₀ :=
  Or.inl rfl

theorem ActiveRootMemory.of_eq
    {body : CapturedMir} {mem₀ mem : Memory} (h : mem = mem₀) :
    ActiveRootMemory body mem₀ mem :=
  h ▸ Or.inl rfl

theorem ActiveRootMemory.with_some
    (body activeBody : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ { mem₀ with activeCallee := some activeBody } :=
  Or.inr ⟨activeBody, rfl⟩

theorem ActiveRootMemory.with_some_body
    (body : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ { mem₀ with activeCallee := some body } :=
  Or.inr ⟨body, rfl⟩

theorem ActiveRootMemory.trans_with_some_body
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    ActiveRootMemory body mem₀ { mem with activeCallee := some body } := by
  rcases h with rfl | ⟨_, rfl⟩ <;> exact Or.inr ⟨body, rfl⟩

theorem ActiveRootMemory.activeCallee_getD
    {body : CapturedMir} {mem₀ mem : Memory}
    (h_act : mem = mem₀ ∨ mem = { mem₀ with activeCallee := some body })
    (h_init : mem₀.activeCallee = none ∨ mem₀.activeCallee = some body) :
    mem.activeCallee.getD body = body := by
  rcases h_act with rfl | rfl
  · rcases h_init with h0 | h0 <;> simp [h0]
  · rfl

theorem ActiveRootMemory.borrows_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.borrows = mem₀.borrows := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.callStack_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callStack = mem₀.callStack := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.activeProtectors_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.activeProtectors = mem₀.activeProtectors := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.callees_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callees = mem₀.callees := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.traitImpls_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.traitImpls = mem₀.traitImpls := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.globals_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.globals = mem₀.globals := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.nextAllocId_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.nextAllocId = mem₀.nextAllocId := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.callerLocals_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callerLocals = mem₀.callerLocals := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.fnPtrs_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.fnPtrs = mem₀.fnPtrs := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem ActiveRootMemory.restore_activeCallee
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    { mem with activeCallee := mem₀.activeCallee } = mem₀ := by
  cases mem₀
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

/--
Callee-aware frame simulation between alias-erased `ps : PureState` and full
`ms : MachineState` at root memory `mem₀`, allowing `ms.memory` to satisfy
`ActiveRootMemory body mem₀ ms.memory` after inlined callee returns.
-/
def MirCalleeFrameSim
    (body : CapturedMir)
    (mem₀ : Memory)
    (ps : PureState)
    (ms : MachineState) : Prop :=
  ms.frame.blockIdx = ps.bb ∧
  ms.frame.stmtIdx = ps.stmtIdx ∧
  ms.frame.locals = ps.env ∧
  ActiveRootMemory body mem₀ ms.memory

theorem MirCalleeFrameSim.of_mirFrameSim
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    MirCalleeFrameSim body mem₀ ps ms :=
  ⟨h.1, h.2.1, h.2.2.1, Or.inl h.2.2.2⟩

/--
Append `baseStack` beneath `m.callStack` and normalize `m.activeCallee` to
`some (m.activeCallee.getD calleeBody)` so an unstacked execution of
`calleeBody` lifts directly onto a caller's suspended `callStack`.
-/
def Memory.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame)
    (m : Memory) : Memory :=
  { m with
    callStack := m.callStack ++ baseStack
    activeCallee := some (m.activeCallee.getD calleeBody) }

/-- Lift `Memory.pushBaseStack` to `MachineState`. -/
def MachineState.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame)
    (ms : MachineState) : MachineState :=
  { ms with memory := Memory.pushBaseStack calleeBody baseStack ms.memory }

/-- Lift `Memory.pushBaseStack` to `RvalueEvalResult`. -/
def RvalueEvalResult.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    RvalueEvalResult → RvalueEvalResult
  | .ok v locals' m => .ok v locals' (Memory.pushBaseStack calleeBody baseStack m)
  | .ub => .ub
  | .unsupported => .unsupported

/-- Lift `Memory.pushBaseStack` to `MirOutcome`. -/
def MirOutcome.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirOutcome → MirOutcome
  | .normal (v, m) => .normal (v, Memory.pushBaseStack calleeBody baseStack m)
  | .panic => .panic
  | .abort => .abort

/-- Lift `Memory.pushBaseStack` to `MirExecState`. -/
def MirExecState.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirExecState → MirExecState
  | .running ms => .running (MachineState.pushBaseStack calleeBody baseStack ms)
  | .halted out => .halted (MirOutcome.pushBaseStack calleeBody baseStack out)
  | .faulted fk => .faulted fk

/-- Lift `Memory.pushBaseStack` to `MirStepNode` (preserving faults and observations). -/
def MirStepNode.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.pushBaseStack calleeBody baseStack out)
  | .tau st => .tau (MirExecState.pushBaseStack calleeBody baseStack st)
  | .vis (.inl fk) k => .vis (.inl fk) k
  | .vis (.inr (.inl obs)) k =>
    .vis (.inr (.inl obs))
      (fun u => MirExecState.pushBaseStack calleeBody baseStack (k u))
  | .vis (.inr (.inr req)) k =>
    .vis (.inr (.inr req))
      (fun ans => MirExecState.pushBaseStack calleeBody baseStack (k ans))

@[simp]
theorem MirStepNode.pushBaseStack_fail
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (fk : FailureKind) :
    MirStepNode.pushBaseStack calleeBody baseStack (MirStepNode.fail fk) =
      MirStepNode.fail fk :=
  rfl

@[simp]
theorem MirStepNode.pushBaseStack_unsupported
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame) :
    MirStepNode.pushBaseStack calleeBody baseStack MirStepNode.unsupported =
      MirStepNode.unsupported :=
  rfl

theorem internFnPtr_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) (defPath : DefPath) (typeArgs : List RigidTy)
    (fnSig : Option RigidTy) :
    internFnPtr (Memory.pushBaseStack calleeBody baseStack mem)
        defPath typeArgs fnSig =
      let (allocId, mem') := internFnPtr mem defPath typeArgs fnSig
      (allocId, Memory.pushBaseStack calleeBody baseStack mem') := by
  unfold internFnPtr
  dsimp only [Memory.pushBaseStack]
  cases findFnPtrEntry? mem.fnPtrs defPath typeArgs fnSig <;> rfl

theorem evalUnsafeFnPointer_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsafeFnPointer locals op targetTy
        (Memory.pushBaseStack calleeBody baseStack mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) := by
  unfold evalUnsafeFnPointer
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem deriveStackElemThinPtr_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (mem : Memory) (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry) (elemCountOpt : Option Nat) :
    deriveStackElemThinPtr locals (Memory.pushBaseStack calleeBody baseStack mem)
        ptrVal parentEntry elemCountOpt =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt) := by
  unfold deriveStackElemThinPtr
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalUnsizeCoercion_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsizeCoercion locals op targetTy
        (Memory.pushBaseStack calleeBody baseStack mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalUnsizeCoercion locals op targetTy mem localDecls layouts) := by
  unfold evalUnsizeCoercion
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalSliceFatPtrDerefBorrow_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (mem : Memory) (parentPtr : ProvenancePtr)
    (ptrSz : Nat) (lenSc : ScalarInt) (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) :
    evalSliceFatPtrDerefBorrow locals
        (Memory.pushBaseStack calleeBody baseStack mem)
        parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalSliceFatPtrDerefBorrow locals mem
          parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts) := by
  unfold evalSliceFatPtrDerefBorrow
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalGlobalThinPtrDerefBorrow_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (mem : Memory) (alloc : CapturedAllocation)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (restProj : List ProjectionElem)
    (isMut : Bool) (pointeeTyOpt : Option Ty) (layouts : LayoutTable) :
    evalGlobalThinPtrDerefBorrow locals
        (Memory.pushBaseStack calleeBody baseStack mem)
        alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalGlobalThinPtrDerefBorrow locals mem
          alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts) := by
  unfold evalGlobalThinPtrDerefBorrow
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalPtrOffsetBinOp_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) :
    evalPtrOffsetBinOp locals₂ (Memory.pushBaseStack calleeBody baseStack mem)
        localDecls layouts lhsOp ptrVal sz offsetSc =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz
          offsetSc) := by
  unfold evalPtrOffsetBinOp ptrAllocByteBound?
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalPlaceLen_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceLen locals place (Memory.pushBaseStack calleeBody baseStack mem)
        localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalPlaceLen locals place mem localDecls layouts) := by
  unfold evalPlaceLen
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalPlaceDiscriminant_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals'
        (Memory.pushBaseStack calleeBody baseStack mem) place localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalPlaceDiscriminant val locals' mem place localDecls layouts) := by
  unfold evalPlaceDiscriminant
  dsimp only
  repeat' (first | rfl | split)

theorem evalReifyFnPointer_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String) :
    evalReifyFnPointer locals op targetTy
        (Memory.pushBaseStack calleeBody baseStack mem)
        localDecls layouts coercionKind =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalReifyFnPointer locals op targetTy mem
          localDecls layouts coercionKind) := by
  unfold evalReifyFnPointer
  cases isReifyFnPointerCoercion coercionKind with
  | false =>
    dsimp only [Memory.pushBaseStack]
    repeat' (first
      | rfl
      | exact evalUnsizeCoercion_pushBaseStack ..
      | exact deriveStackElemThinPtr_pushBaseStack ..
      | split)
  | true =>
    cases stringEq coercionKind "UnsafeFnPointer" with
    | true =>
      exact evalUnsafeFnPointer_pushBaseStack calleeBody baseStack
        locals op targetTy mem localDecls layouts
    | false =>
      dsimp only
      change (match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
        | .ub => _ | .unsupported => _ | .ok v locals' => _) = _
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        dsimp only [Memory.pushBaseStack]
        repeat' (first
          | rfl
          | (rw [internFnPtr_pushBaseStack]; rfl)
          | split)

theorem evalFnPtrToPtr_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnPtrToPtr locals op targetTy
        (Memory.pushBaseStack calleeBody baseStack mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalFnPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalFnPtrToPtr
  dsimp only [Memory.pushBaseStack]
  repeat' (first | rfl | split)

theorem evalByteCast_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCast locals op targetTy
        (Memory.pushBaseStack calleeBody baseStack mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalByteCast locals op targetTy mem localDecls layouts) := by
  unfold evalByteCast
  dsimp only [Memory.pushBaseStack]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    repeat' (first | rfl | split)
    all_goals try dsimp (config := { zeta := true })
    repeat' (first | rfl | split)
    all_goals try rfl

theorem evalSignedDiv_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalSignedDiv a b sz locals mem) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalSignedRem_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalSignedRem a b sz locals mem) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalScalarBinOp_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals
        (Memory.pushBaseStack calleeBody baseStack mem) isSigned =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => rfl
  | false =>
    dsimp only
    cases op <;> dsimp only
    all_goals
      repeat' (first
        | rfl
        | exact evalSignedDiv_pushBaseStack ..
        | exact evalSignedRem_pushBaseStack ..
        | split)

theorem evalUnaryNot_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals
        (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalUnaryNot sc optTy locals mem) := by
  unfold evalUnaryNot
  repeat' (first | rfl | split)

/--
`evalRvalue` is completely independent of `Memory.callStack` and
`Memory.activeCallee`, commuting unconditionally with `Memory.pushBaseStack`.
-/
theorem evalRvalue_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals rv (Memory.pushBaseStack calleeBody baseStack mem)
        localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | use op =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.pushBaseStack]; repeat' (first | rfl | split))
  | «repeat» op count =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.pushBaseStack]; repeat' (first | rfl | split))
  | ref bk place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    repeat' (first
      | rfl
      | exact evalSliceFatPtrDerefBorrow_pushBaseStack ..
      | exact evalGlobalThinPtrDerefBorrow_pushBaseStack ..
      | split)
  | threadLocalRef _ => rfl
  | rawPtr mutab place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    repeat' (first
      | rfl
      | exact evalSliceFatPtrDerefBorrow_pushBaseStack ..
      | exact evalGlobalThinPtrDerefBorrow_pushBaseStack ..
      | split)
  | len place =>
    dsimp only [evalRvalue]
    exact evalPlaceLen_pushBaseStack calleeBody baseStack locals place mem
      localDecls layouts
  | cast ck op targetTy =>
    cases ck with
    | pointerCoercion ckStr =>
      exact evalReifyFnPointer_pushBaseStack calleeBody baseStack
        locals op targetTy mem localDecls layouts ckStr
    | fnPtrToPtr =>
      exact evalFnPtrToPtr_pushBaseStack calleeBody baseStack
        locals op targetTy mem localDecls layouts
    | transmute =>
      exact evalByteCast_pushBaseStack calleeBody baseStack
        locals op targetTy mem localDecls layouts
    | subtype =>
      exact evalByteCast_pushBaseStack calleeBody baseStack
        locals op targetTy mem localDecls layouts
    | _ =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first
        | rfl
        | exact deriveStackElemThinPtr_pushBaseStack ..
        | split)
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhsSc =>
          cases rhsVal with
          | scalar rhsSc =>
            exact evalScalarBinOp_pushBaseStack calleeBody baseStack
              op lhsSc rhsSc locals₂ mem _
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar _ =>
            cases op <;> first | rfl | exact evalPtrOffsetBinOp_pushBaseStack ..
          | _ => rfl
        | _ => rfl
  | nullaryOp _ _ => rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc =>
          exact evalUnaryNot_pushBaseStack calleeBody baseStack sc _ locals' mem
        | _ => rfl
    | neg =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first | rfl | split)
    | ptrMetadata =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first | rfl | split)
  | discriminant place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    repeat' (first
      | rfl
      | exact evalPlaceDiscriminant_pushBaseStack ..
      | split)
  | aggregate kind ops =>
    cases kind <;>
      (dsimp only [evalRvalue, Memory.pushBaseStack];
       repeat' (first | rfl | split))
  | shallowInitBox _ _ => rfl
  | copyForDeref place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    cases evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals <;> repeat' (first | rfl | split)
  | wrapUnsafeBinder op _ =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.pushBaseStack]; repeat' (first | rfl | split))

theorem evalCopySingleDirect_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    evalCopySingleDirect
        (MachineState.pushBaseStack calleeBody baseStack s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopySingleDirect
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | rfl | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first | rfl | split)
  all_goals try rfl

@[simp]
theorem Memory.pushBaseStack_borrows
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).borrows = mem.borrows :=
  rfl

@[simp]
theorem Memory.pushBaseStack_callerLocals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callerLocals =
      mem.callerLocals :=
  rfl

@[simp]
theorem Memory.pushBaseStack_globals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).globals = mem.globals :=
  rfl

@[simp]
theorem Memory.pushBaseStack_callees
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callees = mem.callees :=
  rfl

@[simp]
theorem Memory.pushBaseStack_traitImpls
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).traitImpls =
      mem.traitImpls :=
  rfl

@[simp]
theorem Memory.pushBaseStack_activeProtectors
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).activeProtectors =
      mem.activeProtectors :=
  rfl

@[simp]
theorem Memory.pushBaseStack_callStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callStack =
      mem.callStack ++ baseStack :=
  rfl

@[simp]
theorem MachineState.pushBaseStack_frame
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) :
    (MachineState.pushBaseStack calleeBody baseStack s).frame = s.frame :=
  rfl

@[simp]
theorem MachineState.pushBaseStack_memory
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) :
    (MachineState.pushBaseStack calleeBody baseStack s).memory =
      Memory.pushBaseStack calleeBody baseStack s.memory :=
  rfl

@[simp]
theorem MirStepNode.pushBaseStack_step
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (ms : MachineState) :
    MirStepNode.pushBaseStack calleeBody baseStack (MirStepNode.step ms) =
      MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack ms) :=
  rfl

theorem advanceStmt_pushBaseStack_borrows
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (locs : List LocalSlot) (bs : List BorrowEntry) :
    advanceStmt (MachineState.pushBaseStack calleeBody baseStack s) locs
        { Memory.pushBaseStack calleeBody baseStack s.memory with
          borrows := bs } =
      MachineState.pushBaseStack calleeBody baseStack
        (advanceStmt s locs { s.memory with borrows := bs }) :=
  rfl

theorem advanceStmt_pushBaseStack_borrows_callerLocals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (locs : List LocalSlot)
    (bs : List BorrowEntry) (cl : List LocalSlot) :
    advanceStmt (MachineState.pushBaseStack calleeBody baseStack s) locs
        { Memory.pushBaseStack calleeBody baseStack s.memory with
          borrows := bs
          callerLocals := cl } =
      MachineState.pushBaseStack calleeBody baseStack
        (advanceStmt s locs { s.memory with borrows := bs, callerLocals := cl }) :=
  rfl

private def IsStmtNode (n : MirStepNode) : Prop :=
  (∃ nextSt : MachineState, n = MirStepNode.step nextSt) ∨
  (∃ fk : FailureKind, n = MirStepNode.fail fk) ∨
  n = MirStepNode.unsupported

private def evalCopyNonOverlappingPermOk
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) : MirStepNode :=
  let n := countBits
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  let srcUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ srcEntry
  let dstUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ dstEntry
  let hasUnionEndpoint :=
    match srcUnionOpt, dstUnionOpt with
    | .none, .none => false
    | _, _ => true
  match hasUnionEndpoint with
  | true =>
    evalCopyUnionBytes
      s
      src
      dst
      localDecls
      layouts
      srcPtr
      dstPtr
      srcEntry
      dstEntry
      srcUnionOpt
      dstUnionOpt
      n
      locals₃
  | false =>
    let isSingleDirect :=
      Bool.and
        (Nat.beq n 1)
        (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
    match isSingleDirect with
    | true =>
      evalCopySingleDirect
        s
        src
        dst
        localDecls
        layouts
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        locals₃
    | false =>
      let srcRootSlot : Option LocalSlot :=
        match get? locals₃ srcEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          match get? s.memory.callerLocals srcEntry.targetLocal with
          | .some slot => .some slot
          | .none =>
            get?
              s.memory.callerLocals
              (Nat.sub srcEntry.targetLocal (length locals₃))
      let dstRootSlot : Option LocalSlot :=
        match get? locals₃ dstEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          match get? s.memory.callerLocals dstEntry.targetLocal with
          | .some slot => .some slot
          | .none =>
            get?
              s.memory.callerLocals
              (Nat.sub dstEntry.targetLocal (length locals₃))
      match srcRootSlot, dstRootSlot with
      | .some (.init srcRootVal), .some (.init dstRootVal) =>
        let dstPlace : Place := {
          local_ := dstEntry.targetLocal
          projection := dstEntry.targetProjection
        }
        let dstLocalPlaceTy : Option Ty :=
          match get? locals₃ dstPlace.local_ with
          | .some _ => placeTy localDecls layouts dstPlace
          | .none => .none
        let dstIsAdt : Bool :=
          match dstLocalPlaceTy with
          | .some { kind := .adt _ _, .. } => true
          | _ => false
        let writeDstVal (newVal : Value) : MirStepNode :=
          commitCopyDstPlaceWrite
            s
            dstPlace
            dstEntry.targetLocal
            dstPtr.tag
            locals₃
            newVal
        let copyViaBytes
            (srcSubVal dstSubVal : Value) :
            MirStepNode :=
          let overlaps :=
            match Nat.beq srcPtr.tag dstPtr.tag with
            | true => true
            | false =>
              match
                Nat.beq srcEntry.targetLocal dstEntry.targetLocal
              with
              | false => false
              | true =>
                projectionsOverlap
                  srcEntry.targetProjection
                  dstEntry.targetProjection
          match overlaps with
          | true => MirStepNode.fail .ub
          | false =>
            let srcSliceVal : Option Value :=
              match srcSubVal with
              | .aggregate 0 srcElems =>
                match
                  Nat.ble (Nat.add srcStart n) (length srcElems)
                with
                | true =>
                  .some
                    (.aggregate 0
                      (takeValues n (dropValues srcStart srcElems)))
                | false =>
                  match Nat.beq srcStart 0 with
                  | true => .some srcSubVal
                  | false => .none
              | _ => .some srcSubVal
            let dstTargetTyOpt : Option Ty :=
              match dstLocalPlaceTy with
              | .some t => .some t
              | .none => operandPointeeTy localDecls layouts dst
            match srcSliceVal with
            | .none => MirStepNode.fail .ub
            | .some sVal =>
              match encodeUntypedValueToBytes defaultCodecFuel sVal with
              | .none => MirStepNode.unsupported
              | .some bs =>
                let spliceBytesToDstArray : Option Value :=
                  match Bool.not dstIsAdt, dstSubVal with
                  | true, .aggregate 0 dstElems =>
                    match
                      Nat.ble
                        (Nat.add dstStart (length bs))
                        (length dstElems)
                    with
                    | false => .none
                    | true =>
                      match
                        decodeArrayChunksWith
                          (fun chunk =>
                            decodeValueFromBytes
                              defaultCodecFuel
                              layouts
                              { kind := .uint .u8, layoutIdx := 0 }
                              chunk)
                          1
                          (length bs)
                          bs
                      with
                      | .some copiedBytes =>
                        .some
                          (.aggregate 0
                            (spliceValues
                              copiedBytes
                              dstStart
                              dstElems))
                      | .none => .none
                  | _, _ => .none
                let preferSplicedArray : Bool :=
                  match dstLocalPlaceTy, dstSubVal with
                  | .none, .aggregate 0 _ => true
                  | _, _ => false
                match preferSplicedArray, spliceBytesToDstArray with
                | true, .some splicedVal => writeDstVal splicedVal
                | _, _ =>
                  match dstTargetTyOpt with
                  | .some dstPt =>
                    match rigidTyByteSize layouts dstPt with
                    | .some dstBytes =>
                      match Nat.beq (length bs) dstBytes with
                      | true =>
                        match
                          decodeValueFromBytes
                            defaultCodecFuel
                            layouts
                            dstPt
                            bs
                        with
                        | .some decodedVal => writeDstVal decodedVal
                        | .none =>
                          match spliceBytesToDstArray with
                          | .some splicedVal => writeDstVal splicedVal
                          | .none => MirStepNode.fail .ub
                      | false =>
                        match spliceBytesToDstArray with
                        | .some splicedVal => writeDstVal splicedVal
                        | .none => MirStepNode.unsupported
                    | .none =>
                      match spliceBytesToDstArray with
                      | .some splicedVal => writeDstVal splicedVal
                      | .none => MirStepNode.unsupported
                  | .none =>
                    match spliceBytesToDstArray with
                    | .some splicedVal => writeDstVal splicedVal
                    | .none => MirStepNode.fail .ub
        match
          readProjectedValue
            locals₃
            srcRootVal
            srcEntry.targetProjection,
          readProjectedValue
            locals₃
            dstRootVal
            dstEntry.targetProjection
        with
        | .ok (.aggregate 0 srcElems),
          .ok (.aggregate 0 dstElems) =>
          let inBounds :=
            Bool.and
              (Bool.not dstIsAdt)
              (Bool.and
                (Nat.ble (Nat.add srcStart n) (length srcElems))
                (Nat.ble (Nat.add dstStart n) (length dstElems)))
          match inBounds with
          | false =>
            match
              Bool.and
                (Nat.beq dstStart 0)
                (Nat.ble (Nat.add srcStart n) (length srcElems))
            with
            | true =>
              copyViaBytes
                (.aggregate 0 srcElems)
                (.aggregate 0 dstElems)
            | false => MirStepNode.fail .ub
          | true =>
            let sameContainer :=
              Bool.and
                (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                (projectionsOverlap
                  srcEntry.targetProjection
                  dstEntry.targetProjection)
            let disjoint :=
              match Nat.beq srcPtr.tag dstPtr.tag with
              | true => false
              | false =>
                match sameContainer with
                | false => true
                | true =>
                  Bool.or
                    (Nat.ble (Nat.add srcStart n) dstStart)
                    (Nat.ble (Nat.add dstStart n) srcStart)
            match disjoint with
            | false => MirStepNode.fail .ub
            | true =>
              let copiedSlice :=
                takeValues n (dropValues srcStart srcElems)
              let dstElems' :=
                spliceValues copiedSlice dstStart dstElems
              writeDstVal (.aggregate 0 dstElems')
        | .ok srcSubVal, .ok dstSubVal =>
          copyViaBytes srcSubVal dstSubVal
        | .ok srcSubVal, .ub =>
          match Nat.beq dstStart 0 with
          | true => copyViaBytes srcSubVal .unit
          | false => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub
      | _, _ => MirStepNode.fail .ub

private theorem evalCopyNonOverlappingWithCount_eq
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits locals₃ =
      match Nat.beq countBits 0 with
      | true => MirStepNode.step (advanceStmt s locals₃)
      | false =>
        match srcVal, dstVal with
        | .ptr srcPtr _, .ptr dstPtr _ =>
          match lookupBorrow s.memory.borrows srcPtr.tag, lookupBorrow s.memory.borrows dstPtr.tag with
          | .some srcEntry, .some dstEntry =>
            match srcEntry.perm, dstEntry.perm with
            | .disabled, _ => MirStepNode.fail .ub
            | _, .frozen => MirStepNode.fail .ub
            | _, .disabled => MirStepNode.fail .ub
            | _, _ =>
              evalCopyNonOverlappingPermOk s src dst localDecls layouts srcPtr dstPtr
                srcEntry dstEntry countBits locals₃
          | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub := by
  unfold evalCopyNonOverlappingWithCount
  cases Nat.beq countBits 0 with
  | true => rfl
  | false =>
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        cases lookupBorrow s.memory.borrows srcPtr.tag with
        | none => rfl
        | some srcEntry =>
          cases lookupBorrow s.memory.borrows dstPtr.tag with
          | none => rfl
          | some dstEntry =>
            cases srcEntry.perm <;> cases dstEntry.perm <;> rfl
      | _ => rfl
    | _ => rfl

private theorem evalCopySingleDirect_isStmtNode
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot) :
    IsStmtNode (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

private theorem commitCopyDstPlaceWrite_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (dstPlace : Place) (dstTargetLocal : LocalIdx) (dstTag : Nat)
    (locals₃ : List LocalSlot) (newVal : Value) :
    commitCopyDstPlaceWrite (MachineState.pushBaseStack calleeBody baseStack s)
        dstPlace dstTargetLocal dstTag locals₃ newVal =
      MirStepNode.pushBaseStack calleeBody baseStack
        (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal) := by
  unfold commitCopyDstPlaceWrite
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | rfl | split)

private theorem commitCopyDstPlaceWrite_isStmtNode
    (s : MachineState) (dstPlace : Place) (dstTargetLocal : LocalIdx) (dstTag : Nat)
    (locals₃ : List LocalSlot) (newVal : Value) :
    IsStmtNode (commitCopyDstPlaceWrite s dstPlace dstTargetLocal dstTag locals₃ newVal) := by
  unfold commitCopyDstPlaceWrite
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

private theorem evalCopyUnionBytes_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo) (n : Nat)
    (locals₃ : List LocalSlot) :
    evalCopyUnionBytes (MachineState.pushBaseStack calleeBody baseStack s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃ =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
          srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first
    | rfl
    | exact commitCopyDstPlaceWrite_pushBaseStack ..
    | split)

private theorem evalCopyUnionBytes_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo) (n : Nat)
    (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyUnionBytes s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only
  repeat' (first
    | exact commitCopyDstPlaceWrite_isStmtNode ..
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

private theorem evalCopyNonOverlappingPermOk_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingPermOk
        (MachineState.pushBaseStack calleeBody baseStack s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopyNonOverlappingPermOk
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalCopyNonOverlappingPermOk
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first
    | rfl
    | exact evalCopySingleDirect_pushBaseStack ..
    | exact evalCopyUnionBytes_pushBaseStack ..
    | exact commitCopyDstPlaceWrite_pushBaseStack ..
    | split)

private theorem evalCopyNonOverlappingPermOk_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyNonOverlappingPermOk
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalCopyNonOverlappingPermOk
  dsimp only
  repeat' (first
    | exact evalCopySingleDirect_isStmtNode ..
    | exact evalCopyUnionBytes_isStmtNode ..
    | exact commitCopyDstPlaceWrite_isStmtNode ..
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalCopyNonOverlappingWithCount_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount
        (MachineState.pushBaseStack calleeBody baseStack s)
        src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopyNonOverlappingWithCount
          s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  rw [evalCopyNonOverlappingWithCount_eq, evalCopyNonOverlappingWithCount_eq]
  cases Nat.beq countBits 0 with
  | true => rfl
  | false =>
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
        cases lookupBorrow s.memory.borrows srcPtr.tag with
        | none => rfl
        | some srcEntry =>
          cases lookupBorrow s.memory.borrows dstPtr.tag with
          | none => rfl
          | some dstEntry =>
            dsimp only
            cases srcEntry.perm <;> cases dstEntry.perm <;>
              first
              | rfl
              | exact evalCopyNonOverlappingPermOk_pushBaseStack calleeBody baseStack
                  s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
      | _ => rfl
    | _ => rfl

private theorem evalCopyNonOverlappingWithCount_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyNonOverlappingWithCount
        s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  rw [evalCopyNonOverlappingWithCount_eq]
  cases Nat.beq countBits 0 with
  | true => exact Or.inl ⟨_, rfl⟩
  | false =>
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only
        cases lookupBorrow s.memory.borrows srcPtr.tag with
        | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
        | some srcEntry =>
          cases lookupBorrow s.memory.borrows dstPtr.tag with
          | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
          | some dstEntry =>
            dsimp only
            cases srcEntry.perm <;> cases dstEntry.perm <;>
              first
              | exact Or.inr (Or.inl ⟨_, rfl⟩)
              | exact evalCopyNonOverlappingPermOk_isStmtNode ..
      | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)

private theorem evalCopyNonOverlapping_isStmtNode
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
  | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | unsupported => exact Or.inr (Or.inr rfl)
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
    | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | unsupported => exact Or.inr (Or.inr rfl)
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
      | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | unsupported => exact Or.inr (Or.inr rfl)
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          exact evalCopyNonOverlappingWithCount_isStmtNode s src dst localDecls layouts
            srcVal dstVal countSc.bits locals₃
        | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)

theorem evalCopyNonOverlapping_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCopyNonOverlapping
        (MachineState.pushBaseStack calleeBody baseStack s)
        src dst count localDecls layouts =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
  | ub => rfl
  | unsupported => rfl
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals with
      | ub => rfl
      | unsupported => rfl
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          exact evalCopyNonOverlappingWithCount_pushBaseStack
            calleeBody baseStack s src dst localDecls layouts
            srcVal dstVal countSc.bits locals₃
        | _ => rfl

/--
`evalStmt` is completely independent of `Memory.callStack` and
`Memory.activeCallee`, commuting unconditionally with `MachineState.pushBaseStack`.
-/
theorem evalStmt_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt (MachineState.pushBaseStack calleeBody baseStack s)
        stmt localDecls layouts =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop => rfl
  | coverage => rfl
  | constEvalCounter => rfl
  | placeMention p =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack]
    repeat' (first | rfl | split)
  | retag rk p =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | rfl | split)
  | storageLive loc =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | rfl | split)
  | storageDead loc =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | rfl | split)
  | deinit p =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack]
    repeat' (first | rfl | split)
  | intrinsic intr =>
    cases intr with
    | assume op =>
      unfold evalStmt
      dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
      repeat' (first | rfl | split)
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_pushBaseStack calleeBody baseStack
        s src dst count localDecls layouts
  | setDiscriminant p variantIdx =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | rfl | split)
  | assign dst rv =>
    rw [evalStmt_assign_eq, evalStmt_assign_eq]
    dsimp only [MachineState.pushBaseStack]
    rw [evalRvalue_pushBaseStack calleeBody baseStack
      s.frame.locals rv s.memory localDecls layouts]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => rfl
    | unsupported => rfl
    | ok val locals₁ mem₁ =>
      dsimp only [RvalueEvalResult.pushBaseStack, Memory.pushBaseStack]
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold evalAssignDst
        dsimp only [Memory.pushBaseStack]
        repeat' (first | rfl | split)
      | cons hd tl =>
        by_cases h_d : hd = .deref
        · subst h_d
          unfold evalAssignDst
          dsimp only [Memory.pushBaseStack]
          repeat' (first | rfl | split)
        · rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_d,
              evalAssignDst_nonDeref _ _ _ _ _ _ _ h_d]
          unfold evalAssignNonDeref
          dsimp only [Memory.pushBaseStack]
          repeat' (first | rfl | split)
  | _ => rfl

private theorem evalStmt_isStmtNode
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, _⟩
  cases kind with
  | intrinsic intr =>
    cases intr with
    | assume _ =>
      unfold evalStmt; dsimp only
      repeat' (first
        | exact Or.inl ⟨_, rfl⟩
        | exact Or.inr (Or.inl ⟨_, rfl⟩)
        | exact Or.inr (Or.inr rfl)
        | split)
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_isStmtNode s src dst count localDecls layouts
  | assign dst rv =>
    rw [evalStmt_assign_eq]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | unsupported => exact Or.inr (Or.inr rfl)
    | ok val locals₁ mem₁ =>
      dsimp only
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold evalAssignDst; dsimp only
        repeat' (first
          | exact Or.inl ⟨_, rfl⟩
          | exact Or.inr (Or.inl ⟨_, rfl⟩)
          | exact Or.inr (Or.inr rfl)
          | split)
      | cons hd tl =>
        by_cases h_d : hd = .deref
        · subst h_d
          unfold evalAssignDst; dsimp only
          repeat' (first
            | exact Or.inl ⟨_, rfl⟩
            | exact Or.inr (Or.inl ⟨_, rfl⟩)
            | exact Or.inr (Or.inr rfl)
            | split)
        · rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_d]
          unfold evalAssignNonDeref; dsimp only
          repeat' (first
            | exact Or.inl ⟨_, rfl⟩
            | exact Or.inr (Or.inl ⟨_, rfl⟩)
            | exact Or.inr (Or.inr rfl)
            | split)
  | _ =>
    unfold evalStmt; dsimp only
    repeat' (first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr rfl)
      | split)

@[simp]
theorem resolveCallTarget_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (func : Operand) (argCount : Nat)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) :
    resolveCallTarget (MachineState.pushBaseStack calleeBody baseStack s)
        func argCount bodyLocalDecls bodyLayouts =
      resolveCallTarget s func argCount bodyLocalDecls bodyLayouts := by
  unfold resolveCallTarget
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]

/--
If `unwindFromCallStack stk mem` does not reach the empty stack `.nil` (i.e., it
does not return `.halted .panic`), then appending `baseStack` beneath `stk`
commutes via `MirExecState.pushBaseStack calleeBody baseStack`.
-/
theorem unwindFromCallStack_pushBaseStack_of_ne_panic
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (stk : List SavedCallerFrame) (mem : Memory)
    (h_no_panic : unwindFromCallStack stk mem ≠ .halted .panic) :
    unwindFromCallStack (stk ++ baseStack)
        (Memory.pushBaseStack calleeBody baseStack mem) =
      MirExecState.pushBaseStack calleeBody baseStack
        (unwindFromCallStack stk mem) := by
  induction stk generalizing mem with
  | nil =>
    exact False.elim (h_no_panic rfl)
  | cons caller rest ih =>
    dsimp only [List.cons_append, unwindFromCallStack] at h_no_panic ⊢
    cases h_uw : caller.returnUnwind with
    | unreachable => rfl
    | terminate => rfl
    | cleanup cleanupBb =>
      dsimp only [MirExecState.pushBaseStack, MachineState.pushBaseStack,
        Memory.pushBaseStack, Option.getD]
    | continue_ =>
      rw [h_uw] at h_no_panic
      dsimp only at h_no_panic
      have h_eq :
          ({ Memory.pushBaseStack calleeBody baseStack mem with
              callStack := rest ++ baseStack
              activeCallee := some caller.callerBody
              activeProtectors := restoreCallerProtectors caller } : Memory) =
          Memory.pushBaseStack calleeBody baseStack
            { mem with
              callStack := rest
              activeCallee := some caller.callerBody
              activeProtectors := restoreCallerProtectors caller } := rfl
      rw [h_eq]
      exact ih _ h_no_panic

theorem unwindFromCallStack_ne_normal
    (stk : List SavedCallerFrame) (mem : Memory) (rv : MirReturn) :
    unwindFromCallStack stk mem ≠ .halted (.normal rv) := by
  induction stk generalizing mem with
  | nil => intro h; cases h
  | cons hd tl ih =>
    dsimp only [unwindFromCallStack]
    cases hd.returnUnwind with
    | continue_ => exact ih _
    | unreachable => intro h; cases h
    | terminate => intro h; cases h
    | cleanup _ => intro h; cases h

theorem applyUnwindAction_ne_normal
    (s : MachineState) (localsAfterArgs : List LocalSlot)
    (mem : Memory) (unwind : UnwindAction) (rv : MirReturn) :
    applyUnwindAction s localsAfterArgs mem unwind ≠ .halted (.normal rv) := by
  cases unwind with
  | continue_ => exact unwindFromCallStack_ne_normal mem.callStack mem rv
  | unreachable => intro h; cases h
  | terminate => intro h; cases h
  | cleanup _ => intro h; cases h

theorem applyUnwindAction_pushBaseStack_of_ne_panic
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (localsAfterArgs : List LocalSlot)
    (unwind : UnwindAction)
    (h_no_panic :
      applyUnwindAction s localsAfterArgs s.memory unwind ≠ .halted .panic) :
    applyUnwindAction
        (MachineState.pushBaseStack calleeBody baseStack s)
        localsAfterArgs
        (Memory.pushBaseStack calleeBody baseStack s.memory)
        unwind =
      MirExecState.pushBaseStack calleeBody baseStack
        (applyUnwindAction s localsAfterArgs s.memory unwind) := by
  cases unwind with
  | unreachable => rfl
  | terminate => rfl
  | cleanup cleanupBb => rfl
  | continue_ =>
    dsimp only [applyUnwindAction, Memory.pushBaseStack] at h_no_panic ⊢
    exact unwindFromCallStack_pushBaseStack_of_ne_panic
      calleeBody baseStack s.memory.callStack s.memory h_no_panic

private def IsIntrinsicCallFamily
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (f : MachineState → MirStepNode) : Prop :=
  (∃ retVal,
    ∀ s : MachineState,
      f s = writeIntrinsicReturn s locals' destination targetBb retVal) ∨
  (∃ fk, ∀ s : MachineState, f s = MirStepNode.fail fk) ∨
  (∀ s : MachineState, f s = MirStepNode.unsupported)

private theorem IsIntrinsicCallFamily.of_eq
    {locals' : List LocalSlot} {destination : Place} {targetBb : BasicBlockIdx}
    {f g : MachineState → MirStepNode}
    (h_eq : ∀ s, f s = g s)
    (h : IsIntrinsicCallFamily locals' destination targetBb g) :
    IsIntrinsicCallFamily locals' destination targetBb f := by
  rcases h with ⟨retVal, hr⟩ | ⟨fk, hf⟩ | hu
  · exact Or.inl ⟨retVal, fun s => (h_eq s).trans (hr s)⟩
  · exact Or.inr (Or.inl ⟨fk, fun s => (h_eq s).trans (hf s)⟩)
  · exact Or.inr (Or.inr fun s => (h_eq s).trans (hu s))

private theorem writeIntrinsicScalarResult_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s => writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  cases resOpt with
  | some sc => exact Or.inl ⟨.scalar sc, fun _ => rfl⟩
  | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

private theorem intrinsicUnresolvedLayoutStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (ty : RigidTy) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicUnresolvedLayoutStep ty) := by
  unfold intrinsicUnresolvedLayoutStep
  cases isUnsizedRigidTy 8 ty with
  | true => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | false => exact Or.inr (Or.inr fun _ => rfl)

private theorem intrinsicWidePointeeStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (ty : RigidTy) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicWidePointeeStep ty) := by
  unfold intrinsicWidePointeeStep
  cases intrinsicTailMayBeUnsized 8 ty with
  | true => exact Or.inr (Or.inr fun _ => rfl)
  | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

private theorem intrinsicMissingPointeeStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
  unfold intrinsicMissingPointeeStep
  cases argOps with
  | nil => exact Or.inr (Or.inr fun _ => rfl)
  | cons ptrOp _ =>
    dsimp only
    cases operandTy bodyLocalDecls bodyLayouts ptrOp with
    | some _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | none => exact Or.inr (Or.inr fun _ => rfl)

private theorem unaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value) (g : ScalarInt → Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar sc :: .nil =>
          writeIntrinsicScalarResult s locals' destination targetBb (g sc)
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | sc | _ | _, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  exact writeIntrinsicScalarResult_cases locals' destination targetBb (g sc)

private theorem binaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value)
    (body : ScalarInt → ScalarInt → MachineState → MirStepNode)
    (h : ∀ lhs rhs, IsIntrinsicCallFamily locals' destination targetBb (body lhs rhs)) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar lhs :: .scalar rhs :: .nil => body lhs rhs s
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | lhs | _ | _, _ | ⟨_ | rhs | _ | _, _ | _⟩⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  exact h lhs rhs

private theorem optSignedBinaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value) (optSigned : Option Bool)
    (op : ScalarInt → ScalarInt → Bool → Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar lhs :: .scalar rhs :: .nil =>
          match optSigned with
          | .some flag =>
            writeIntrinsicScalarResult s locals' destination targetBb (op lhs rhs flag)
          | .none => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub) := by
  refine binaryScalarIntrinsic_family locals' destination targetBb argVals
    (fun lhs rhs s =>
      match optSigned with
      | .some flag =>
        writeIntrinsicScalarResult s locals' destination targetBb (op lhs rhs flag)
      | .none => MirStepNode.unsupported)
    fun lhs rhs => ?_
  cases optSigned with
  | none => exact Or.inr (Or.inr fun _ => rfl)
  | some flag =>
    exact writeIntrinsicScalarResult_cases locals' destination targetBb (op lhs rhs flag)

private theorem arithOffsetIntrinsic_family
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .ptr ptrVal ptrSz :: .scalar countSc :: .nil =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
            | .some pointeeTy =>
              match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
              | .some elemSz =>
                match evalArithOffset ptrVal ptrSz countSc elemSz with
                | .some retPtrVal =>
                  writeIntrinsicReturn s locals' destination targetBb (.ptr retPtrVal 8)
                | .none => MirStepNode.fail .ub
              | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .none => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | _ | ⟨ptrVal, ptrSz⟩ | _, _ | ⟨_ | countSc | _ | _, _ | _⟩⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  dsimp only
  cases Nat.beq ptrSz 8 with
  | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | true =>
    dsimp only
    cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | none =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
    | some pointeeTy =>
      dsimp only
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
      | some elemSz =>
        dsimp only
        cases evalArithOffset ptrVal ptrSz countSc elemSz with
        | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
        | some retPtrVal => exact Or.inl ⟨.ptr retPtrVal 8, fun _ => rfl⟩

private theorem wideSliceIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value) (body : ScalarInt → MachineState → MirStepNode)
    (h : ∀ lenSc, IsIntrinsicCallFamily locals' destination targetBb (body lenSc)) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true => body lenSc s
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨_ | lenSc | _ | _, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Nat.beq ptrSz 8 with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact h lenSc
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

private theorem wideMetaOnlyIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨metaVal, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact Or.inr (Or.inr fun _ => rfl)
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

private theorem thinOrWideMetaIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value)
    (thinBody : MachineState → MirStepNode)
    (wideBody : MachineState → MirStepNode)
    (h_thin : IsIntrinsicCallFamily locals' destination targetBb thinBody)
    (h_wide : IsIntrinsicCallFamily locals' destination targetBb wideBody) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true => thinBody s
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => wideBody s
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | ptr _ ptrSz =>
    dsimp only
    cases Nat.beq ptrSz 8 with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true => exact h_thin
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨metaVal, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact h_wide
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

private def sizeOfValOneArg
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptOpt : Option RigidTy) : MirStepNode :=
  match ptOpt with
  | .some (.slice elemTy) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
        | .some elemSz =>
          writeIntrinsicScalarResult s locals' destination targetBb
            (evalSliceSizeOfVal elemSz lenSc)
        | .none => intrinsicUnresolvedLayoutStep elemTy
    | _ => MirStepNode.fail .ub
  | .some .str =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalSliceSizeOfVal 1 lenSc)
    | _ => MirStepNode.fail .ub
  | .some (.dynamic _) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .some pointeeTy =>
    match ptrArgVal with
    | .ptr _ ptrSz =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicTailIsExtern 8 pointeeTy with
        | true => MirStepNode.unsupported
        | false =>
          match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
          | .some sz =>
            match Nat.ble (signedHalfModulus 8) sz with
            | true => MirStepNode.fail .ub
            | false =>
              writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
          | .none => intrinsicUnresolvedLayoutStep pointeeTy
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => intrinsicWidePointeeStep pointeeTy
    | _ => MirStepNode.fail .ub
  | .none =>
    match isValidIntrinsicPtrArgVal ptrArgVal with
    | false => MirStepNode.fail .ub
    | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps

private theorem evalSizeOfVal_oneArg_eq
    (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts
        argOps [ptrArgVal] locals' destination targetBb =
      sizeOfValOneArg s bodyLocalDecls bodyLayouts argOps ptrArgVal
        locals' destination targetBb
        (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps) := by
  unfold evalNonSelectIntrinsicCall sizeOfValOneArg
  dsimp only
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none => rfl
  | some pt => cases pt <;> rfl

private theorem evalSizeOfValIntrinsicCall_cases
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  refine IsIntrinsicCallFamily.of_eq
    (fun s => evalSizeOfVal_oneArg_eq s target bodyLocalDecls bodyLayouts argOps
      ptrArgVal locals' destination targetBb) ?_
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none =>
    unfold sizeOfValOneArg
    cases isValidIntrinsicPtrArgVal ptrArgVal with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
  | some pointeeTy =>
    by_cases h_sl : ∃ elemTy, pointeeTy = .slice elemTy
    · rcases h_sl with ⟨elemTy, rfl⟩
      unfold sizeOfValOneArg
      refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
        (fun lenSc s =>
          match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
          | .some elemSz =>
            writeIntrinsicScalarResult s locals' destination targetBb
              (evalSliceSizeOfVal elemSz lenSc)
          | .none => intrinsicUnresolvedLayoutStep elemTy)
        fun lenSc => ?_
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
      | some elemSz =>
        exact writeIntrinsicScalarResult_cases locals' destination targetBb
          (evalSliceSizeOfVal elemSz lenSc)
    · by_cases h_str : pointeeTy = .str
      · subst h_str
        unfold sizeOfValOneArg
        exact wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
          (fun lenSc s =>
            writeIntrinsicScalarResult s locals' destination targetBb
              (evalSliceSizeOfVal 1 lenSc))
          fun lenSc =>
            writeIntrinsicScalarResult_cases locals' destination targetBb
              (evalSliceSizeOfVal 1 lenSc)
      · by_cases h_dyn : ∃ preds, pointeeTy = .dynamic preds
        · rcases h_dyn with ⟨_, rfl⟩
          unfold sizeOfValOneArg
          exact wideMetaOnlyIntrinsic_family locals' destination targetBb ptrArgVal
        · refine IsIntrinsicCallFamily.of_eq (g := fun s =>
            match ptrArgVal with
            | .ptr _ ptrSz =>
              match Nat.beq ptrSz 8 with
              | false => MirStepNode.fail .ub
              | true =>
                match intrinsicTailIsExtern 8 pointeeTy with
                | true => MirStepNode.unsupported
                | false =>
                  match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
                  | .some sz =>
                    match Nat.ble (signedHalfModulus 8) sz with
                    | true => MirStepNode.fail .ub
                    | false =>
                      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
                  | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
              match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
              | false => MirStepNode.fail .ub
              | true => intrinsicWidePointeeStep pointeeTy
            | _ => MirStepNode.fail .ub) (fun s => ?_) ?_
          · unfold sizeOfValOneArg
            cases pointeeTy <;>
              first
              | exact False.elim (h_sl ⟨_, rfl⟩)
              | exact False.elim (h_str rfl)
              | exact False.elim (h_dyn ⟨_, rfl⟩)
              | rfl
          · refine thinOrWideMetaIntrinsic_family locals' destination targetBb ptrArgVal _ _ ?_
              (intrinsicWidePointeeStep_cases locals' destination targetBb pointeeTy)
            cases intrinsicTailIsExtern 8 pointeeTy with
            | true => exact Or.inr (Or.inr fun _ => rfl)
            | false =>
              dsimp only
              cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
              | none =>
                exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
              | some sz =>
                dsimp only
                cases Nat.ble (signedHalfModulus 8) sz with
                | true => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
                | false => exact Or.inl ⟨.scalar ⟨sz, 8⟩, fun _ => rfl⟩

private def alignOfValOneArg
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptOpt : Option RigidTy) : MirStepNode :=
  match ptOpt with
  | .some (.slice elemTy) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSz, .some alignBytes =>
          match evalSliceSizeOfVal elemSz lenSc with
          | .some _ =>
            writeIntrinsicReturn s locals' destination targetBb
              (.scalar ⟨alignBytes, 8⟩)
          | .none => MirStepNode.fail .ub
        | _, _ => intrinsicUnresolvedLayoutStep elemTy
    | _ => MirStepNode.fail .ub
  | .some .str =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match evalSliceSizeOfVal 1 lenSc with
        | .some _ =>
          writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
        | .none => MirStepNode.fail .ub
    | _ => MirStepNode.fail .ub
  | .some (.dynamic _) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .some pointeeTy =>
    match ptrArgVal with
    | .ptr _ ptrSz =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicTailIsExtern 8 pointeeTy with
        | true => MirStepNode.unsupported
        | false =>
          match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
          | .some alignBytes =>
            writeIntrinsicReturn s locals' destination targetBb
              (.scalar ⟨alignBytes, 8⟩)
          | .none => intrinsicUnresolvedLayoutStep pointeeTy
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => intrinsicWidePointeeStep pointeeTy
    | _ => MirStepNode.fail .ub
  | .none =>
    match isValidIntrinsicPtrArgVal ptrArgVal with
    | false => MirStepNode.fail .ub
    | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps

private theorem evalAlignOfVal_oneArg_eq
    (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts
        argOps [ptrArgVal] locals' destination targetBb =
      alignOfValOneArg s bodyLocalDecls bodyLayouts argOps ptrArgVal
        locals' destination targetBb
        (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps) := by
  unfold evalNonSelectIntrinsicCall alignOfValOneArg
  dsimp only
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none => rfl
  | some pt => cases pt <;> rfl

private theorem evalAlignOfValIntrinsicCall_cases
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  refine IsIntrinsicCallFamily.of_eq
    (fun s => evalAlignOfVal_oneArg_eq s target bodyLocalDecls bodyLayouts argOps
      ptrArgVal locals' destination targetBb) ?_
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none =>
    unfold alignOfValOneArg
    cases isValidIntrinsicPtrArgVal ptrArgVal with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
  | some pointeeTy =>
    by_cases h_sl : ∃ elemTy, pointeeTy = .slice elemTy
    · rcases h_sl with ⟨elemTy, rfl⟩
      unfold alignOfValOneArg
      refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
        (fun lenSc s =>
          match
            intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
            intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
          with
          | .some elemSz, .some alignBytes =>
            match evalSliceSizeOfVal elemSz lenSc with
            | .some _ =>
              writeIntrinsicReturn s locals' destination targetBb
                (.scalar ⟨alignBytes, 8⟩)
            | .none => MirStepNode.fail .ub
          | _, _ => intrinsicUnresolvedLayoutStep elemTy)
        fun lenSc => ?_
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
      | some elemSz =>
        cases intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy with
        | none =>
          exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
        | some alignBytes =>
          dsimp only
          cases evalSliceSizeOfVal elemSz lenSc with
          | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
          | some _ => exact Or.inl ⟨.scalar ⟨alignBytes, 8⟩, fun _ => rfl⟩
    · by_cases h_str : pointeeTy = .str
      · subst h_str
        unfold alignOfValOneArg
        refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
          (fun lenSc s =>
            match evalSliceSizeOfVal 1 lenSc with
            | .some _ =>
              writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
            | .none => MirStepNode.fail .ub)
          fun lenSc => ?_
        cases evalSliceSizeOfVal 1 lenSc with
        | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
        | some _ => exact Or.inl ⟨.scalar ⟨1, 8⟩, fun _ => rfl⟩
      · by_cases h_dyn : ∃ preds, pointeeTy = .dynamic preds
        · rcases h_dyn with ⟨_, rfl⟩
          unfold alignOfValOneArg
          exact wideMetaOnlyIntrinsic_family locals' destination targetBb ptrArgVal
        · refine IsIntrinsicCallFamily.of_eq (g := fun s =>
            match ptrArgVal with
            | .ptr _ ptrSz =>
              match Nat.beq ptrSz 8 with
              | false => MirStepNode.fail .ub
              | true =>
                match intrinsicTailIsExtern 8 pointeeTy with
                | true => MirStepNode.unsupported
                | false =>
                  match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
                  | .some alignBytes =>
                    writeIntrinsicReturn s locals' destination targetBb
                      (.scalar ⟨alignBytes, 8⟩)
                  | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
              match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
              | false => MirStepNode.fail .ub
              | true => intrinsicWidePointeeStep pointeeTy
            | _ => MirStepNode.fail .ub) (fun s => ?_) ?_
          · unfold alignOfValOneArg
            cases pointeeTy <;>
              first
              | exact False.elim (h_sl ⟨_, rfl⟩)
              | exact False.elim (h_str rfl)
              | exact False.elim (h_dyn ⟨_, rfl⟩)
              | rfl
          · refine thinOrWideMetaIntrinsic_family locals' destination targetBb ptrArgVal _ _ ?_
              (intrinsicWidePointeeStep_cases locals' destination targetBb pointeeTy)
            cases intrinsicTailIsExtern 8 pointeeTy with
            | true => exact Or.inr (Or.inr fun _ => rfl)
            | false =>
              dsimp only
              cases intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
              | none =>
                exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
              | some alignBytes =>
                exact Or.inl ⟨.scalar ⟨alignBytes, 8⟩, fun _ => rfl⟩

private theorem evalNonSelectIntrinsicCall_cases
    (kind : RustIntrinsicKind)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    (∃ retVal,
      ∀ s : MachineState,
        evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb =
          writeIntrinsicReturn s locals' destination targetBb retVal) ∨
    (∃ fk, ∀ s : MachineState,
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb = MirStepNode.fail fk) ∨
    (∀ s : MachineState,
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb = MirStepNode.unsupported) := by
  change IsIntrinsicCallFamily locals' destination targetBb
    (fun s =>
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb)
  cases kind with
  | ubChecks =>
    cases argVals with
    | nil => exact Or.inl ⟨.scalar ⟨1, 1⟩, fun _ => rfl⟩
    | cons _ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | constEvalSelect =>
    exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | ctlz =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtlz
  | ctlzNonzero =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtlzNonzero
  | cttz =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCttz
  | cttzNonzero =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCttzNonzero
  | ctpop =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtpop
  | bswap =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalBswap
  | bitreverse =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalBitreverse
  | wrappingAdd =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingAdd lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingAdd lhs rhs)
  | wrappingSub =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingSub lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingSub lhs rhs)
  | wrappingMul =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingMul lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingMul lhs rhs)
  | saturatingAdd =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => Trusted.Rustc.V2026_06_01.MirSemantics.evalSaturatingAdd lhs rhs flag)
  | saturatingSub =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => Trusted.Rustc.V2026_06_01.MirSemantics.evalSaturatingSub lhs rhs flag)
  | uncheckedShl =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedShl lhs rhs flag)
  | uncheckedShr =>
    refine binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        match
          resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (sameRhsTy := false),
          resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps
        with
        | .some lhsSigned, .some rhsSigned =>
          writeIntrinsicScalarResult s locals' destination targetBb
            (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
        | _, _ => MirStepNode.unsupported)
      fun lhs rhs => ?_
    cases resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (sameRhsTy := false) with
    | none => exact Or.inr (Or.inr fun _ => rfl)
    | some lhsSigned =>
      cases resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps with
      | none => exact Or.inr (Or.inr fun _ => rfl)
      | some rhsSigned =>
        exact writeIntrinsicScalarResult_cases locals' destination targetBb
          (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
  | uncheckedAdd =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedAdd lhs rhs flag)
  | uncheckedSub =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedSub lhs rhs flag)
  | uncheckedMul =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedMul lhs rhs flag)
  | uncheckedDiv =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedDiv lhs rhs flag)
  | uncheckedRem =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedRem lhs rhs flag)
  | threeWayCompare =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (allowChar := true))
      (fun lhs rhs flag => evalThreeWayCompare lhs rhs flag)
  | arithOffset =>
    exact arithOffsetIntrinsic_family target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb
  | sizeOfVal =>
    exact evalSizeOfValIntrinsicCall_cases target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb
  | alignOfVal =>
    exact evalAlignOfValIntrinsicCall_cases target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb

private theorem writeIntrinsicReturn_pushBaseStack_of_noCallWP
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (ms : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value)
    {Q : MirExecState → Prop} {P : Value → Memory → Prop}
    (h_st :
      evalNodeNoCallWP Q (mirNormalPost P)
        (writeIntrinsicReturn ms locals' destination targetBb retVal)) :
    ∃ nextSt : MachineState,
      writeIntrinsicReturn ms locals' destination targetBb retVal =
        MirStepNode.step nextSt ∧
      writeIntrinsicReturn (MachineState.pushBaseStack calleeBody baseStack ms)
        locals' destination targetBb retVal =
        MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack nextSt) := by
  unfold writeIntrinsicReturn at h_st ⊢
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  cases h_wr : writePlaceValue locals' ms.memory.borrows destination retVal with
  | ub => rw [h_wr] at h_st; exact False.elim h_st
  | unsupported => rw [h_wr] at h_st; exact False.elim h_st
  | ok updL =>
    exact ⟨{ frame := { ms.frame with blockIdx := targetBb, stmtIdx := 0, locals := updL }
             memory := ms.memory }, rfl, rfl⟩

private theorem evalNonSelectIntrinsicCall_pushBaseStack_of_noCallWP
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (kind : RustIntrinsicKind) (ms : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    {Q : MirExecState → Prop} {P : Value → Memory → Prop}
    (h_st :
      evalNodeNoCallWP Q (mirNormalPost P)
        (evalNonSelectIntrinsicCall kind ms target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)) :
    ∃ nextSt : MachineState,
      evalNonSelectIntrinsicCall kind ms target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb =
        MirStepNode.step nextSt ∧
      evalNonSelectIntrinsicCall kind
        (MachineState.pushBaseStack calleeBody baseStack ms) target
        bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb =
        MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack nextSt) := by
  rcases evalNonSelectIntrinsicCall_cases kind target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb with ⟨retVal, h_wr⟩ | ⟨fk, h_fl⟩ | h_un
  · rw [h_wr ms] at h_st ⊢
    rw [h_wr (MachineState.pushBaseStack calleeBody baseStack ms)]
    exact writeIntrinsicReturn_pushBaseStack_of_noCallWP calleeBody baseStack
      ms locals' destination targetBb retVal h_st
  · rw [h_fl ms] at h_st; exact False.elim h_st
  · rw [h_un ms] at h_st; exact False.elim h_st

@[reducible]
def selectTupleTyOpt : List RigidTy → Option RigidTy
  | firstTy :: _ => some firstTy
  | [] => none

@[reducible]
def selectRtFnOpOpt : List Operand → Option Operand
  | _ :: _ :: rtOp :: _ => some rtOp
  | _ => none

private def evalConstEvalSelectThree
    (s : MachineState) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (tupleArgVal rtFnVal : Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction) :
    MirStepNode :=
  let tupleTyOpt := selectTupleTyOpt target.typeArgs
  match unpackConstEvalSelectArgs? tupleArgVal tupleTyOpt with
  | .none => MirStepNode.fail .ub
  | .some unpackedArgs =>
    match
      resolveConstEvalSelectTarget? s target bodyLocalDecls bodyLayouts
        (selectRtFnOpOpt argOps) rtFnVal (length unpackedArgs)
    with
    | .none => MirStepNode.fail .ub
    | .some rtTarget =>
      match lookupCallee s.memory.callees bodyLayouts rtTarget.defPath rtTarget.typeArgs s.memory.traitImpls with
      | .some calleeBody =>
        match
          Bool.and (Nat.beq calleeBody.argCount (length unpackedArgs))
            (Bool.and (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
              (checkCalleeTargetCompatible rtTarget calleeBody (length unpackedArgs)))
        with
        | false => MirStepNode.fail .ub
        | true =>
          match currentBody with
          | .none => MirStepNode.unsupported
          | .some callerBody =>
            MirStepNode.step
              (pushCalleeFrame s callerBody locals' destination targetBb calleeBody unpackedArgs unwind)
      | .none =>
        match rtTarget.isIndirect with
        | true =>
          MirStepNode.extCall
            { defPath := rtTarget.defPath, typeArgs := rtTarget.typeArgs, args := unpackedArgs, memory := s.memory }
            (resumeExternalCall s locals' destination targetBb unwind)
        | false =>
          let selectArgOps := constEvalSelectTupleArgOps tupleTyOpt
          match isDirectExactDivTarget rtTarget with
          | true =>
            match unpackedArgs with
            | .scalar lhs :: .scalar rhs :: .nil =>
              let rtTarget' := withConstEvalSelectIntrinsicTypeArgs rtTarget tupleTyOpt false
              match resolveIntrinsicIsSigned rtTarget' bodyLocalDecls bodyLayouts selectArgOps with
              | .none => MirStepNode.unsupported
              | .some isSigned =>
                writeIntrinsicScalarResult s locals' destination targetBb (evalExactDiv lhs rhs isSigned)
            | _ => MirStepNode.fail .ub
          | false =>
            match classifyRustIntrinsic? rtTarget.defPath with
            | .some .constEvalSelect => MirStepNode.fail .ub
            | .some rtKind =>
              let rtTarget' :=
                withConstEvalSelectIntrinsicTypeArgs rtTarget tupleTyOpt (isPtrPointeeIntrinsicKind rtKind)
              evalNonSelectIntrinsicCall rtKind s rtTarget' bodyLocalDecls bodyLayouts
                selectArgOps unpackedArgs locals' destination targetBb
            | .none =>
              match isUnreachableCallTarget rtTarget.defPath with
              | true => MirStepNode.fail .ub
              | false =>
                match isAbortingPanicDefPath rtTarget.defPath with
                | true => MirStepNode.retOutcome .abort
                | false =>
                  match isUnwindingPanicDefPath rtTarget.defPath with
                  | true =>
                    match applyUnwindAction s locals' s.memory unwind with
                    | .running nextState => MirStepNode.step nextState
                    | .halted out => MirStepNode.retOutcome out
                    | .faulted fk => MirStepNode.fail fk
                  | false =>
                    MirStepNode.extCall
                      { defPath := rtTarget.defPath, typeArgs := rtTarget.typeArgs, args := unpackedArgs, memory := s.memory }
                      (resumeExternalCall s locals' destination targetBb unwind)

private theorem evalDirectRustIntrinsic?_constEvalSelect_three
    (s : MachineState) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (tupleArgVal ctFnVal rtFnVal : Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : classifyRustIntrinsic? target.defPath = some .constEvalSelect) :
    evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
      argOps [tupleArgVal, ctFnVal, rtFnVal] locals' destination targetBb unwind =
    some (evalConstEvalSelectThree s currentBody target bodyLocalDecls bodyLayouts
      argOps tupleArgVal rtFnVal locals' destination targetBb unwind) := by
  unfold evalDirectRustIntrinsic? evalConstEvalSelectThree
  rw [h_cl]
  rcases target.typeArgs with _ | ⟨_, _⟩ <;>
    (rcases argOps with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl)

private theorem evalDirectRustIntrinsic?_nonSelect
    (s : MachineState) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    {rk : RustIntrinsicKind}
    (h_cl : classifyRustIntrinsic? target.defPath = some rk)
    (h_ne : rk ≠ .constEvalSelect) :
    evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb unwind =
    some (evalNonSelectIntrinsicCall rk s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb) := by
  unfold evalDirectRustIntrinsic?
  rw [h_cl]
  cases rk <;> first | exact False.elim (h_ne rfl) | rfl

private theorem evalDirectRustIntrinsic?_pushBaseStack_of_noCallWP
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (ms : MachineState) (curBody : CapturedMir)
    (target : ResolvedCallTarget) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (stepNode : MirStepNode)
    {Q : MirExecState → Prop} {P : Value → Memory → Prop}
    (h_di :
      evalDirectRustIntrinsic? ms (some curBody) target
        curBody.localDecls curBody.layouts argOps argVals locals'
        destination targetBb unwind = some stepNode)
    (h_st : evalNodeNoCallWP Q (mirNormalPost P) stepNode) :
    ∃ nextSt : MachineState,
      stepNode = MirStepNode.step nextSt ∧
      evalDirectRustIntrinsic? (MachineState.pushBaseStack calleeBody baseStack ms)
        (some curBody) target curBody.localDecls curBody.layouts argOps
        argVals locals' destination targetBb unwind =
        some (MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack nextSt)) := by
  cases h_cl : classifyRustIntrinsic? target.defPath with
  | none =>
    unfold evalDirectRustIntrinsic? at h_di
    rw [h_cl] at h_di
    cases h_di
  | some rk =>
    by_cases h_cs : rk = .constEvalSelect
    · subst h_cs
      rcases argVals with _ | ⟨tupleArgVal, _ | ⟨ctFnVal, _ | ⟨rtFnVal, _ | _⟩⟩⟩
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; exact False.elim h_st
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; exact False.elim h_st
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; exact False.elim h_st
      · rw [evalDirectRustIntrinsic?_constEvalSelect_three _ _ _ _ _ _ _ _ _ _ _ _ _ h_cl] at h_di ⊢
        injection h_di with h_sn
        subst h_sn
        revert h_st
        unfold evalConstEvalSelectThree
        dsimp only
        cases unpackConstEvalSelectArgs? tupleArgVal (selectTupleTyOpt target.typeArgs) with
        | none => intro h_st; exact False.elim h_st
        | some unpackedArgs =>
          dsimp only
          have h_res_eq :
              resolveConstEvalSelectTarget?
                (MachineState.pushBaseStack calleeBody baseStack ms) target
                curBody.localDecls curBody.layouts
                (selectRtFnOpOpt argOps) rtFnVal (length unpackedArgs) =
              resolveConstEvalSelectTarget? ms target curBody.localDecls
                curBody.layouts (selectRtFnOpOpt argOps) rtFnVal
                (length unpackedArgs) := rfl
          rw [h_res_eq]
          cases
            resolveConstEvalSelectTarget? ms target curBody.localDecls
              curBody.layouts (selectRtFnOpOpt argOps) rtFnVal
              (length unpackedArgs) with
          | none => intro h_st; exact False.elim h_st
          | some rtTarget =>
            dsimp only
            have h_lk_eq :
                lookupCallee
                  (MachineState.pushBaseStack calleeBody baseStack ms).memory.callees
                  curBody.layouts rtTarget.defPath rtTarget.typeArgs
                  (MachineState.pushBaseStack calleeBody baseStack ms).memory.traitImpls =
                lookupCallee ms.memory.callees curBody.layouts rtTarget.defPath
                  rtTarget.typeArgs ms.memory.traitImpls := rfl
            rw [h_lk_eq]
            cases
              lookupCallee ms.memory.callees curBody.layouts
                rtTarget.defPath rtTarget.typeArgs ms.memory.traitImpls with
            | some subCallee =>
              dsimp only
              cases
                Bool.and (Nat.beq subCallee.argCount (length unpackedArgs))
                  (Bool.and (Bool.not (callConvEq subCallee.fnAbi.conv .rustIntrinsic))
                    (checkCalleeTargetCompatible rtTarget subCallee (length unpackedArgs))) with
              | false => intro h_st; exact False.elim h_st
              | true =>
                intro _
                exact ⟨pushCalleeFrame ms curBody locals' destination targetBb
                  subCallee unpackedArgs unwind, rfl, rfl⟩
            | none =>
              dsimp only
              cases rtTarget.isIndirect with
              | true => intro h_st; exact False.elim h_st
              | false =>
                dsimp only
                cases isDirectExactDivTarget rtTarget with
                | true =>
                  dsimp only
                  rcases unpackedArgs with _ | ⟨_ | lhs | _ | _, _ | ⟨_ | rhs | _ | _, _ | _⟩⟩ <;>
                    try (intro h_st; exact False.elim h_st)
                  dsimp only
                  cases
                    resolveIntrinsicIsSigned
                      (withConstEvalSelectIntrinsicTypeArgs rtTarget
                        (selectTupleTyOpt target.typeArgs) false)
                      curBody.localDecls curBody.layouts
                      (constEvalSelectTupleArgOps (selectTupleTyOpt target.typeArgs)) with
                  | none => intro h_st; exact False.elim h_st
                  | some isSigned =>
                    dsimp only [writeIntrinsicScalarResult]
                    cases evalExactDiv lhs rhs isSigned with
                    | none => intro h_st; exact False.elim h_st
                    | some retSc =>
                      intro h_st
                      rcases writeIntrinsicReturn_pushBaseStack_of_noCallWP
                          calleeBody baseStack ms locals' destination targetBb
                          (.scalar retSc) h_st with ⟨nextSt, h1, h2⟩
                      exact ⟨nextSt, h1, congrArg some h2⟩
                | false =>
                  dsimp only
                  cases classifyRustIntrinsic? rtTarget.defPath with
                  | some rtKind =>
                    cases rtKind <;>
                      first
                      | (intro h_st; exact False.elim h_st)
                      | (dsimp only
                         intro h_st
                         rcases evalNonSelectIntrinsicCall_pushBaseStack_of_noCallWP
                             calleeBody baseStack _ ms _ curBody.localDecls
                             curBody.layouts _ unpackedArgs locals' destination targetBb h_st with
                           ⟨nextSt, h1, h2⟩
                         exact ⟨nextSt, h1, congrArg some h2⟩)
                  | none =>
                    dsimp only
                    cases isUnreachableCallTarget rtTarget.defPath with
                    | true => intro h_st; exact False.elim h_st
                    | false =>
                      dsimp only
                      cases isAbortingPanicDefPath rtTarget.defPath with
                      | true => intro h_st; exact False.elim h_st
                      | false =>
                        dsimp only
                        cases isUnwindingPanicDefPath rtTarget.defPath with
                        | false => intro h_st; exact False.elim h_st
                        | true =>
                          dsimp only
                          intro h_st
                          have h_np :
                              applyUnwindAction ms locals' ms.memory unwind ≠
                                .halted .panic := by
                            intro hp; rw [hp] at h_st; exact h_st
                          have h_ap_eq := applyUnwindAction_pushBaseStack_of_ne_panic
                            calleeBody baseStack ms locals' unwind h_np
                          change
                            applyUnwindAction
                              (MachineState.pushBaseStack calleeBody baseStack ms)
                              locals'
                              (MachineState.pushBaseStack calleeBody baseStack ms).memory
                              unwind = _ at h_ap_eq
                          rw [h_ap_eq]
                          cases h_ap : applyUnwindAction ms locals' ms.memory unwind with
                          | running nextSt => exact ⟨nextSt, rfl, rfl⟩
                          | halted out =>
                            rw [h_ap] at h_st
                            cases out with
                            | panic => exact False.elim h_st
                            | abort => exact False.elim h_st
                            | normal rv =>
                              exact False.elim
                                (applyUnwindAction_ne_normal ms locals' ms.memory unwind rv h_ap)
                          | faulted _ => rw [h_ap] at h_st; exact False.elim h_st
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; exact False.elim h_st
    · rw [evalDirectRustIntrinsic?_nonSelect _ _ _ _ _ _ _ _ _ _ _ h_cl h_cs] at h_di ⊢
      injection h_di with h_sn
      subst h_sn
      rcases evalNonSelectIntrinsicCall_pushBaseStack_of_noCallWP calleeBody
          baseStack rk ms target curBody.localDecls curBody.layouts argOps
          argVals locals' destination targetBb h_st with ⟨nextSt, h1, h2⟩
      exact ⟨nextSt, h1, congrArg some h2⟩

/--
Core stack-frame suffix simulation theorem (`wpMirExecNoCallSym_pushCalleeFrame`):
Suppose `calleeBody` converges without external calls (`wpMirExecNoCallSym`) from
an unstacked entry state `(initPureState calleeBody argVals).toMachineState
{ s.memory with callStack := [], activeCallee := none }` to `mirNormalPost P`.
Then from `pushCalleeFrame s callerBody locals' destination targetBb calleeBody
argVals unwind`, `outerBody` steps (`MirStepsConverges`) across the entire
execution of `calleeBody` and its root `.return_` directly into the resumed
caller frame `{ frame := { s.frame with blockIdx := targetBb, stmtIdx := 0,
locals := updatedLocals }, memory := { memOut with callStack :=
s.memory.callStack, activeCallee := some callerBody, activeProtectors :=
s.memory.activeProtectors } }` whenever `writePlaceValue` succeeds for every
`(retVal, memOut)` satisfying `P retVal memOut`.
-/
theorem wpMirExecNoCallSym_pushCalleeFrame
    {outerBody callerBody calleeBody : CapturedMir}
    {s : MachineState}
    {locals' : List LocalSlot}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {argVals : List Value}
    {unwind : UnwindAction}
    {P : Value → Memory → Prop}
    {mid : MachineState → Prop}
    {post : MirOutcome → Prop}
    (h_callee :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { s.memory with callStack := [], activeCallee := none })
        (mirNormalPost P))
    (h_prot_nil : s.memory.activeProtectors = [])
    (h_cont :
      ∀ (retVal : Value) (memOut : Memory),
        P retVal memOut →
        ∃ updatedLocals : List LocalSlot,
          writePlaceValue locals' memOut.borrows destination retVal =
            .ok updatedLocals ∧
          mid {
            frame := {
              s.frame with
              blockIdx := targetBb
              stmtIdx := 0
              locals := updatedLocals
            }
            memory := {
              memOut with
              callStack := s.memory.callStack
              activeCallee := some callerBody
              activeProtectors := []
            }
          }) :
    MirStepsConverges outerBody
      (pushCalleeFrame s callerBody locals' destination targetBb calleeBody
        argVals unwind)
      mid post := by
  rcases h_callee with ⟨fuel, h_wp⟩
  let savedCaller : SavedCallerFrame := {
    callerBody := callerBody
    frame := { s.frame with locals := locals' }
    destination := destination
    returnTarget := targetBb
    calleeProtectors := s.memory.activeProtectors
    returnUnwind := unwind
    isDiverging := false
  }
  let baseStack : List SavedCallerFrame := savedCaller :: s.memory.callStack
  have h_restore_prot : restoreCallerProtectors savedCaller = [] := by
    simp [savedCaller, restoreCallerProtectors, h_prot_nil]
  suffices ∀ (f : Nat) (st : MirExecState),
      wpMirExecNoCallSym f calleeBody st (mirNormalPost P) →
      (∀ rv m, st = .halted (.normal (rv, m)) → False) →
      ∃ f_out : Nat,
        wpMirExecStepsSym f_out outerBody
          (MirExecState.pushBaseStack calleeBody baseStack st)
          (fun
            | .running ms' => mid ms'
            | .halted out => post out
            | .faulted _ => False)
          post by
    have h_init_eq :
        MirExecState.pushBaseStack calleeBody baseStack
          (.running (initMachineStateWithMemory calleeBody argVals
            { s.memory with callStack := [], activeCallee := none })) =
        .running (pushCalleeFrame s callerBody locals' destination targetBb
          calleeBody argVals unwind) := rfl
    rcases this fuel _ h_wp (fun _ _ h_eq => by cases h_eq) with ⟨f_out, hf_out⟩
    rw [h_init_eq] at hf_out
    exact ⟨f_out, hf_out⟩
  intro f
  induction f with
  | zero =>
    intro st h_st
    exact False.elim h_st
  | succ f' ih =>
    intro st h_st h_not_halted
    unfold wpMirExecNoCallSym at h_st
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_st
    have mkStep :
        ∀ {f_sub : Nat},
          evalNodeNoCallWP
            (fun st' =>
              wpMirExecStepsSym f_sub outerBody st'
                (fun
                  | .running ms' => mid ms'
                  | .halted out => post out
                  | .faulted _ => False)
                post)
            post
            (stepMirState outerBody
              (MirExecState.pushBaseStack calleeBody baseStack st)) →
          ∃ f_out : Nat,
            wpMirExecStepsSym f_out outerBody
              (MirExecState.pushBaseStack calleeBody baseStack st)
              (fun
                | .running ms' => mid ms'
                | .halted out => post out
                | .faulted _ => False)
              post := by
      intro f_sub h_node
      refine ⟨f_sub + 1, ?_⟩
      unfold wpMirExecStepsSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
      exact h_node
    cases st with
    | faulted fk =>
      exact False.elim h_st
    | halted out =>
      cases out with
      | normal rv => exact False.elim (h_not_halted rv.1 rv.2 rfl)
      | panic => exact False.elim h_st
      | abort => exact False.elim h_st
    | running ms =>
      dsimp only [MirExecState.pushBaseStack, stepMirState] at h_st ⊢
      have h_act :
          (MachineState.pushBaseStack calleeBody baseStack ms).memory.activeCallee.getD outerBody =
            ms.memory.activeCallee.getD calleeBody := rfl
      let curBody := ms.memory.activeCallee.getD calleeBody
      rw [stepMirFn_eq_ite] at h_st
      dsimp only at h_st
      have liftTau :
          ∀ {st_un : MirExecState},
            stepMirFn outerBody (MachineState.pushBaseStack calleeBody baseStack ms) =
              .tau (MirExecState.pushBaseStack calleeBody baseStack st_un) →
            wpMirExecNoCallSym f' calleeBody st_un (mirNormalPost P) →
            (∀ rv m, st_un = .halted (.normal (rv, m)) → False) →
            ∃ f_out : Nat,
              wpMirExecStepsSym f_out outerBody
                (.running (MachineState.pushBaseStack calleeBody baseStack ms))
                (fun
                  | .running ms' => mid ms'
                  | .halted out => post out
                  | .faulted _ => False)
                post := by
        intro st_un h_step_eq h_next h_nh
        rcases ih st_un h_next h_nh with ⟨f_sub, hf_sub⟩
        refine mkStep (f_sub := f_sub) ?_
        dsimp only [MirExecState.pushBaseStack, stepMirState]
        rw [h_step_eq]
        exact hf_sub
      have liftObs :
          ∀ {obs : MirObsE.I} {k_un : PUnit → MirExecState},
            stepMirFn outerBody (MachineState.pushBaseStack calleeBody baseStack ms) =
              .vis (.inr (.inl obs))
                (fun u => MirExecState.pushBaseStack calleeBody baseStack (k_un u)) →
            wpMirExecNoCallSym f' calleeBody (k_un PUnit.unit) (mirNormalPost P) →
            (∀ rv m, k_un PUnit.unit = .halted (.normal (rv, m)) → False) →
            ∃ f_out : Nat,
              wpMirExecStepsSym f_out outerBody
                (.running (MachineState.pushBaseStack calleeBody baseStack ms))
                (fun
                  | .running ms' => mid ms'
                  | .halted out => post out
                  | .faulted _ => False)
                post := by
        intro obs k_un h_step_eq h_next h_nh
        rcases ih (k_un PUnit.unit) h_next h_nh with ⟨f_sub, hf_sub⟩
        refine mkStep (f_sub := f_sub) ?_
        dsimp only [MirExecState.pushBaseStack, stepMirState]
        rw [h_step_eq]
        exact hf_sub
      have h_phase_or :
          (∃ tag, curBody.phase = .other tag) ∨
          (evalNodeNoCallWP
              (fun st' => wpMirExecNoCallSym f' calleeBody st' (mirNormalPost P))
              (mirNormalPost P)
              (match get? curBody.basicBlocks ms.frame.blockIdx with
               | none => MirStepNode.fail .ub
               | some bb =>
                 match get? bb.statements ms.frame.stmtIdx with
                 | some stmt =>
                   evalStmt ms stmt curBody.localDecls curBody.layouts
                 | none =>
                   if ms.frame.stmtIdx == length bb.statements then
                     evalTerminator ms bb.terminator (some curBody)
                   else MirStepNode.fail .ub) ∧
           stepMirFn outerBody (MachineState.pushBaseStack calleeBody baseStack ms) =
              match get? curBody.basicBlocks ms.frame.blockIdx with
              | none => MirStepNode.fail .ub
              | some bb =>
                match get? bb.statements ms.frame.stmtIdx with
                | some stmt =>
                  evalStmt (MachineState.pushBaseStack calleeBody baseStack ms)
                    stmt curBody.localDecls curBody.layouts
                | none =>
                  if ms.frame.stmtIdx == length bb.statements then
                    evalTerminator (MachineState.pushBaseStack calleeBody baseStack ms)
                      bb.terminator (some curBody)
                  else MirStepNode.fail .ub) := by
        cases h_ph : isOtherPhase curBody.phase with
        | true => exact Or.inl (isOtherPhase_eq_true_iff h_ph)
        | false =>
          refine Or.inr ⟨?_, ?_⟩
          · rw [h_ph] at h_st; exact h_st
          · rw [stepMirFn_eq_ite]
            dsimp only
            rw [h_act, h_ph]
            rfl
      rcases h_phase_or with ⟨tag, h_ph⟩ | ⟨h_st_body, h_step_body⟩
      · rw [h_ph] at h_st
        exact False.elim h_st
      · clear h_st
        have h_st := h_st_body
        clear h_st_body
        cases h_bb : get? curBody.basicBlocks (ms.frame.blockIdx : Nat) with
        | none =>
          rw [h_bb] at h_st
          exact False.elim h_st
        | some bb =>
          rw [h_bb] at h_st h_step_body
          dsimp only at h_st h_step_body
          cases h_stmt : get? bb.statements (ms.frame.stmtIdx : Nat) with
          | some stmt =>
            rw [h_stmt] at h_st h_step_body
            dsimp only at h_st h_step_body
            rw [evalStmt_pushBaseStack calleeBody baseStack ms stmt
              curBody.localDecls curBody.layouts] at h_step_body
            cases h_ev : evalStmt ms stmt curBody.localDecls curBody.layouts with
            | ret out =>
              rcases evalStmt_isStmtNode ms stmt curBody.localDecls curBody.layouts with
                ⟨_, h_sh⟩ | ⟨_, h_sh⟩ | h_sh <;> rw [h_sh] at h_ev <;> cases h_ev
            | tau st' =>
              rw [h_ev] at h_st h_step_body
              dsimp only [MirStepNode.pushBaseStack, evalNodeNoCallWP] at h_st h_step_body
              refine liftTau h_step_body h_st (fun rv m h_halt => ?_)
              rcases evalStmt_isStmtNode ms stmt curBody.localDecls curBody.layouts with
                ⟨_, h_sh⟩ | ⟨_, h_sh⟩ | h_sh
              · rw [h_sh, h_halt] at h_ev; cases h_ev
              · rw [h_sh] at h_ev; cases h_ev
              · rw [h_sh] at h_ev; cases h_ev
            | vis i k =>
              rw [h_ev] at h_st h_step_body
              rcases i with fk | (obs | req)
              · exact False.elim h_st
              · dsimp only [MirStepNode.pushBaseStack, evalNodeNoCallWP] at h_st h_step_body
                refine liftObs (k_un := k) h_step_body h_st (fun rv m h_halt => ?_)
                rcases evalStmt_isStmtNode ms stmt curBody.localDecls curBody.layouts with
                  ⟨_, h_sh⟩ | ⟨_, h_sh⟩ | h_sh <;> rw [h_sh] at h_ev <;> cases h_ev
              · exact False.elim h_st
          | none =>
            rw [h_stmt] at h_st h_step_body
            dsimp only at h_st h_step_body
            by_cases h_len : (ms.frame.stmtIdx == length bb.statements) = true
            · simp only [h_len, ite_true] at h_st h_step_body
              rcases bb with ⟨stmts, ⟨tkind, tspan⟩, isCl⟩
              dsimp only at h_st h_step_body
              cases tkind with
              | goto target =>
                dsimp only [evalTerminator, MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                exact liftTau
                  (st_un := .running {
                    ms with frame := { ms.frame with blockIdx := target, stmtIdx := 0 } })
                  h_step_body h_st (fun _ _ h => by cases h)
              | switchInt discr targets =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                  Memory.pushBaseStack_globals, Memory.pushBaseStack_callerLocals] at h_st h_step_body
                cases h_op : evalOperand ms.frame.locals discr ms.memory.borrows
                    ms.memory.globals curBody.layouts ms.memory.callerLocals with
                | ub => rw [h_op] at h_st; exact False.elim h_st
                | unsupported => rw [h_op] at h_st; exact False.elim h_st
                | ok v locals1 =>
                  rw [h_op] at h_st h_step_body
                  cases v with
                  | scalar sc =>
                    dsimp only [MirStepNode.emitStep, evalNodeNoCallWP] at h_st h_step_body
                    exact liftObs
                      (k_un := fun _ => .running {
                        ms with frame := {
                          blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise
                          stmtIdx := 0
                          locals := locals1 } })
                      h_step_body h_st (fun _ _ h => by cases h)
                  | _ => exact False.elim h_st
              | unreachable =>
                exact False.elim h_st
              | unwindTerminate =>
                exact False.elim h_st
              | unwindResume =>
                simp only [evalTerminator, MachineState.pushBaseStack_memory,
                  Memory.pushBaseStack_callStack] at h_st h_step_body
                have h_np : unwindFromCallStack ms.memory.callStack ms.memory ≠ .halted .panic := by
                  intro h_p; rw [h_p] at h_st; exact h_st
                have h_uw_eq := unwindFromCallStack_pushBaseStack_of_ne_panic
                  calleeBody baseStack ms.memory.callStack ms.memory h_np
                rw [h_uw_eq] at h_step_body
                cases h_uw : unwindFromCallStack ms.memory.callStack ms.memory with
                | running nextSt =>
                  rw [h_uw] at h_st h_step_body
                  dsimp only [MirExecState.pushBaseStack, MirStepNode.step,
                    evalNodeNoCallWP] at h_st h_step_body
                  exact liftTau (st_un := .running nextSt) h_step_body h_st (fun _ _ h => by cases h)
                | halted out =>
                  rw [h_uw] at h_st
                  cases out with
                  | panic => exact False.elim h_st
                  | abort => exact False.elim h_st
                  | normal rv =>
                    exact False.elim (unwindFromCallStack_ne_normal ms.memory.callStack ms.memory rv h_uw)
                | faulted fk =>
                  rw [h_uw] at h_st
                  exact False.elim h_st
              | drop place target _ =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame] at h_st h_step_body
                cases h_g : get? ms.frame.locals place.local_ with
                | none => rw [h_g] at h_st; exact False.elim h_st
                | some slot =>
                  rw [h_g] at h_st h_step_body
                  cases slot with
                  | dead => exact False.elim h_st
                  | uninit =>
                    cases h_pr : place.projection with
                    | nil =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_s : set? ms.frame.locals place.local_ .uninit with
                      | none => rw [h_s] at h_st; exact False.elim h_st
                      | some l' =>
                        rw [h_s] at h_st h_step_body
                        dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                        exact liftTau
                          (st_un := .running {
                            ms with frame := { blockIdx := target, stmtIdx := 0, locals := l' } })
                          h_step_body h_st (fun _ _ h => by cases h)
                    | cons _ _ =>
                      rw [h_pr] at h_st
                      exact False.elim h_st
                  | init rootVal =>
                    cases h_pr : place.projection with
                    | nil =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_s : set? ms.frame.locals place.local_ .uninit with
                      | none => rw [h_s] at h_st; exact False.elim h_st
                      | some l' =>
                        rw [h_s] at h_st h_step_body
                        dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                        exact liftTau
                          (st_un := .running {
                            ms with frame := { blockIdx := target, stmtIdx := 0, locals := l' } })
                          h_step_body h_st (fun _ _ h => by cases h)
                    | cons pHead pTail =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_rp : readProjectedValue ms.frame.locals rootVal (pHead :: pTail) with
                      | ok _ =>
                        rw [h_rp] at h_st h_step_body
                        dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                        exact liftTau
                          (st_un := .running {
                            ms with frame := { ms.frame with blockIdx := target, stmtIdx := 0 } })
                          h_step_body h_st (fun _ _ h => by cases h)
                      | ub => rw [h_rp] at h_st; exact False.elim h_st
                      | unsupported => rw [h_rp] at h_st; exact False.elim h_st
              | assert cond expected target aUnwind =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                  Memory.pushBaseStack_globals, Memory.pushBaseStack_callerLocals] at h_st h_step_body
                cases h_op : evalOperand ms.frame.locals cond ms.memory.borrows
                    ms.memory.globals curBody.layouts ms.memory.callerLocals with
                | ub => rw [h_op] at h_st; exact False.elim h_st
                | unsupported => rw [h_op] at h_st; exact False.elim h_st
                | ok v locals1 =>
                  rw [h_op] at h_st h_step_body
                  cases v with
                  | scalar sc =>
                    have h_assert_branch :
                        ∀ expBit : Nat,
                          evalNodeNoCallWP
                            (fun st' => wpMirExecNoCallSym f' calleeBody st' (mirNormalPost P))
                            (mirNormalPost P)
                            (match Nat.beq sc.bits expBit with
                             | true =>
                               MirStepNode.step { ms with frame := { blockIdx := target, stmtIdx := 0, locals := locals1 } }
                             | false =>
                               match applyUnwindAction ms locals1 ms.memory aUnwind with
                               | .running nextSt => MirStepNode.step nextSt
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) →
                          stepMirFn outerBody (MachineState.pushBaseStack calleeBody baseStack ms) =
                            (match Nat.beq sc.bits expBit with
                             | true =>
                               MirStepNode.step
                                 { MachineState.pushBaseStack calleeBody baseStack ms with
                                   frame := { blockIdx := target, stmtIdx := 0, locals := locals1 } }
                             | false =>
                               match applyUnwindAction (MachineState.pushBaseStack calleeBody baseStack ms)
                                   locals1 (Memory.pushBaseStack calleeBody baseStack ms.memory) aUnwind with
                               | .running nextSt => MirStepNode.step nextSt
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) →
                          ∃ f_out : Nat,
                            wpMirExecStepsSym f_out outerBody
                              (.running (MachineState.pushBaseStack calleeBody baseStack ms))
                              (fun
                                | .running ms' => mid ms'
                                | .halted out => post out
                                | .faulted _ => False)
                              post := by
                      intro expBit h_st_a h_sb_a
                      cases h_b : Nat.beq sc.bits expBit with
                      | true =>
                        rw [h_b] at h_st_a h_sb_a
                        dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st_a h_sb_a
                        exact liftTau
                          (st_un := .running {
                            ms with frame := { blockIdx := target, stmtIdx := 0, locals := locals1 } })
                          h_sb_a h_st_a (fun _ _ h => by cases h)
                      | false =>
                        rw [h_b] at h_st_a h_sb_a
                        dsimp only at h_st_a h_sb_a
                        have h_np : applyUnwindAction ms locals1 ms.memory aUnwind ≠ .halted .panic := by
                          intro h_p; rw [h_p] at h_st_a; exact h_st_a
                        have h_ap_eq := applyUnwindAction_pushBaseStack_of_ne_panic
                          calleeBody baseStack ms locals1 aUnwind h_np
                        rw [h_ap_eq] at h_sb_a
                        cases h_ap : applyUnwindAction ms locals1 ms.memory aUnwind with
                        | running nextSt =>
                          rw [h_ap] at h_st_a h_sb_a
                          dsimp only [MirExecState.pushBaseStack, MirStepNode.step,
                            evalNodeNoCallWP] at h_st_a h_sb_a
                          exact liftTau (st_un := .running nextSt) h_sb_a h_st_a (fun _ _ h => by cases h)
                        | halted out =>
                          rw [h_ap] at h_st_a
                          cases out with
                          | panic => exact False.elim h_st_a
                          | abort => exact False.elim h_st_a
                          | normal rv =>
                            exact False.elim
                              (applyUnwindAction_ne_normal ms locals1 ms.memory aUnwind rv h_ap)
                        | faulted _ =>
                          rw [h_ap] at h_st_a
                          exact False.elim h_st_a
                    cases expected with
                    | true => exact h_assert_branch 1 h_st h_step_body
                    | false => exact h_assert_branch 0 h_st h_step_body
                  | _ => exact False.elim h_st
              | tailCall func argOps =>
                simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf,
                  resolveCallTarget_pushBaseStack, MachineState.pushBaseStack_memory,
                  Memory.pushBaseStack_borrows, Memory.pushBaseStack_globals,
                  Memory.pushBaseStack_callerLocals, Memory.pushBaseStack_callees,
                  Memory.pushBaseStack_traitImpls] at h_st h_step_body
                cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                | ub => rw [h_rt] at h_st; exact False.elim h_st
                | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                | ok rTarget localsAfterFunc =>
                  rw [h_rt] at h_st h_step_body
                  dsimp only at h_st h_step_body
                  cases h_ops : evalOperands localsAfterFunc argOps ms.memory.borrows
                      ms.memory.globals curBody.layouts ms.memory.callerLocals with
                  | ub => rw [h_ops] at h_st; exact False.elim h_st
                  | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                  | ok aVals _ =>
                    rw [h_ops] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_lk : lookupCallee ms.memory.callees curBody.layouts
                        rTarget.defPath rTarget.typeArgs ms.memory.traitImpls with
                    | none => rw [h_lk] at h_st; exact False.elim h_st
                    | some subCallee =>
                      rw [h_lk] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_ck : checkCalleeTargetCompatible rTarget subCallee (length aVals) with
                      | false => rw [h_ck] at h_st; exact False.elim h_st
                      | true =>
                        rw [h_ck] at h_st h_step_body
                        dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                        exact liftTau
                          (st_un := .running (enterTailCalleeFrame ms.memory subCallee aVals))
                          h_step_body h_st (fun _ _ h => by cases h)
              | call func argOps cDest cTarget cUnwind =>
                cases cTarget with
                | none =>
                  simp only [evalTerminator, bodyLocalDeclsOf,
                    resolveCallTarget_pushBaseStack, MachineState.pushBaseStack_memory,
                    Memory.pushBaseStack_borrows, Memory.pushBaseStack_globals,
                    Memory.pushBaseStack_callerLocals, Memory.pushBaseStack_callees,
                    Memory.pushBaseStack_traitImpls] at h_st h_step_body
                  cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                  | ub => rw [h_rt] at h_st; exact False.elim h_st
                  | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                  | ok rTarget localsAfterFunc =>
                    rw [h_rt] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_ops : evalOperands localsAfterFunc argOps ms.memory.borrows
                        ms.memory.globals curBody.layouts ms.memory.callerLocals with
                    | ub => rw [h_ops] at h_st; exact False.elim h_st
                    | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                    | ok aVals cLocals' =>
                      rw [h_ops] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_lk : lookupCallee ms.memory.callees curBody.layouts
                          rTarget.defPath rTarget.typeArgs ms.memory.traitImpls with
                      | some subCallee =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ck : checkCalleeTargetCompatible rTarget subCallee (length aVals) with
                        | false => rw [h_ck] at h_st; exact False.elim h_st
                        | true =>
                          rw [h_ck] at h_st h_step_body
                          dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                          exact liftTau
                            (st_un := .running (pushDivergingCalleeFrame ms curBody cLocals'
                              cDest cUnwind subCallee aVals))
                            h_step_body h_st (fun _ _ h => by cases h)
                      | none =>
                        rw [h_lk] at h_st h_step_body
                        cases h_ind : rTarget.isIndirect with
                        | true => rw [h_ind] at h_st; exact False.elim h_st
                        | false =>
                          rw [h_ind] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases h_unr : isUnreachableCallTarget rTarget.defPath with
                          | true => rw [h_unr] at h_st; exact False.elim h_st
                          | false =>
                            rw [h_unr] at h_st h_step_body
                            dsimp only at h_st h_step_body
                            cases h_ab : isAbortingPanicDefPath rTarget.defPath with
                            | true => rw [h_ab] at h_st; exact False.elim h_st
                            | false =>
                              rw [h_ab] at h_st h_step_body
                              dsimp only at h_st h_step_body
                              cases h_up : isUnwindingPanicDefPath rTarget.defPath with
                              | false => rw [h_up] at h_st; exact False.elim h_st
                              | true =>
                                rw [h_up] at h_st h_step_body
                                dsimp only at h_st h_step_body
                                have h_np :
                                    applyUnwindAction ms cLocals' ms.memory cUnwind ≠
                                      .halted .panic := by
                                  intro h_p; rw [h_p] at h_st; exact h_st
                                have h_ap_eq := applyUnwindAction_pushBaseStack_of_ne_panic
                                  calleeBody baseStack ms cLocals' cUnwind h_np
                                rw [h_ap_eq] at h_step_body
                                cases h_ap : applyUnwindAction ms cLocals' ms.memory cUnwind with
                                | running nextSt =>
                                  rw [h_ap] at h_st h_step_body
                                  dsimp only [MirExecState.pushBaseStack, MirStepNode.step,
                                    evalNodeNoCallWP] at h_st h_step_body
                                  exact liftTau (st_un := .running nextSt) h_step_body h_st (fun _ _ h => by cases h)
                                | halted out =>
                                  rw [h_ap] at h_st
                                  cases out with
                                  | panic => exact False.elim h_st
                                  | abort => exact False.elim h_st
                                  | normal rv =>
                                    exact False.elim
                                      (applyUnwindAction_ne_normal ms cLocals' ms.memory cUnwind rv h_ap)
                                | faulted _ =>
                                  rw [h_ap] at h_st
                                  exact False.elim h_st
                | some cTargetBb =>
                  simp only [evalTerminator, bodyLocalDeclsOf,
                    resolveCallTarget_pushBaseStack, MachineState.pushBaseStack_memory,
                    Memory.pushBaseStack_borrows, Memory.pushBaseStack_globals,
                    Memory.pushBaseStack_callerLocals, Memory.pushBaseStack_callees,
                    Memory.pushBaseStack_traitImpls] at h_st h_step_body
                  cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                  | ub => rw [h_rt] at h_st; exact False.elim h_st
                  | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                  | ok rTarget localsAfterFunc =>
                    rw [h_rt] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_ops : evalOperands localsAfterFunc argOps ms.memory.borrows
                        ms.memory.globals curBody.layouts ms.memory.callerLocals with
                    | ub => rw [h_ops] at h_st; exact False.elim h_st
                    | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                    | ok aVals cLocals' =>
                      rw [h_ops] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_lk : lookupCallee ms.memory.callees curBody.layouts
                          rTarget.defPath rTarget.typeArgs ms.memory.traitImpls with
                      | some subCallee =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ck : checkCalleeTargetCompatible rTarget subCallee (length aVals) with
                        | false => rw [h_ck] at h_st; exact False.elim h_st
                        | true =>
                          rw [h_ck] at h_st h_step_body
                          dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                          exact liftTau
                            (st_un := .running (pushCalleeFrame ms curBody cLocals'
                              cDest cTargetBb subCallee aVals cUnwind))
                            h_step_body h_st (fun _ _ h => by cases h)
                      | none =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ed : isDirectExactDivTarget rTarget with
                        | false =>
                          rw [h_ed] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases h_ind : rTarget.isIndirect with
                          | true => rw [h_ind] at h_st; exact False.elim h_st
                          | false =>
                            rw [h_ind] at h_st h_step_body
                            dsimp only at h_st h_step_body
                            cases h_di :
                              evalDirectRustIntrinsic? ms (some curBody) rTarget
                                curBody.localDecls curBody.layouts argOps aVals
                                cLocals' cDest cTargetBb cUnwind with
                            | none => rw [h_di] at h_st; exact False.elim h_st
                            | some stepNode =>
                              rw [h_di] at h_st
                              dsimp only at h_st
                              rcases evalDirectRustIntrinsic?_pushBaseStack_of_noCallWP
                                  calleeBody baseStack ms curBody rTarget argOps
                                  aVals cLocals' cDest cTargetBb cUnwind stepNode
                                  h_di h_st with
                                ⟨nextSt, rfl, h_m2⟩
                              rw [h_m2] at h_step_body
                              dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                              exact liftTau (st_un := .running nextSt) h_step_body h_st
                                (fun _ _ h => by cases h)
                        | true =>
                          rw [h_ed] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases aVals with
                          | nil => exact False.elim h_st
                          | cons v1 tl1 =>
                            cases v1 <;> try exact False.elim h_st
                            cases tl1 with
                            | nil => exact False.elim h_st
                            | cons v2 tl2 =>
                              cases v2 <;> try exact False.elim h_st
                              cases tl2 with
                              | cons _ _ => exact False.elim h_st
                              | nil =>
                                rename_i lhsSc rhsSc
                                dsimp only at h_st h_step_body
                                cases h_sig :
                                  resolveIntrinsicIsSigned rTarget curBody.localDecls
                                    curBody.layouts argOps with
                                | none => rw [h_sig] at h_st; exact False.elim h_st
                                | some isSigned =>
                                  rw [h_sig] at h_st h_step_body
                                  dsimp only at h_st h_step_body
                                  cases h_div : evalExactDiv lhsSc rhsSc isSigned with
                                  | none => rw [h_div] at h_st; exact False.elim h_st
                                  | some retSc =>
                                    rw [h_div] at h_st h_step_body
                                    dsimp only at h_st h_step_body
                                    cases h_wr : writePlaceValue cLocals' ms.memory.borrows cDest (.scalar retSc) with
                                    | ub => rw [h_wr] at h_st; exact False.elim h_st
                                    | unsupported => rw [h_wr] at h_st; exact False.elim h_st
                                    | ok updL =>
                                      rw [h_wr] at h_st h_step_body
                                      dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                                      exact liftTau
                                        (st_un := .running {
                                          ms with frame := {
                                            ms.frame with
                                            blockIdx := cTargetBb
                                            stmtIdx := 0
                                            locals := updL } })
                                        h_step_body h_st (fun _ _ h => by cases h)
              | return_ =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_callStack,
                  Memory.pushBaseStack_borrows] at h_st h_step_body
                cases h_g : get? ms.frame.locals 0 with
                | none => rw [h_g] at h_st; exact False.elim h_st
                | some slot =>
                  rw [h_g] at h_st h_step_body
                  cases slot with
                  | uninit => exact False.elim h_st
                  | dead => exact False.elim h_st
                  | init retVal =>
                    dsimp only at h_st h_step_body
                    cases h_stk : ms.memory.callStack with
                    | cons innerCaller innerRest =>
                      rw [h_stk] at h_st h_step_body
                      dsimp only [List.cons_append] at h_st h_step_body
                      cases h_div : innerCaller.isDiverging with
                      | true => rw [h_div] at h_st; exact False.elim h_st
                      | false =>
                        rw [h_div] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_wr : writePlaceValue innerCaller.frame.locals
                            ms.memory.borrows innerCaller.destination retVal with
                        | ub => rw [h_wr] at h_st; exact False.elim h_st
                        | unsupported => rw [h_wr] at h_st; exact False.elim h_st
                        | ok updLocals =>
                          rw [h_wr] at h_st h_step_body
                          dsimp only [MirStepNode.step, evalNodeNoCallWP] at h_st h_step_body
                          exact liftTau
                            (st_un := .running {
                              frame := {
                                innerCaller.frame with
                                blockIdx := innerCaller.returnTarget
                                stmtIdx := 0
                                locals := updLocals }
                              memory := {
                                ms.memory with
                                callStack := innerRest
                                activeCallee := some innerCaller.callerBody
                                activeProtectors := restoreCallerProtectors innerCaller } })
                            h_step_body h_st (fun _ _ h => by cases h)
                    | nil =>
                      rw [h_stk] at h_st h_step_body
                      dsimp only [List.nil_append, MirStepNode.retNormal,
                        evalNodeNoCallWP, mirNormalPost, baseStack] at h_st h_step_body
                      rcases h_cont retVal ms.memory h_st with ⟨updLocals, h_wr, h_mid⟩
                      refine mkStep (f_sub := 0) ?_
                      dsimp only [MirExecState.pushBaseStack, stepMirState]
                      rw [h_step_body]
                      dsimp only [savedCaller]
                      rw [h_wr]
                      dsimp only [MirStepNode.step, evalNodeNoCallWP, wpMirExecStepsSym,
                        Memory.pushBaseStack]
                      rw [h_restore_prot]
                      exact h_mid
              | inlineAsm =>
                dsimp only [evalTerminator, evalNodeNoCallWP] at h_st
                exact False.elim h_st
            · simp only [h_len] at h_st
              exact False.elim h_st

/-! ## 8. Callee-Aware Pure Execution (`PureMirConvergesWithCallees`) & 1-Step Compositional `call_summary` -/

/--
Default upper bound on transitive inline call-stack depth (`32` frames) for
bounded syntactic callee checking (`checkPureMirWithCallees`) and compositional
call-depth guards (`callDepth < maxCallDepth`).
-/
abbrev defaultMaxCallDepth : Nat := 32

/--
Canonical pure callee-resolution memory seeding `Memory.callees := callees` and
`Memory.traitImpls := traitImpls` over `emptyMemory` (with empty heap, borrow
table, call stack, and protector list).
-/
def pureCalleeMemory
    (callees : List CapturedMir)
    (traitImpls : List TraitImplEntry := []) : Memory :=
  { emptyMemory with callees := callees, traitImpls := traitImpls }

@[simp]
theorem pureCalleeMemory_nil_nil : pureCalleeMemory [] [] = emptyMemory := rfl

@[simp]
theorem pureCalleeMemory_callees
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).callees = callees := rfl

@[simp]
theorem pureCalleeMemory_traitImpls
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).traitImpls = traitImpls := rfl

@[simp]
theorem pureCalleeMemory_borrows
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).borrows = [] := rfl

@[simp]
theorem pureCalleeMemory_globals
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).globals = [] := rfl

@[simp]
theorem pureCalleeMemory_callStack
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).callStack = [] := rfl

@[simp]
theorem pureCalleeMemory_activeCallee
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).activeCallee = none := rfl

@[simp]
theorem pureCalleeMemory_activeProtectors
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).activeProtectors = [] := rfl

@[simp]
theorem pureCalleeMemory_callerLocals
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).callerLocals = [] := rfl

@[simp]
theorem pureCalleeMemory_fnPtrs
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    (pureCalleeMemory callees traitImpls).fnPtrs = [] := rfl

@[simp]
theorem rootActiveMemory_pureCalleeMemory
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry) :
    RootActiveMemory (pureCalleeMemory callees traitImpls) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Every `MirCallE` interaction emitted by `stepMirFn` maps `MirCallAns.aborted`
to `.halted .abort` (`resumeExternalCall`, `resumeExternalDivergingCall`, and
`resumeExternalTailCall`).
-/
private theorem evalStmt_not_extCall
    (s : MachineState) (stmt : Statement)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (c : MirCallE.I) (k : MirCallE.O c → MirExecState) :
    evalStmt s stmt decls layouts ≠ .vis (.inr (.inr c)) k := by
  intro h_ev
  rcases evalStmt_isStmtNode s stmt decls layouts with
    ⟨_, h_sh⟩ | ⟨_, h_sh⟩ | h_sh <;> rw [h_sh] at h_ev <;> cases h_ev

private def extCallAbortsProp : MirStepNode → Prop
  | .vis (.inr (.inr _)) k => k .aborted = .halted .abort
  | _ => True

private theorem extCallAbortsProp_step (s : MachineState) :
    extCallAbortsProp (MirStepNode.step s) := trivial

private theorem extCallAbortsProp_fail (fk : FailureKind) :
    extCallAbortsProp (MirStepNode.fail fk) := trivial

private theorem extCallAbortsProp_unsupported :
    extCallAbortsProp MirStepNode.unsupported := trivial

private theorem extCallAbortsProp_emitStep (obs : MirObs) (s : MachineState) :
    extCallAbortsProp (MirStepNode.emitStep obs s) := by
  cases obs <;> trivial

private theorem extCallAbortsProp_retNormal (v : Value) (m : Memory) :
    extCallAbortsProp (MirStepNode.retNormal v m) := trivial

private theorem extCallAbortsProp_retOutcome (out : MirOutcome) :
    extCallAbortsProp (MirStepNode.retOutcome out) := trivial

private theorem extCallAbortsProp_extCall_resume
    (req : MirCallReq) (s : MachineState) (l : List LocalSlot)
    (d : Place) (t : BasicBlockIdx) (u : UnwindAction) :
    extCallAbortsProp (MirStepNode.extCall req (resumeExternalCall s l d t u)) := rfl

private theorem extCallAbortsProp_extCall_diverging
    (req : MirCallReq) (s : MachineState) (l : List LocalSlot) (u : UnwindAction) :
    extCallAbortsProp (MirStepNode.extCall req (resumeExternalDivergingCall s l u)) := rfl

private theorem extCallAbortsProp_extCall_tail (req : MirCallReq) :
    extCallAbortsProp (MirStepNode.extCall req resumeExternalTailCall) := rfl

private theorem evalStmt_extCall_aborts_prop
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    extCallAbortsProp (evalStmt s stmt localDecls layouts) := by
  cases h_ev : evalStmt s stmt localDecls layouts with
  | ret _ => trivial
  | tau _ => trivial
  | vis i k =>
    rcases i with _ | (_ | c)
    · trivial
    · trivial
    · exact False.elim (evalStmt_not_extCall s stmt localDecls layouts c k h_ev)

private theorem extCallAbortsProp_writeIntrinsicReturn
    (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    extCallAbortsProp
      (writeIntrinsicReturn s locals' destination targetBb retVal) := by
  unfold writeIntrinsicReturn
  cases writePlaceValue locals' s.memory.borrows destination retVal <;> trivial

private theorem extCallAbortsProp_writeIntrinsicScalarResult
    (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (res : Option ScalarInt) :
    extCallAbortsProp
      (writeIntrinsicScalarResult s locals' destination targetBb res) := by
  cases res with
  | none => trivial
  | some sc =>
    exact extCallAbortsProp_writeIntrinsicReturn s locals' destination targetBb (.scalar sc)

private theorem extCallAbortsProp_evalNonSelectIntrinsicCall
    (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    extCallAbortsProp
      (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb) := by
  rcases evalNonSelectIntrinsicCall_cases kind target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb with ⟨retVal, h_wr⟩ | ⟨fk, h_fl⟩ | h_un
  · rw [h_wr s]; exact extCallAbortsProp_writeIntrinsicReturn s locals' destination targetBb retVal
  · rw [h_fl s]; trivial
  · rw [h_un s]; trivial

private theorem extCallAbortsProp_evalDirectRustIntrinsic?
    (s : MachineState) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (stepNode : MirStepNode)
    (h_di :
      evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb unwind = some stepNode) :
    extCallAbortsProp stepNode := by
  cases h_cl : classifyRustIntrinsic? target.defPath with
  | none =>
    unfold evalDirectRustIntrinsic? at h_di
    rw [h_cl] at h_di
    cases h_di
  | some rk =>
    by_cases h_cs : rk = .constEvalSelect
    · subst h_cs
      rcases argVals with _ | ⟨tupleArgVal, _ | ⟨ctFnVal, _ | ⟨rtFnVal, _ | _⟩⟩⟩
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; trivial
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; trivial
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; trivial
      · rw [evalDirectRustIntrinsic?_constEvalSelect_three _ _ _ _ _ _ _ _ _ _ _ _ _ h_cl] at h_di
        injection h_di with h_sn
        subst h_sn
        unfold evalConstEvalSelectThree
        dsimp only
        cases unpackConstEvalSelectArgs? tupleArgVal (selectTupleTyOpt target.typeArgs) with
        | none => trivial
        | some unpackedArgs =>
          dsimp only
          cases resolveConstEvalSelectTarget? s target bodyLocalDecls bodyLayouts
              (selectRtFnOpOpt argOps) rtFnVal (length unpackedArgs) with
          | none => trivial
          | some rtTarget =>
            dsimp only
            cases lookupCallee s.memory.callees bodyLayouts rtTarget.defPath
                rtTarget.typeArgs s.memory.traitImpls with
            | some calleeBody =>
              dsimp only
              cases Bool.and (Nat.beq calleeBody.argCount (length unpackedArgs))
                  (Bool.and (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
                    (checkCalleeTargetCompatible rtTarget calleeBody (length unpackedArgs))) with
              | false => trivial
              | true => dsimp only; cases currentBody <;> trivial
            | none =>
              dsimp only
              cases rtTarget.isIndirect with
              | true => exact extCallAbortsProp_extCall_resume _ _ _ _ _ _
              | false =>
                dsimp only
                cases isDirectExactDivTarget rtTarget with
                | true =>
                  dsimp only
                  rcases unpackedArgs with _ | ⟨_ | lhs | _ | _, _ | ⟨_ | rhs | _ | _, _ | _⟩⟩ <;>
                    try trivial
                  dsimp only
                  cases resolveIntrinsicIsSigned
                      (withConstEvalSelectIntrinsicTypeArgs rtTarget
                        (selectTupleTyOpt target.typeArgs) false)
                      bodyLocalDecls bodyLayouts
                      (constEvalSelectTupleArgOps (selectTupleTyOpt target.typeArgs)) with
                  | none => trivial
                  | some isSigned =>
                    exact extCallAbortsProp_writeIntrinsicScalarResult s locals'
                      destination targetBb (evalExactDiv lhs rhs isSigned)
                | false =>
                  dsimp only
                  cases classifyRustIntrinsic? rtTarget.defPath with
                  | some rtKind =>
                    cases rtKind <;>
                      first
                      | trivial
                      | exact extCallAbortsProp_evalNonSelectIntrinsicCall _ s _
                          bodyLocalDecls bodyLayouts _ unpackedArgs locals' destination targetBb
                  | none =>
                    dsimp only
                    cases isUnreachableCallTarget rtTarget.defPath with
                    | true => trivial
                    | false =>
                      dsimp only
                      cases isAbortingPanicDefPath rtTarget.defPath with
                      | true => trivial
                      | false =>
                        dsimp only
                        cases isUnwindingPanicDefPath rtTarget.defPath with
                        | true =>
                          dsimp only
                          cases applyUnwindAction s locals' s.memory unwind <;> trivial
                        | false => exact extCallAbortsProp_extCall_resume _ _ _ _ _ _
      · unfold evalDirectRustIntrinsic? at h_di; rw [h_cl] at h_di
        injection h_di with h_sn; subst h_sn; trivial
    · rw [evalDirectRustIntrinsic?_nonSelect _ _ _ _ _ _ _ _ _ _ _ h_cl h_cs] at h_di
      injection h_di with h_sn
      subst h_sn
      exact extCallAbortsProp_evalNonSelectIntrinsicCall rk s target
        bodyLocalDecls bodyLayouts argOps argVals locals' destination targetBb

private theorem stepMirFn_extCall_aborts_prop
    (body : CapturedMir) (s : MachineState) :
    extCallAbortsProp (stepMirFn body s) := by
  rw [stepMirFn_eq_ite]
  dsimp only
  cases isOtherPhase (s.memory.activeCallee.getD body).phase with
  | true =>
    simp only [ite_true]
    trivial
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some bb =>
      dsimp only
      cases get? bb.statements s.frame.stmtIdx with
      | some stmt =>
        exact evalStmt_extCall_aborts_prop s stmt
          (s.memory.activeCallee.getD body).localDecls
          (s.memory.activeCallee.getD body).layouts
      | none =>
        dsimp only
        by_cases h_len : (s.frame.stmtIdx == length bb.statements) = true
        · simp only [h_len, ite_true]
          rcases bb with ⟨_, ⟨tkind, _⟩, _⟩
          cases tkind with
          | call func argOps destination targetOpt unwind =>
            cases targetOpt with
            | none =>
              dsimp only [evalTerminator, bodyLocalDeclsOf]
              cases resolveCallTarget s func (length argOps) _ _ with
              | ub => trivial
              | unsupported => trivial
              | ok target localsAfterFunc =>
                dsimp only
                cases evalOperands localsAfterFunc argOps _ _ _ _ with
                | ub => trivial
                | unsupported => trivial
                | ok argVals locals' =>
                  dsimp only
                  cases lookupCallee _ _ _ _ _ with
                  | some calleeBody =>
                    dsimp only
                    cases checkCalleeTargetCompatible target calleeBody (length argVals) <;> trivial
                  | none =>
                    dsimp only
                    cases target.isIndirect with
                    | true => exact extCallAbortsProp_extCall_diverging _ _ _ _
                    | false =>
                      dsimp only
                      cases isUnreachableCallTarget target.defPath with
                      | true => trivial
                      | false =>
                        dsimp only
                        cases isAbortingPanicDefPath target.defPath with
                        | true => trivial
                        | false =>
                          dsimp only
                          cases isUnwindingPanicDefPath target.defPath with
                          | true =>
                            dsimp only
                            cases applyUnwindAction s locals' s.memory unwind <;> trivial
                          | false => exact extCallAbortsProp_extCall_diverging _ _ _ _
            | some targetBb =>
              dsimp only [evalTerminator, bodyLocalDeclsOf]
              cases resolveCallTarget s func (length argOps) _ _ with
              | ub => trivial
              | unsupported => trivial
              | ok target localsAfterFunc =>
                dsimp only
                cases evalOperands localsAfterFunc argOps _ _ _ _ with
                | ub => trivial
                | unsupported => trivial
                | ok argVals locals' =>
                  dsimp only
                  cases lookupCallee _ _ _ _ _ with
                  | some calleeBody =>
                    dsimp only
                    cases checkCalleeTargetCompatible target calleeBody (length argVals) <;> trivial
                  | none =>
                    dsimp only
                    cases isDirectExactDivTarget target with
                    | true =>
                      dsimp only
                      rcases argVals with _ | ⟨_ | lhs | _ | _, _ | ⟨_ | rhs | _ | _, _ | _⟩⟩ <;>
                        try trivial
                      dsimp only
                      cases resolveIntrinsicIsSigned target _ _ argOps with
                      | none => trivial
                      | some isSigned =>
                        dsimp only
                        cases evalExactDiv lhs rhs isSigned with
                        | none => trivial
                        | some sc =>
                          dsimp only
                          cases writePlaceValue locals' s.memory.borrows destination (.scalar sc) <;> trivial
                    | false =>
                      dsimp only
                      cases target.isIndirect with
                      | true => exact extCallAbortsProp_extCall_resume _ _ _ _ _ _
                      | false =>
                        dsimp only
                        cases h_di :
                          evalDirectRustIntrinsic? s _ target _ _ argOps argVals
                            locals' destination targetBb unwind with
                        | none => exact extCallAbortsProp_extCall_resume _ _ _ _ _ _
                        | some stepNode =>
                          exact extCallAbortsProp_evalDirectRustIntrinsic? s _ target
                            _ _ argOps argVals locals' destination targetBb unwind
                            stepNode h_di
          | goto _ => exact extCallAbortsProp_step _
          | switchInt discr _ =>
            dsimp only [evalTerminator]
            cases evalOperand s.frame.locals discr s.memory.borrows
                s.memory.globals _ s.memory.callerLocals with
            | ub => trivial
            | unsupported => trivial
            | ok v _ => cases v <;> trivial
          | unwindResume =>
            dsimp only [evalTerminator]
            cases unwindFromCallStack s.memory.callStack s.memory <;> trivial
          | unwindTerminate => trivial
          | return_ =>
            dsimp only [evalTerminator]
            cases get? s.frame.locals 0 with
            | none => trivial
            | some slot =>
              cases slot with
              | dead => trivial
              | uninit => trivial
              | init retVal =>
                cases s.memory.callStack with
                | nil => trivial
                | cons caller _ =>
                  dsimp only
                  cases caller.isDiverging with
                  | true => trivial
                  | false =>
                    dsimp only
                    cases writePlaceValue caller.frame.locals s.memory.borrows
                      caller.destination retVal <;> trivial
          | unreachable => trivial
          | drop place _ _ =>
            dsimp only [evalTerminator]
            cases get? s.frame.locals place.local_ with
            | none => trivial
            | some slot =>
              cases slot with
              | dead => trivial
              | uninit =>
                cases place.projection with
                | nil =>
                  dsimp only
                  cases set? s.frame.locals place.local_ .uninit <;> trivial
                | cons _ _ => trivial
              | init rootVal =>
                cases place.projection with
                | nil =>
                  dsimp only
                  cases set? s.frame.locals place.local_ .uninit <;> trivial
                | cons _ _ =>
                  dsimp only
                  cases readProjectedValue s.frame.locals rootVal _ <;> trivial
          | tailCall func argOps =>
            dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
            cases resolveCallTarget s func (length argOps) _ _ with
            | ub => trivial
            | unsupported => trivial
            | ok target localsAfterFunc =>
              dsimp only
              cases evalOperands localsAfterFunc argOps _ _ _ _ with
              | ub => trivial
              | unsupported => trivial
              | ok argVals _ =>
                dsimp only
                cases lookupCallee _ _ _ _ _ with
                | some calleeBody =>
                  dsimp only
                  cases checkCalleeTargetCompatible target calleeBody (length argVals) <;> trivial
                | none => exact extCallAbortsProp_extCall_tail _
          | assert cond expected _ unwind =>
            dsimp only [evalTerminator]
            cases evalOperand s.frame.locals cond s.memory.borrows
                s.memory.globals _ s.memory.callerLocals with
            | ub => trivial
            | unsupported => trivial
            | ok v locals' =>
              cases v with
              | scalar sc =>
                cases expected with
                | false =>
                  dsimp only
                  cases Nat.beq sc.bits 0 with
                  | true => trivial
                  | false =>
                    dsimp only
                    cases applyUnwindAction s locals' s.memory unwind <;> trivial
                | true =>
                  dsimp only
                  cases Nat.beq sc.bits 1 with
                  | true => trivial
                  | false =>
                    dsimp only
                    cases applyUnwindAction s locals' s.memory unwind <;> trivial
              | _ => trivial
          | inlineAsm _ _ _ => trivial
        · simp only [h_len]; trivial

/--
Any panic-and-abort-forbidding `wpMirExecSym` proof (`mirNormalPost P`) implies
call-forbidding `wpMirExecNoCallSym` at the exact same fuel budget, because any
un-inlined `MirCallE` interaction would admit `MirCallAns.aborted` and violate
`mirNormalPost P`.
-/
theorem wpMirExecNoCallSym_of_wpMirExecSym_normal
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P : Value → Memory → Prop}
    (h : wpMirExecSym fuel body st (mirNormalPost P)) :
    wpMirExecNoCallSym fuel body st (mirNormalPost P) := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecSym at h
    unfold wpMirExecNoCallSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval] at h
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    cases st with
    | halted out => exact h
    | faulted fk => exact False.elim h
    | running s =>
      dsimp only [stepMirState] at h ⊢
      have h_ext := stepMirFn_extCall_aborts_prop body s
      cases h_step : stepMirFn body s with
      | ret out =>
        rw [h_step] at h
        exact h
      | tau st' =>
        rw [h_step] at h
        exact ih h
      | vis i k =>
        rw [h_step] at h h_ext
        rcases i with f | (e | c)
        · exact False.elim h
        · cases e
          exact ih h
        · rcases c with ⟨req⟩
          have h_ab := h .aborted
          rw [h_ext] at h_ab
          cases fuel' with
          | zero => exact False.elim h_ab
          | succ f'' =>
            unfold wpMirExecSym at h_ab
            rw [evalSymNodeTree_eq, stepMirExecSymTree_eval] at h_ab
            exact False.elim h_ab

/--
Lift any `MirWpConverges` summary with `mirNormalPost P` into
`MirNoCallWpConverges` without requiring syntactic purity of `body`.
-/
theorem mirNoCallWpConverges_of_mirWpConverges_normal
    {body : CapturedMir} {s : MachineState} {P : Value → Memory → Prop}
    (h : MirWpConverges body s (mirNormalPost P)) :
    MirNoCallWpConverges body s (mirNormalPost P) := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecNoCallSym_of_wpMirExecSym_normal h_wp⟩

/-- Sequential composition of `MirStepsConverges` with `MirNoCallWpConverges`. -/
theorem MirNoCallWpConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid post)
    (h₂ : ∀ s', mid s' → MirNoCallWpConverges body s' post) :
    MirNoCallWpConverges body s post := by
  rcases h₁ with ⟨f₁, h_steps⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      ∃ f_tot : Nat, wpMirExecNoCallSym f_tot body st post from
    this (.running s) h_steps
  clear h_steps s
  induction f₁ with
  | zero =>
    intro st h_mid
    cases st with
    | running s' => exact h₂ s' h_mid
    | halted out =>
      refine ⟨1, ?_⟩
      unfold wpMirExecNoCallSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
      exact h_mid
    | faulted _ => exact False.elim h_mid
  | succ f₁' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_st
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at h_st
      refine ⟨1, ?_⟩
      unfold wpMirExecNoCallSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, h_step]
      exact h_st
    | tau st' =>
      rw [h_step] at h_st
      rcases ih st' h_st with ⟨f_sub, hf_sub⟩
      refine ⟨f_sub + 1, ?_⟩
      unfold wpMirExecNoCallSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, h_step]
      exact hf_sub
    | vis i k =>
      rw [h_step] at h_st
      rcases i with f | (e | c)
      · exact False.elim h_st
      · cases e
        rcases ih (k PUnit.unit) h_st with ⟨f_sub, hf_sub⟩
        refine ⟨f_sub + 1, ?_⟩
        unfold wpMirExecNoCallSym
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, h_step]
        exact hf_sub
      · exact False.elim h_st

/-- Single-step unfolding rule for `MirNoCallWpConverges`. -/
theorem MirNoCallWpConverges.step
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h :
      evalNodeNoCallWP
        (fun
          | .running s' => MirNoCallWpConverges body s' post
          | .halted out => post out
          | .faulted _ => False)
        post
        (stepMirFn body s)) :
    MirNoCallWpConverges body s post := by
  have h1 : MirStepsConverges body s
      (fun s' => MirNoCallWpConverges body s' post) post := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    cases h_sf : stepMirFn body s with
    | ret out =>
      rw [h_sf] at h
      exact h
    | tau st' =>
      rw [h_sf] at h
      dsimp only [evalNodeNoCallWP, wpMirExecStepsSym] at h ⊢
      exact h
    | vis i k =>
      rw [h_sf] at h
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        dsimp only [evalNodeNoCallWP, wpMirExecStepsSym] at h ⊢
        exact h
      · exact False.elim h
  exact MirNoCallWpConverges.bind h1 (fun _ hw => hw)

private theorem wpMirExecNoCallSym_halted_panic_false
    {fuel : Nat} {body : CapturedMir} {P : Value → Memory → Prop}
    (h : wpMirExecNoCallSym fuel body (.halted .panic) (mirNormalPost P)) :
    False := by
  cases fuel with
  | zero => exact h
  | succ f' =>
    unfold wpMirExecNoCallSym at h
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h
    exact h

/--
Lifting `wpMirExecNoCallSym` along `MirExecState.pushBaseStack body []`:
normalizing `activeCallee` from `none` to `some body` at the root frame preserves
execution step-for-step at the identical fuel budget.
-/
theorem wpMirExecNoCallSym_pushBaseStack_nil_outer
    {fuel : Nat} {outerBody body : CapturedMir} {st : MirExecState}
    {P : Value → Memory → Prop}
    (h : wpMirExecNoCallSym fuel body st (mirNormalPost P)) :
    wpMirExecNoCallSym fuel outerBody (MirExecState.pushBaseStack body [] st)
      (mirNormalPost
        (fun retVal mem' =>
          ∃ mem₀, mem' = Memory.pushBaseStack body [] mem₀ ∧ P retVal mem₀)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ f' ih =>
    unfold wpMirExecNoCallSym at h ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h ⊢
    cases st with
    | faulted fk => exact False.elim h
    | halted out =>
      cases out with
      | normal rv => exact ⟨rv.2, rfl, h⟩
      | panic => exact False.elim h
      | abort => exact False.elim h
    | running ms =>
      dsimp only [MirExecState.pushBaseStack, stepMirState] at h ⊢
      have h_act :
          (MachineState.pushBaseStack body [] ms).memory.activeCallee.getD outerBody =
            ms.memory.activeCallee.getD body := rfl
      let curBody := ms.memory.activeCallee.getD body
      rw [stepMirFn_eq_ite] at h
      dsimp only at h
      have h_phase_or :
          (∃ tag, curBody.phase = .other tag) ∨
          (evalNodeNoCallWP
              (fun st' => wpMirExecNoCallSym f' body st' (mirNormalPost P))
              (mirNormalPost P)
              (match get? curBody.basicBlocks ms.frame.blockIdx with
               | none => MirStepNode.fail .ub
               | some bb =>
                 match get? bb.statements ms.frame.stmtIdx with
                 | some stmt =>
                   evalStmt ms stmt curBody.localDecls curBody.layouts
                 | none =>
                   if ms.frame.stmtIdx == length bb.statements then
                     evalTerminator ms bb.terminator (some curBody)
                   else MirStepNode.fail .ub) ∧
           stepMirFn outerBody (MachineState.pushBaseStack body [] ms) =
              match get? curBody.basicBlocks ms.frame.blockIdx with
              | none => MirStepNode.fail .ub
              | some bb =>
                match get? bb.statements ms.frame.stmtIdx with
                | some stmt =>
                  evalStmt (MachineState.pushBaseStack body [] ms)
                    stmt curBody.localDecls curBody.layouts
                | none =>
                  if ms.frame.stmtIdx == length bb.statements then
                    evalTerminator (MachineState.pushBaseStack body [] ms)
                      bb.terminator (some curBody)
                  else MirStepNode.fail .ub) := by
        cases h_ph : isOtherPhase curBody.phase with
        | true => exact Or.inl (isOtherPhase_eq_true_iff h_ph)
        | false =>
          refine Or.inr ⟨?_, ?_⟩
          · rw [h_ph] at h; exact h
          · rw [stepMirFn_eq_ite]
            dsimp only
            rw [h_act, h_ph]
            rfl
      rcases h_phase_or with ⟨tag, h_oth⟩ | ⟨h_st, h_step_body⟩
      · rw [h_oth] at h; exact False.elim h
      · cases h_bb : get? curBody.basicBlocks ms.frame.blockIdx with
        | none =>
          rw [h_bb] at h_st; exact False.elim h_st
        | some bb =>
          rw [h_bb] at h_st h_step_body
          dsimp only at h_st h_step_body
          cases h_stmt : get? bb.statements ms.frame.stmtIdx with
          | some stmt =>
            rw [h_stmt] at h_st h_step_body
            dsimp only at h_st h_step_body
            have h_es :=
              evalStmt_pushBaseStack body [] ms stmt curBody.localDecls curBody.layouts
            cases h_ev : evalStmt ms stmt curBody.localDecls curBody.layouts with
            | ret out =>
              rcases evalStmt_isStmtNode ms stmt curBody.localDecls curBody.layouts with
                ⟨_, h_sh⟩ | ⟨_, h_sh⟩ | h_sh <;> rw [h_sh] at h_ev <;> cases h_ev
            | tau st1 =>
              rw [h_ev] at h_st h_es
              dsimp only [MirStepNode.pushBaseStack, evalNodeNoCallWP] at h_st h_es
              rw [h_step_body, h_es]
              exact ih h_st
            | vis i k =>
              rw [h_ev] at h_st h_es
              rcases i with f | (e | c)
              · exact False.elim h_st
              · cases e
                dsimp only [MirStepNode.pushBaseStack, evalNodeNoCallWP] at h_st h_es
                rw [h_step_body, h_es]
                exact ih h_st
              · exact False.elim h_st
          | none =>
            rw [h_stmt] at h_st h_step_body
            dsimp only at h_st h_step_body
            by_cases h_len : (ms.frame.stmtIdx == length bb.statements) = true
            · simp only [h_len, ite_true] at h_st h_step_body
              rcases bb with ⟨_, ⟨tkind, tspan⟩, _⟩
              cases tkind with
              | goto target =>
                rw [h_step_body]
                exact ih h_st
              | switchInt discr targets =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                  Memory.pushBaseStack_globals, Memory.pushBaseStack_callerLocals] at h_st h_step_body
                cases h_op : evalOperand ms.frame.locals discr ms.memory.borrows
                    ms.memory.globals curBody.layouts ms.memory.callerLocals with
                | ub => rw [h_op] at h_st; exact False.elim h_st
                | unsupported => rw [h_op] at h_st; exact False.elim h_st
                | ok v locs' =>
                  rw [h_op] at h_st h_step_body
                  cases v with
                  | scalar sc =>
                    rw [h_step_body]
                    exact ih h_st
                  | _ => exact False.elim h_st
              | unwindResume =>
                simp only [evalTerminator, MachineState.pushBaseStack_memory,
                  Memory.pushBaseStack_callStack] at h_st h_step_body
                have h_ne_pan : unwindFromCallStack ms.memory.callStack ms.memory ≠ .halted .panic := by
                  intro h_pan
                  rw [h_pan] at h_st
                  exact h_st
                have h_uw := unwindFromCallStack_pushBaseStack_of_ne_panic body []
                  ms.memory.callStack ms.memory h_ne_pan
                cases h_u : unwindFromCallStack ms.memory.callStack ms.memory with
                | faulted fk => rw [h_u] at h_st; exact False.elim h_st
                | halted out =>
                  rw [h_u] at h_st h_uw
                  cases out with
                  | normal rv => exact False.elim (unwindFromCallStack_ne_normal _ _ _ h_u)
                  | panic => exact False.elim (h_ne_pan h_u)
                  | abort => exact False.elim h_st
                | running ns =>
                  rw [h_u] at h_st h_uw
                  rw [h_step_body, h_uw]
                  exact ih h_st
              | unwindTerminate =>
                exact False.elim h_st
              | unreachable =>
                exact False.elim h_st
              | inlineAsm =>
                exact False.elim h_st
              | drop pl target unw =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame] at h_st h_step_body
                cases h_g : get? ms.frame.locals pl.local_ with
                | none => rw [h_g] at h_st; exact False.elim h_st
                | some sl =>
                  rw [h_g] at h_st h_step_body
                  cases sl with
                  | dead => exact False.elim h_st
                  | uninit =>
                    cases h_pr : pl.projection with
                    | cons _ _ => rw [h_pr] at h_st; exact False.elim h_st
                    | nil =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_s : set? ms.frame.locals pl.local_ .uninit with
                      | none => rw [h_s] at h_st; exact False.elim h_st
                      | some locs' =>
                        rw [h_s] at h_st h_step_body
                        rw [h_step_body]
                        exact ih h_st
                  | init rv =>
                    cases h_pr : pl.projection with
                    | nil =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_s : set? ms.frame.locals pl.local_ .uninit with
                      | none => rw [h_s] at h_st; exact False.elim h_st
                      | some locs' =>
                        rw [h_s] at h_st h_step_body
                        rw [h_step_body]
                        exact ih h_st
                    | cons hd tl =>
                      rw [h_pr] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_rd : readProjectedValue ms.frame.locals rv (hd :: tl) with
                      | ub => rw [h_rd] at h_st; exact False.elim h_st
                      | unsupported => rw [h_rd] at h_st; exact False.elim h_st
                      | ok _ =>
                        rw [h_rd] at h_st h_step_body
                        rw [h_step_body]
                        exact ih h_st
              | assert cond exp target unw =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                  Memory.pushBaseStack_globals, Memory.pushBaseStack_callerLocals] at h_st h_step_body
                cases h_op : evalOperand ms.frame.locals cond ms.memory.borrows
                    ms.memory.globals curBody.layouts ms.memory.callerLocals with
                | ub => rw [h_op] at h_st; exact False.elim h_st
                | unsupported => rw [h_op] at h_st; exact False.elim h_st
                | ok v locs' =>
                  rw [h_op] at h_st h_step_body
                  cases v with
                  | scalar sc =>
                    dsimp only at h_st h_step_body
                    have h_ab :
                        ∀ expBit : Nat,
                          evalNodeNoCallWP
                            (fun st' => wpMirExecNoCallSym f' body st' (mirNormalPost P))
                            (mirNormalPost P)
                            (match Nat.beq sc.bits expBit with
                             | true =>
                               MirStepNode.step
                                 { ms with frame := { blockIdx := target, stmtIdx := 0, locals := locs' } }
                             | false =>
                               match applyUnwindAction ms locs' ms.memory unw with
                               | .running ns => MirStepNode.step ns
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) →
                          stepMirFn outerBody (MachineState.pushBaseStack body [] ms) =
                            (match Nat.beq sc.bits expBit with
                             | true =>
                               MirStepNode.step
                                 { frame := { blockIdx := target, stmtIdx := 0, locals := locs' }
                                   memory := Memory.pushBaseStack body [] ms.memory }
                             | false =>
                               match applyUnwindAction (MachineState.pushBaseStack body [] ms) locs'
                                   (Memory.pushBaseStack body [] ms.memory) unw with
                               | .running ns => MirStepNode.step ns
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) →
                          evalNodeNoCallWP
                            (fun st' =>
                              wpMirExecNoCallSym f' outerBody st'
                                (mirNormalPost (fun retVal mem' => ∃ mem₀, mem' = Memory.pushBaseStack body [] mem₀ ∧ P retVal mem₀)))
                            (mirNormalPost (fun retVal mem' => ∃ mem₀, mem' = Memory.pushBaseStack body [] mem₀ ∧ P retVal mem₀))
                            (stepMirFn outerBody (MachineState.pushBaseStack body [] ms)) := by
                      intro expBit h_st_b h_sb_b
                      cases h_eqb : Nat.beq sc.bits expBit with
                      | true =>
                        rw [h_eqb] at h_st_b h_sb_b
                        rw [h_sb_b]
                        exact ih h_st_b
                      | false =>
                        rw [h_eqb] at h_st_b h_sb_b
                        dsimp only at h_st_b h_sb_b
                        have h_ne_pan : applyUnwindAction ms locs' ms.memory unw ≠ .halted .panic := by
                          intro h_pan; rw [h_pan] at h_st_b; exact h_st_b
                        have h_au := applyUnwindAction_pushBaseStack_of_ne_panic body [] ms locs' unw h_ne_pan
                        cases h_a : applyUnwindAction ms locs' ms.memory unw with
                        | faulted fk => rw [h_a] at h_st_b; exact False.elim h_st_b
                        | halted out =>
                          rw [h_a] at h_st_b h_au
                          cases out with
                          | normal rv => exact False.elim (applyUnwindAction_ne_normal _ _ _ _ _ h_a)
                          | panic => exact False.elim (h_ne_pan h_a)
                          | abort => exact False.elim h_st_b
                        | running ns =>
                          rw [h_a] at h_st_b h_au
                          rw [h_sb_b, h_au]
                          exact ih h_st_b
                    cases exp with
                    | true => exact h_ab 1 h_st h_step_body
                    | false => exact h_ab 0 h_st h_step_body
                  | _ => exact False.elim h_st
              | tailCall func argOps =>
                simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf,
                  resolveCallTarget_pushBaseStack, MachineState.pushBaseStack_memory,
                  Memory.pushBaseStack_borrows, Memory.pushBaseStack_globals,
                  Memory.pushBaseStack_callees, Memory.pushBaseStack_traitImpls,
                  Memory.pushBaseStack_callerLocals] at h_st h_step_body
                cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                | ub => rw [h_rt] at h_st; exact False.elim h_st
                | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                | ok target locsF =>
                  rw [h_rt] at h_st h_step_body
                  dsimp only at h_st h_step_body
                  cases h_ops : evalOperands locsF argOps ms.memory.borrows ms.memory.globals curBody.layouts ms.memory.callerLocals with
                  | ub => rw [h_ops] at h_st; exact False.elim h_st
                  | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                  | ok avs _ =>
                    rw [h_ops] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_lk : lookupCallee ms.memory.callees curBody.layouts target.defPath target.typeArgs ms.memory.traitImpls with
                    | none => rw [h_lk] at h_st; exact False.elim h_st
                    | some nextCallee =>
                      rw [h_lk] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_ok : checkCalleeTargetCompatible target nextCallee (length avs) with
                      | false => rw [h_ok] at h_st; exact False.elim h_st
                      | true =>
                        rw [h_ok] at h_st h_step_body
                        rw [h_step_body]
                        have h_eq_tc :
                            enterTailCalleeFrame (Memory.pushBaseStack body [] ms.memory) nextCallee avs =
                              MachineState.pushBaseStack body [] (enterTailCalleeFrame ms.memory nextCallee avs) := by
                          simp [enterTailCalleeFrame, MachineState.pushBaseStack, Memory.pushBaseStack]
                        rw [h_eq_tc]
                        exact ih h_st
              | call func argOps cDest cTarget cUnw =>
                cases cTarget with
                | none =>
                  simp only [evalTerminator, bodyLocalDeclsOf,
                    resolveCallTarget_pushBaseStack,
                    MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                    Memory.pushBaseStack_globals, Memory.pushBaseStack_callees,
                    Memory.pushBaseStack_traitImpls,
                    Memory.pushBaseStack_callerLocals] at h_st h_step_body
                  cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                  | ub => rw [h_rt] at h_st; exact False.elim h_st
                  | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                  | ok target locsF =>
                    rw [h_rt] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_ops : evalOperands locsF argOps ms.memory.borrows ms.memory.globals curBody.layouts ms.memory.callerLocals with
                    | ub => rw [h_ops] at h_st; exact False.elim h_st
                    | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                    | ok avs cLocals' =>
                      rw [h_ops] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_lk : lookupCallee ms.memory.callees curBody.layouts target.defPath target.typeArgs ms.memory.traitImpls with
                      | some nextCallee =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ok : checkCalleeTargetCompatible target nextCallee (length avs) with
                        | false => rw [h_ok] at h_st; exact False.elim h_st
                        | true =>
                          rw [h_ok] at h_st h_step_body
                          rw [h_step_body]
                          have h_eq_dc :
                              pushDivergingCalleeFrame (MachineState.pushBaseStack body [] ms) curBody cLocals' cDest cUnw nextCallee avs =
                                MachineState.pushBaseStack body [] (pushDivergingCalleeFrame ms curBody cLocals' cDest cUnw nextCallee avs) := by
                            simp [pushDivergingCalleeFrame, MachineState.pushBaseStack, Memory.pushBaseStack]
                          dsimp only
                          rw [h_eq_dc]
                          exact ih h_st
                      | none =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ind : target.isIndirect with
                        | true => rw [h_ind] at h_st; exact False.elim h_st
                        | false =>
                          rw [h_ind] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases h_unr : isUnreachableCallTarget target.defPath with
                          | true => rw [h_unr] at h_st; exact False.elim h_st
                          | false =>
                            rw [h_unr] at h_st h_step_body
                            dsimp only at h_st h_step_body
                            cases h_abp : isAbortingPanicDefPath target.defPath with
                            | true => rw [h_abp] at h_st; exact False.elim h_st
                            | false =>
                              rw [h_abp] at h_st h_step_body
                              dsimp only at h_st h_step_body
                              cases h_uwp : isUnwindingPanicDefPath target.defPath with
                              | false => rw [h_uwp] at h_st; exact False.elim h_st
                              | true =>
                                rw [h_uwp] at h_st h_step_body
                                dsimp only at h_st h_step_body
                                have h_ne_pan : applyUnwindAction ms cLocals' ms.memory cUnw ≠ .halted .panic := by
                                  intro h_pan; rw [h_pan] at h_st; exact h_st
                                have h_au := applyUnwindAction_pushBaseStack_of_ne_panic body [] ms cLocals' cUnw h_ne_pan
                                cases h_a : applyUnwindAction ms cLocals' ms.memory cUnw with
                                | faulted fk => rw [h_a] at h_st; exact False.elim h_st
                                | halted out =>
                                  rw [h_a] at h_st h_au
                                  cases out with
                                  | normal rv => exact False.elim (applyUnwindAction_ne_normal _ _ _ _ _ h_a)
                                  | panic => exact False.elim (h_ne_pan h_a)
                                  | abort => exact False.elim h_st
                                | running ns =>
                                  rw [h_a] at h_st h_au
                                  rw [h_step_body, h_au]
                                  exact ih h_st
                | some cTargetBb =>
                  simp only [evalTerminator, bodyLocalDeclsOf,
                    resolveCallTarget_pushBaseStack,
                    MachineState.pushBaseStack_memory, Memory.pushBaseStack_borrows,
                    Memory.pushBaseStack_globals, Memory.pushBaseStack_callees,
                    Memory.pushBaseStack_traitImpls,
                    Memory.pushBaseStack_callerLocals] at h_st h_step_body
                  cases h_rt : resolveCallTarget ms func (length argOps) curBody.localDecls curBody.layouts with
                  | ub => rw [h_rt] at h_st; exact False.elim h_st
                  | unsupported => rw [h_rt] at h_st; exact False.elim h_st
                  | ok target locsF =>
                    rw [h_rt] at h_st h_step_body
                    dsimp only at h_st h_step_body
                    cases h_ops : evalOperands locsF argOps ms.memory.borrows ms.memory.globals curBody.layouts ms.memory.callerLocals with
                    | ub => rw [h_ops] at h_st; exact False.elim h_st
                    | unsupported => rw [h_ops] at h_st; exact False.elim h_st
                    | ok avs cLocals' =>
                      rw [h_ops] at h_st h_step_body
                      dsimp only at h_st h_step_body
                      cases h_lk : lookupCallee ms.memory.callees curBody.layouts target.defPath target.typeArgs ms.memory.traitImpls with
                      | some nextCallee =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ok : checkCalleeTargetCompatible target nextCallee (length avs) with
                        | false => rw [h_ok] at h_st; exact False.elim h_st
                        | true =>
                          rw [h_ok] at h_st h_step_body
                          rw [h_step_body]
                          have h_eq_pc :
                              pushCalleeFrame (MachineState.pushBaseStack body [] ms) curBody cLocals' cDest cTargetBb nextCallee avs cUnw =
                                MachineState.pushBaseStack body [] (pushCalleeFrame ms curBody cLocals' cDest cTargetBb nextCallee avs cUnw) := by
                            simp [pushCalleeFrame, MachineState.pushBaseStack, Memory.pushBaseStack]
                          dsimp only
                          rw [h_eq_pc]
                          exact ih h_st
                      | none =>
                        rw [h_lk] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_ed : isDirectExactDivTarget target with
                        | false =>
                          rw [h_ed] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases h_ind : target.isIndirect with
                          | true => rw [h_ind] at h_st; exact False.elim h_st
                          | false =>
                            rw [h_ind] at h_st h_step_body
                            dsimp only at h_st h_step_body
                            cases h_di :
                              evalDirectRustIntrinsic? ms (some curBody) target
                                curBody.localDecls curBody.layouts argOps avs
                                cLocals' cDest cTargetBb cUnw with
                            | none => rw [h_di] at h_st; exact False.elim h_st
                            | some stepNode =>
                              rw [h_di] at h_st
                              dsimp only at h_st
                              rcases evalDirectRustIntrinsic?_pushBaseStack_of_noCallWP
                                  body [] ms curBody target argOps avs cLocals'
                                  cDest cTargetBb cUnw stepNode h_di h_st with
                                ⟨nextSt, rfl, h_m2⟩
                              rw [h_m2] at h_step_body
                              rw [h_step_body]
                              exact ih h_st
                        | true =>
                          rw [h_ed] at h_st h_step_body
                          dsimp only at h_st h_step_body
                          cases avs with
                          | nil => exact False.elim h_st
                          | cons v1 tl1 =>
                            cases v1 <;> try exact False.elim h_st
                            cases tl1 with
                            | nil => exact False.elim h_st
                            | cons v2 tl2 =>
                              cases v2 <;> try exact False.elim h_st
                              cases tl2 with
                              | cons _ _ => exact False.elim h_st
                              | nil =>
                                rename_i lhsSc rhsSc
                                dsimp only at h_st h_step_body
                                cases h_sig :
                                  resolveIntrinsicIsSigned target curBody.localDecls
                                    curBody.layouts argOps with
                                | none => rw [h_sig] at h_st; exact False.elim h_st
                                | some isSigned =>
                                  rw [h_sig] at h_st h_step_body
                                  dsimp only at h_st h_step_body
                                  cases h_div : evalExactDiv lhsSc rhsSc isSigned with
                                  | none => rw [h_div] at h_st; exact False.elim h_st
                                  | some retSc =>
                                    rw [h_div] at h_st h_step_body
                                    dsimp only at h_st h_step_body
                                    cases h_wr : writePlaceValue cLocals' ms.memory.borrows cDest (.scalar retSc) with
                                    | ub => rw [h_wr] at h_st; exact False.elim h_st
                                    | unsupported => rw [h_wr] at h_st; exact False.elim h_st
                                    | ok updL =>
                                      rw [h_wr] at h_st h_step_body
                                      rw [h_step_body]
                                      exact ih h_st
              | return_ =>
                simp only [evalTerminator, MachineState.pushBaseStack_frame,
                  MachineState.pushBaseStack_memory, Memory.pushBaseStack_callStack,
                  Memory.pushBaseStack_borrows] at h_st h_step_body
                cases h_g : get? ms.frame.locals 0 with
                | none => rw [h_g] at h_st; exact False.elim h_st
                | some slot =>
                  rw [h_g] at h_st h_step_body
                  cases slot with
                  | uninit => exact False.elim h_st
                  | dead => exact False.elim h_st
                  | init retVal =>
                    dsimp only at h_st h_step_body
                    cases h_stk : ms.memory.callStack with
                    | cons innerCaller innerRest =>
                      rw [h_stk] at h_st h_step_body
                      dsimp only [List.cons_append] at h_st h_step_body
                      cases h_div : innerCaller.isDiverging with
                      | true => rw [h_div] at h_st; exact False.elim h_st
                      | false =>
                        rw [h_div] at h_st h_step_body
                        dsimp only at h_st h_step_body
                        cases h_wr : writePlaceValue innerCaller.frame.locals
                            ms.memory.borrows innerCaller.destination retVal with
                        | ub => rw [h_wr] at h_st; exact False.elim h_st
                        | unsupported => rw [h_wr] at h_st; exact False.elim h_st
                        | ok updLocals =>
                          rw [h_wr] at h_st h_step_body
                          rw [h_step_body]
                          exact ih h_st
                    | nil =>
                      rw [h_stk] at h_st h_step_body
                      dsimp only [List.nil_append] at h_st h_step_body
                      rw [h_step_body]
                      exact ⟨ms.memory, rfl, h_st⟩
            · simp only [h_len] at h_st
              exact False.elim h_st

/--
Specialization of `wpMirExecNoCallSym_pushBaseStack_nil_outer` when `outerBody =
body`.
-/
theorem wpMirExecNoCallSym_pushBaseStack_nil
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P : Value → Memory → Prop}
    (h : wpMirExecNoCallSym fuel body st (mirNormalPost P)) :
    wpMirExecNoCallSym fuel body (MirExecState.pushBaseStack body [] st)
      (mirNormalPost
        (fun retVal mem' =>
          ∃ mem₀, mem' = Memory.pushBaseStack body [] mem₀ ∧ P retVal mem₀)) :=
  wpMirExecNoCallSym_pushBaseStack_nil_outer h

/--
Fuel-bounded callee-aware pure execution predicate over `PureState`, seeding
`pureCalleeMemory callees traitImpls` and requiring `ActiveRootMemory`
preservation alongside `post retVal`.
-/
def wpPureMirExecWithCallees
    (fuel : Nat)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (ps : PureState)
    (post : Value → Prop)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Prop :=
  wpMirExecNoCallSym fuel body
    (.running (ps.toMachineState (pureCalleeMemory callees traitImpls)))
    (mirNormalPost
      (fun retVal mem' =>
        ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
        post retVal))

/--
Fuel-bounded partial-correctness (`mirSafePost`) callee-aware pure execution
predicate over `PureState`.
-/
def wpPureMirSafeExecWithCallees
    (fuel : Nat)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (ps : PureState)
    (post : Value → Prop)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Prop :=
  wpMirExecSym fuel body
    (.running (ps.toMachineState (pureCalleeMemory callees traitImpls)))
    (mirSafePost
      (fun retVal mem' =>
        ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
        post retVal))

/--
Fuel-free callee-aware total-correctness convergence over `PureState`.
-/
def PureMirConvergesWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (ps : PureState)
    (post : Value → Prop)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Prop :=
  ∃ fuel : Nat, wpPureMirExecWithCallees fuel body callees ps post traitImpls

/--
Fuel-free callee-aware partial-correctness (`mirSafePost`) convergence over
`PureState`.
-/
def PureMirSafeConvergesWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (ps : PureState)
    (post : Value → Prop)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Prop :=
  ∃ fuel : Nat, wpPureMirSafeExecWithCallees fuel body callees ps post traitImpls

/-- Postcondition monotonicity for `PureMirConvergesWithCallees`. -/
theorem PureMirConvergesWithCallees.mono
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {P Q : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirConvergesWithCallees body callees ps P traitImpls) :
    PureMirConvergesWithCallees body callees ps Q traitImpls := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecNoCallSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact ⟨h_out.1, h_imp rv.1 h_out.2⟩
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Postcondition monotonicity for `PureMirSafeConvergesWithCallees`. -/
theorem PureMirSafeConvergesWithCallees.mono
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {P Q : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirSafeConvergesWithCallees body callees ps P traitImpls) :
    PureMirSafeConvergesWithCallees body callees ps Q traitImpls := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact ⟨h_out.1, h_imp rv.1 h_out.2⟩
  | panic => trivial
  | abort => trivial

/--
Every `PureMirConvergesWithCallees` proof implies
`PureMirSafeConvergesWithCallees`.
-/
theorem PureMirSafeConvergesWithCallees.of_pureMirConvergesWithCallees
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h : PureMirConvergesWithCallees body callees ps post traitImpls) :
    PureMirSafeConvergesWithCallees body callees ps post traitImpls := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_mono_post (fun _ => mirNormalPost_imp_mirSafePost)
    (wpMirExecSym_of_wpMirExecNoCallSym h_wp)⟩

/--
Lift any `FF-2.1` call-free `PureMirConverges body ps post` proof into
`PureMirConvergesWithCallees body callees ps post traitImpls` for arbitrary
`callees` and `traitImpls`.
-/
theorem PureMirConvergesWithCallees.of_pureMirConverges
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_pure : checkPureMir body = true)
    (h : PureMirConverges body ps post) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  rcases h with ⟨fuel, h_wp⟩
  have h_nc : wpMirExecNoCallSym fuel body
      (.running (ps.toMachineState emptyMemory))
      (mirNormalPost (fun retVal _ => post retVal)) :=
    wpMirExecNoCallSym_of_wpMirExecSym_normal h_wp
  have h_lifted :=
    wpMirExecNoCallSym_withMem_of_emptyMemory
      (mem₀ := pureCalleeMemory callees traitImpls)
      (.running (ps.toMachineState emptyMemory))
      h_pure
      (rootActiveMemory_pureCalleeMemory callees traitImpls)
      h_nc
  refine ⟨fuel, wpMirExecNoCallSym_mono_post ?_ h_lifted⟩
  intro out h_out
  cases out with
  | normal rv => exact ⟨Or.inl h_out.1, h_out.2⟩
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Alias `PureMirConverges.toWithCallees` for dot-notation lifting. -/
theorem PureMirConverges.toWithCallees
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h : PureMirConverges body ps post)
    (h_pure : checkPureMir body = true) :
    PureMirConvergesWithCallees body callees ps post traitImpls :=
  PureMirConvergesWithCallees.of_pureMirConverges h_pure h

/--
Lift `PureMirConvergesWithCallees` from `ps.toMachineState m0` to
`ps.toMachineState { m0 with activeCallee := some body }` (`Memory.pushBaseStack
body [] m0`)
so post-return continuations in `body` compose without exposing `activeCallee`.
-/
theorem PureMirConvergesWithCallees.toNoCall_some_activeCallee
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h : PureMirConvergesWithCallees body callees ps post traitImpls) :
    MirNoCallWpConverges body
      (ps.toMachineState { pureCalleeMemory callees traitImpls with activeCallee := some body })
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
          post retVal)) := by
  rcases h with ⟨fuel, h_wp⟩
  have h_pushed := wpMirExecNoCallSym_pushBaseStack_nil h_wp
  have h_state_eq :
      MirExecState.pushBaseStack body []
        (.running (ps.toMachineState (pureCalleeMemory callees traitImpls))) =
      .running (ps.toMachineState
        { pureCalleeMemory callees traitImpls with activeCallee := some body }) := rfl
  rw [h_state_eq] at h_pushed
  refine ⟨fuel, wpMirExecNoCallSym_mono_post ?_ h_pushed⟩
  intro out h_out
  cases out with
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out
  | normal rv =>
    rcases rv with ⟨retVal, mem'⟩
    rcases h_out with ⟨mem₀, rfl, h_act, h_post⟩
    refine ⟨?_, h_post⟩
    rcases h_act with rfl | ⟨b, rfl⟩
    · exact Or.inr ⟨body, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

/--
Single-step symbolic unfolding rule for `PureMirConvergesWithCallees` over
`PureState` (covering statements, `goto`, `switchInt`, `assert`, `drop`,
`return_`, and inline `core::intrinsics::exact_div`).
-/
theorem PureMirConvergesWithCallees.step
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h :
      evalNodeNoCallWP
        (fun
          | .running s' =>
            s'.memory = pureCalleeMemory callees traitImpls ∧
            PureMirConvergesWithCallees body callees
              (PureState.ofMachineState s') post traitImpls
          | .halted out =>
            mirNormalPost
              (fun retVal mem' =>
                ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
                post retVal) out
          | .faulted _ => False)
        (mirNormalPost
          (fun retVal mem' =>
            ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
            post retVal))
        (stepMirFn body (ps.toMachineState (pureCalleeMemory callees traitImpls)))) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine MirNoCallWpConverges.step ?_
  cases h_sf : stepMirFn body (ps.toMachineState (pureCalleeMemory callees traitImpls)) with
  | ret out =>
    rw [h_sf] at h
    exact h
  | tau st' =>
    rw [h_sf] at h
    cases st' with
    | faulted _ => exact False.elim h
    | halted out => exact h
    | running s' =>
      dsimp only [evalNodeNoCallWP] at h ⊢
      rcases h with ⟨h_mem, h_conv⟩
      have h_eq : (PureState.ofMachineState s').toMachineState (pureCalleeMemory callees traitImpls) = s' := by
        cases s'
        dsimp only [PureState.ofMachineState, PureState.toMachineState] at h_mem ⊢
        subst h_mem
        rfl
      rw [← h_eq]
      exact h_conv
  | vis i k =>
    rw [h_sf] at h
    rcases i with f | (e | c)
    · exact False.elim h
    · cases e
      dsimp only [evalNodeNoCallWP] at h ⊢
      cases h_ku : k PUnit.unit with
      | faulted _ =>
        rw [h_ku] at h
        exact False.elim h
      | halted out =>
        rw [h_ku] at h
        exact h
      | running s' =>
        rw [h_ku] at h
        rcases h with ⟨h_mem, h_conv⟩
        have h_eq : (PureState.ofMachineState s').toMachineState (pureCalleeMemory callees traitImpls) = s' := by
          cases s'
          dsimp only [PureState.ofMachineState, PureState.toMachineState] at h_mem ⊢
          subst h_mem
          rfl
        rw [← h_eq]
        exact h_conv
    · exact False.elim h

private theorem get?_length_eq_none {α : Type} (xs : List α) :
    get? xs (length xs) = none := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact ih

/--
General stateful 1-step compositional callee summary rule
(`MirWpConverges.call_summary`):
when the active frame in `s` reaches `TerminatorKind.call func argOps
destination (.some targetBb) unwind`
with `s.memory.callStack.length < maxCallDepth` and `s.memory.activeProtectors =
[]`,
resolving `(defPath, typeArgs)` via `resolveCallTarget` and `lookupCallee` to
`calleeBody`
with `checkCalleeTargetCompatible = true`, and `calleeBody` has an established
`MirWpConverges` summary producing `calleePost retVal` while preserving
`ActiveRootMemory`,
the caller steps in **1 compositional step** to `targetBb` with `destination :=
retVal`
without re-stepping `calleeBody`'s basic blocks or guessing combined fuel.
-/
theorem MirWpConverges.call_summary
    {outerBody : CapturedMir}
    {s : MachineState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {localsAfterFunc localsAfterArgs : List LocalSlot}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : MirOutcome → Prop}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, (s.memory.activeCallee.getD outerBody).phase ≠ .other tag)
    (h_bb : get? (s.memory.activeCallee.getD outerBody).basicBlocks s.frame.blockIdx = some bb)
    (h_end : s.frame.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : s.memory.callStack.length < maxCallDepth := by
      first | decide | exact Nat.lt_succ_self _)
    (h_prot : s.memory.activeProtectors = [] := by rfl)
    (h_resolve :
      resolveCallTarget s func (length argOps)
        (s.memory.activeCallee.getD outerBody).localDecls
        (s.memory.activeCallee.getD outerBody).layouts =
        .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (s.memory.activeCallee.getD outerBody).layouts s.memory.callerLocals =
        .ok argVals localsAfterArgs)
    (h_lookup :
      lookupCallee s.memory.callees
        (s.memory.activeCallee.getD outerBody).layouts
        resolvedTarget.defPath resolvedTarget.typeArgs s.memory.traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { s.memory with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ActiveRootMemory calleeBody
              { s.memory with callStack := [], activeCallee := none } memOut ∧
            calleePost retVal)))
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedLocals : List LocalSlot,
          writePlaceValue localsAfterArgs s.memory.borrows destination retVal =
            .ok updatedLocals ∧
          MirWpConverges outerBody
            { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
              memory := { s.memory with activeCallee := some (s.memory.activeCallee.getD outerBody) } }
            post) :
    MirWpConverges outerBody s post := by
  let _ := h_depth
  let curBody := s.memory.activeCallee.getD outerBody
  have h_stmt_none : get? bb.statements s.frame.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn outerBody s =
        MirStepNode.step
          (pushCalleeFrame s curBody localsAfterArgs destination targetBb
            calleeBody argVals unwind) := by
    rw [stepMirFn_eq_ite]
    dsimp only
    cases h_ph : isOtherPhase curBody.phase with
    | true => exact False.elim (Bool.noConfusion (h_ph.symm.trans (isOtherPhase_eq_false h_phase)))
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_resolve]
      dsimp only
      rw [h_args]
      dsimp only
      rw [h_lookup]
      dsimp only
      rw [h_compat]
  have h_callee_nc := mirNoCallWpConverges_of_mirWpConverges_normal h_callee_summary
  have h_push_steps :
      MirStepsConverges outerBody
        (pushCalleeFrame s curBody localsAfterArgs destination targetBb
          calleeBody argVals unwind)
        (fun ms' => MirWpConverges outerBody ms' post)
        post := by
    refine wpMirExecNoCallSym_pushCalleeFrame h_callee_nc h_prot ?_
    intro retVal memOut ⟨h_act_out, h_cpost⟩
    have h_bor_eq : memOut.borrows = s.memory.borrows := by
      rcases h_act_out with rfl | ⟨_, rfl⟩ <;> rfl
    rcases h_after retVal h_cpost with ⟨updLocs, h_wr, h_next_wp⟩
    refine ⟨updLocs, ?_, ?_⟩
    · rw [h_bor_eq]; exact h_wr
    · have h_mem_eq :
          { memOut with
            callStack := s.memory.callStack
            activeCallee := some curBody
            activeProtectors := [] } =
          { s.memory with activeCallee := some curBody } := by
        rcases s with ⟨sFrame, sMem⟩
        cases sMem
        rcases h_act_out with rfl | ⟨_, rfl⟩ <;>
          (dsimp only at h_prot ⊢; subst h_prot; rfl)
      rw [h_mem_eq]
      exact h_next_wp
  have h_one_step :
      MirStepsConverges outerBody s
        (fun ms' => ms' = pushCalleeFrame s curBody localsAfterArgs destination targetBb
          calleeBody argVals unwind)
        post := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    rw [h_step_eq]
    rfl
  exact MirWpConverges.bind h_one_step (fun ms' h_eq => by
    subst h_eq
    exact MirWpConverges.bind h_push_steps (fun _ hw => hw))

/-- Top-level alias for `MirWpConverges.call_summary`. -/
abbrev mirWpConverges_call_summary := @MirWpConverges.call_summary

/--
Stateful 1-step compositional root `tailCall` summary rule
(`MirWpConverges.tailCall_summary`):
when a root frame (`s.memory.callStack = []`) reaches `TerminatorKind.tailCall
func argOps` with `0 < maxCallDepth`, resolving `(defPath, typeArgs)` via
`resolveCallTarget` and `lookupCallee` to `calleeBody` with
`checkCalleeTargetCompatible = true`, and `calleeBody` has an established
`MirWpConverges` summary producing `calleePost retVal` while preserving
`ActiveRootMemory`, the caller steps in **1 compositional step** to `post`
without re-stepping `calleeBody`'s basic blocks or exposing fuel.
-/
theorem MirWpConverges.tailCall_summary
    {outerBody : CapturedMir}
    {s : MachineState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {localsAfterFunc localsAfterArgs : List LocalSlot}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : MirOutcome → Prop}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, (s.memory.activeCallee.getD outerBody).phase ≠ .other tag)
    (h_bb : get? (s.memory.activeCallee.getD outerBody).basicBlocks s.frame.blockIdx = some bb)
    (h_end : s.frame.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_stack : s.memory.callStack = [] := by rfl)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget s func (length argOps)
        (s.memory.activeCallee.getD outerBody).localDecls
        (s.memory.activeCallee.getD outerBody).layouts =
        .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (s.memory.activeCallee.getD outerBody).layouts s.memory.callerLocals =
        .ok argVals localsAfterArgs)
    (h_lookup :
      lookupCallee s.memory.callees
        (s.memory.activeCallee.getD outerBody).layouts
        resolvedTarget.defPath resolvedTarget.typeArgs s.memory.traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { s.memory with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ActiveRootMemory calleeBody
              { s.memory with callStack := [], activeCallee := none } memOut ∧
            calleePost retVal)))
    (h_after :
      ∀ (retVal : Value) (memOut : Memory),
        ActiveRootMemory outerBody
          { s.memory with callStack := [], activeCallee := none } memOut →
        calleePost retVal →
        post (.normal (retVal, memOut))) :
    MirWpConverges outerBody s post := by
  let _ := h_depth
  let curBody := s.memory.activeCallee.getD outerBody
  have h_stmt_none : get? bb.statements s.frame.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn outerBody s =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals) := by
    rw [stepMirFn_eq_ite]
    dsimp only
    cases h_ph : isOtherPhase curBody.phase with
    | true => exact False.elim (Bool.noConfusion (h_ph.symm.trans (isOtherPhase_eq_false h_phase)))
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
      rw [h_resolve]
      dsimp only
      rw [h_args]
      dsimp only
      rw [h_lookup]
      dsimp only
      rw [h_compat]
  rcases mirNoCallWpConverges_of_mirWpConverges_normal h_callee_summary with ⟨fuel_c, h_nc⟩
  have h_pushed :=
    wpMirExecNoCallSym_pushBaseStack_nil_outer (outerBody := outerBody) h_nc
  have h_state_eq :
      MirExecState.pushBaseStack calleeBody []
        (.running (initMachineStateWithMemory calleeBody argVals
          { s.memory with callStack := [], activeCallee := none })) =
      .running (enterTailCalleeFrame s.memory calleeBody argVals) := by
    rcases s with ⟨sFrame, sMem⟩
    cases sMem
    dsimp only at h_stack ⊢
    subst h_stack
    rfl
  rw [h_state_eq] at h_pushed
  have h_tail_nc :
      MirNoCallWpConverges outerBody
        (enterTailCalleeFrame s.memory calleeBody argVals) post := by
    refine ⟨fuel_c, wpMirExecNoCallSym_mono_post ?_ h_pushed⟩
    intro out h_out
    cases out with
    | panic => exact False.elim h_out
    | abort => exact False.elim h_out
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases h_out with ⟨mem₀, rfl, h_act₀, h_cp⟩
      refine h_after retVal (Memory.pushBaseStack calleeBody [] mem₀) ?_ h_cp
      rcases h_act₀ with rfl | ⟨ab, rfl⟩
      · exact Or.inr ⟨calleeBody, rfl⟩
      · exact Or.inr ⟨ab, rfl⟩
  have h_one_step :
      MirStepsConverges outerBody s
        (fun ms' => ms' = enterTailCalleeFrame s.memory calleeBody argVals)
        post := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    rw [h_step_eq]
    rfl
  have h_root_nc : MirNoCallWpConverges outerBody s post :=
    MirNoCallWpConverges.bind h_one_step (fun ms' h_eq => by
      subst h_eq
      exact h_tail_nc)
  rcases h_root_nc with ⟨fuel_tot, h_tot⟩
  exact ⟨fuel_tot, wpMirExecSym_of_wpMirExecNoCallSym h_tot⟩

/--
Stateful 1-step compositional nested `tailCall` summary rule
(`MirWpConverges.tailCall_nested_summary`):
when a non-root frame (`s.memory.callStack = caller :: restStack` with
`caller.isDiverging = false` and `caller.calleeProtectors = []`) executes
`TerminatorKind.tailCall func argOps`, `calleeBody` returns directly into the
suspended `caller` frame without growing `callStack`.
-/
theorem MirWpConverges.tailCall_nested_summary
    {outerBody : CapturedMir}
    {s : MachineState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {caller : SavedCallerFrame}
    {restStack : List SavedCallerFrame}
    {resolvedTarget : ResolvedCallTarget}
    {localsAfterFunc localsAfterArgs : List LocalSlot}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : MirOutcome → Prop}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, (s.memory.activeCallee.getD outerBody).phase ≠ .other tag)
    (h_bb : get? (s.memory.activeCallee.getD outerBody).basicBlocks s.frame.blockIdx = some bb)
    (h_end : s.frame.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_stack : s.memory.callStack = caller :: restStack)
    (h_depth : s.memory.callStack.length < maxCallDepth := by
      first | decide | exact Nat.lt_succ_self _)
    (h_prot : s.memory.activeProtectors = [] := by rfl)
    (h_cprot : caller.calleeProtectors = [] := by rfl)
    (h_ccprot : caller.callerProtector = none := by rfl)
    (h_cdiv : caller.isDiverging = false := by rfl)
    (h_resolve :
      resolveCallTarget s func (length argOps)
        (s.memory.activeCallee.getD outerBody).localDecls
        (s.memory.activeCallee.getD outerBody).layouts =
        .ok resolvedTarget localsAfterFunc)
    (h_args :
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        (s.memory.activeCallee.getD outerBody).layouts s.memory.callerLocals =
        .ok argVals localsAfterArgs)
    (h_lookup :
      lookupCallee s.memory.callees
        (s.memory.activeCallee.getD outerBody).layouts
        resolvedTarget.defPath resolvedTarget.typeArgs s.memory.traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { s.memory with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ActiveRootMemory calleeBody
              { s.memory with callStack := [], activeCallee := none } memOut ∧
            calleePost retVal)))
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedLocals : List LocalSlot,
          writePlaceValue caller.frame.locals s.memory.borrows
            caller.destination retVal = .ok updatedLocals ∧
          MirWpConverges outerBody
            { frame := {
                caller.frame with
                blockIdx := caller.returnTarget
                stmtIdx := 0
                locals := updatedLocals }
              memory := {
                s.memory with
                callStack := restStack
                activeCallee := some caller.callerBody
                activeProtectors := [] } }
            post) :
    MirWpConverges outerBody s post := by
  let _ := h_depth
  let curBody := s.memory.activeCallee.getD outerBody
  have h_stmt_none : get? bb.statements s.frame.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn outerBody s =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals) := by
    rw [stepMirFn_eq_ite]
    dsimp only
    cases h_ph : isOtherPhase curBody.phase with
    | true => exact False.elim (Bool.noConfusion (h_ph.symm.trans (isOtherPhase_eq_false h_phase)))
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (s.frame.stmtIdx == length bb.statements) = true := by
        simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
      rw [h_resolve]
      dsimp only
      rw [h_args]
      dsimp only
      rw [h_lookup]
      dsimp only
      rw [h_compat]
  let sParent : MachineState := {
    frame := caller.frame
    memory := { s.memory with callStack := restStack, activeProtectors := [] }
  }
  have h_enter_eq :
      enterTailCalleeFrame s.memory calleeBody argVals =
        pushCalleeFrame sParent caller.callerBody caller.frame.locals
          caller.destination caller.returnTarget calleeBody argVals
          caller.returnUnwind := by
    have h_frame_eta :
        ({ caller.frame with locals := caller.frame.locals } : StackFrame) =
          caller.frame := by
      cases caller.frame
      rfl
    rcases s with ⟨sFrame, sMem⟩
    cases sMem
    cases caller
    dsimp only [sParent, enterTailCalleeFrame, pushCalleeFrame] at h_stack h_prot h_cprot h_ccprot h_cdiv h_frame_eta ⊢
    rw [h_frame_eta]
    subst h_stack h_prot h_cprot h_ccprot h_cdiv
    rfl
  have h_init_eq :
      initMachineStateWithMemory calleeBody argVals
        { sParent.memory with callStack := [], activeCallee := none } =
      initMachineStateWithMemory calleeBody argVals
        { s.memory with callStack := [], activeCallee := none } := by
    rcases s with ⟨sFrame, sMem⟩
    cases sMem
    dsimp only [sParent] at h_prot ⊢
    subst h_prot
    rfl
  have h_callee_nc :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { sParent.memory with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ActiveRootMemory calleeBody
              { s.memory with callStack := [], activeCallee := none } memOut ∧
            calleePost retVal)) := by
    rw [h_init_eq]
    exact mirNoCallWpConverges_of_mirWpConverges_normal h_callee_summary
  have h_push_steps :
      MirStepsConverges outerBody
        (enterTailCalleeFrame s.memory calleeBody argVals)
        (fun ms' => MirWpConverges outerBody ms' post)
        post := by
    rw [h_enter_eq]
    refine wpMirExecNoCallSym_pushCalleeFrame h_callee_nc rfl ?_
    intro retVal memOut ⟨h_act_out, h_cpost⟩
    have h_bor_eq : memOut.borrows = s.memory.borrows := by
      rcases h_act_out with rfl | ⟨_, rfl⟩ <;> rfl
    rcases h_after retVal h_cpost with ⟨updLocs, h_wr, h_next_wp⟩
    refine ⟨updLocs, ?_, ?_⟩
    · rw [h_bor_eq]; exact h_wr
    · have h_mem_eq :
          { memOut with
            callStack := sParent.memory.callStack
            activeCallee := some caller.callerBody
            activeProtectors := [] } =
          { s.memory with
            callStack := restStack
            activeCallee := some caller.callerBody
            activeProtectors := [] } := by
        rcases s with ⟨sFrame, sMem⟩
        cases sMem
        rcases h_act_out with rfl | ⟨_, rfl⟩ <;> rfl
      rw [h_mem_eq]
      exact h_next_wp
  have h_one_step :
      MirStepsConverges outerBody s
        (fun ms' => ms' = enterTailCalleeFrame s.memory calleeBody argVals)
        post := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    rw [h_step_eq]
    rfl
  exact MirWpConverges.bind h_one_step (fun ms' h_eq => by
    subst h_eq
    exact MirWpConverges.bind h_push_steps (fun _ hw => hw))

/--
Compositional 1-step callee summary rule on `PureState`
(`PureMirConvergesWithCallees.call_summary`):
when `body` at `ps` reaches `TerminatorKind.call func argOps destination (.some
targetBb) unwind`
with `0 < maxCallDepth`, resolving `(defPath, typeArgs)` via `resolveCallTarget`
and
`lookupCallee callees body.layouts resolvedTarget.defPath
resolvedTarget.typeArgs traitImpls`
(including polymorphic instantiation and `TraitImplEntry` dispatch) to
`calleeBody`
with `checkCalleeTargetCompatible = true`, and `calleeBody` has an established
`PureMirConvergesWithCallees` summary producing `calleePost retVal`, the caller
steps directly in **1 compositional step** to `{ bb := targetBb, stmtIdx := 0,
env := updatedEnv }`
in `PureState` without re-stepping `calleeBody`'s basic blocks or guessing
combined fuel.
-/
theorem PureMirConvergesWithCallees.call_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirConvergesWithCallees body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  let _ := h_depth
  let m0 := pureCalleeMemory callees traitImpls
  let s0 := ps.toMachineState m0
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step
          (pushCalleeFrame s0 body envAfterArgs destination targetBb
            calleeBody argVals unwind) := by
    unfold stepMirFn
    dsimp only [s0, m0, PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      dsimp only
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by
        simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [PureState.toMachineState] at h_resolve
      unfold evalPureOperands at h_args
      dsimp only [evalTerminator, bodyLocalDeclsOf,
        pureCalleeMemory_borrows, pureCalleeMemory_globals,
        pureCalleeMemory_callerLocals, pureCalleeMemory_callees,
        pureCalleeMemory_traitImpls]
      rw [h_resolve]
      dsimp only
      rw [h_args]
      dsimp only
      rw [h_lookup]
      dsimp only
      rw [h_compat]
  have h_init_eq :
      initMachineStateWithMemory calleeBody argVals
        { s0.memory with callStack := [], activeCallee := none } =
      (initPureState calleeBody argVals).toMachineState m0 := rfl
  have h_callee_nc :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { s0.memory with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ActiveRootMemory calleeBody m0 memOut ∧ calleePost retVal)) := by
    rw [h_init_eq]
    exact h_callee_summary
  let targetPost :=
    mirNormalPost
      (fun retVal mem' =>
        ActiveRootMemory body m0 mem' ∧ post retVal)
  have h_push_steps :
      MirStepsConverges body
        (pushCalleeFrame s0 body envAfterArgs destination targetBb
          calleeBody argVals unwind)
        (fun ms' => MirNoCallWpConverges body ms' targetPost)
        targetPost := by
    refine wpMirExecNoCallSym_pushCalleeFrame h_callee_nc rfl ?_
    intro retVal memOut ⟨h_act_out, h_cpost⟩
    have h_bor_eq : memOut.borrows = [] := ActiveRootMemory.borrows_eq h_act_out
    rcases h_after retVal h_cpost with ⟨updEnv, h_wr, h_next_conv⟩
    refine ⟨updEnv, ?_, ?_⟩
    · rw [h_bor_eq]; exact h_wr
    · have h_mem_eq :
          { memOut with
            callStack := s0.memory.callStack
            activeCallee := some body
            activeProtectors := [] } =
          { m0 with activeCallee := some body } := by
        rcases h_act_out with rfl | ⟨_, rfl⟩ <;> rfl
      rw [h_mem_eq]
      exact PureMirConvergesWithCallees.toNoCall_some_activeCallee h_next_conv
  have h_one_step :
      MirStepsConverges body s0
        (fun ms' => ms' = pushCalleeFrame s0 body envAfterArgs destination targetBb
          calleeBody argVals unwind)
        targetPost := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    rw [h_step_eq]
    rfl
  exact MirNoCallWpConverges.bind h_one_step (fun ms' h_eq => by
    subst h_eq
    exact MirNoCallWpConverges.bind h_push_steps (fun _ hw => hw))

/--
Headline compositional 1-step callee summary rule
(`PureMirConverges.call_summary`,
`FF-2.2` Section 4): resolves direct or polymorphic `(defPath, typeArgs)`
callees
in `callees` (with `0 < maxCallDepth`) using an established
`PureMirConvergesWithCallees`
summary (which includes leaf `PureMirConverges` summaries via `.toWithCallees`
as
well as nested multi-callee summaries) and advances the caller directly to
`{ bb := targetBb, stmtIdx := 0, env := updatedEnv }` in 1 compositional step.
-/
theorem PureMirConverges.call_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirConvergesWithCallees body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls :=
  PureMirConvergesWithCallees.call_summary
    h_phase h_bb h_end h_term h_depth h_resolve h_args h_lookup h_compat
    h_callee_summary h_after

/--
Leaf specialization of `PureMirConverges.call_summary` accepting an `FF-2.1`
call-free `PureMirConverges calleeBody (initPureState calleeBody argVals)
calleePost`
summary directly (given `checkPureMir calleeBody = true`).
-/
theorem PureMirConverges.call_leaf_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_pure : checkPureMir calleeBody = true)
    (h_callee_summary :
      PureMirConverges calleeBody (initPureState calleeBody argVals) calleePost)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirConvergesWithCallees body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls :=
  PureMirConverges.call_summary
    h_phase h_bb h_end h_term h_depth h_resolve h_args h_lookup h_compat
    (PureMirConvergesWithCallees.of_pureMirConverges h_callee_pure h_callee_summary)
    h_after

/--
Compositional 1-step `tailCall` summary rule on `PureState`
(`PureMirConvergesWithCallees.tailCall_summary`):
when `body` at `ps` reaches `TerminatorKind.tailCall func argOps` with
`0 < maxCallDepth`, resolving `(defPath, typeArgs)` via `resolveCallTarget` and
`lookupCallee` to `calleeBody` with `checkCalleeTargetCompatible = true`, and
`calleeBody` has an established `PureMirConvergesWithCallees` summary producing
`calleePost retVal`, the caller converges in **1 compositional step** to `post`
without re-stepping `calleeBody`'s basic blocks or exposing fuel.
-/
theorem PureMirConvergesWithCallees.tailCall_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_imp : ∀ retVal : Value, calleePost retVal → post retVal) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  let _ := h_depth
  let m0 := pureCalleeMemory callees traitImpls
  let s0 := ps.toMachineState m0
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step (enterTailCalleeFrame m0 calleeBody argVals) := by
    unfold stepMirFn
    dsimp only [s0, m0, PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      dsimp only
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by
        simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [PureState.toMachineState] at h_resolve
      unfold evalPureOperands at h_args
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf,
        pureCalleeMemory_borrows, pureCalleeMemory_globals,
        pureCalleeMemory_callerLocals, pureCalleeMemory_callees,
        pureCalleeMemory_traitImpls]
      rw [h_resolve]
      dsimp only
      rw [h_args]
      dsimp only
      rw [h_lookup]
      dsimp only
      rw [h_compat]
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_pushed :=
    wpMirExecNoCallSym_pushBaseStack_nil_outer (outerBody := body) h_wp_c
  have h_state_eq :
      MirExecState.pushBaseStack calleeBody []
        (.running ((initPureState calleeBody argVals).toMachineState m0)) =
      .running (enterTailCalleeFrame m0 calleeBody argVals) := rfl
  rw [h_state_eq] at h_pushed
  let targetPost :=
    mirNormalPost
      (fun retVal mem' =>
        ActiveRootMemory body m0 mem' ∧ post retVal)
  have h_tail_nc :
      MirNoCallWpConverges body
        (enterTailCalleeFrame m0 calleeBody argVals) targetPost := by
    refine ⟨fuel_c, wpMirExecNoCallSym_mono_post ?_ h_pushed⟩
    intro out h_out
    cases out with
    | panic => exact False.elim h_out
    | abort => exact False.elim h_out
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases h_out with ⟨memOut, rfl, h_act_out, h_cp⟩
      refine ⟨?_, h_imp retVal h_cp⟩
      rcases h_act_out with rfl | ⟨ab, rfl⟩
      · exact Or.inr ⟨calleeBody, rfl⟩
      · exact Or.inr ⟨ab, rfl⟩
  have h_one_step :
      MirStepsConverges body s0
        (fun ms' => ms' = enterTailCalleeFrame m0 calleeBody argVals)
        targetPost := by
    refine ⟨1, ?_⟩
    unfold wpMirStepsSym wpMirExecStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    rw [h_step_eq]
    rfl
  exact MirNoCallWpConverges.bind h_one_step (fun ms' h_eq => by
    subst h_eq
    exact h_tail_nc)

/--
Headline compositional 1-step `tailCall` summary rule
(`PureMirConverges.tailCall_summary`).
-/
theorem PureMirConverges.tailCall_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_imp : ∀ retVal : Value, calleePost retVal → post retVal) :
    PureMirConvergesWithCallees body callees ps post traitImpls :=
  PureMirConvergesWithCallees.tailCall_summary
    h_phase h_bb h_end h_term h_depth h_resolve h_args h_lookup h_compat
    h_callee_summary h_imp

/--
Leaf specialization of `PureMirConverges.tailCall_summary` accepting an `FF-2.1`
call-free `PureMirConverges calleeBody (initPureState calleeBody argVals)
calleePost` summary directly (given `checkPureMir calleeBody = true`).
-/
theorem PureMirConverges.tailCall_leaf_summary
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_pure : checkPureMir calleeBody = true)
    (h_callee_summary :
      PureMirConverges calleeBody (initPureState calleeBody argVals) calleePost)
    (h_imp : ∀ retVal : Value, calleePost retVal → post retVal) :
    PureMirConvergesWithCallees body callees ps post traitImpls :=
  PureMirConverges.tailCall_summary
    h_phase h_bb h_end h_term h_depth h_resolve h_args h_lookup h_compat
    (PureMirConvergesWithCallees.of_pureMirConverges h_callee_pure h_callee_summary)
    h_imp

/--
1-step compositional rule for inline `core::intrinsics::exact_div` calls in
`PureMirConvergesWithCallees` (when `lookupCallee = none` and
`isDirectExactDivTarget resolvedTarget = true`).
-/
theorem PureMirConvergesWithCallees.call_exact_div
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs updatedEnv : List SlotState}
    {lhsSc rhsSc retSc : ScalarInt}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_resolve :
      resolveCallTarget
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        func (length argOps) body.localDecls body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok [.scalar lhsSc, .scalar rhsSc] envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts
        resolvedTarget.defPath resolvedTarget.typeArgs traitImpls = none)
    (h_exact : isDirectExactDivTarget resolvedTarget = true)
    (h_div :
      (match resolveIntrinsicIsSigned resolvedTarget body.localDecls body.layouts argOps with
       | some isSigned => evalExactDiv lhsSc rhsSc isSigned
       | none => none) = some retSc)
    (h_wr : writePurePlaceValue envAfterArgs destination (.scalar retSc) = .ok updatedEnv)
    (h_after :
      PureMirConvergesWithCallees body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]
    exact get?_length_eq_none bb.statements
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by
      simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [PureState.toMachineState] at h_resolve
    unfold evalPureOperands at h_args
    unfold writePurePlaceValue at h_wr
    dsimp only [evalTerminator, bodyLocalDeclsOf,
      pureCalleeMemory_borrows, pureCalleeMemory_globals,
      pureCalleeMemory_callerLocals, pureCalleeMemory_callees,
      pureCalleeMemory_traitImpls]
    rw [h_resolve]
    dsimp only
    rw [h_args]
    dsimp only
    rw [h_lookup]
    dsimp only
    rw [h_exact]
    dsimp only
    generalize h_sig :
      resolveIntrinsicIsSigned resolvedTarget body.localDecls body.layouts argOps =
        sigOpt at h_div ⊢
    cases sigOpt with
    | none => nomatch h_div
    | some isSigned =>
      dsimp only at h_div ⊢
      rw [h_div]
      dsimp only
      rw [h_wr]
      exact ⟨rfl, h_after⟩

/--
1-step root `.return_` terminator rule for `PureMirConvergesWithCallees` over
symbolic `PureState`.
-/
theorem PureMirConvergesWithCallees.return_
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData} {retVal : Value}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .return_)
    (h_ret : get? ps.env 0 = some (.init retVal))
    (h_post : post retVal) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, pureCalleeMemory_callStack]
    rw [h_ret]
    exact ⟨Or.inl rfl, h_post⟩

/--
1-step `.goto` terminator rule for `PureMirConvergesWithCallees` over symbolic
`PureState`.
-/
theorem PureMirConvergesWithCallees.step_goto
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData} {targetBb : BasicBlockIdx}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .goto targetBb)
    (h_next :
      PureMirConvergesWithCallees body callees
        { bb := targetBb, stmtIdx := 0, env := ps.env } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    exact ⟨rfl, h_next⟩

/--
1-step `.switchInt` terminator rule for `PureMirConvergesWithCallees` over
symbolic `PureState`.
-/
theorem PureMirConvergesWithCallees.step_switchInt
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData}
    {discr : Operand} {targets : SwitchTargets}
    {sc : ScalarInt} {env' : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .switchInt discr targets)
    (h_eval : evalPureOperand ps.env discr body.layouts = .ok (.scalar sc) env')
    (h_next :
      PureMirConvergesWithCallees body callees
        { bb := lookupSwitchTarget sc.bits targets.branches targets.otherwise
          stmtIdx := 0
          env := env' }
        post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    unfold evalPureOperand at h_eval
    dsimp only [evalTerminator, pureCalleeMemory_borrows,
      pureCalleeMemory_globals, pureCalleeMemory_callerLocals]
    rw [h_eval]
    exact ⟨rfl, h_next⟩

/--
1-step passing `.assert` terminator rule for `PureMirConvergesWithCallees` over
symbolic `PureState`.
-/
theorem PureMirConvergesWithCallees.step_assert_true
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData}
    {cond : Operand} {expected : Bool}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {sc : ScalarInt} {env' : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .assert cond expected targetBb unwind)
    (h_eval : evalPureOperand ps.env cond body.layouts = .ok (.scalar sc) env')
    (h_ok : Nat.beq sc.bits (if expected then 1 else 0) = true)
    (h_next :
      PureMirConvergesWithCallees body callees
        { bb := targetBb, stmtIdx := 0, env := env' } post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    unfold evalPureOperand at h_eval
    dsimp only [evalTerminator, pureCalleeMemory_borrows,
      pureCalleeMemory_globals, pureCalleeMemory_callerLocals]
    rw [h_eval]
    cases expected
    · simp only [Bool.false_eq_true, ↓reduceIte] at h_ok
      dsimp only [BEq.beq]
      rw [h_ok]
      exact ⟨rfl, h_next⟩
    · simp only [↓reduceIte] at h_ok
      dsimp only [BEq.beq]
      rw [h_ok]
      exact ⟨rfl, h_next⟩

/--
1-step pure `Statement` rule for `PureMirConvergesWithCallees` over symbolic
`PureState`.
-/
theorem PureMirConvergesWithCallees.step_stmt
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData}
    {stmt : Statement} {s_emp : MachineState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_stmt : get? bb.statements ps.stmtIdx = some stmt)
    (h_pure : isPureStatement stmt.kind = true)
    (h_eval :
      evalStmt (ps.toMachineState emptyMemory) stmt body.localDecls body.layouts =
        MirStepNode.step s_emp)
    (h_next :
      PureMirConvergesWithCallees body callees
        (PureState.ofMachineState s_emp) post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt]
    dsimp only
    have h_eq :=
      evalStmt_toMachineState_eq_withMem ps
        (pureCalleeMemory callees traitImpls) stmt body.localDecls body.layouts
        h_pure (rootActiveMemory_pureCalleeMemory callees traitImpls)
    dsimp only [PureState.toMachineState] at h_eq h_eval
    rw [h_eq, h_eval]
    exact ⟨rfl, h_next⟩

/--
1-step `.drop` terminator rule for `PureMirConvergesWithCallees` over symbolic
`PureState`.
-/
theorem PureMirConvergesWithCallees.step_drop
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {bb : BasicBlockData}
    {place : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {s_emp : MachineState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .drop place targetBb unwind)
    (h_eval :
      evalTerminator (ps.toMachineState emptyMemory) bb.terminator (some body) =
        MirStepNode.step s_emp)
    (h_next :
      PureMirConvergesWithCallees body callees
        (PureState.ofMachineState s_emp) post traitImpls) :
    PureMirConvergesWithCallees body callees ps post traitImpls := by
  refine PureMirConvergesWithCallees.step ?_
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_drop_m :
      evalTerminator
        (ps.toMachineState (pureCalleeMemory callees traitImpls))
        bb.terminator (some body) =
      MirStepNode.step
        ((PureState.ofMachineState s_emp).toMachineState
          (pureCalleeMemory callees traitImpls)) := by
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    rcases place with ⟨loc, proj⟩
    dsimp only at h_term
    subst h_term
    unfold evalTerminator at h_eval ⊢
    dsimp only [PureState.toMachineState] at h_eval ⊢
    cases h_g : get? ps.env loc with
    | none => rw [h_g] at h_eval; nomatch h_eval
    | some sl =>
      rw [h_g] at h_eval
      cases sl with
      | dead => nomatch h_eval
      | uninit =>
        cases proj with
        | nil =>
          dsimp only at h_eval ⊢
          cases h_s : set? ps.env loc .uninit with
          | none => rw [h_s] at h_eval; nomatch h_eval
          | some _ =>
            rw [h_s] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
        | cons _ _ => nomatch h_eval
      | init rv =>
        cases proj with
        | nil =>
          dsimp only at h_eval ⊢
          cases h_s : set? ps.env loc .uninit with
          | none => rw [h_s] at h_eval; nomatch h_eval
          | some _ =>
            rw [h_s] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
        | cons hd tl =>
          dsimp only at h_eval ⊢
          cases h_rd : readProjectedValue ps.env rv (hd :: tl) with
          | ub => rw [h_rd] at h_eval; nomatch h_eval
          | unsupported => rw [h_rd] at h_eval; nomatch h_eval
          | ok _ =>
            rw [h_rd] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
  unfold stepMirFn
  dsimp only [PureState.toMachineState, pureCalleeMemory_activeCallee, Option.getD] at h_drop_m ⊢
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    dsimp only
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rw [h_drop_m]
    exact ⟨rfl, h_next⟩

/-!
## 9. Inline Pure Callee Checker (`checkPureMirWithCallees`), Pure
`CallConv.rustIntrinsic`, & `#[external_spec]` Modular Integration
-/

/--
Extract the static `(defPath, typeArgs)` target of a pure call `func` operand:
- First tries `extractCalleeDefPath? func` (direct function-item constant).
- Otherwise, when `isPureOperand func = true`, inspects
  `extractFnItemTarget? (operandTy callerLocalDecls callerLayouts func)` to
  support local variables, parameters, and tuple/field projections of
  zero-sized function-item type `RigidTy.fnDef defPath typeArgs`.
-/
def extractPureCalleeTarget?
    (callerLocalDecls : List LocalDecl)
    (callerLayouts : LayoutTable)
    (func : Operand) : Option (DefPath × List RigidTy) :=
  match extractCalleeDefPath? func with
  | .some defPath => .some (defPath, extractCalleeTypeArgs func)
  | .none =>
    if isPureOperand func then
      extractFnItemTarget? (operandTy callerLocalDecls callerLayouts func)
    else
      .none

/--
Memory-independent pure call-target evaluation matching `resolveCallTarget`
whenever `extractPureCalleeTarget? callerLocalDecls callerLayouts func =
some (defPath, typeArgs)`.
-/
def resolvePureCalleeTarget
    (locals : List LocalSlot)
    (func : Operand)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (callerLayouts : LayoutTable) : CallTargetResult :=
  match extractCalleeDefPath? func with
  | .some _ =>
    .ok
      { defPath := defPath
        typeArgs := typeArgs
        fnSig := .none
        isIndirect := false }
      locals
  | .none =>
    match evalOperand locals func [] [] callerLayouts [] with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok .unit localsAfterFunc =>
      .ok
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := .none
          isIndirect := false }
        localsAfterFunc
    | .ok (.aggregate 0 .nil) localsAfterFunc =>
      .ok
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := .none
          isIndirect := false }
        localsAfterFunc
    | .ok _ _ => .ub

/--
Memory-erasure theorem for `resolveCallTarget` on pure function-item operands
(both direct constants and local/projected zero-sized `RigidTy.fnDef` slots).
-/
theorem resolveCallTarget_eq_of_extractPureCalleeTarget
    (s : MachineState)
    (func : Operand)
    (argCount : Nat)
    (callerLocalDecls : List LocalDecl)
    (callerLayouts : LayoutTable)
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    (h_ext :
      extractPureCalleeTarget? callerLocalDecls callerLayouts func =
        some (defPath, typeArgs)) :
    resolveCallTarget s func argCount callerLocalDecls callerLayouts =
      resolvePureCalleeTarget s.frame.locals func defPath typeArgs
        callerLayouts := by
  unfold extractPureCalleeTarget? at h_ext
  unfold resolveCallTarget resolvePureCalleeTarget
  cases h_def : extractCalleeDefPath? func with
  | some dp =>
    rw [h_def] at h_ext
    injection h_ext with h_pair
    injection h_pair with h_dp h_ta
    subst h_dp h_ta
    rfl
  | none =>
    rw [h_def] at h_ext
    cases h_pure : isPureOperand func with
    | false =>
      rw [h_pure] at h_ext
      nomatch h_ext
    | true =>
      rw [h_pure] at h_ext
      simp only [↓reduceIte] at h_ext
      rw [evalOperand_pure_eq s.frame.locals func s.memory.borrows
        s.memory.globals callerLayouts s.memory.callerLocals h_pure]
      cases evalOperand s.frame.locals func [] [] callerLayouts [] with
      | ub => rfl
      | unsupported => rfl
      | ok val localsAfterFunc =>
        cases val with
        | unit =>
          dsimp only
          rw [h_ext]
        | aggregate vIdx flds =>
          cases vIdx with
          | zero =>
            cases flds with
            | nil =>
              simp only [Nat.zero_eq]
              rw [h_ext]
            | cons _ _ => rfl
          | succ _ => rfl
        | ptr ptrVal sz =>
          dsimp only
          have h_sig_false :
              ∀ fnEntry : FnPtrEntry,
                fnEntryCompatibleWithCallSite fnEntry argCount
                  (operandTy callerLocalDecls callerLayouts func) = false := by
            intro fnEntry
            cases h_oty : operandTy callerLocalDecls callerLayouts func with
            | none =>
              rw [h_oty] at h_ext
              nomatch h_ext
            | some ty =>
              rw [h_oty] at h_ext
              rcases ty with ⟨kind, lidx⟩
              cases kind with
              | fnDef _ _ =>
                dsimp only [fnEntryCompatibleWithCallSite]
                exact Bool.and_false _
              | _ =>
                dsimp only [extractFnItemTarget?] at h_ext
                nomatch h_ext
          cases Bool.and (Nat.beq sz 8)
            (Bool.and (Nat.beq ptrVal.offsetBytes 0)
              (match lookupBorrow s.memory.borrows ptrVal.tag with
               | .some _ => false
               | .none => true)) with
          | false => rfl
          | true =>
            dsimp only
            cases lookupFnPtr s.memory.fnPtrs ptrVal.allocId with
            | none => rfl
            | some fnEntry =>
              dsimp only
              rw [h_sig_false fnEntry]
        | _ => rfl

private theorem resolvePureCalleeTarget_ok_target
    {locals locals' : List LocalSlot} {func : Operand}
    {defPath : DefPath} {typeArgs : List RigidTy}
    {callerLayouts : LayoutTable} {target : ResolvedCallTarget}
    (h :
      resolvePureCalleeTarget locals func defPath typeArgs callerLayouts =
        .ok target locals') :
    target =
      { defPath := defPath
        typeArgs := typeArgs
        fnSig := .none
        isIndirect := false } := by
  unfold resolvePureCalleeTarget at h
  cases h_def : extractCalleeDefPath? func with
  | some _ =>
    rw [h_def] at h
    injection h with ht _
    exact ht.symm
  | none =>
    rw [h_def] at h
    dsimp only at h
    cases h_ev : evalOperand locals func [] [] callerLayouts [] with
    | ub =>
      rw [h_ev] at h
      nomatch h
    | unsupported =>
      rw [h_ev] at h
      nomatch h
    | ok v _ =>
      rw [h_ev] at h
      cases v with
      | unit =>
        dsimp only at h
        injection h with ht _
        exact ht.symm
      | aggregate vIdx flds =>
        cases vIdx with
        | zero =>
          cases flds with
          | nil =>
            simp only [Nat.zero_eq] at h
            injection h with ht _
            exact ht.symm
          | cons _ _ =>
            nomatch h
        | succ _ =>
          nomatch h
      | _ =>
        dsimp only at h
        nomatch h

/--
Syntactic purity check on a `TerminatorKind` parameterized by a boolean
predicate `checkCallee : CapturedMir → Bool` on resolved callees in `callees`:
- Accepts every call-free terminator accepted by `isPureTerminator`.
- Accepts `TerminatorKind.call func argOps destination (.some _) _` when
  `isPurePlace destination`, `argOps.all isPureOperand`, and
  `extractPureCalleeTarget? callerLocalDecls callerLayouts func =
  some (defPath, typeArgs)` (including both constant function items and local
  or projected zero-sized `RigidTy.fnDef` slots), provided either
  `lookupCallee callees callerLayouts defPath typeArgs traitImpls` resolves to
  `some calleeBody` with `checkCallee calleeBody = true`, or resolves to `none`
  with `defPath == "core::intrinsics::exact_div"`.
- Accepts diverging `TerminatorKind.call func argOps destination .none _` when
  `isPurePlace destination`, `argOps.all isPureOperand`, and
  `extractPureCalleeTarget?` resolves `(defPath, typeArgs)` either to a pure
  `calleeBody` or to a standard Rust panic/abort/unreachable target.
- Accepts `TerminatorKind.tailCall func argOps` when `argOps.all isPureOperand`
  and `extractPureCalleeTarget?` resolves `(defPath, typeArgs)` to
  `some calleeBody` in `lookupCallee` with `checkCallee calleeBody = true`.
-/
def checkPureTerminatorWith
    (callees : List CapturedMir)
    (callerLayouts : LayoutTable)
    (traitImpls : List TraitImplEntry)
    (checkCallee : CapturedMir → Bool)
    (tk : TerminatorKind)
    (callerLocalDecls : List LocalDecl := []) : Bool :=
  if isPureTerminator tk then
    true
  else
    match tk with
    | .call func argOps destination targetOpt _ =>
      isPurePlace destination &&
      argOps.all isPureOperand &&
      match extractPureCalleeTarget? callerLocalDecls callerLayouts func with
      | .none => false
      | .some (defPath, typeArgs) =>
        match lookupCallee callees callerLayouts defPath typeArgs traitImpls with
        | .some calleeBody => checkCallee calleeBody
        | .none =>
          match targetOpt with
          | .some _ => stringEq defPath "core::intrinsics::exact_div"
          | .none =>
            isUnreachableCallTarget defPath ||
            isAbortingPanicDefPath defPath ||
            isUnwindingPanicDefPath defPath
    | .tailCall func argOps =>
      argOps.all isPureOperand &&
      match extractPureCalleeTarget? callerLocalDecls callerLayouts func with
      | .none => false
      | .some (defPath, typeArgs) =>
        match lookupCallee callees callerLayouts defPath typeArgs traitImpls with
        | .some calleeBody => checkCallee calleeBody
        | .none => false
    | _ => false

/--
Computable callee-aware syntactic purity checker (`FF-2.2` Section 2 & 4):
recursively verifies `body` and all direct, local zero-sized function-item,
polymorphic `(defPath, typeArgs)`, and `TraitImplEntry`-dispatched callees
reachable in `callees` up to structural call-depth bound `maxCallDepth`
(defaulting to `defaultMaxCallDepth`).
-/
def checkPureMirWithCallees
    (callees : List CapturedMir)
    (body : CapturedMir)
    (maxCallDepth : Nat := defaultMaxCallDepth)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Bool :=
  match maxCallDepth with
  | 0 =>
    body.basicBlocks.all (fun block =>
      block.statements.all (fun stmt => isPureStatement stmt.kind) &&
      checkPureTerminatorWith callees body.layouts traitImpls (fun _ => false)
        block.terminator.kind body.localDecls)
  | depth' + 1 =>
    body.basicBlocks.all (fun block =>
      block.statements.all (fun stmt => isPureStatement stmt.kind) &&
      checkPureTerminatorWith callees body.layouts traitImpls
        (fun calleeBody =>
          checkPureMirWithCallees callees calleeBody depth' traitImpls)
        block.terminator.kind body.localDecls)

theorem checkPureTerminatorWith_mono
    {callees : List CapturedMir} {layouts : LayoutTable}
    {traitImpls : List TraitImplEntry}
    {f g : CapturedMir → Bool} {tk : TerminatorKind}
    {callerLocalDecls : List LocalDecl}
    (h_imp : ∀ cb, f cb = true → g cb = true)
    (h :
      checkPureTerminatorWith callees layouts traitImpls f tk
        callerLocalDecls = true) :
    checkPureTerminatorWith callees layouts traitImpls g tk
      callerLocalDecls = true := by
  unfold checkPureTerminatorWith at h ⊢
  by_cases h_pt : isPureTerminator tk = true
  · simp [h_pt]
  · simp only [h_pt, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases tk <;> try exact False.elim (Bool.false_ne_true h)
    · simp only [Bool.and_eq_true] at h ⊢
      rcases h with ⟨⟨hp1, hp2⟩, h_ext⟩
      refine ⟨⟨hp1, hp2⟩, ?_⟩
      cases h_ed : extractPureCalleeTarget? callerLocalDecls layouts _ with
      | none =>
        rw [h_ed] at h_ext
        exact False.elim (Bool.false_ne_true h_ext)
      | some dt =>
        rcases dt with ⟨defPath, typeArgs⟩
        rw [h_ed] at h_ext
        dsimp only at h_ext ⊢
        cases h_lk : lookupCallee callees layouts defPath typeArgs traitImpls with
        | none =>
          rw [h_lk] at h_ext
          exact h_ext
        | some cb =>
          rw [h_lk] at h_ext
          exact h_imp cb h_ext
    · simp only [Bool.and_eq_true] at h ⊢
      rcases h with ⟨hp1, h_ext⟩
      refine ⟨hp1, ?_⟩
      cases h_ed : extractPureCalleeTarget? callerLocalDecls layouts _ with
      | none =>
        rw [h_ed] at h_ext
        exact False.elim (Bool.false_ne_true h_ext)
      | some dt =>
        rcases dt with ⟨defPath, typeArgs⟩
        rw [h_ed] at h_ext
        dsimp only at h_ext ⊢
        cases h_lk : lookupCallee callees layouts defPath typeArgs traitImpls with
        | none =>
          rw [h_lk] at h_ext
          exact h_ext
        | some cb =>
          rw [h_lk] at h_ext
          exact h_imp cb h_ext

private theorem list_all_mono {α : Type} {p q : α → Bool} {xs : List α}
    (h_imp : ∀ x, p x = true → q x = true)
    (h : xs.all p = true) :
    xs.all q = true := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨h_imp hd h.1, ih h.2⟩

/--
Every call-free `checkPureMir body = true` witness is also accepted by
`checkPureMirWithCallees` at any `callees`, `maxCallDepth`, and `traitImpls`.
-/
theorem checkPureMirWithCallees_of_checkPureMir
    {body : CapturedMir}
    (callees : List CapturedMir)
    (maxCallDepth : Nat := defaultMaxCallDepth)
    (traitImpls : List TraitImplEntry := body.traitImpls)
    (h_pure : checkPureMir body = true) :
    checkPureMirWithCallees callees body maxCallDepth traitImpls = true := by
  unfold checkPureMir at h_pure
  cases maxCallDepth <;>
    (unfold checkPureMirWithCallees;
     refine list_all_mono (fun block h_b => ?_) h_pure;
     simp only [Bool.and_eq_true] at h_b ⊢;
     refine ⟨h_b.1, ?_⟩;
     unfold checkPureTerminatorWith;
     simp [h_b.2])

/-- Monotonicity of `checkPureMirWithCallees` in `maxCallDepth`. -/
theorem checkPureMirWithCallees_mono_depth
    {callees : List CapturedMir} {body : CapturedMir}
    {d₁ d₂ : Nat} {traitImpls : List TraitImplEntry}
    (h_le : d₁ ≤ d₂)
    (h : checkPureMirWithCallees callees body d₁ traitImpls = true) :
    checkPureMirWithCallees callees body d₂ traitImpls = true := by
  induction d₁ generalizing body d₂ with
  | zero =>
    cases d₂ with
    | zero => exact h
    | succ d₂' =>
      unfold checkPureMirWithCallees at h ⊢
      refine list_all_mono (fun block h_b => ?_) h
      simp only [Bool.and_eq_true] at h_b ⊢
      exact ⟨h_b.1, checkPureTerminatorWith_mono
        (fun _ h_f => False.elim (Bool.false_ne_true h_f)) h_b.2⟩
  | succ d₁' ih =>
    cases d₂ with
    | zero => omega
    | succ d₂' =>
      have h_le' : d₁' ≤ d₂' := by omega
      unfold checkPureMirWithCallees at h ⊢
      refine list_all_mono (fun block h_b => ?_) h
      simp only [Bool.and_eq_true] at h_b ⊢
      exact ⟨h_b.1, checkPureTerminatorWith_mono (fun cb h_cb => ih h_le' h_cb) h_b.2⟩

/--
Existential purity witness over `callees` and `traitImpls` at some finite call
depth `d`.
-/
def IsPureWithCalleesAtSomeDepth
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (body : CapturedMir) : Prop :=
  ∃ d : Nat, checkPureMirWithCallees callees body d traitImpls = true

theorem IsPureWithCalleesAtSomeDepth.block
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h_pure : IsPureWithCalleesAtSomeDepth callees traitImpls body)
    (h_bb : get? body.basicBlocks bbIdx = some bb) :
    bb.statements.all (fun stmt => isPureStatement stmt.kind) = true ∧
    checkPureTerminatorWith callees body.layouts traitImpls
      (fun cb =>
        match Classical.propDecidable (IsPureWithCalleesAtSomeDepth callees traitImpls cb) with
        | .isTrue _ => true
        | .isFalse _ => false)
      bb.terminator.kind body.localDecls = true := by
  have h_bb_nat : List.get?Internal body.basicBlocks (bbIdx : Nat) = some bb := h_bb
  let _ := h_bb_nat
  rcases h_pure with ⟨d, hd⟩
  cases d with
  | zero =>
    unfold checkPureMirWithCallees at hd
    have hb := Bool.and_eq_true_iff.mp
      (list_all_of_get? (xs := body.basicBlocks) (idx := (bbIdx : Nat)) hd h_bb)
    refine ⟨hb.1, checkPureTerminatorWith_mono (fun _ hf => ?_) hb.2⟩
    exact False.elim (Bool.false_ne_true hf)
  | succ d' =>
    unfold checkPureMirWithCallees at hd
    have hb := Bool.and_eq_true_iff.mp
      (list_all_of_get? (xs := body.basicBlocks) (idx := (bbIdx : Nat)) hd h_bb)
    refine ⟨hb.1, checkPureTerminatorWith_mono (fun cb hcb => ?_) hb.2⟩
    have h_ex : IsPureWithCalleesAtSomeDepth callees traitImpls cb := ⟨d', hcb⟩
    cases Classical.propDecidable (IsPureWithCalleesAtSomeDepth callees traitImpls cb) with
    | isTrue _ => rfl
    | isFalse h_not => exact False.elim (h_not h_ex)

/--
Transplant the transient call-stack activation fields (`callStack`,
`activeCallee`, `activeProtectors`) from a pure reference memory `m` onto root
caller memory `mem₀`, preserving all persistent caller fields (`nextAllocId`,
`globals`, `borrows`, `nextTag`, `callees`, `traitImpls`, `nextProtector`,
`callerLocals`, `fnPtrs`) of `mem₀`.
-/
def Memory.replaceRoot (mem₀ m : Memory) : Memory :=
  { mem₀ with
    callStack := m.callStack
    activeCallee := m.activeCallee
    activeProtectors := m.activeProtectors }

/-- Lift `Memory.replaceRoot mem₀` to `MachineState`. -/
def MachineState.replaceRoot (mem₀ : Memory) (s : MachineState) : MachineState :=
  { s with memory := Memory.replaceRoot mem₀ s.memory }

/-- Lift `Memory.replaceRoot mem₀` to `MirOutcome`. -/
def MirOutcome.replaceRoot (mem₀ : Memory) : MirOutcome → MirOutcome
  | .normal (v, m) => .normal (v, Memory.replaceRoot mem₀ m)
  | .panic => .panic
  | .abort => .abort

/-- Lift `Memory.replaceRoot mem₀` to `MirExecState`. -/
def MirExecState.replaceRoot (mem₀ : Memory) : MirExecState → MirExecState
  | .running s => .running (MachineState.replaceRoot mem₀ s)
  | .halted out => .halted (MirOutcome.replaceRoot mem₀ out)
  | .faulted fk => .faulted fk

/-- Lift `Memory.replaceRoot mem₀` to `MirStepNode`. -/
def MirStepNode.replaceRoot (mem₀ : Memory) : MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.replaceRoot mem₀ out)
  | .tau st => .tau (MirExecState.replaceRoot mem₀ st)
  | .vis (.inl f) k => .vis (.inl f) k
  | .vis (.inr e) k => .vis (.inr e) (fun o => MirExecState.replaceRoot mem₀ (k o))

@[simp]
theorem Memory.replaceRoot_pureCalleeMemory_of_rootActive
    {mem₀ : Memory} {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    (h_root : RootActiveMemory mem₀) :
    Memory.replaceRoot mem₀ (pureCalleeMemory callees traitImpls) = mem₀ := by
  rcases h_root with ⟨_, h_cs, h_ac, h_ap⟩
  cases mem₀
  dsimp only [Memory.replaceRoot, pureCalleeMemory] at h_cs h_ac h_ap ⊢
  subst h_cs h_ac h_ap
  rfl

theorem ActiveRootMemory.replaceRoot_of_pureCalleeMemory
    {body : CapturedMir} {mem₀ m : Memory}
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    (h_root : RootActiveMemory mem₀)
    (h_act : ActiveRootMemory body (pureCalleeMemory callees traitImpls) m) :
    ActiveRootMemory body mem₀ (Memory.replaceRoot mem₀ m) := by
  rcases h_act with rfl | ⟨b, rfl⟩
  · rw [Memory.replaceRoot_pureCalleeMemory_of_rootActive h_root]
    exact Or.inl rfl
  · rcases h_root with ⟨_, h_cs, _, h_ap⟩
    have h_eq :
        Memory.replaceRoot mem₀
          { pureCalleeMemory callees traitImpls with activeCallee := some b } =
        { mem₀ with activeCallee := some b } := by
      cases mem₀
      dsimp only [Memory.replaceRoot, pureCalleeMemory] at h_cs h_ap ⊢
      subst h_cs h_ap
      rfl
    rw [h_eq]
    exact Or.inr ⟨b, rfl⟩

private theorem MirStepNode.replaceRoot_withMem
    (mem₀ m : Memory) (node : MirStepNode) :
    MirStepNode.replaceRoot mem₀ (MirStepNode.withMem m node) =
      MirStepNode.withMem (Memory.replaceRoot mem₀ m) node := by
  cases node with
  | ret out =>
    cases out with
    | normal rv => rfl
    | panic => rfl
    | abort => rfl
  | tau st =>
    cases st with
    | running s => rfl
    | halted out =>
      cases out with
      | normal rv => rfl
      | panic => rfl
      | abort => rfl
    | faulted fk => rfl
  | vis i k =>
    cases i with
    | inl f => rfl
    | inr e =>
      dsimp only [MirStepNode.withMem, MirStepNode.replaceRoot]
      congr 1
      funext o
      cases k o with
      | running s => rfl
      | halted out =>
        cases out with
        | normal rv => rfl
        | panic => rfl
        | abort => rfl
      | faulted fk => rfl

private theorem unwindFromCallStack_replaceRoot
    (mem₀ : Memory) (cs : List SavedCallerFrame) (m : Memory) :
    unwindFromCallStack cs (Memory.replaceRoot mem₀ m) =
      MirExecState.replaceRoot mem₀ (unwindFromCallStack cs m) := by
  induction cs generalizing m with
  | nil => rfl
  | cons caller rest ih =>
    dsimp only [unwindFromCallStack]
    cases caller.returnUnwind with
    | unreachable => rfl
    | terminate => rfl
    | cleanup cleanupBb => rfl
    | continue_ =>
      exact ih {
        m with
        callStack := rest
        activeCallee := some caller.callerBody
        activeProtectors := restoreCallerProtectors caller
      }

private theorem applyUnwindAction_replaceRoot
    (mem₀ : Memory) (s : MachineState) (locs : List LocalSlot)
    (m : Memory) (unwind : UnwindAction) :
    applyUnwindAction (MachineState.replaceRoot mem₀ s) locs
        (Memory.replaceRoot mem₀ m) unwind =
      MirExecState.replaceRoot mem₀ (applyUnwindAction s locs m unwind) := by
  cases unwind with
  | unreachable => rfl
  | terminate => rfl
  | cleanup _ => rfl
  | continue_ => exact unwindFromCallStack_replaceRoot mem₀ m.callStack m

/--
Frame-and-stack invariant maintained across all reachable `MachineState`s from
`ps.toMachineState (pureCalleeMemory callees traitImpls)` when `body` passes
`checkPureMirWithCallees`.
-/
def PureCalleeMachineInv
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (body : CapturedMir) (s : MachineState) : Prop :=
  s.memory.borrows = [] ∧
  s.memory.globals = [] ∧
  s.memory.callerLocals = [] ∧
  s.memory.activeProtectors = [] ∧
  s.memory.callees = callees ∧
  s.memory.traitImpls = traitImpls ∧
  IsPureWithCalleesAtSomeDepth callees traitImpls (s.memory.activeCallee.getD body) ∧
  ∀ f ∈ s.memory.callStack,
    f.callerProtector = none ∧
    f.calleeProtectors = [] ∧
    IsPureWithCalleesAtSomeDepth callees traitImpls f.callerBody

private theorem PureCalleeMachineInv.init
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} (ps : PureState)
    (h_pure : IsPureWithCalleesAtSomeDepth callees traitImpls body) :
    PureCalleeMachineInv callees traitImpls body
      (ps.toMachineState (pureCalleeMemory callees traitImpls)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, h_pure, fun _ hf => nomatch hf⟩

private theorem unwindFromCallStack_preserves_inv
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} {cs : List SavedCallerFrame} {m : Memory}
    (h_bor : m.borrows = [])
    (h_glob : m.globals = [])
    (h_cloc : m.callerLocals = [])
    (h_cal : m.callees = callees)
    (h_tr : m.traitImpls = traitImpls)
    (h_stack : ∀ f ∈ cs,
      f.callerProtector = none ∧
      f.calleeProtectors = [] ∧
      IsPureWithCalleesAtSomeDepth callees traitImpls f.callerBody) :
    match unwindFromCallStack cs m with
    | .running s' => PureCalleeMachineInv callees traitImpls body s'
    | _ => True := by
  induction cs generalizing m with
  | nil => trivial
  | cons caller rest ih =>
    have h_hd := h_stack caller (List.Mem.head rest)
    have h_tl : ∀ f ∈ rest,
        f.callerProtector = none ∧
        f.calleeProtectors = [] ∧
        IsPureWithCalleesAtSomeDepth callees traitImpls f.callerBody :=
      fun f hf => h_stack f (List.Mem.tail caller hf)
    have h_prot_nil : restoreCallerProtectors caller = [] := by
      rcases h_hd with ⟨hp1, hp2, _⟩
      simp [restoreCallerProtectors, hp1, hp2]
    dsimp only [unwindFromCallStack]
    cases caller.returnUnwind with
    | unreachable => trivial
    | terminate => trivial
    | continue_ =>
      exact ih h_bor h_glob h_cloc h_cal h_tr h_tl
    | cleanup cleanupBb =>
      exact ⟨h_bor, h_glob, h_cloc, h_prot_nil, h_cal, h_tr, h_hd.2.2, h_tl⟩

private theorem applyUnwindAction_preserves_inv
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} {s : MachineState} {locs : List LocalSlot}
    {unwind : UnwindAction}
    (h_inv : PureCalleeMachineInv callees traitImpls body s) :
    match applyUnwindAction s locs s.memory unwind with
    | .running s' => PureCalleeMachineInv callees traitImpls body s'
    | _ => True := by
  rcases h_inv with ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
  cases unwind with
  | unreachable => trivial
  | terminate => trivial
  | cleanup _ =>
    exact ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
  | continue_ =>
    exact unwindFromCallStack_preserves_inv h_bor h_glob h_cloc h_cal h_tr h_stack

private def pureNodeStepInv
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (body : CapturedMir) : MirStepNode → Prop
  | .ret _ => True
  | .tau st' =>
    match st' with
    | .running s' => PureCalleeMachineInv callees traitImpls body s'
    | _ => True
  | .vis (.inl _) _ => True
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => PureCalleeMachineInv callees traitImpls body s'
    | _ => True
  | .vis (.inr (.inr _)) _ => False

private theorem evalStmt_preserves_pureCalleeMachineInv
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} {s : MachineState} {stmt : Statement}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h_pure : isPureStatement stmt.kind = true)
    (h_inv : PureCalleeMachineInv callees traitImpls body s) :
    pureNodeStepInv callees traitImpls body
      (evalStmt s stmt localDecls layouts) := by
  have h_eq : s = (PureState.ofMachineState s).toMachineState s.memory := by
    cases s; rfl
  have h_stmt :=
    evalStmt_toMachineState_eq_withMem_of_frameFree
      (PureState.ofMachineState s) s.memory stmt localDecls layouts
      h_pure h_inv.1 h_inv.2.2.2.1
  rw [← h_eq] at h_stmt
  have h_no_ext :=
    evalStmt_not_extCall (PureState.ofMachineState s |>.toMachineState emptyMemory)
      stmt localDecls layouts
  rw [h_stmt]
  cases h_emp : evalStmt ((PureState.ofMachineState s).toMachineState emptyMemory)
      stmt localDecls layouts with
  | ret _ => trivial
  | tau st' =>
    cases st' with
    | halted _ => trivial
    | faulted _ => trivial
    | running s' =>
      dsimp only [MirStepNode.withMem, MirExecState.withMem, pureNodeStepInv]
      exact h_inv
  | vis i k =>
    rcases i with f | (e | c)
    · trivial
    · cases e
      dsimp only [MirStepNode.withMem, pureNodeStepInv]
      cases k PUnit.unit with
      | halted _ => trivial
      | faulted _ => trivial
      | running s' => exact h_inv
    · exact False.elim (h_no_ext c k h_emp)

private def evalCallTerminatorUnified
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (unwind : UnwindAction)
    (currentBody : Option CapturedMir) :
    MirStepNode :=
  let bodyLocalDecls := bodyLocalDeclsOf currentBody
  let bodyLayouts : LayoutTable :=
    match currentBody with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  match resolveCallTarget s func (length argOps) bodyLocalDecls bodyLayouts with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok target localsAfterFunc =>
    match
      evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
        bodyLayouts s.memory.callerLocals
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok argVals locals' =>
      match lookupCallee s.memory.callees bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
      | .some calleeBody =>
        match targetOpt with
        | .some targetBb =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind)
        | .none =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushDivergingCalleeFrame s callerBody locals' destination unwind calleeBody argVals)
      | .none =>
        match targetOpt with
        | .some targetBb =>
          match isDirectExactDivTarget target with
          | true =>
            match argVals with
            | .scalar lhs :: .scalar rhs :: .nil =>
              match resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps with
              | .none => MirStepNode.unsupported
              | .some isSigned =>
                match evalExactDiv lhs rhs isSigned with
                | .some retScalar =>
                  match writePlaceValue locals' s.memory.borrows destination (.scalar retScalar) with
                  | .ok updatedLocals =>
                    MirStepNode.step {
                      frame := {
                        s.frame with
                        blockIdx := targetBb
                        stmtIdx := 0
                        locals := updatedLocals
                      }
                      memory := s.memory
                    }
                  | .ub => MirStepNode.fail .ub
                  | .unsupported => MirStepNode.unsupported
                | .none => MirStepNode.fail .ub
            | _ => MirStepNode.fail .ub
          | false =>
            match target.isIndirect with
            | true =>
              MirStepNode.extCall
                { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
            | false =>
              match
                evalDirectRustIntrinsic? s currentBody target bodyLocalDecls
                  bodyLayouts argOps argVals locals' destination targetBb unwind
              with
              | .some stepNode => stepNode
              | .none =>
                MirStepNode.extCall
                  { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                  (resumeExternalCall s locals' destination targetBb unwind)
        | .none =>
          match target.isIndirect with
          | false =>
            match isUnreachableCallTarget target.defPath with
            | true => MirStepNode.fail .ub
            | false =>
              match isAbortingPanicDefPath target.defPath with
              | true => MirStepNode.retOutcome .abort
              | false =>
                match isUnwindingPanicDefPath target.defPath with
                | true =>
                  match applyUnwindAction s locals' s.memory unwind with
                  | .running nextState => MirStepNode.step nextState
                  | .halted out => MirStepNode.retOutcome out
                  | .faulted fk => MirStepNode.fail fk
                | false =>
                  MirStepNode.extCall
                    { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                    (resumeExternalDivergingCall s locals' unwind)
          | true =>
            MirStepNode.extCall
              { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)

private theorem evalTerminator_call_eq_unified
    (s : MachineState) (func : Operand) (argOps : List Operand)
    (destination : Place) (targetOpt : Option BasicBlockIdx)
    (unwind : UnwindAction) (sp : String) (currentBody : Option CapturedMir) :
    evalTerminator s { kind := .call func argOps destination targetOpt unwind, span := sp } currentBody =
      evalCallTerminatorUnified s func argOps destination targetOpt unwind currentBody := by
  cases currentBody with
  | none =>
    cases targetOpt <;>
      (dsimp only [evalTerminator, evalCallTerminatorUnified, bodyLocalDeclsOf];
       cases resolveCallTarget s func (length argOps) [] emptyLayoutTable with
       | ub => rfl
       | unsupported => rfl
       | ok target localsAfterFunc =>
         cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
             emptyLayoutTable s.memory.callerLocals with
         | ub => rfl
         | unsupported => rfl
         | ok argVals locals' =>
           cases lookupCallee s.memory.callees emptyLayoutTable
               target.defPath target.typeArgs s.memory.traitImpls <;> rfl)
  | some b =>
    cases targetOpt <;>
      (dsimp only [evalTerminator, evalCallTerminatorUnified, bodyLocalDeclsOf];
       cases resolveCallTarget s func (length argOps) b.localDecls b.layouts with
       | ub => rfl
       | unsupported => rfl
       | ok target localsAfterFunc =>
         cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
             b.layouts s.memory.callerLocals with
         | ub => rfl
         | unsupported => rfl
         | ok argVals locals' =>
           cases lookupCallee s.memory.callees b.layouts
               target.defPath target.typeArgs s.memory.traitImpls <;> rfl)

/--
Core one-step lockstep theorem for `checkPureMirWithCallees`:
under `PureCalleeMachineInv callees traitImpls body s` and a caller memory
`mem₀` with `mem₀.borrows = []`, `mem₀.callees = callees`, and
`mem₀.traitImpls = traitImpls`:
1. `stepMirFn body s` preserves `PureCalleeMachineInv` and never emits an
   external `MirCallE` interaction (`pureNodeStepInv`), and
2. `stepMirFn body (MachineState.replaceRoot mem₀ s)` equals
   `MirStepNode.replaceRoot mem₀ (stepMirFn body s)`.
-/
private theorem stepMirFn_pureCallee_step_and_replaceRoot
    {callees : List CapturedMir} {traitImpls : List TraitImplEntry}
    {body : CapturedMir} {mem₀ : Memory} {s : MachineState}
    (h_inv : PureCalleeMachineInv callees traitImpls body s)
    (h_mem_bor : mem₀.borrows = [])
    (h_mem_cal : mem₀.callees = callees)
    (h_mem_tr : mem₀.traitImpls = traitImpls) :
    pureNodeStepInv callees traitImpls body (stepMirFn body s) ∧
    stepMirFn body (MachineState.replaceRoot mem₀ s) =
      MirStepNode.replaceRoot mem₀ (stepMirFn body s) := by
  rcases h_inv with ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
  have h_inv_full : PureCalleeMachineInv callees traitImpls body s :=
    ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
  rw [stepMirFn_eq_ite, stepMirFn_eq_ite]
  dsimp only [MachineState.replaceRoot, Memory.replaceRoot]
  cases isOtherPhase (s.memory.activeCallee.getD body).phase with
  | true =>
    simp only [ite_true]
    exact ⟨trivial, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => exact ⟨trivial, rfl⟩
    | some bb =>
      dsimp only
      have ⟨h_stmts, h_term⟩ := IsPureWithCalleesAtSomeDepth.block h_act h_bb
      cases h_stmt : get? bb.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        have h_s := list_all_of_get? h_stmts h_stmt
        refine ⟨evalStmt_preserves_pureCalleeMachineInv h_s h_inv_full, ?_⟩
        have h_eq1 :=
          evalStmt_toMachineState_eq_withMem_of_frameFree
            (PureState.ofMachineState s) (Memory.replaceRoot mem₀ s.memory) stmt
            (s.memory.activeCallee.getD body).localDecls
            (s.memory.activeCallee.getD body).layouts
            h_s h_mem_bor h_ap
        have h_eq2 :=
          evalStmt_toMachineState_eq_withMem_of_frameFree
            (PureState.ofMachineState s) s.memory stmt
            (s.memory.activeCallee.getD body).localDecls
            (s.memory.activeCallee.getD body).layouts
            h_s h_bor h_ap
        have hs1 :
            (PureState.ofMachineState s).toMachineState
              (Memory.replaceRoot mem₀ s.memory) =
            { s with memory := Memory.replaceRoot mem₀ s.memory } := by
          cases s; rfl
        have hs2 :
            (PureState.ofMachineState s).toMachineState s.memory = s := by
          cases s; rfl
        rw [hs1] at h_eq1
        rw [hs2] at h_eq2
        dsimp only [Memory.replaceRoot] at h_eq1
        rw [h_eq1, h_eq2, MirStepNode.replaceRoot_withMem]
        rfl
      | none =>
        dsimp only
        by_cases h_len : (s.frame.stmtIdx == length bb.statements) = true
        · simp only [h_len, ite_true]
          rcases bb with ⟨stmts, ⟨tkind, tspan⟩, isCl⟩
          dsimp only at h_term
          by_cases h_pt : isPureTerminator tkind = true
          · cases tkind with
            | goto target =>
              exact ⟨h_inv_full, rfl⟩
            | unreachable =>
              exact ⟨trivial, rfl⟩
            | unwindTerminate =>
              exact ⟨trivial, rfl⟩
            | inlineAsm =>
              cases h_pt
            | call _ _ _ _ _ =>
              cases h_pt
            | tailCall _ _ =>
              cases h_pt
            | drop p target unwind =>
              rcases p with ⟨loc, proj⟩
              dsimp only [evalTerminator]
              cases h_g : get? s.frame.locals loc with
              | none => exact ⟨trivial, rfl⟩
              | some slot =>
                cases slot with
                | dead => exact ⟨trivial, rfl⟩
                | uninit =>
                  dsimp only
                  cases proj with
                  | nil =>
                    dsimp only
                    cases set? s.frame.locals loc .uninit with
                    | none => exact ⟨trivial, rfl⟩
                    | some _ => exact ⟨h_inv_full, rfl⟩
                  | cons _ _ => exact ⟨trivial, rfl⟩
                | init rv =>
                  dsimp only
                  cases proj with
                  | nil =>
                    dsimp only
                    cases set? s.frame.locals loc .uninit with
                    | none => exact ⟨trivial, rfl⟩
                    | some _ => exact ⟨h_inv_full, rfl⟩
                  | cons hd tl =>
                    dsimp only
                    cases readProjectedValue s.frame.locals rv (hd :: tl) with
                    | ub => exact ⟨trivial, rfl⟩
                    | unsupported => exact ⟨trivial, rfl⟩
                    | ok _ => exact ⟨h_inv_full, rfl⟩
            | unwindResume =>
              dsimp only [evalTerminator]
              have h_unw :=
                unwindFromCallStack_preserves_inv (body := body)
                  h_bor h_glob h_cloc h_cal h_tr h_stack
              have h_rep :=
                unwindFromCallStack_replaceRoot mem₀ s.memory.callStack s.memory
              dsimp only [Memory.replaceRoot] at h_rep
              rw [h_rep]
              cases h_u : unwindFromCallStack s.memory.callStack s.memory with
              | running ns =>
                rw [h_u] at h_unw
                exact ⟨h_unw, rfl⟩
              | halted out =>
                cases out <;> exact ⟨trivial, rfl⟩
              | faulted fk => exact ⟨trivial, rfl⟩
            | return_ =>
              dsimp only [evalTerminator]
              cases get? s.frame.locals 0 with
              | none => exact ⟨trivial, rfl⟩
              | some slot =>
                cases slot with
                | uninit => exact ⟨trivial, rfl⟩
                | dead => exact ⟨trivial, rfl⟩
                | init retVal =>
                  dsimp only
                  cases h_cs : s.memory.callStack with
                  | nil =>
                    refine ⟨trivial, ?_⟩
                    dsimp only [MirStepNode.replaceRoot, MirOutcome.replaceRoot,
                      Memory.replaceRoot, MirStepNode.retNormal]
                    simp only [h_cs]
                  | cons caller rest =>
                    dsimp only
                    cases caller.isDiverging with
                    | true => exact ⟨trivial, rfl⟩
                    | false =>
                      dsimp only
                      rw [h_mem_bor, h_bor]
                      cases writePlaceValue caller.frame.locals []
                          caller.destination retVal with
                      | ub => exact ⟨trivial, rfl⟩
                      | unsupported => exact ⟨trivial, rfl⟩
                      | ok updLocals =>
                        have h_hd := h_stack caller (by rw [h_cs]; exact List.Mem.head rest)
                        have h_tl : ∀ f ∈ rest,
                            f.callerProtector = none ∧
                            f.calleeProtectors = [] ∧
                            IsPureWithCalleesAtSomeDepth callees traitImpls f.callerBody :=
                          fun f hf => h_stack f (by rw [h_cs]; exact List.Mem.tail caller hf)
                        have h_prot_nil : restoreCallerProtectors caller = [] := by
                          rcases h_hd with ⟨hp1, hp2, _⟩
                          simp [restoreCallerProtectors, hp1, hp2]
                        refine ⟨⟨rfl, h_glob, h_cloc, h_prot_nil, h_cal, h_tr,
                          h_hd.2.2, h_tl⟩, ?_⟩
                        dsimp only [MirStepNode.replaceRoot, MirExecState.replaceRoot,
                          MachineState.replaceRoot, Memory.replaceRoot, MirStepNode.step]
                        simp only [h_mem_bor]
            | switchInt discr targets =>
              dsimp only [isPureTerminator] at h_pt
              dsimp only [evalTerminator]
              rw [evalOperand_pure_eq s.frame.locals discr mem₀.borrows
                mem₀.globals (s.memory.activeCallee.getD body).layouts
                mem₀.callerLocals h_pt]
              rw [evalOperand_pure_eq s.frame.locals discr s.memory.borrows
                s.memory.globals (s.memory.activeCallee.getD body).layouts
                s.memory.callerLocals h_pt]
              cases evalOperand s.frame.locals discr [] []
                  (s.memory.activeCallee.getD body).layouts [] with
              | ub => exact ⟨trivial, rfl⟩
              | unsupported => exact ⟨trivial, rfl⟩
              | ok val locals' =>
                cases val with
                | scalar sc => exact ⟨h_inv_full, rfl⟩
                | _ => exact ⟨trivial, rfl⟩
            | assert cond expected target unwind =>
              dsimp only [isPureTerminator] at h_pt
              dsimp only [evalTerminator]
              rw [evalOperand_pure_eq s.frame.locals cond mem₀.borrows
                mem₀.globals (s.memory.activeCallee.getD body).layouts
                mem₀.callerLocals h_pt]
              rw [evalOperand_pure_eq s.frame.locals cond s.memory.borrows
                s.memory.globals (s.memory.activeCallee.getD body).layouts
                s.memory.callerLocals h_pt]
              cases evalOperand s.frame.locals cond [] []
                  (s.memory.activeCallee.getD body).layouts [] with
              | ub => exact ⟨trivial, rfl⟩
              | unsupported => exact ⟨trivial, rfl⟩
              | ok val locals' =>
                cases val with
                | scalar sc =>
                  cases expected <;> dsimp only
                  · cases Nat.beq sc.bits 0 with
                    | true => exact ⟨h_inv_full, rfl⟩
                    | false =>
                      dsimp only
                      have h_unw :=
                        applyUnwindAction_preserves_inv (locs := locals')
                          (unwind := unwind) h_inv_full
                      have h_rep :=
                        applyUnwindAction_replaceRoot mem₀ s locals' s.memory unwind
                      dsimp only [MachineState.replaceRoot, Memory.replaceRoot] at h_rep
                      rw [h_rep]
                      cases h_app : applyUnwindAction s locals' s.memory unwind with
                      | running ns => rw [h_app] at h_unw; exact ⟨h_unw, rfl⟩
                      | halted out => cases out <;> exact ⟨trivial, rfl⟩
                      | faulted fk => exact ⟨trivial, rfl⟩
                  · cases Nat.beq sc.bits 1 with
                    | true => exact ⟨h_inv_full, rfl⟩
                    | false =>
                      dsimp only
                      have h_unw :=
                        applyUnwindAction_preserves_inv (locs := locals')
                          (unwind := unwind) h_inv_full
                      have h_rep :=
                        applyUnwindAction_replaceRoot mem₀ s locals' s.memory unwind
                      dsimp only [MachineState.replaceRoot, Memory.replaceRoot] at h_rep
                      rw [h_rep]
                      cases h_app : applyUnwindAction s locals' s.memory unwind with
                      | running ns => rw [h_app] at h_unw; exact ⟨h_unw, rfl⟩
                      | halted out => cases out <;> exact ⟨trivial, rfl⟩
                      | faulted fk => exact ⟨trivial, rfl⟩
                | _ => exact ⟨trivial, rfl⟩
          · unfold checkPureTerminatorWith at h_term
            simp only [h_pt, Bool.false_eq_true, ↓reduceIte] at h_term
            cases tkind with
            | call func argOps destination targetOpt unwind =>
              simp only [Bool.and_eq_true] at h_term
              rcases h_term with ⟨⟨h_dst, h_args⟩, h_ext⟩
              cases h_def : extractPureCalleeTarget?
                  (s.memory.activeCallee.getD body).localDecls
                  (s.memory.activeCallee.getD body).layouts func with
              | none =>
                rw [h_def] at h_ext
                exact False.elim (Bool.false_ne_true h_ext)
              | some dt =>
                rcases dt with ⟨defPath, typeArgs⟩
                rw [h_def] at h_ext
                dsimp only at h_ext
                simp only [evalTerminator_call_eq_unified]
                dsimp only [evalCallTerminatorUnified, bodyLocalDeclsOf]
                have h_res_rep :=
                  resolveCallTarget_eq_of_extractPureCalleeTarget
                    ({ s with memory :=
                        { mem₀ with
                          callStack := s.memory.callStack
                          activeCallee := s.memory.activeCallee
                          activeProtectors := s.memory.activeProtectors } })
                    func (length argOps)
                    (s.memory.activeCallee.getD body).localDecls
                    (s.memory.activeCallee.getD body).layouts h_def
                have h_res_s :=
                  resolveCallTarget_eq_of_extractPureCalleeTarget
                    s func (length argOps)
                    (s.memory.activeCallee.getD body).localDecls
                    (s.memory.activeCallee.getD body).layouts h_def
                dsimp only at h_res_rep h_res_s
                rw [h_res_rep, h_res_s]
                cases h_rp : resolvePureCalleeTarget s.frame.locals func
                    defPath typeArgs
                    (s.memory.activeCallee.getD body).layouts with
                | ub => exact ⟨trivial, rfl⟩
                | unsupported => exact ⟨trivial, rfl⟩
                | ok rTarget localsAfterFunc =>
                  have h_rt := resolvePureCalleeTarget_ok_target h_rp
                  subst h_rt
                  dsimp only
                  rw [evalOperands_pure_eq localsAfterFunc argOps mem₀.borrows
                    mem₀.globals (s.memory.activeCallee.getD body).layouts
                    mem₀.callerLocals h_args]
                  rw [evalOperands_pure_eq localsAfterFunc argOps s.memory.borrows
                    s.memory.globals (s.memory.activeCallee.getD body).layouts
                    s.memory.callerLocals h_args]
                  cases evalOperands localsAfterFunc argOps [] []
                      (s.memory.activeCallee.getD body).layouts [] with
                  | ub =>
                    cases targetOpt <;> exact ⟨trivial, rfl⟩
                  | unsupported =>
                    cases targetOpt <;> exact ⟨trivial, rfl⟩
                  | ok argVals locals' =>
                    rw [h_mem_cal, h_mem_tr, h_cal, h_tr]
                    cases h_lk : lookupCallee callees
                        (s.memory.activeCallee.getD body).layouts
                        defPath typeArgs traitImpls with
                    | some calleeBody =>
                      rw [h_lk] at h_ext
                      dsimp only at h_ext
                      have h_cb_pure :
                          IsPureWithCalleesAtSomeDepth callees traitImpls calleeBody := by
                        cases h_dec : Classical.propDecidable
                            (IsPureWithCalleesAtSomeDepth callees traitImpls calleeBody) with
                        | isTrue h_yes => exact h_yes
                        | isFalse _ =>
                          rw [h_dec] at h_ext
                          exact False.elim (Bool.false_ne_true h_ext)
                      have h_stack' :
                          ∀ (callerFrame : SavedCallerFrame),
                            callerFrame.callerProtector = none →
                            callerFrame.calleeProtectors = s.memory.activeProtectors →
                            callerFrame.callerBody = (s.memory.activeCallee.getD body) →
                            ∀ f ∈ callerFrame :: s.memory.callStack,
                              f.callerProtector = none ∧
                              f.calleeProtectors = [] ∧
                              IsPureWithCalleesAtSomeDepth callees traitImpls f.callerBody := by
                        intro cf hcp1 hcp2 hcb f hf
                        cases hf with
                        | head =>
                          rw [hcp1, hcp2, h_ap, hcb]
                          exact ⟨rfl, rfl, h_act⟩
                        | tail _ hmem => exact h_stack f hmem
                      cases targetOpt with
                      | none =>
                        dsimp only [checkCalleeTargetCompatible, pushDivergingCalleeFrame]
                        refine ⟨⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_cb_pure,
                          h_stack' _ rfl rfl rfl⟩, ?_⟩
                        dsimp only [MirStepNode.replaceRoot, MirExecState.replaceRoot,
                          MachineState.replaceRoot, Memory.replaceRoot, MirStepNode.step]
                        simp only [h_mem_cal, h_mem_tr]
                      | some targetBb =>
                        dsimp only [checkCalleeTargetCompatible, pushCalleeFrame]
                        refine ⟨⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_cb_pure,
                          h_stack' _ rfl rfl rfl⟩, ?_⟩
                        dsimp only [MirStepNode.replaceRoot, MirExecState.replaceRoot,
                          MachineState.replaceRoot, Memory.replaceRoot, MirStepNode.step]
                        simp only [h_mem_cal, h_mem_tr]
                    | none =>
                      rw [h_lk] at h_ext
                      cases targetOpt with
                      | some targetBb =>
                        dsimp only at h_ext ⊢
                        dsimp only [isDirectExactDivTarget]
                        rw [h_ext]
                        dsimp only
                        cases argVals with
                        | nil => exact ⟨trivial, rfl⟩
                        | cons v1 vs1 =>
                          cases v1 with
                          | scalar lhsSc =>
                            cases vs1 with
                            | nil => exact ⟨trivial, rfl⟩
                            | cons v2 vs2 =>
                              cases v2 with
                              | scalar rhsSc =>
                                cases vs2 with
                                | cons _ _ => exact ⟨trivial, rfl⟩
                                | nil =>
                                  dsimp only
                                  cases resolveIntrinsicIsSigned
                                      { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
                                      (s.memory.activeCallee.getD body).localDecls
                                      (s.memory.activeCallee.getD body).layouts
                                      argOps with
                                  | none => exact ⟨trivial, rfl⟩
                                  | some isSigned =>
                                    dsimp only
                                    cases evalExactDiv lhsSc rhsSc isSigned with
                                    | none => exact ⟨trivial, rfl⟩
                                    | some retSc =>
                                      dsimp only
                                      rw [h_mem_bor, h_bor]
                                      cases writePlaceValue locals' [] destination
                                          (.scalar retSc) with
                                      | ub => exact ⟨trivial, rfl⟩
                                      | unsupported => exact ⟨trivial, rfl⟩
                                      | ok updLocals =>
                                        refine ⟨h_inv_full, ?_⟩
                                        dsimp only [MirStepNode.replaceRoot,
                                          MirExecState.replaceRoot,
                                          MachineState.replaceRoot,
                                          Memory.replaceRoot, MirStepNode.step]
                                        simp only [h_mem_bor, h_mem_cal, h_mem_tr]
                              | _ => exact ⟨trivial, rfl⟩
                          | _ => exact ⟨trivial, rfl⟩
                      | none =>
                        dsimp only at h_ext ⊢
                        cases h_unr : isUnreachableCallTarget defPath with
                        | true => exact ⟨trivial, rfl⟩
                        | false =>
                          dsimp only
                          cases h_ab : isAbortingPanicDefPath defPath with
                          | true => exact ⟨trivial, rfl⟩
                          | false =>
                            dsimp only
                            rw [h_unr, h_ab] at h_ext
                            simp only [Bool.false_or] at h_ext
                            rw [h_ext]
                            dsimp only
                            have h_unw :=
                              applyUnwindAction_preserves_inv (locs := locals')
                                (unwind := unwind) h_inv_full
                            have h_rep :=
                              applyUnwindAction_replaceRoot mem₀ s locals'
                                s.memory unwind
                            dsimp only [MachineState.replaceRoot, Memory.replaceRoot] at h_rep
                            simp only [h_mem_cal, h_mem_tr] at h_rep
                            rw [h_rep]
                            cases h_app : applyUnwindAction s locals' s.memory unwind with
                            | running ns =>
                              rw [h_app] at h_unw
                              exact ⟨h_unw, rfl⟩
                            | halted out =>
                              cases out <;> exact ⟨trivial, rfl⟩
                            | faulted fk => exact ⟨trivial, rfl⟩
            | tailCall func argOps =>
              simp only [Bool.and_eq_true] at h_term
              rcases h_term with ⟨h_args, h_ext⟩
              cases h_def : extractPureCalleeTarget?
                  (s.memory.activeCallee.getD body).localDecls
                  (s.memory.activeCallee.getD body).layouts func with
              | none =>
                rw [h_def] at h_ext
                exact False.elim (Bool.false_ne_true h_ext)
              | some dt =>
                rcases dt with ⟨defPath, typeArgs⟩
                rw [h_def] at h_ext
                dsimp only at h_ext
                dsimp only [evalTerminator, evalTailCallTerminator,
                  bodyLocalDeclsOf]
                have h_res_rep :=
                  resolveCallTarget_eq_of_extractPureCalleeTarget
                    ({ s with memory :=
                        { mem₀ with
                          callStack := s.memory.callStack
                          activeCallee := s.memory.activeCallee
                          activeProtectors := s.memory.activeProtectors } })
                    func (length argOps)
                    (s.memory.activeCallee.getD body).localDecls
                    (s.memory.activeCallee.getD body).layouts h_def
                have h_res_s :=
                  resolveCallTarget_eq_of_extractPureCalleeTarget
                    s func (length argOps)
                    (s.memory.activeCallee.getD body).localDecls
                    (s.memory.activeCallee.getD body).layouts h_def
                dsimp only at h_res_rep h_res_s
                rw [h_res_rep, h_res_s]
                cases h_rp : resolvePureCalleeTarget s.frame.locals func
                    defPath typeArgs
                    (s.memory.activeCallee.getD body).layouts with
                | ub => exact ⟨trivial, rfl⟩
                | unsupported => exact ⟨trivial, rfl⟩
                | ok rTarget localsAfterFunc =>
                  have h_rt := resolvePureCalleeTarget_ok_target h_rp
                  subst h_rt
                  dsimp only
                  rw [evalOperands_pure_eq localsAfterFunc argOps mem₀.borrows
                    mem₀.globals (s.memory.activeCallee.getD body).layouts
                    mem₀.callerLocals h_args]
                  rw [evalOperands_pure_eq localsAfterFunc argOps s.memory.borrows
                    s.memory.globals (s.memory.activeCallee.getD body).layouts
                    s.memory.callerLocals h_args]
                  cases evalOperands localsAfterFunc argOps [] []
                      (s.memory.activeCallee.getD body).layouts [] with
                  | ub => exact ⟨trivial, rfl⟩
                  | unsupported => exact ⟨trivial, rfl⟩
                  | ok argVals _ =>
                    rw [h_mem_cal, h_mem_tr, h_cal, h_tr]
                    cases h_lk : lookupCallee callees
                        (s.memory.activeCallee.getD body).layouts
                        defPath typeArgs traitImpls with
                    | none =>
                      rw [h_lk] at h_ext
                      exact False.elim (Bool.false_ne_true h_ext)
                    | some calleeBody =>
                      rw [h_lk] at h_ext
                      dsimp only at h_ext
                      have h_cb_pure :
                          IsPureWithCalleesAtSomeDepth callees traitImpls calleeBody := by
                        cases h_dec : Classical.propDecidable
                            (IsPureWithCalleesAtSomeDepth callees traitImpls calleeBody) with
                        | isTrue h_yes => exact h_yes
                        | isFalse _ =>
                          rw [h_dec] at h_ext
                          exact False.elim (Bool.false_ne_true h_ext)
                      dsimp only [checkCalleeTargetCompatible, enterTailCalleeFrame]
                      refine ⟨⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr,
                        h_cb_pure, h_stack⟩, ?_⟩
                      dsimp only [MirStepNode.replaceRoot, MirExecState.replaceRoot,
                        MachineState.replaceRoot, Memory.replaceRoot, MirStepNode.step]
                      simp only [h_mem_cal, h_mem_tr]
            | _ => exact False.elim (Bool.false_ne_true h_term)
        · simp only [h_len]
          exact ⟨trivial, rfl⟩

/--
Core inductive memory-replacement simulation theorem lifting
`wpMirExecNoCallSym` from `pureCalleeMemory callees traitImpls` to any
root-active caller memory `mem₀` with `mem₀.callees = callees` and
`mem₀.traitImpls = traitImpls`.
-/
theorem wpMirExecNoCallSym_replaceRoot
    {fuel : Nat} {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {mem₀ : Memory}
    {st : MirExecState} {post : Value → Prop}
    (h_st_inv :
      match st with
      | .running s => PureCalleeMachineInv callees traitImpls body s
      | _ => True)
    (h_root : RootActiveMemory mem₀)
    (h_mem_cal : mem₀.callees = callees)
    (h_mem_tr : mem₀.traitImpls = traitImpls)
    (h_wp :
      wpMirExecNoCallSym fuel body st
        (mirNormalPost
          (fun retVal mem' =>
            ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
            post retVal))) :
    wpMirExecNoCallSym fuel body (MirExecState.replaceRoot mem₀ st)
      (mirNormalPost
        (fun retVal mem' => ActiveRootMemory body mem₀ mem' ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecNoCallSym at h_wp ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_wp ⊢
    cases st with
    | faulted _ => exact False.elim h_wp
    | halted out =>
      cases out with
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
      | normal rv =>
        rcases rv with ⟨retVal, memOut⟩
        exact ⟨ActiveRootMemory.replaceRoot_of_pureCalleeMemory h_root h_wp.1,
          h_wp.2⟩
    | running s =>
      dsimp only [MirExecState.replaceRoot, stepMirState] at h_wp ⊢
      have ⟨h_step_inv, h_step_eq⟩ :=
        stepMirFn_pureCallee_step_and_replaceRoot h_st_inv h_root.1 h_mem_cal h_mem_tr
      rw [h_step_eq]
      cases h_sf : stepMirFn body s with
      | ret out =>
        rw [h_sf] at h_wp
        dsimp only [MirStepNode.replaceRoot, evalNodeNoCallWP] at h_wp ⊢
        cases out with
        | panic => exact False.elim h_wp
        | abort => exact False.elim h_wp
        | normal rv =>
          rcases rv with ⟨retVal, memOut⟩
          exact ⟨ActiveRootMemory.replaceRoot_of_pureCalleeMemory h_root h_wp.1,
            h_wp.2⟩
      | tau st' =>
        rw [h_sf] at h_wp h_step_inv
        dsimp only [MirStepNode.replaceRoot, evalNodeNoCallWP, pureNodeStepInv] at h_wp h_step_inv ⊢
        exact ih h_step_inv h_wp
      | vis i k =>
        rw [h_sf] at h_wp h_step_inv
        rcases i with f | (e | c)
        · exact False.elim h_wp
        · cases e
          dsimp only [MirStepNode.replaceRoot, evalNodeNoCallWP, pureNodeStepInv] at h_wp h_step_inv ⊢
          exact ih h_step_inv h_wp
        · exact False.elim h_step_inv

/--
Core inductive memory-replacement simulation theorem for `mirSafePost` lifting
`wpMirExecSym` from `pureCalleeMemory callees traitImpls` to any root-active
caller memory `mem₀` with `mem₀.callees = callees` and
`mem₀.traitImpls = traitImpls`.
-/
theorem wpMirExecSym_safe_replaceRoot
    {fuel : Nat} {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {mem₀ : Memory}
    {st : MirExecState} {post : Value → Prop}
    (h_st_inv :
      match st with
      | .running s => PureCalleeMachineInv callees traitImpls body s
      | _ => True)
    (h_root : RootActiveMemory mem₀)
    (h_mem_cal : mem₀.callees = callees)
    (h_mem_tr : mem₀.traitImpls = traitImpls)
    (h_wp :
      wpMirExecSym fuel body st
        (mirSafePost
          (fun retVal mem' =>
            ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
            post retVal))) :
    wpMirExecSym fuel body (MirExecState.replaceRoot mem₀ st)
      (mirSafePost
        (fun retVal mem' => ActiveRootMemory body mem₀ mem' ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecSym at h_wp ⊢
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval] at h_wp ⊢
    cases st with
    | faulted _ => exact False.elim h_wp
    | halted out =>
      cases out with
      | panic => trivial
      | abort => trivial
      | normal rv =>
        rcases rv with ⟨retVal, memOut⟩
        exact ⟨ActiveRootMemory.replaceRoot_of_pureCalleeMemory h_root h_wp.1,
          h_wp.2⟩
    | running s =>
      dsimp only [MirExecState.replaceRoot, stepMirState] at h_wp ⊢
      have ⟨h_step_inv, h_step_eq⟩ :=
        stepMirFn_pureCallee_step_and_replaceRoot h_st_inv h_root.1 h_mem_cal h_mem_tr
      rw [h_step_eq]
      cases h_sf : stepMirFn body s with
      | ret out =>
        rw [h_sf] at h_wp
        dsimp only [MirStepNode.replaceRoot, evalNodeWP] at h_wp ⊢
        cases out with
        | panic => trivial
        | abort => trivial
        | normal rv =>
          rcases rv with ⟨retVal, memOut⟩
          exact ⟨ActiveRootMemory.replaceRoot_of_pureCalleeMemory h_root h_wp.1,
            h_wp.2⟩
      | tau st' =>
        rw [h_sf] at h_wp h_step_inv
        dsimp only [MirStepNode.replaceRoot, evalNodeWP, pureNodeStepInv] at h_wp h_step_inv ⊢
        exact ih h_step_inv h_wp
      | vis i k =>
        rw [h_sf] at h_wp h_step_inv
        rcases i with f | (e | c)
        · exact False.elim h_wp
        · cases e
          dsimp only [MirStepNode.replaceRoot, evalNodeWP, pureNodeStepInv] at h_wp h_step_inv ⊢
          exact ih h_step_inv h_wp
        · exact False.elim h_step_inv

/--
Soundness of `PureMirConvergesWithCallees` under `checkPureMirWithCallees` into
call-forbidding `MirNoCallWpConverges` for any root-active memory `mem₀` with
matching `callees` and `traitImpls`.
-/
theorem mirNoCallWpConverges_of_pureExecWithCallees
    {body : CapturedMir} {callees : List CapturedMir} {args : List Value}
    {post : Value → Prop} {mem₀ : Memory} {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth mem₀.traitImpls = true)
    (h_conv :
      PureMirConvergesWithCallees body callees (initPureState body args)
        post mem₀.traitImpls)
    (h_callees : mem₀.callees = callees := by rfl)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirNoCallWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost
        (fun retVal mem' => ActiveRootMemory body mem₀ mem' ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  have h_inv :
      PureCalleeMachineInv callees mem₀.traitImpls body
        ((initPureState body args).toMachineState
          (pureCalleeMemory callees mem₀.traitImpls)) :=
    PureCalleeMachineInv.init (initPureState body args) ⟨maxCallDepth, h_pure⟩
  have h_sim :=
    wpMirExecNoCallSym_replaceRoot h_inv h_root h_callees rfl h_wp
  have h_st_eq :
      MirExecState.replaceRoot mem₀
        (.running ((initPureState body args).toMachineState
          (pureCalleeMemory callees mem₀.traitImpls))) =
      .running (initMachineStateWithMemory body args mem₀) := by
    dsimp only [MirExecState.replaceRoot, MachineState.replaceRoot,
      PureState.toMachineState, initPureState, initMachineStateWithMemory]
    rw [Memory.replaceRoot_pureCalleeMemory_of_rootActive h_root]
  rw [h_st_eq] at h_sim
  exact ⟨fuel, h_sim⟩

/--
Headline soundness theorem (`mirWpConverges_of_pureExecWithCallees`, `FF-2.2`):
lifts `PureMirConvergesWithCallees` under `checkPureMirWithCallees` to
`MirWpConverges` over `initMachineStateWithMemory body args mem₀` for any
root-active `mem₀ : Memory`.
-/
theorem mirWpConverges_of_pureExecWithCallees
    {body : CapturedMir} {callees : List CapturedMir} {args : List Value}
    {post : Value → Prop} {mem₀ : Memory} {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth mem₀.traitImpls = true)
    (h_conv :
      PureMirConvergesWithCallees body callees (initPureState body args)
        post mem₀.traitImpls)
    (h_callees : mem₀.callees = callees := by rfl)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost
        (fun retVal mem' => ActiveRootMemory body mem₀ mem' ∧ post retVal)) :=
  MirWpConverges.of_noCall
    (mirNoCallWpConverges_of_pureExecWithCallees h_pure h_conv h_callees h_root)

/--
Specialization of `mirWpConverges_of_pureExecWithCallees` to
`initMachineStateWithCallees body args callees`.
-/
theorem mirWpConverges_of_pureExecWithCallees_init
    {body : CapturedMir} {callees : List CapturedMir} {args : List Value}
    {post : Value → Prop} {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth body.traitImpls = true)
    (h_conv :
      PureMirConvergesWithCallees body callees (initPureState body args)
        post body.traitImpls) :
    MirWpConverges body (initMachineStateWithCallees body args callees)
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory body
            (initMachineStateWithCallees body args callees).memory mem' ∧
          post retVal)) := by
  have h_cal :
      (initMachineStateWithCallees body args callees).memory.callees = callees := by
    cases callees <;> rfl
  have h_tr :
      (initMachineStateWithCallees body args callees).memory.traitImpls =
        body.traitImpls := by
    cases callees <;> rfl
  have h_pure' :
      checkPureMirWithCallees callees body maxCallDepth
        (initMachineStateWithCallees body args callees).memory.traitImpls = true := by
    rw [h_tr]; exact h_pure
  have h_conv' :
      PureMirConvergesWithCallees body callees (initPureState body args) post
        (initMachineStateWithCallees body args callees).memory.traitImpls := by
    rw [h_tr]; exact h_conv
  have h :=
    mirWpConverges_of_pureExecWithCallees
      (mem₀ := (initMachineStateWithCallees body args callees).memory)
      h_pure' h_conv' h_cal
      (rootActiveMemory_initMachineStateWithCallees body args callees)
  rwa [← initMachineStateWithCallees_eq_withMemory] at h

/--
Partial-correctness (`mirSafePost`) soundness of
`PureMirSafeConvergesWithCallees`
under `checkPureMirWithCallees`.
-/
theorem mirSafeWpConverges_of_pureExecWithCallees
    {body : CapturedMir} {callees : List CapturedMir} {args : List Value}
    {post : Value → Prop} {mem₀ : Memory} {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth mem₀.traitImpls = true)
    (h_conv :
      PureMirSafeConvergesWithCallees body callees (initPureState body args)
        post mem₀.traitImpls)
    (h_callees : mem₀.callees = callees := by rfl)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirSafePost
        (fun retVal mem' => ActiveRootMemory body mem₀ mem' ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  have h_inv :
      PureCalleeMachineInv callees mem₀.traitImpls body
        ((initPureState body args).toMachineState
          (pureCalleeMemory callees mem₀.traitImpls)) :=
    PureCalleeMachineInv.init (initPureState body args) ⟨maxCallDepth, h_pure⟩
  have h_sim :=
    wpMirExecSym_safe_replaceRoot h_inv h_root h_callees rfl h_wp
  have h_st_eq :
      MirExecState.replaceRoot mem₀
        (.running ((initPureState body args).toMachineState
          (pureCalleeMemory callees mem₀.traitImpls))) =
      .running (initMachineStateWithMemory body args mem₀) := by
    dsimp only [MirExecState.replaceRoot, MachineState.replaceRoot,
      PureState.toMachineState, initPureState, initMachineStateWithMemory]
    rw [Memory.replaceRoot_pureCalleeMemory_of_rootActive h_root]
  rw [h_st_eq] at h_sim
  exact ⟨fuel, h_sim⟩

/--
Discharge a stateless `VerificationResult c` from panic-forbidding callee-aware
pure execution (`PureMirConvergesWithCallees` + `checkPureMirWithCallees`).
-/
theorem verifyMirNoPanic_of_pureExecWithCallees
    (c : Claim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirConvergesWithCallees c.body c.callees (initPureState c.body args)
          (c.post args) c.body.traitImpls) :
    VerificationResult c := by
  refine verifyMirNoPanic_of_wpConverges c (fun args h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExecWithCallees_init h_pure (h_wp args h_pre))

/-- Primary alias for stateless callee-aware pure verification. -/
abbrev verifyMir_of_pureExecWithCallees := @verifyMirNoPanic_of_pureExecWithCallees

/--
Discharge a stateless `VerificationResult c` from partial-correctness
callee-aware pure execution (`PureMirSafeConvergesWithCallees`).
-/
theorem verifyMirSafe_of_pureExecWithCallees
    (c : Claim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirSafeConvergesWithCallees c.body c.callees
          (initPureState c.body args) (c.post args) c.body.traitImpls) :
    VerificationResult c := by
  refine verifyMirSafe_of_wpConverges c (fun args h_pre => ?_)
  have h_cal :
      (initMachineStateWithCallees c.body args c.callees).memory.callees =
        c.callees := by
    cases c.callees <;> rfl
  have h_tr :
      (initMachineStateWithCallees c.body args c.callees).memory.traitImpls =
        c.body.traitImpls := by
    cases c.callees <;> rfl
  have h_pure' :
      checkPureMirWithCallees c.callees c.body maxCallDepth
        (initMachineStateWithCallees c.body args c.callees).memory.traitImpls =
        true := by
    rw [h_tr]; exact h_pure
  have h_conv' :
      PureMirSafeConvergesWithCallees c.body c.callees
        (initPureState c.body args) (c.post args)
        (initMachineStateWithCallees c.body args c.callees).memory.traitImpls := by
    rw [h_tr]; exact h_wp args h_pre
  have h :=
    mirSafeWpConverges_of_pureExecWithCallees
      (mem₀ := (initMachineStateWithCallees c.body args c.callees).memory)
      h_pure' h_conv' h_cal
      (rootActiveMemory_initMachineStateWithCallees c.body args c.callees)
  rw [← initMachineStateWithCallees_eq_withMemory] at h
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => trivial
      | abort => trivial)
    h

/--
Discharge a stateful `StatefulVerificationResult c` with non-empty `c.callees`
from panic-forbidding callee-aware pure execution, automatically supplying
`ActiveRootMemory` on the returned `Memory`.
-/
theorem verifyStatefulMirNoPanic_of_pureExecWithCallees
    (c : StatefulClaim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_nonempty : c.callees ≠ [] := by decide)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConvergesWithCallees c.body c.callees (initPureState c.body args)
          (fun retVal =>
            ∀ mem',
              ActiveRootMemory c.body
                (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                  c.body args mem c.callees).memory mem' →
              c.post args mem retVal mem')
          c.body.traitImpls) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanic_of_wpConverges c (fun args mem h_pre => ?_)
  let initMem :=
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      c.body args mem c.callees).memory
  have h_cal_tr :
      initMem.callees = c.callees ∧ initMem.traitImpls = c.body.traitImpls := by
    dsimp only [initMem,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : c.callees with
    | nil => exact False.elim (h_nonempty hc)
    | cons _ _ => exact ⟨rfl, rfl⟩
  have h_pure' :
      checkPureMirWithCallees c.callees c.body maxCallDepth initMem.traitImpls =
        true := by
    rw [h_cal_tr.2]; exact h_pure
  have h_conv' := h_wp args mem h_pre
  rw [← h_cal_tr.2] at h_conv'
  have h :=
    mirWpConverges_of_pureExecWithCallees (mem₀ := initMem)
      h_pure' h_conv' h_cal_tr.1
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre))
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        exact h_out.2 mem' h_out.1
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    h

/-- Primary alias for stateful callee-aware pure verification. -/
abbrev verifyStatefulMir_of_pureExecWithCallees :=
  @verifyStatefulMirNoPanic_of_pureExecWithCallees

/--
Discharge a total-correctness `TotalVerificationResult c` with non-empty
`c.callees` from callee-aware pure execution (`PureMirConvergesWithCallees`).
-/
theorem verifyTotalMir_of_pureExecWithCallees
    (c : TotalClaim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_nonempty : c.callees ≠ [] := by decide)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConvergesWithCallees c.body c.callees (initPureState c.body args)
          (fun retVal =>
            ∀ mem',
              ActiveRootMemory c.body
                (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                  c.body args mem c.callees).memory mem' →
              c.post args mem retVal mem')
          c.body.traitImpls) :
    TotalVerificationResult c := by
  refine verifyTotalMir_of_wpConverges c (fun args mem h_pre => ?_)
  let initMem :=
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      c.body args mem c.callees).memory
  have h_cal_tr :
      initMem.callees = c.callees ∧ initMem.traitImpls = c.body.traitImpls := by
    dsimp only [initMem,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : c.callees with
    | nil => exact False.elim (h_nonempty hc)
    | cons _ _ => exact ⟨rfl, rfl⟩
  have h_pure' :
      checkPureMirWithCallees c.callees c.body maxCallDepth initMem.traitImpls =
        true := by
    rw [h_cal_tr.2]; exact h_pure
  have h_conv' := h_wp args mem h_pre
  rw [← h_cal_tr.2] at h_conv'
  have h :=
    mirWpConverges_of_pureExecWithCallees (mem₀ := initMem)
      h_pure' h_conv' h_cal_tr.1
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre))
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        exact h_out.2 mem' h_out.1
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    h

/--
Discharge `MirBoolPredicateHoldsWithCallees specBody callees args` from
callee-aware pure execution (`PureMirConvergesWithCallees`).
-/
theorem mirBoolPredicateHoldsWithCallees_of_pureExecWithCallees
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    {maxCallDepth : Nat}
    (h_pure :
      checkPureMirWithCallees callees specBody maxCallDepth
        specBody.traitImpls = true)
    (h_conv :
      PureMirConvergesWithCallees specBody callees (initPureState specBody args)
        (· = .scalar { bits := 1, sizeBytes := 1 }) specBody.traitImpls) :
    MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args := by
  refine mirBoolPredicateHoldsWithCallees_of_wpConverges specBody callees args ?_
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExecWithCallees_init h_pure h_conv)

/--
Generalized `StatefulVerificationResult` gate for callee-aware pure execution
that handles both non-empty `c.callees ≠ []` and empty `c.callees = []` (when
`c.pre` pins `mem.callees = []` and `mem.traitImpls = c.body.traitImpls`).
-/
theorem verifyStatefulMirNoPanic_of_pureExecWithCallees_any
    (c : StatefulClaim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_callees :
      c.callees ≠ [] ∨
      ∀ args mem, c.pre args mem → mem.callees = [] ∧ mem.traitImpls = c.body.traitImpls)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConvergesWithCallees c.body c.callees (initPureState c.body args)
          (fun retVal =>
            ∀ mem',
              ActiveRootMemory c.body
                (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                  c.body args mem c.callees).memory mem' →
              c.post args mem retVal mem')
          c.body.traitImpls) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanic_of_wpConverges c (fun args mem h_pre => ?_)
  let initMem :=
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      c.body args mem c.callees).memory
  have h_cal_tr :
      initMem.callees = c.callees ∧ initMem.traitImpls = c.body.traitImpls := by
    dsimp only [initMem,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : c.callees with
    | cons _ _ => exact ⟨rfl, rfl⟩
    | nil =>
      rcases h_callees with h_ne | h_emp
      · exact False.elim (h_ne hc)
      · exact h_emp args mem h_pre
  have h_pure' :
      checkPureMirWithCallees c.callees c.body maxCallDepth initMem.traitImpls =
        true := by
    rw [h_cal_tr.2]; exact h_pure
  have h_conv' := h_wp args mem h_pre
  rw [← h_cal_tr.2] at h_conv'
  have h :=
    mirWpConverges_of_pureExecWithCallees (mem₀ := initMem)
      h_pure' h_conv' h_cal_tr.1
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre))
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        exact h_out.2 mem' h_out.1
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    h

/--
Generalized `TotalVerificationResult` gate for callee-aware pure execution
that handles both non-empty `c.callees ≠ []` and empty `c.callees = []` (when
`c.pre` pins `mem.callees = []` and `mem.traitImpls = c.body.traitImpls`).
-/
theorem verifyTotalMir_of_pureExecWithCallees_any
    (c : TotalClaim)
    {maxCallDepth : Nat}
    (h_pure : checkPureMirWithCallees c.callees c.body maxCallDepth c.body.traitImpls = true)
    (h_callees :
      c.callees ≠ [] ∨
      ∀ args mem, c.pre args mem → mem.callees = [] ∧ mem.traitImpls = c.body.traitImpls)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConvergesWithCallees c.body c.callees (initPureState c.body args)
          (fun retVal =>
            ∀ mem',
              ActiveRootMemory c.body
                (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                  c.body args mem c.callees).memory mem' →
              c.post args mem retVal mem')
          c.body.traitImpls) :
    TotalVerificationResult c := by
  refine verifyTotalMir_of_wpConverges c (fun args mem h_pre => ?_)
  let initMem :=
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      c.body args mem c.callees).memory
  have h_cal_tr :
      initMem.callees = c.callees ∧ initMem.traitImpls = c.body.traitImpls := by
    dsimp only [initMem,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : c.callees with
    | cons _ _ => exact ⟨rfl, rfl⟩
    | nil =>
      rcases h_callees with h_ne | h_emp
      · exact False.elim (h_ne hc)
      · exact h_emp args mem h_pre
  have h_pure' :
      checkPureMirWithCallees c.callees c.body maxCallDepth initMem.traitImpls =
        true := by
    rw [h_cal_tr.2]; exact h_pure
  have h_conv' := h_wp args mem h_pre
  rw [← h_cal_tr.2] at h_conv'
  have h :=
    mirWpConverges_of_pureExecWithCallees (mem₀ := initMem)
      h_pure' h_conv' h_cal_tr.1
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre))
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        exact h_out.2 mem' h_out.1
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    h

private def mirStepNodeObsCont : MirStepNode → PUnit → Option MirExecState
  | .vis (.inr (.inl _)) k, u => some (k u)
  | _, _ => none

/--
Executable fuel-bounded pure MIR state evaluator supporting multi-frame inline
calls (`TerminatorKind.call` and `TerminatorKind.tailCall`), `switchInt`
observations, and root-frame `return_` validation.
-/
def evalPureMirStateWithCallees
    (fuel : Nat)
    (body : CapturedMir)
    (s : MachineState) : Option (Value × Memory) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirFn body s with
    | .ret (.normal (retVal, memOut)) =>
      if memOut.callStack.isEmpty && memOut.activeProtectors.isEmpty then
        some (retVal, memOut)
      else
        none
    | .tau (.running s') => evalPureMirStateWithCallees fuel' body s'
    | .vis (.inr (.inl _)) k =>
      match k PUnit.unit with
      | .running s' => evalPureMirStateWithCallees fuel' body s'
      | _ => none
    | _ => none

/--
Public computable evaluator for pure MIR functions with inline linked `callees`
and `traitImpls` (`FF-2.2` Section 3): runs `stepMirFn` across `pushCalleeFrame`,
`enterTailCalleeFrame`, `switchInt`, and callee `return_` transitions without
constructing `Prop` proof terms at each step.
-/
def evalPureMirWithCallees
    (fuel : Nat)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Option Value :=
  (evalPureMirStateWithCallees fuel body
    ((initPureState body args).toMachineState
      (pureCalleeMemory callees traitImpls))).map Prod.fst

/--
Executable boolean contract checker (`checkPureMirBoolPredWithCallees`) for
`MirBoolPredicateHoldsWithCallees` on concrete argument vectors.
-/
def checkPureMirBoolPredWithCallees
    (fuel : Nat)
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Bool :=
  match evalPureMirWithCallees fuel specBody callees args specBody.traitImpls with
  | some (.scalar sc) => sc.sizeBytes == 1 && sc.bits == 1
  | _ => false

private theorem wpMirExecNoCallSym_of_evalPureMirStateWithCallees
    {fuel : Nat} {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {s : MachineState}
    {retVal : Value} {memOut : Memory}
    (h_inv : PureCalleeMachineInv callees traitImpls body s)
    (h_rep :
      MachineState.replaceRoot (pureCalleeMemory callees traitImpls) s = s)
    (h_eval : evalPureMirStateWithCallees fuel body s = some (retVal, memOut)) :
    wpMirExecNoCallSym fuel body (.running s)
      (mirNormalPost
        (fun rv m' =>
          ActiveRootMemory body (pureCalleeMemory callees traitImpls) m' ∧
          rv = retVal)) := by
  let m0 := pureCalleeMemory callees traitImpls
  induction fuel generalizing s with
  | zero => nomatch h_eval
  | succ fuel' ih =>
    have ⟨h_step_inv, h_step_eq⟩ :=
      stepMirFn_pureCallee_step_and_replaceRoot (mem₀ := m0) h_inv rfl rfl rfl
    rw [h_rep] at h_step_eq
    unfold wpMirExecNoCallSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
    dsimp only [stepMirState]
    dsimp only [evalPureMirStateWithCallees] at h_eval
    cases h_sf : stepMirFn body s with
    | ret out =>
      rw [h_sf] at h_eval h_step_eq
      cases out with
      | panic => nomatch h_eval
      | abort => nomatch h_eval
      | normal rv =>
        rcases rv with ⟨v, mOut⟩
        dsimp only at h_eval
        cases h_ok : (mOut.callStack.isEmpty && mOut.activeProtectors.isEmpty) with
        | false => rw [h_ok] at h_eval; nomatch h_eval
        | true =>
          rw [h_ok] at h_eval
          injection h_eval with h_pair
          injection h_pair with hv hm_eq
          subst hv hm_eq
          simp only [Bool.and_eq_true, List.isEmpty_iff] at h_ok
          rcases h_ok with ⟨h_cs, h_ap⟩
          dsimp only [MirStepNode.replaceRoot, MirOutcome.replaceRoot] at h_step_eq
          injection h_step_eq with h_out_eq
          injection h_out_eq with h_prod_eq
          injection h_prod_eq with _ hm_rep
          dsimp only [evalNodeNoCallWP, mirNormalPost]
          refine ⟨?_, rfl⟩
          rw [hm_rep]
          dsimp only [Memory.replaceRoot]
          rw [h_cs, h_ap]
          cases mOut.activeCallee with
          | none => exact Or.inl rfl
          | some ab => exact Or.inr ⟨ab, rfl⟩
    | tau st' =>
      rw [h_sf] at h_eval h_step_inv h_step_eq
      cases st' with
      | halted _ => nomatch h_eval
      | faulted _ => nomatch h_eval
      | running s' =>
        dsimp only [MirStepNode.replaceRoot, MirExecState.replaceRoot] at h_step_eq
        injection h_step_eq with h_st_eq
        injection h_st_eq with h_s_rep
        dsimp only [evalNodeNoCallWP, pureNodeStepInv] at h_step_inv ⊢
        exact ih h_step_inv h_s_rep.symm h_eval
    | vis i k =>
      rw [h_sf] at h_eval h_step_inv h_step_eq
      rcases i with fk | (ev | c)
      · nomatch h_eval
      · cases ev
        dsimp only [evalNodeNoCallWP, pureNodeStepInv] at h_eval h_step_inv ⊢
        have h_cont_eq := congrArg (fun n => mirStepNodeObsCont n PUnit.unit) h_step_eq
        dsimp only [MirStepNode.replaceRoot, mirStepNodeObsCont] at h_cont_eq
        cases hk : k PUnit.unit with
        | halted _ => rw [hk] at h_eval; nomatch h_eval
        | faulted _ => rw [hk] at h_eval; nomatch h_eval
        | running s' =>
          rw [hk] at h_eval h_step_inv h_cont_eq
          dsimp only [MirExecState.replaceRoot] at h_eval h_step_inv h_cont_eq
          injection h_cont_eq with h_st_eq
          injection h_st_eq with h_s_rep
          exact ih h_step_inv h_s_rep.symm h_eval
      · exact False.elim h_step_inv

/--
Soundness of the computable `evalPureMirWithCallees` evaluator: if
`checkPureMirWithCallees` holds and `evalPureMirWithCallees` evaluates to
`some retVal`, then `PureMirConvergesWithCallees` holds with ZERO step-by-step
proof obligations.
-/
theorem pureMirConvergesWithCallees_of_evalPureMirWithCallees
    {fuel maxCallDepth : Nat}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {args : List Value}
    {traitImpls : List TraitImplEntry}
    {retVal : Value}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth traitImpls = true)
    (h_eval : evalPureMirWithCallees fuel body callees args traitImpls = some retVal) :
    PureMirConvergesWithCallees body callees (initPureState body args)
      (· = retVal) traitImpls := by
  unfold evalPureMirWithCallees at h_eval
  cases h_st : evalPureMirStateWithCallees fuel body
      ((initPureState body args).toMachineState
        (pureCalleeMemory callees traitImpls)) with
  | none => rw [h_st] at h_eval; nomatch h_eval
  | some rv =>
    rw [h_st] at h_eval
    rcases rv with ⟨v, memOut⟩
    dsimp only [Option.map] at h_eval
    injection h_eval with hv
    subst hv
    exact ⟨fuel, wpMirExecNoCallSym_of_evalPureMirStateWithCallees
      (PureCalleeMachineInv.init (initPureState body args) ⟨maxCallDepth, h_pure⟩)
      rfl h_st⟩

/--
Lift computable `evalPureMirWithCallees` directly to `MirWpConverges` on any
root-active caller `Memory`.
-/
theorem mirWpConverges_of_evalPureMirWithCallees
    {fuel maxCallDepth : Nat}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {args : List Value}
    {mem₀ : Memory}
    {retVal : Value}
    (h_pure : checkPureMirWithCallees callees body maxCallDepth mem₀.traitImpls = true)
    (h_eval :
      evalPureMirWithCallees fuel body callees args mem₀.traitImpls = some retVal)
    (h_callees : mem₀.callees = callees := by rfl)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost
        (fun rv mem' => ActiveRootMemory body mem₀ mem' ∧ rv = retVal)) :=
  mirWpConverges_of_pureExecWithCallees h_pure
    (pureMirConvergesWithCallees_of_evalPureMirWithCallees h_pure h_eval)
    h_callees h_root

/--
Discharge `MirBoolPredicateHoldsWithCallees` by `decide`/`rfl` from computable
`checkPureMirWithCallees` and `checkPureMirBoolPredWithCallees`.
-/
theorem mirBoolPredicateHoldsWithCallees_of_checkPureMirBoolPredWithCallees
    {fuel maxCallDepth : Nat}
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value)
    (h_pure :
      checkPureMirWithCallees callees specBody maxCallDepth
        specBody.traitImpls = true)
    (h_check :
      checkPureMirBoolPredWithCallees fuel specBody callees args = true) :
    MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args := by
  unfold checkPureMirBoolPredWithCallees at h_check
  cases h_ev : evalPureMirWithCallees fuel specBody callees args specBody.traitImpls with
  | none => rw [h_ev] at h_check; nomatch h_check
  | some v =>
    rw [h_ev] at h_check
    cases v with
    | scalar sc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h_check
      rcases sc with ⟨bits, sz⟩
      dsimp only at h_check
      rcases h_check with ⟨rfl, rfl⟩
      exact mirBoolPredicateHoldsWithCallees_of_pureExecWithCallees
        specBody callees args h_pure
        (pureMirConvergesWithCallees_of_evalPureMirWithCallees h_pure h_ev)
    | _ => nomatch h_check

/-!
### 9B. Pure `CallConv.rustIntrinsic` Semantics &
`pureRustIntrinsicContract`
-/

open Anneal.Rustc.V2026_06_01.Lower

/--
Catalog of pure `CallConv.rustIntrinsic` operations (`FF-2.2` Section 2 & 3):
covers bit-counting and byte/bit permutation (`ctlz`, `ctlz_nonzero`, `cttz`,
`cttz_nonzero`, `ctpop`, `bswap`, `bitreverse`), wrapping and saturating
arithmetic (`wrapping_add/sub/mul`, `saturating_add/sub`), UB-guarded unchecked
and exact arithmetic (`unchecked_add/sub/mul/div/rem/shl/shr`, `exact_div`),
three-way comparison (`three_way_compare`), `ub_checks`, and runtime-dispatched
`const_eval_select`.
-/
inductive PureRustIntrinsicKind : Type
  | ctlz
  | ctlzNonzero
  | cttz
  | cttzNonzero
  | ctpop
  | bswap
  | bitreverse
  | wrappingAdd
  | wrappingSub
  | wrappingMul
  | saturatingAdd
  | saturatingSub
  | uncheckedAdd
  | uncheckedSub
  | uncheckedMul
  | uncheckedDiv
  | uncheckedRem
  | uncheckedShl
  | uncheckedShr
  | exactDiv
  | threeWayCompare
  | ubChecks
  | constEvalSelect
  deriving DecidableEq, Repr

private def stripCharPrefix : List Char → List Char → Option (List Char)
  | [], s => some s
  | p :: ps, c :: cs => if p == c then stripCharPrefix ps cs else none
  | _ :: _, [] => none

/--
Strip `"core::intrinsics::"` or `"std::intrinsics::"` prefix from a `DefPath`
by structural character-list matching (100% kernel-reducible via `rfl`),
returning the bare intrinsic name when matched.
-/
def stripRustIntrinsicsPrefix? (defPath : DefPath) : Option String :=
  let cs := defPath.toList
  match stripCharPrefix "core::intrinsics::".toList cs with
  | some rest => some (String.ofList rest)
  | none =>
    match stripCharPrefix "std::intrinsics::".toList cs with
    | some rest => some (String.ofList rest)
    | none => none

/-- Classify a `DefPath` into a `PureRustIntrinsicKind` when recognized. -/
def classifyPureRustIntrinsic? (defPath : DefPath) : Option PureRustIntrinsicKind :=
  match stripRustIntrinsicsPrefix? defPath with
  | none => none
  | some name =>
    if stringEq name "ctlz" then some .ctlz
    else if stringEq name "ctlz_nonzero" then some .ctlzNonzero
    else if stringEq name "cttz" then some .cttz
    else if stringEq name "cttz_nonzero" then some .cttzNonzero
    else if stringEq name "ctpop" then some .ctpop
    else if stringEq name "bswap" then some .bswap
    else if stringEq name "bitreverse" then some .bitreverse
    else if stringEq name "wrapping_add" then some .wrappingAdd
    else if stringEq name "wrapping_sub" then some .wrappingSub
    else if stringEq name "wrapping_mul" then some .wrappingMul
    else if stringEq name "saturating_add" then some .saturatingAdd
    else if stringEq name "saturating_sub" then some .saturatingSub
    else if stringEq name "unchecked_add" then some .uncheckedAdd
    else if stringEq name "unchecked_sub" then some .uncheckedSub
    else if stringEq name "unchecked_mul" then some .uncheckedMul
    else if stringEq name "unchecked_div" then some .uncheckedDiv
    else if stringEq name "unchecked_rem" then some .uncheckedRem
    else if stringEq name "unchecked_shl" then some .uncheckedShl
    else if stringEq name "unchecked_shr" then some .uncheckedShr
    else if stringEq name "exact_div" then some .exactDiv
    else if stringEq name "three_way_compare" then some .threeWayCompare
    else if stringEq name "ub_checks" then some .ubChecks
    else if stringEq name "const_eval_select" then some .constEvalSelect
    else none

/--
Resolve a monomorphized `RigidTy` argument of an integer intrinsic to its
`(sizeBytes, isSigned)` pair, failing closed (`none`) on unresolved generic
parameters (`.param ..`), non-integer types, or `pointerBytes = 0`.
When `allowChar = true` (`three_way_compare`), `RigidTy.char` resolves to
`(4, false)`.
-/
def intrinsicScalarTyInfo?
    (pointerBytes : Nat := 8)
    (allowChar : Bool := false) :
    RigidTy → Option (Nat × Bool)
  | .uint .u8 => some (1, false)
  | .uint .u16 => some (2, false)
  | .uint .u32 => some (4, false)
  | .uint .u64 => some (8, false)
  | .uint .u128 => some (16, false)
  | .uint .usize => if 0 < pointerBytes then some (pointerBytes, false) else none
  | .int .i8 => some (1, true)
  | .int .i16 => some (2, true)
  | .int .i32 => some (4, true)
  | .int .i64 => some (8, true)
  | .int .i128 => some (16, true)
  | .int .isize => if 0 < pointerBytes then some (pointerBytes, true) else none
  | .char => if allowChar then some (4, false) else none
  | _ => none

/--
Check that `sc` has exact width `sz > 0` and canonical bit range `sc.bits <
256^sz`.
-/
def isCanonicalScalarOfSize (sc : ScalarInt) (sz : Nat) : Bool :=
  0 < sz && sc.sizeBytes == sz && sc.bits < scalarModulus sz

/--
Evaluate `saturating_add<T>(a, b)` on canonical equal-width `ScalarInt`
operands (unsigned clamping to `2^(8*sz) - 1`; two's-complement signed clamping
to `INT_MIN = 2^(8*sz - 1)` or `INT_MAX = 2^(8*sz - 1) - 1`).
-/
def evalSaturatingAdd (a b : ScalarInt) (isSigned : Bool) : Option ScalarInt :=
  if a.sizeBytes == 0 || a.sizeBytes != b.sizeBytes then
    none
  else
    let sz := a.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits a.bits modulus
    let cb := wrapScalarBits b.bits modulus
    match isSigned with
    | false =>
      let sum := ca + cb
      let clamped := if sum < modulus then sum else modulus - 1
      some ⟨clamped, sz⟩
    | true =>
      match signedOverflowAdd ca cb sz with
      | false => some ⟨wrapScalarBits (ca + cb) modulus, sz⟩
      | true =>
        let half := signedHalfModulus sz
        if isSignedNegative ca sz then
          some ⟨half, sz⟩
        else
          some ⟨half - 1, sz⟩

/--
Count the number of set (`1`) bits in the low `remBits` bits of `bits` by
structural recursion (`core::intrinsics::ctpop`).
-/
def pureCtpopLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    Nat.add (Nat.mod bits 2) (pureCtpopLoop remBits (Nat.div bits 2))

/--
Count consecutive trailing zero (`0`) bits starting from the least significant
bit across `remBits` bits of `bits` (`core::intrinsics::cttz`).
-/
def pureCttzLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    match Nat.beq (Nat.mod bits 2) 0 with
    | true => Nat.add 1 (pureCttzLoop remBits (Nat.div bits 2))
    | false => 0

/--
Reverse the low `remBits` bits of `bits` into accumulator `acc`
(`core::intrinsics::bitreverse`).
-/
def pureBitreverseLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBits, bits, acc =>
    pureBitreverseLoop
      remBits
      (Nat.div bits 2)
      (Nat.add (Nat.mul acc 2) (Nat.mod bits 2))

/--
Count consecutive leading zero (`0`) bits of a `numBits`-bit unsigned word
`bits` (`core::intrinsics::ctlz`).
-/
def pureCtlzBits (numBits bits : Nat) : Nat :=
  pureCttzLoop numBits (pureBitreverseLoop numBits bits 0)

/--
Reverse the low `remBytes` bytes of `bits` into accumulator `acc`
(`core::intrinsics::bswap`).
-/
def pureBswapLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBytes, bits, acc =>
    pureBswapLoop
      remBytes
      (Nat.div bits 256)
      (Nat.add (Nat.mul acc 256) (Nat.mod bits 256))

/--
Evaluate a pure scalar `BinOp` directly via `Trusted`'s `evalScalarBinOp`,
returning `some sc` on `.ok (.scalar sc) _ _` and `none` on UB or unsupported
operands.
-/
def evalPureScalarBinOp?
    (op : BinOp)
    (a b : ScalarInt)
    (isSigned : Bool) : Option ScalarInt :=
  match evalScalarBinOp op a b [] emptyMemory isSigned with
  | .ok (.scalar sc) _ _ => some sc
  | _ => none

/--
Evaluate `saturating_sub<T>(a, b)` on equal-width `ScalarInt` operands,
normalizing non-canonical bit representations modulo `256^sz` (unsigned
clamping to `0`; two's-complement signed clamping to `INT_MIN` or `INT_MAX`).
-/
def evalSaturatingSub (a b : ScalarInt) (isSigned : Bool) : Option ScalarInt :=
  if a.sizeBytes == 0 || a.sizeBytes != b.sizeBytes then
    none
  else
    let sz := a.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits a.bits modulus
    let cb := wrapScalarBits b.bits modulus
    match isSigned with
    | false => some ⟨ca - cb, sz⟩
    | true =>
      match signedOverflowSub ca cb sz with
      | false => evalPureScalarBinOp? .sub ⟨ca, sz⟩ ⟨cb, sz⟩ true
      | true =>
        let half := signedHalfModulus sz
        if isSignedNegative ca sz then
          some ⟨half, sz⟩
        else
          some ⟨half - 1, sz⟩

/--
Evaluate any of the 22 direct value-returning `PureRustIntrinsicKind`
intrinsics on `typeArgs` and `args`, returning `none` on undefined behavior
(`ctlz_nonzero(0)`, `cttz_nonzero(0)`, `unchecked_*` overflow / negative or
out-of-bounds shift / division by zero / `INT_MIN ÷ -1`, `exact_div` non-zero
remainder / zero / `INT_MIN ÷ -1`) or unresolved generic type arguments.
-/
def evalPureScalarIntrinsic
    (kind : PureRustIntrinsicKind)
    (typeArgs : List RigidTy)
    (args : List Value)
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true) : Option Value :=
  match kind with
  | .ubChecks =>
    match typeArgs, args with
    | [], [] => some (.scalar (boolToScalar ubChecksEnabled))
    | _, _ => none
  | .constEvalSelect => none
  | .ctlz =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz then
          some (.scalar ⟨pureCtlzBits (sz * 8) x.bits, 4⟩)
        else none
      | none => none
    | _, _ => none
  | .ctlzNonzero =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz && x.bits != 0 then
          some (.scalar ⟨pureCtlzBits (sz * 8) x.bits, 4⟩)
        else none
      | none => none
    | _, _ => none
  | .cttz =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz then
          some (.scalar ⟨pureCttzLoop (sz * 8) x.bits, 4⟩)
        else none
      | none => none
    | _, _ => none
  | .cttzNonzero =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz && x.bits != 0 then
          some (.scalar ⟨pureCttzLoop (sz * 8) x.bits, 4⟩)
        else none
      | none => none
    | _, _ => none
  | .ctpop =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz then
          some (.scalar ⟨pureCtpopLoop (sz * 8) x.bits, 4⟩)
        else none
      | none => none
    | _, _ => none
  | .bswap =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz then
          some (.scalar ⟨pureBswapLoop sz x.bits 0, sz⟩)
        else none
      | none => none
    | _, _ => none
  | .bitreverse =>
    match typeArgs, args with
    | [ty], [.scalar x] =>
      match intrinsicScalarTyInfo? pointerBytes false ty with
      | some (sz, _) =>
        if isCanonicalScalarOfSize x sz then
          some (.scalar ⟨pureBitreverseLoop (sz * 8) x.bits 0, sz⟩)
        else none
      | none => none
    | _, _ => none
  | .uncheckedShl | .uncheckedShr =>
    let tyPairOpt :=
      match typeArgs with
      | [lhsTy, rhsTy] =>
        match intrinsicScalarTyInfo? pointerBytes false lhsTy,
              intrinsicScalarTyInfo? pointerBytes false rhsTy with
        | some lInfo, some rInfo => some (lInfo, rInfo)
        | _, _ => none
      | [lhsTy] =>
        match intrinsicScalarTyInfo? pointerBytes false lhsTy with
        | some lInfo => some (lInfo, lInfo)
        | none => none
      | _ => none
    match tyPairOpt, args with
    | some ((lhsSz, lhsSigned), (rhsSz, rhsSigned)), [.scalar a, .scalar b] =>
      if isCanonicalScalarOfSize a lhsSz &&
         isCanonicalScalarOfSize b rhsSz &&
         (!rhsSigned || !isSignedNegative b.bits rhsSz) &&
         b.bits < lhsSz * 8 then
        let binOp : BinOp :=
          match kind with
          | .uncheckedShl => .shlUnchecked
          | _ => .shrUnchecked
        (evalPureScalarBinOp? binOp a b lhsSigned).map Value.scalar
      else none
    | _, _ => none
  | _ =>
    let allowChar := kind == .threeWayCompare
    let singleTyOpt : Option RigidTy :=
      match typeArgs with
      | [ty] => some ty
      | [ty₁, ty₂] => if rigidTyEq ty₁ ty₂ then some ty₁ else none
      | _ => none
    match singleTyOpt, args with
    | some ty, [.scalar a, .scalar b] =>
      match intrinsicScalarTyInfo? pointerBytes allowChar ty with
      | some (sz, isSigned) =>
        if isCanonicalScalarOfSize a sz && isCanonicalScalarOfSize b sz then
          match kind with
          | .wrappingAdd =>
            (evalPureScalarBinOp? .add a b isSigned).map Value.scalar
          | .wrappingSub =>
            (evalPureScalarBinOp? .sub a b isSigned).map Value.scalar
          | .wrappingMul =>
            (evalPureScalarBinOp? .mul a b isSigned).map Value.scalar
          | .saturatingAdd =>
            (evalSaturatingAdd a b isSigned).map Value.scalar
          | .saturatingSub =>
            (evalSaturatingSub a b isSigned).map Value.scalar
          | .uncheckedAdd =>
            (evalPureScalarBinOp? .addUnchecked a b isSigned).map Value.scalar
          | .uncheckedSub =>
            (evalPureScalarBinOp? .subUnchecked a b isSigned).map Value.scalar
          | .uncheckedMul =>
            (evalPureScalarBinOp? .mulUnchecked a b isSigned).map Value.scalar
          | .uncheckedDiv =>
            (evalPureScalarBinOp? .div a b isSigned).map Value.scalar
          | .uncheckedRem =>
            (evalPureScalarBinOp? .rem a b isSigned).map Value.scalar
          | .exactDiv =>
            (evalExactDiv a b isSigned).map Value.scalar
          | .threeWayCompare =>
            (evalPureScalarBinOp? .cmp a b isSigned).map Value.scalar
          | _ => none
        else none
      | none => none
    | _, _ => none

/--
Check whether `v` is a valid zero-sized function-item or capture-free closure
value (`.unit` or `.aggregate 0 []`).
-/
def isZeroSizedFnItemValue : Value → Bool
  | .unit => true
  | .aggregate 0 [] => true
  | _ => false

/--
Extract `(defPath, typeArgs)` from a zero-sized `.fnDef` or capture-free
`.closure` runtime target type. Because `RigidTy.closure defPath upvars` stores
captured upvar types in `upvars` (rather than generic `typeArgs`), only
capture-free closures (`upvars = []`) are zero-sized callable targets, and their
lookup `typeArgs` list is `[]`.
-/
def extractZeroSizedCallableTy? : RigidTy → Option (DefPath × List RigidTy)
  | .fnDef defPath typeArgs => some (defPath, typeArgs)
  | .closure defPath upvars =>
    if upvars.isEmpty then some (defPath, []) else none
  | _ => none

mutual
/--
Check whether `ty` is an inhabited zero-sized unit-like element type whose
runtime representation in `Value` can be `Value.unit`.
-/
def isZeroSizedUnitElemTy : Nat → RigidTy → Bool
  | 0, _ => false
  | fuel + 1, .tuple ts => isZeroSizedUnitElemTyList fuel ts
  | _ + 1, .fnDef _ _ => true
  | fuel + 1, .closure _ upvars => isZeroSizedUnitElemTyList fuel upvars
  | fuel + 1, .array elemTy n => n == 0 || isZeroSizedUnitElemTy fuel elemTy
  | _ + 1, _ => false

def isZeroSizedUnitElemTyList : Nat → List RigidTy → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, t :: ts =>
    isZeroSizedUnitElemTy fuel t && isZeroSizedUnitElemTyList fuel ts
end

/--
Unpack a runtime `core::intrinsics::const_eval_select<ARG, F, G, RET>` call's
`typeArgs = [.tuple elemTys, constFnTy, rtFnTy, _retTy]` and
`args = [tupleVal, constFnVal, rtFnVal]` into `(elemTys, rtDefPath, rtTypeArgs,
unpackedArgs)`, requiring both `constFnTy` and `rtFnTy` to be zero-sized
`.fnDef` or capture-free `.closure` callable types (`upvars = []`), as well as
supporting non-empty inhabited ZST argument tuples represented as `Value.unit`.
-/
def unpackConstEvalSelectWithElemTys?
    (typeArgs : List RigidTy)
    (args : List Value) :
    Option (List RigidTy × DefPath × List RigidTy × List Value) :=
  match typeArgs, args with
  | [.tuple elemTys, constFnTy, rtFnTy, _], [tupleVal, constFnVal, rtFnVal] =>
    match extractZeroSizedCallableTy? constFnTy,
          extractZeroSizedCallableTy? rtFnTy with
    | some _, some (rtDefPath, rtTypeArgs) =>
      if isZeroSizedFnItemValue constFnVal && isZeroSizedFnItemValue rtFnVal then
        match elemTys, tupleVal with
        | [], .unit => some ([], rtDefPath, rtTypeArgs, [])
        | _, .unit =>
          if isZeroSizedUnitElemTyList 8 elemTys then
            some (elemTys, rtDefPath, rtTypeArgs,
              List.replicate elemTys.length Value.unit)
          else none
        | _, .aggregate 0 fieldVals =>
          if fieldVals.length == elemTys.length then
            some (elemTys, rtDefPath, rtTypeArgs, fieldVals)
          else none
        | _, _ => none
      else none
    | _, _ => none
  | _, _ => none

/--
Unpack a runtime `core::intrinsics::const_eval_select<ARG, F, G, RET>` call into
`(rtDefPath, rtTypeArgs, unpackedArgs)`.
-/
def unpackConstEvalSelect?
    (typeArgs : List RigidTy)
    (args : List Value) :
    Option (DefPath × List RigidTy × List Value) :=
  match unpackConstEvalSelectWithElemTys? typeArgs args with
  | some (_, rtDefPath, rtTypeArgs, unpackedArgs) =>
    some (rtDefPath, rtTypeArgs, unpackedArgs)
  | none => none

/--
Bounded-depth helper evaluating `PureRustIntrinsicKind` operations, supporting
nested `const_eval_select` chains up to `fuel` levels (falling back to `rtEval`
first and then recursive `evalPureRustIntrinsicFuel` when the selected runtime
function is itself a pure `CallConv.rustIntrinsic` operation).
-/
def evalPureRustIntrinsicFuel
    (fuel : Nat)
    (rtEval : DefPath → List RigidTy → List Value → Option Value := fun _ _ _ => none)
    (kind : PureRustIntrinsicKind)
    (typeArgs : List RigidTy)
    (args : List Value)
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true) : Option Value :=
  match kind with
  | .constEvalSelect =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match unpackConstEvalSelectWithElemTys? typeArgs args with
      | some (elemTys, rtDefPath, rtTypeArgs, unpackedArgs) =>
        match rtEval rtDefPath rtTypeArgs unpackedArgs with
        | some v => some v
        | none =>
          match classifyPureRustIntrinsic? rtDefPath with
          | some subKind =>
            let effTypeArgs := if rtTypeArgs.isEmpty then elemTys else rtTypeArgs
            evalPureRustIntrinsicFuel fuel' rtEval subKind effTypeArgs
              unpackedArgs pointerBytes ubChecksEnabled
          | none => none
      | none => none
  | _ => evalPureScalarIntrinsic kind typeArgs args pointerBytes ubChecksEnabled

/--
Evaluate any of the 23 `PureRustIntrinsicKind` operations, delegating
`const_eval_select` to `rtEval rtDefPath rtTypeArgs unpackedArgs` first and
automatically falling back to nested pure `CallConv.rustIntrinsic` evaluation
(up to depth `8`) when `rtDefPath` is itself a pure Rust intrinsic.
-/
def evalPureRustIntrinsicWithRuntime
    (rtEval : DefPath → List RigidTy → List Value → Option Value := fun _ _ _ => none)
    (kind : PureRustIntrinsicKind)
    (typeArgs : List RigidTy)
    (args : List Value)
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true) : Option Value :=
  match kind with
  | .constEvalSelect =>
    match unpackConstEvalSelectWithElemTys? typeArgs args with
    | some (elemTys, rtDefPath, rtTypeArgs, unpackedArgs) =>
      match rtEval rtDefPath rtTypeArgs unpackedArgs with
      | some v => some v
      | none =>
        match classifyPureRustIntrinsic? rtDefPath with
        | some subKind =>
          let effTypeArgs := if rtTypeArgs.isEmpty then elemTys else rtTypeArgs
          match subKind with
          | .constEvalSelect =>
            evalPureRustIntrinsicFuel 7 rtEval .constEvalSelect effTypeArgs
              unpackedArgs pointerBytes ubChecksEnabled
          | _ =>
            evalPureScalarIntrinsic subKind effTypeArgs unpackedArgs
              pointerBytes ubChecksEnabled
        | none => none
    | none => none
  | _ => evalPureScalarIntrinsic kind typeArgs args pointerBytes ubChecksEnabled

/--
Check whether parameter `_1` (`index 1` of `calleeBody.localDecls`) is a
capture-free closure self-environment slot of type `RigidTy.closure
calleeBody.defPath []` (`argCount ≥ 1`), as emitted by `rustc` for capture-free
closures implementing `FnOnce<ARG>`.
-/
def isCaptureFreeClosureSelfLocal (calleeBody : CapturedMir) : Bool :=
  0 < calleeBody.argCount &&
  match get? calleeBody.localDecls 1 with
  | some decl =>
    match decl.ty.kind with
    | .closure cp upvars => stringEq cp calleeBody.defPath && upvars.isEmpty
    | _ => false
  | none => false

/--
Validate exact parameter arity and construct the effective `MirSemantics` frame
argument list for a `const_eval_select` runtime target `calleeBody` given
unpacked tuple elements `unpackedArgs`:
- When `isCaptureFreeClosureSelfLocal calleeBody = true`, prepends the zero-sized
  closure environment `Value.unit` for `_1` and requires
  `calleeBody.argCount == unpackedArgs.length + 1`.
- Otherwise (a `fn` item `calleeBody`), requires exact parameter arity
  `calleeBody.argCount == unpackedArgs.length` so `initLocalsAux` cannot
  silently initialize temporary locals (`local > argCount`) or leave parameter
  locals `.dead`.
-/
def effectiveConstEvalCalleeArgs?
    (calleeBody : CapturedMir)
    (unpackedArgs : List Value) : Option (List Value) :=
  if isCaptureFreeClosureSelfLocal calleeBody then
    if calleeBody.argCount == unpackedArgs.length + 1 then
      some (.unit :: unpackedArgs)
    else
      none
  else if calleeBody.argCount == unpackedArgs.length then
    some unpackedArgs
  else
    none

/--
Linked-callee runtime evaluator for `core::intrinsics::const_eval_select`
(`FF-2.2` Section 3): resolves `(rtDefPath, rtTypeArgs)` in `callees` (including
polymorphic `(defPath, typeArgs)` instantiation, capture-free closures with
`_1 : .closure defPath []`, and `TraitImplEntry` dispatch), enforces exact
parameter arity via `effectiveConstEvalCalleeArgs?`, verifies
`checkPureMirWithCallees`, and evaluates `calleeBody` via
`evalPureMirWithCallees fuel`.
-/
def calleeRuntimeEval
    (fuel : Nat)
    (callees : List CapturedMir)
    (callerLayouts : LayoutTable)
    (traitImpls : List TraitImplEntry := [])
    (maxCallDepth : Nat := defaultMaxCallDepth) :
    DefPath → List RigidTy → List Value → Option Value :=
  fun rtDefPath rtTypeArgs unpackedArgs =>
    match lookupCallee callees callerLayouts rtDefPath rtTypeArgs traitImpls with
    | some calleeBody =>
      match effectiveConstEvalCalleeArgs? calleeBody unpackedArgs with
      | some callArgs =>
        if checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls then
          evalPureMirWithCallees fuel calleeBody callees callArgs traitImpls
        else
          none
      | none => none
    | none => none

/--
Operational soundness of `calleeRuntimeEval`: whenever `calleeRuntimeEval`
returns `some retVal`, `lookupCallee` resolves `(rtDefPath, rtTypeArgs)` to a
pure `calleeBody` with validated frame arguments `callArgs` (via
`effectiveConstEvalCalleeArgs?`) whose operational `MirWpConverges` semantics
converges to `retVal` on any root-active caller memory `mem₀`.
-/
theorem calleeRuntimeEval_sound
    {fuel maxCallDepth : Nat}
    {callees : List CapturedMir}
    {callerLayouts : LayoutTable}
    {mem₀ : Memory}
    {rtDefPath : DefPath}
    {rtTypeArgs : List RigidTy}
    {unpackedArgs : List Value}
    {retVal : Value}
    (h_eval :
      calleeRuntimeEval fuel callees callerLayouts mem₀.traitImpls maxCallDepth
        rtDefPath rtTypeArgs unpackedArgs = some retVal)
    (h_callees : mem₀.callees = callees := by rfl)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    ∃ (calleeBody : CapturedMir) (callArgs : List Value),
      lookupCallee callees callerLayouts rtDefPath rtTypeArgs mem₀.traitImpls =
        some calleeBody ∧
      effectiveConstEvalCalleeArgs? calleeBody unpackedArgs = some callArgs ∧
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody callArgs mem₀)
        (mirNormalPost
          (fun rv mem' => ActiveRootMemory calleeBody mem₀ mem' ∧ rv = retVal)) := by
  unfold calleeRuntimeEval at h_eval
  cases h_lk : lookupCallee callees callerLayouts rtDefPath rtTypeArgs mem₀.traitImpls with
  | none =>
    rw [h_lk] at h_eval
    nomatch h_eval
  | some calleeBody =>
    rw [h_lk] at h_eval
    dsimp only at h_eval
    cases h_eff : effectiveConstEvalCalleeArgs? calleeBody unpackedArgs with
    | none =>
      rw [h_eff] at h_eval
      nomatch h_eval
    | some callArgs =>
      rw [h_eff] at h_eval
      dsimp only at h_eval
      cases h_pure :
          checkPureMirWithCallees callees calleeBody maxCallDepth mem₀.traitImpls with
      | false =>
        rw [h_pure] at h_eval
        nomatch h_eval
      | true =>
        rw [h_pure] at h_eval
        simp only [↓reduceIte] at h_eval
        exact ⟨calleeBody, callArgs, rfl, h_eff,
          mirWpConverges_of_evalPureMirWithCallees h_pure h_eval h_callees h_root⟩

/--
Kernel-checked operational agreement between `evalPureRustIntrinsicWithRuntime`
on `.exactDiv` and `Trusted`'s `evalExactDiv` (`Scalars.lean`) for any integer
type `ty` resolving via `intrinsicScalarTyInfo? pointerBytes false ty =
some (sz, isSigned)` and canonical `ScalarInt` operands `a, b` of width `sz`.
-/
theorem evalPureRustIntrinsic_exactDiv_eq_evalExactDiv
    (rtEval : DefPath → List RigidTy → List Value → Option Value)
    (pointerBytes : Nat) (ubChecksEnabled : Bool)
    (ty : RigidTy) (sz : Nat) (isSigned : Bool)
    (a b : ScalarInt)
    (h_ty : intrinsicScalarTyInfo? pointerBytes false ty = some (sz, isSigned))
    (h_ca : isCanonicalScalarOfSize a sz = true)
    (h_cb : isCanonicalScalarOfSize b sz = true) :
    evalPureRustIntrinsicWithRuntime rtEval .exactDiv [ty] [.scalar a, .scalar b]
      pointerBytes ubChecksEnabled =
      (evalExactDiv a b isSigned).map Value.scalar := by
  unfold evalPureRustIntrinsicWithRuntime evalPureScalarIntrinsic
  have h_ac : (PureRustIntrinsicKind.exactDiv == PureRustIntrinsicKind.threeWayCompare) = false := rfl
  dsimp only; rw [h_ac, h_ty]
  simp only [h_ca, h_cb, Bool.and_self, ↓reduceIte]

/--
Map binary arithmetic/comparison `PureRustIntrinsicKind` variants directly
modeled via `Trusted`'s `evalScalarBinOp` (`Scalars.lean`) to their underlying
`BinOp`.
-/
def pureIntrinsicToScalarBinOp? : PureRustIntrinsicKind → Option BinOp
  | .wrappingAdd => some .add
  | .wrappingSub => some .sub
  | .wrappingMul => some .mul
  | .uncheckedAdd => some .addUnchecked
  | .uncheckedSub => some .subUnchecked
  | .uncheckedMul => some .mulUnchecked
  | .uncheckedDiv => some .div
  | .uncheckedRem => some .rem
  | .threeWayCompare => some .cmp
  | _ => none

/--
Kernel-checked operational agreement between `evalPureRustIntrinsicWithRuntime`
and `Trusted`'s `evalScalarBinOp` across all 9 wrapping, unchecked-arithmetic,
and three-way comparison intrinsics in `pureIntrinsicToScalarBinOp?`.
-/
theorem evalPureRustIntrinsic_binOp_eq_evalScalarBinOp
    (rtEval : DefPath → List RigidTy → List Value → Option Value)
    (kind : PureRustIntrinsicKind) (op : BinOp)
    (pointerBytes : Nat) (ubChecksEnabled : Bool)
    (ty : RigidTy) (sz : Nat) (isSigned : Bool)
    (a b : ScalarInt)
    (h_kind : pureIntrinsicToScalarBinOp? kind = some op)
    (h_ty :
      intrinsicScalarTyInfo? pointerBytes (kind == .threeWayCompare) ty =
        some (sz, isSigned))
    (h_ca : isCanonicalScalarOfSize a sz = true)
    (h_cb : isCanonicalScalarOfSize b sz = true) :
    evalPureRustIntrinsicWithRuntime rtEval kind [ty] [.scalar a, .scalar b]
      pointerBytes ubChecksEnabled =
      match evalScalarBinOp op a b [] emptyMemory isSigned with
      | .ok (.scalar sc) _ _ => some (.scalar sc)
      | _ => none := by
  cases kind <;>
    (dsimp only [pureIntrinsicToScalarBinOp?] at h_kind) <;>
    (try contradiction) <;>
    (injection h_kind with h_eq;
     have h_eq_symm := h_eq.symm;
     subst h_eq_symm;
     unfold evalPureRustIntrinsicWithRuntime evalPureScalarIntrinsic evalPureScalarBinOp?;
     dsimp only at h_ty ⊢;
     rw [h_ty];
     simp only [h_ca, h_cb, Bool.and_self, ↓reduceIte];
     cases evalScalarBinOp _ a b [] emptyMemory isSigned with
     | ub => rfl
     | unsupported => rfl
     | ok v _ _ => cases v <;> rfl)

/--
Modular `MirCallContract` modeling pure `#[rustc_nounwind]`
`CallConv.rustIntrinsic` calls (`FF-2.2` Section 2 & 3):
- Requires `req.defPath` to classify as a `PureRustIntrinsicKind` whose pure
  evaluator returns `some expectedVal` (rejecting all UB inputs).
- Guarantees normal return `.returned expectedVal req.memory` with zero memory
  mutation (`memAfter = req.memory`) and forbids unwinding or abort.
-/
def pureRustIntrinsicContract
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true)
    (rtEval : DefPath → List RigidTy → List Value → Option Value := fun _ _ _ => none) :
    MirCallContract where
  pre req :=
    ∃ (kind : PureRustIntrinsicKind) (retVal : Value),
      classifyPureRustIntrinsic? req.defPath = some kind ∧
      evalPureRustIntrinsicWithRuntime rtEval kind req.typeArgs req.args
        pointerBytes ubChecksEnabled = some retVal
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      memAfter = req.memory ∧
      ∃ kind : PureRustIntrinsicKind,
        classifyPureRustIntrinsic? req.defPath = some kind ∧
        evalPureRustIntrinsicWithRuntime rtEval kind req.typeArgs req.args
          pointerBytes ubChecksEnabled = some retVal
    | _ => False

theorem pureRustIntrinsicContract_frameAndTraitsPreserved
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true)
    (rtEval : DefPath → List RigidTy → List Value → Option Value := fun _ _ _ => none) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval).post req ans →
      ans.frameAndTraitsPreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    rcases h_post with ⟨rfl, _⟩
    exact ⟨⟨rfl, rfl, rfl, rfl, [], rfl⟩, rfl⟩
  | panicked _ => exact False.elim h_post
  | aborted => trivial

theorem pureRustIntrinsicContract_framePreserved
    (pointerBytes : Nat := 8)
    (ubChecksEnabled : Bool := true)
    (rtEval : DefPath → List RigidTy → List Value → Option Value := fun _ _ _ => none) :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval).post req ans →
      ans.framePreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned retVal memAfter =>
    rcases h_post with ⟨rfl, _⟩
    exact ⟨rfl, rfl, rfl, rfl, [], rfl⟩
  | panicked _ => exact False.elim h_post
  | aborted => trivial

/--
Combine two `MirCallContract`s (`c₁` and `c₂`, e.g., `pureRustIntrinsicContract`
and `polyExternalSpecCallContract` / `externalSpecCallContract`) into a single
intersection-of-guarantees modular rely contract so callers can freely mix
sub-contract call rules via `MirCallContract.Subsumes` without domain-disjointness
side conditions.
-/
def combineMirCallContracts (c₁ c₂ : MirCallContract) : MirCallContract where
  pre req := c₁.pre req ∨ c₂.pre req
  post req ans :=
    (c₁.pre req ∨ c₂.pre req) ∧
    (c₁.pre req → c₁.post req ans) ∧
    (c₂.pre req → c₂.post req ans)

theorem combineMirCallContracts_holdsOn
    {c₁ c₂ : MirCallContract} {h : ExternalCallHandler}
    (h₁ : c₁.holdsOn h) (h₂ : c₂.holdsOn h) :
    (combineMirCallContracts c₁ c₂).holdsOn h := by
  intro req h_pre
  refine ⟨?_, fun tr ans h_ret =>
    ⟨h_pre,
     fun hp₁ => (h₁ req hp₁).2 tr ans h_ret,
     fun hp₂ => (h₂ req hp₂).2 tr ans h_ret⟩⟩
  rcases h_pre with hp₁ | hp₂
  · exact (h₁ req hp₁).1
  · exact (h₂ req hp₂).1

theorem combineMirCallContracts_frameAndTraitsPreserved
    {c₁ c₂ : MirCallContract}
    (hf₁ : ∀ req ans, c₁.post req ans → ans.frameAndTraitsPreserved req.memory)
    (hf₂ : ∀ req ans, c₂.post req ans → ans.frameAndTraitsPreserved req.memory) :
    ∀ req ans,
      (combineMirCallContracts c₁ c₂).post req ans →
      ans.frameAndTraitsPreserved req.memory := by
  intro req ans ⟨h_pre, hi₁, hi₂⟩
  rcases h_pre with hp₁ | hp₂
  · exact hf₁ req ans (hi₁ hp₁)
  · exact hf₂ req ans (hi₂ hp₂)

/--
Contract refinement / subsumption relation `MirCallContract.Subsumes cSub cSuper`:
every call request permitted by `cSub` is permitted by `cSuper`, and every
answer allowed by `cSuper` satisfies `cSub.post`.
-/
def MirCallContract.Subsumes (cSub cSuper : MirCallContract) : Prop :=
  ∀ req : MirCallReq,
    cSub.pre req →
    cSuper.pre req ∧ ∀ ans : MirCallAns, cSuper.post req ans → cSub.post req ans

theorem MirCallContract.Subsumes.refl (c : MirCallContract) :
    MirCallContract.Subsumes c c :=
  fun _ hp => ⟨hp, fun _ hq => hq⟩

theorem MirCallContract.Subsumes.trans
    {c₁ c₂ c₃ : MirCallContract}
    (h₁₂ : MirCallContract.Subsumes c₁ c₂)
    (h₂₃ : MirCallContract.Subsumes c₂ c₃) :
    MirCallContract.Subsumes c₁ c₃ := by
  intro req hp₁
  rcases h₁₂ req hp₁ with ⟨hp₂, hq₁₂⟩
  rcases h₂₃ req hp₂ with ⟨hp₃, hq₂₃⟩
  exact ⟨hp₃, fun ans hq₃ => hq₁₂ ans (hq₂₃ ans hq₃)⟩

theorem MirCallContract.Subsumes.combine_left
    (c₁ c₂ : MirCallContract) :
    MirCallContract.Subsumes c₁ (combineMirCallContracts c₁ c₂) :=
  fun _ hp₁ => ⟨Or.inl hp₁, fun _ hq => hq.2.1 hp₁⟩

theorem MirCallContract.Subsumes.combine_right
    (c₁ c₂ : MirCallContract) :
    MirCallContract.Subsumes c₂ (combineMirCallContracts c₁ c₂) :=
  fun _ hp₂ => ⟨Or.inr hp₂, fun _ hq => hq.2.2 hp₂⟩

/-!
### 9C. `#[external_spec]` & Modular Call Execution on `PureState`
(`PureMirModularConverges`)
-/

/--
Root-frame memory invariant for modular pure callers (`FF-2.2` Section 2 & 4):
preserves `callees`, `traitImpls`, `callStack = []`, root/self `activeCallee`,
and `activeProtectors = []`, while allowing arbitrary `borrows`, `globals`, and
`fnPtrs` across `#[external_spec]` and `polyExternalSpecCallContract` calls.
-/
def ModularRootMemory
    (body : CapturedMir) (callees : List CapturedMir)
    (traitImpls : List TraitImplEntry) (m : Memory) : Prop :=
  m.callees = callees ∧
  m.traitImpls = traitImpls ∧
  m.callStack = [] ∧
  (m.activeCallee = none ∨ m.activeCallee = some body) ∧
  m.activeProtectors = []

theorem ModularRootMemory.activeCallee_getD
    {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {m : Memory}
    (h : ModularRootMemory body callees traitImpls m) :
    m.activeCallee.getD body = body := by
  rcases h.2.2.2.1 with h_none | h_some
  · simp [h_none]
  · simp [h_some]

theorem ModularRootMemory.withBorrows
    {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {m : Memory}
    (h : ModularRootMemory body callees traitImpls m)
    (bs : List BorrowEntry) :
    ModularRootMemory body callees traitImpls { m with borrows := bs } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem ModularRootMemory.withSomeActiveCallee
    {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {m : Memory}
    (h : ModularRootMemory body callees traitImpls m) :
    ModularRootMemory body callees traitImpls { m with activeCallee := some body } :=
  ⟨h.1, h.2.1, h.2.2.1, Or.inr rfl, h.2.2.2.2⟩

theorem ModularRootMemory.of_callFrameAndTraitsPreserved
    {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry} {m memAfter : Memory}
    (h : ModularRootMemory body callees traitImpls m)
    (h_pres : callFrameAndTraitsPreserved m memAfter) :
    ModularRootMemory body callees traitImpls memAfter := by
  rcases h with ⟨hc, ht, hcs, hac, hap⟩
  rcases h_pres with ⟨⟨hc', hcs', hac', hap', _⟩, ht'⟩
  exact ⟨by rw [hc', hc], by rw [ht', ht], by rw [hcs', hcs],
    by rw [hac']; exact hac, by rw [hap', hap]⟩

theorem ModularRootMemory.of_callFramePreserved_nil_traits
    {body : CapturedMir} {callees : List CapturedMir}
    {m memAfter : Memory}
    (h : ModularRootMemory body callees memAfter.traitImpls m)
    (h_pres : callFramePreserved m memAfter) :
    ModularRootMemory body callees memAfter.traitImpls memAfter := by
  rcases h with ⟨hc, _, hcs, hac, hap⟩
  rcases h_pres with ⟨hc', hcs', hac', hap', _⟩
  exact ⟨by rw [hc', hc], rfl, by rw [hcs', hcs],
    by rw [hac']; exact hac, by rw [hap', hap]⟩

/--
Fuel-free modular pure convergence (`FF-2.2` Section 2 & 4):
from any `m : Memory` satisfying `ModularRootMemory body callees traitImpls m`,
the coinductive `ITree` `mirTree body (ps.toMachineState m)` converges (`DWP`)
under `mirModularWP contract.toCallContract` to
`mirSafePost (fun retVal _ => post retVal)`.
-/
def PureMirModularConverges
    (contract : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (ps : PureState)
    (post : Value → Prop)
    (traitImpls : List TraitImplEntry := body.traitImpls) : Prop :=
  ∀ m : Memory,
    ModularRootMemory body callees traitImpls m →
    Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
      (mirTree body (ps.toMachineState m))
      (fun out _ => mirSafePost (fun retVal _ => post retVal) out)
      PUnit.unit

/-- Postcondition monotonicity for `PureMirModularConverges`. -/
theorem PureMirModularConverges.mono
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {P Q : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirModularConverges contract body callees ps P traitImpls) :
    PureMirModularConverges contract body callees ps Q traitImpls := by
  intro m hm
  refine Anneal.ITreeWP.DWP.mono ?_ (h m hm)
  intro out _ h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => trivial
  | abort => trivial

/--
Contract refinement / subsumption monotonicity for `PureMirModularConverges`:
lifts any modular convergence proof under `cSub` to a larger combined rely
contract `cSuper` whenever `cSub.Subsumes cSuper`.
-/
theorem PureMirModularConverges.mono_contract
    {cSub cSuper : MirCallContract}
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes cSub cSuper)
    (h : PureMirModularConverges cSub body callees ps post traitImpls) :
    PureMirModularConverges cSuper body callees ps post traitImpls := by
  intro m hm
  refine Anneal.ITreeWP.DWP.induct
    (fun x s₀ =>
      Anneal.ITreeWP.DWP (mirModularWP cSuper.toCallContract) x
        (fun out _ => mirSafePost (fun retVal _ => post retVal) out) s₀)
    ?_ (h m hm)
  intro x s₀ hx
  rw [Anneal.ITreeWP.DWP.unfold_eq]
  cases hx_obs : x.observe with
  | ret _ => rw [hx_obs] at hx; exact hx
  | tau _ => rw [hx_obs] at hx; exact hx
  | vis i k =>
    rw [hx_obs] at hx
    rcases i with _ | (ev | callOp)
    · exact False.elim hx
    · cases ev; exact hx
    · cases callOp with
      | call req =>
        rcases hx with ⟨h_pre, h_cont⟩
        rcases h_sub req h_pre with ⟨h_sup_pre, h_sup_post⟩
        exact ⟨h_sup_pre, fun ans h_ans => h_cont ans (h_sup_post ans h_ans)⟩

/--
Lift bounded frame-and-traits symbolic modular evaluation
(`wpMirFrameAndTraitsModularSym`) into `PureMirModularConverges`.
-/
theorem PureMirModularConverges.of_wpFrameAndTraitsModular
    {contract : MirCallContract}
    (h_frame :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        contract.post req ans → ans.frameAndTraitsPreserved req.memory)
    {body : CapturedMir} {callees : List CapturedMir}
    {ps : PureState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_wp :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        ∃ fuel : Nat,
          wpMirFrameAndTraitsModularSym contract fuel body
            (ps.toMachineState m)
            (mirSafePost (fun retVal _ => post retVal))) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  rcases h_wp m hm with ⟨fuel, hf⟩
  have h_mod : MirModularWpConverges contract body (ps.toMachineState m)
      (mirSafePost (fun retVal _ => post retVal)) :=
    ⟨fuel, wpMirExecModularSym_of_wpMirExecFrameAndTraitsModularSym
      contract h_frame fuel body _ _ hf⟩
  exact dwp_of_mirModularWpConverges h_mod

private theorem dwp_modular_of_noCallWp
    {contract : MirCallContract} {body : CapturedMir}
    {s : MachineState} {Q : MirOutcome → Prop}
    (h_nc : MirNoCallWpConverges body s Q) :
    Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
      (mirTree body s) (fun out _ => Q out) PUnit.unit := by
  rcases h_nc with ⟨f, hf⟩
  suffices ∀ st : MirExecState,
      wpMirExecNoCallSym f body st Q →
      Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
        (Trusted.ITree.ITree.cofix (stepMirState body) st)
        (fun out _ => Q out) PUnit.unit from
    this (.running s) hf
  clear hf
  induction f with
  | zero => intro _ h_st; exact False.elim h_st
  | succ f' ih =>
    intro st h_st
    unfold wpMirExecNoCallSym at h_st
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_st
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    cases h_sf : stepMirState body st with
    | ret out => rw [h_sf] at h_st; exact h_st
    | tau st' => rw [h_sf] at h_st; exact ih st' h_st
    | vis i k =>
      rw [h_sf] at h_st
      rcases i with fk | (e | c)
      · exact False.elim h_st
      · cases e; exact ih (k PUnit.unit) h_st
      · exact False.elim h_st

private theorem dwp_modular_bind_steps
    {contract : MirCallContract} {body : CapturedMir}
    {s : MachineState} {mid : MachineState → Prop}
    {Q : MirOutcome → Prop}
    (h_steps : MirStepsConverges body s mid Q)
    (h_cont :
      ∀ s', mid s' →
        Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
          (mirTree body s') (fun out _ => Q out) PUnit.unit) :
    Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
      (mirTree body s) (fun out _ => Q out) PUnit.unit := by
  rcases h_steps with ⟨f, hf⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f body st
        (fun
          | .running s' => mid s'
          | .halted out => Q out
          | .faulted _ => False)
        Q →
      Anneal.ITreeWP.DWP (mirModularWP contract.toCallContract)
        (Trusted.ITree.ITree.cofix (stepMirState body) st)
        (fun out _ => Q out) PUnit.unit from
    this (.running s) hf
  clear hf
  induction f with
  | zero =>
    intro st h_st
    cases st with
    | running s' => exact h_cont s' h_st
    | halted out =>
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      exact h_st
    | faulted _ => exact False.elim h_st
  | succ f' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_st
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    cases h_sf : stepMirState body st with
    | ret out =>
      rw [h_sf] at h_st
      exact h_st
    | tau st' =>
      rw [h_sf] at h_st
      exact ih st' h_st
    | vis i k =>
      rw [h_sf] at h_st
      rcases i with fk | (e | c)
      · exact False.elim h_st
      · cases e
        exact ih (k PUnit.unit) h_st
      · exact False.elim h_st

/--
1-step `return_` rule for `PureMirModularConverges`.
-/
theorem PureMirModularConverges.return_
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {retVal : Value}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .return_)
    (h_ret : get? ps.env 0 = some (.init retVal))
    (h_post : post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator]
    rw [h_ret]
    dsimp only
    rw [hm.2.2.1]
    dsimp only [MirStepNode.retNormal, Trusted.ITree.ITreeF.map]
    exact h_post

/--
1-step pure statement rule for `PureMirModularConverges` (valid even when
`m.borrows` is non-empty after an external modular call).
-/
theorem PureMirModularConverges.step_stmt
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {stmt : Statement} {s_emp : MachineState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_stmt : get? bb.statements ps.stmtIdx = some stmt)
    (h_pure : isPureStatement stmt.kind = true)
    (h_eval :
      evalStmt (ps.toMachineState emptyMemory) stmt body.localDecls body.layouts =
        MirStepNode.step s_emp)
    (h_next :
      PureMirModularConverges contract body callees
        (PureState.ofMachineState s_emp) post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_ap : m.activeProtectors = [] := hm.2.2.2.2
  have h_step_m :
      ∃ bs : List BorrowEntry,
        evalStmt (ps.toMachineState m) stmt body.localDecls body.layouts =
          MirStepNode.step
            ((PureState.ofMachineState s_emp).toMachineState
              { m with borrows := bs }) := by
    rcases stmt with ⟨skind, sspan⟩
    cases skind with
    | nop =>
      injection h_eval with h_se; injection h_se with h_eq
      subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
    | coverage =>
      injection h_eval with h_se; injection h_se with h_eq
      subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
    | constEvalCounter =>
      injection h_eval with h_se; injection h_se with h_eq
      subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
    | placeMention p =>
      unfold evalStmt at h_eval ⊢
      dsimp only [PureState.toMachineState] at h_eval ⊢
      cases h_g : get? ps.env p.local_ with
      | none => rw [h_g] at h_eval; nomatch h_eval
      | some sl =>
        rw [h_g] at h_eval
        cases sl with
        | dead => nomatch h_eval
        | uninit =>
          dsimp only at h_eval ⊢
          cases h_ok : placeMentionOperandsInit ps.env .uninit p.projection with
          | false => rw [h_ok] at h_eval; nomatch h_eval
          | true =>
            rw [h_ok] at h_eval
            injection h_eval with h_se; injection h_se with h_eq
            subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
        | init v =>
          dsimp only at h_eval ⊢
          cases h_ok : placeMentionOperandsInit ps.env (.init v) p.projection with
          | false => rw [h_ok] at h_eval; nomatch h_eval
          | true =>
            rw [h_ok] at h_eval
            injection h_eval with h_se; injection h_se with h_eq
            subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
    | storageLive loc =>
      unfold evalStmt at h_eval ⊢
      dsimp only [PureState.toMachineState] at h_eval ⊢
      cases h_g : get? ps.env loc with
      | none => rw [h_g] at h_eval; nomatch h_eval
      | some _ =>
        rw [h_g] at h_eval
        cases h_s : set? ps.env loc .uninit with
        | none => rw [h_s] at h_eval; nomatch h_eval
        | some l' =>
          rw [h_s] at h_eval
          injection h_eval with h_se; injection h_se with h_eq
          subst h_eq; exact ⟨purgeLocalBorrows m.borrows loc, by cases m; rfl⟩
    | storageDead loc =>
      unfold evalStmt at h_eval ⊢
      dsimp only [PureState.toMachineState] at h_eval ⊢
      cases h_g : get? ps.env loc with
      | none => rw [h_g] at h_eval; nomatch h_eval
      | some _ =>
        rw [h_g] at h_eval
        cases h_s : set? ps.env loc .dead with
        | none => rw [h_s] at h_eval; nomatch h_eval
        | some l' =>
          rw [h_s] at h_eval
          injection h_eval with h_se; injection h_se with h_eq
          subst h_eq
          rcases m with ⟨_, _, bor, _, _, _, _, _, ap, _, _, _⟩
          dsimp only at h_ap
          subst h_ap
          exact ⟨purgeLocalBorrows bor loc, rfl⟩
    | deinit p =>
      unfold evalStmt at h_eval ⊢
      dsimp only [PureState.toMachineState] at h_eval ⊢
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        dsimp only at h_eval ⊢
        cases h_g : get? ps.env loc with
        | none => rw [h_g] at h_eval; nomatch h_eval
        | some sl =>
          rw [h_g] at h_eval
          cases sl with
          | dead => nomatch h_eval
          | uninit =>
            cases h_s : set? ps.env loc .uninit with
            | none => rw [h_s] at h_eval; nomatch h_eval
            | some _ =>
              rw [h_s] at h_eval
              injection h_eval with h_se; injection h_se with h_eq
              subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
          | init _ =>
            cases h_s : set? ps.env loc .uninit with
            | none => rw [h_s] at h_eval; nomatch h_eval
            | some _ =>
              rw [h_s] at h_eval
              injection h_eval with h_se; injection h_se with h_eq
              subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
      | cons hd tl =>
        dsimp only at h_eval ⊢
        cases h_g : get? ps.env loc with
        | none => rw [h_g] at h_eval; nomatch h_eval
        | some sl =>
          rw [h_g] at h_eval
          cases sl with
          | uninit => nomatch h_eval
          | dead => nomatch h_eval
          | init rv =>
            dsimp only at h_eval ⊢
            cases h_rd : readProjectedValue ps.env rv (hd :: tl) with
            | ub => rw [h_rd] at h_eval; nomatch h_eval
            | unsupported => rw [h_rd] at h_eval; nomatch h_eval
            | ok _ =>
              rw [h_rd] at h_eval
              injection h_eval with h_se; injection h_se with h_eq
              subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
    | intrinsic intr =>
      cases intr with
      | copyNonOverlapping _ _ _ => cases h_pure
      | assume op =>
        dsimp only [isPureStatement] at h_pure
        unfold evalStmt at h_eval ⊢
        dsimp only [PureState.toMachineState] at h_eval ⊢
        rw [evalOperand_pure_eq ps.env op m.borrows m.globals body.layouts m.callerLocals h_pure]
        rw [evalOperand_pure_eq ps.env op emptyMemory.borrows emptyMemory.globals body.layouts emptyMemory.callerLocals h_pure] at h_eval
        cases h_ev : evalOperand ps.env op [] [] body.layouts [] with
        | ub => rw [h_ev] at h_eval; nomatch h_eval
        | unsupported => rw [h_ev] at h_eval; nomatch h_eval
        | ok val l' =>
          rw [h_ev] at h_eval
          cases val with
          | scalar sc =>
            dsimp only at h_eval ⊢
            cases h_ok : Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
            | false => rw [h_ok] at h_eval; nomatch h_eval
            | true =>
              rw [h_ok] at h_eval
              injection h_eval with h_se; injection h_se with h_eq
              subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
          | _ => nomatch h_eval
    | retag _ _ => cases h_pure
    | backwardIncompatibleDropHint _ => cases h_pure
    | setDiscriminant p varIdx =>
      dsimp only [isPureStatement] at h_pure
      have h_op : isPureOperand (.copy p) = true := h_pure
      unfold evalStmt at h_eval ⊢
      dsimp only [PureState.toMachineState] at h_eval ⊢
      rcases p with ⟨loc, proj⟩
      cases proj with
      | nil =>
        dsimp only at h_eval ⊢
        cases h_g : get? ps.env loc with
        | none => rw [h_g] at h_eval; nomatch h_eval
        | some sl =>
          rw [h_g] at h_eval
          cases sl with
          | uninit => nomatch h_eval
          | dead => nomatch h_eval
          | init v =>
            cases v with
            | aggregate _ flds =>
              dsimp only at h_eval ⊢
              cases h_s : set? ps.env loc (.init (.aggregate varIdx flds)) with
              | none => rw [h_s] at h_eval; nomatch h_eval
              | some _ =>
                rw [h_s] at h_eval
                injection h_eval with h_se; injection h_se with h_eq
                subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
            | _ => nomatch h_eval
      | cons hd tl =>
        dsimp only at h_eval ⊢
        rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
          m.borrows m.globals body.layouts m.callerLocals h_op]
        rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
          emptyMemory.borrows emptyMemory.globals body.layouts emptyMemory.callerLocals h_op] at h_eval
        cases h_ev : evalOperand ps.env (.copy { local_ := loc, projection := hd :: tl }) [] [] body.layouts [] with
        | ub => rw [h_ev] at h_eval; nomatch h_eval
        | unsupported => rw [h_ev] at h_eval; nomatch h_eval
        | ok v l1 =>
          rw [h_ev] at h_eval
          cases v with
          | aggregate _ flds =>
            dsimp only at h_eval ⊢
            rw [writePlaceValue_pure_eq l1 m.borrows { local_ := loc, projection := hd :: tl } (.aggregate varIdx flds) h_pure]
            rw [writePlaceValue_pure_eq l1 emptyMemory.borrows { local_ := loc, projection := hd :: tl } (.aggregate varIdx flds) h_pure] at h_eval
            cases h_w : writePlaceValue l1 [] { local_ := loc, projection := hd :: tl } (.aggregate varIdx flds) with
            | ub => rw [h_w] at h_eval; nomatch h_eval
            | unsupported => rw [h_w] at h_eval; nomatch h_eval
            | ok _ =>
              rw [h_w] at h_eval
              injection h_eval with h_se; injection h_se with h_eq
              subst h_eq; exact ⟨m.borrows, by cases m; rfl⟩
          | _ => nomatch h_eval
    | assign dst rv =>
      simp only [isPureStatement, Bool.and_eq_true] at h_pure
      rcases h_pure with ⟨h_dst, h_rv⟩
      rw [evalStmt_assign_eq] at h_eval
      rw [evalStmt_assign_eq]
      dsimp only [PureState.toMachineState] at h_eval ⊢
      rw [evalRvalue_pure_eq_withMem ps.env rv m body.localDecls body.layouts h_rv]
      have h_emp := evalRvalue_pure_eq_withMem ps.env rv emptyMemory body.localDecls body.layouts h_rv
      cases h_res : evalRvalue ps.env rv emptyMemory body.localDecls body.layouts with
      | ub => rw [h_res] at h_eval; nomatch h_eval
      | unsupported => rw [h_res] at h_eval; nomatch h_eval
      | ok val l1 mem1 =>
        have h_mem1 : mem1 = emptyMemory := by
          rw [h_res] at h_emp; injection h_emp
        subst h_mem1
        rw [h_res] at h_eval
        dsimp only [RvalueEvalResult.withMem] at h_eval ⊢
        rcases dst with ⟨dstLoc, dstProj⟩
        cases dstProj with
        | nil =>
          unfold evalAssignDst at h_eval ⊢
          dsimp only at h_eval ⊢
          cases h_g : get? l1 dstLoc with
          | none => rw [h_g] at h_eval; nomatch h_eval
          | some sl =>
            rw [h_g] at h_eval
            cases sl with
            | dead => nomatch h_eval
            | uninit =>
              cases h_s : set? l1 dstLoc (.init val) with
              | none => rw [h_s] at h_eval; nomatch h_eval
              | some l2 =>
                rw [h_s] at h_eval
                dsimp only [emptyMemory] at h_eval
                rw [h_ap]
                injection h_eval with h_se; injection h_se with h_eq
                subst h_eq
                exact ⟨invalidateConflictingBorrows m.borrows dstLoc .none, rfl⟩
            | init _ =>
              cases h_s : set? l1 dstLoc (.init val) with
              | none => rw [h_s] at h_eval; nomatch h_eval
              | some l2 =>
                rw [h_s] at h_eval
                dsimp only [emptyMemory] at h_eval
                rw [h_ap]
                injection h_eval with h_se; injection h_se with h_eq
                subst h_eq
                exact ⟨invalidateConflictingBorrows m.borrows dstLoc .none, rfl⟩
        | cons hd tl =>
          simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_dst
          have h_nd := ne_deref_of_isPureProjElem h_dst.1
          rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd] at h_eval
          rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd]
          unfold evalAssignNonDeref at h_eval ⊢
          dsimp only at h_eval ⊢
          cases h_g : get? l1 dstLoc with
          | none => rw [h_g] at h_eval; nomatch h_eval
          | some sl =>
            rw [h_g] at h_eval
            cases sl with
            | uninit => nomatch h_eval
            | dead => nomatch h_eval
            | init rootVal =>
              dsimp only at h_eval ⊢
              generalize writeProjectedValue l1 rootVal _ val = wpvRes at h_eval ⊢
              cases wpvRes with
              | ub => nomatch h_eval
              | unsupported => nomatch h_eval
              | ok rootVal' =>
                dsimp only at h_eval ⊢
                cases h_s : set? l1 dstLoc (.init rootVal') with
                | none => rw [h_s] at h_eval; nomatch h_eval
                | some l2 =>
                  rw [h_s] at h_eval
                  dsimp only [emptyMemory] at h_eval
                  rw [h_ap]
                  injection h_eval with h_se; injection h_se with h_eq
                  subst h_eq
                  exact ⟨invalidateConflictingBorrowsAtProj m.borrows dstLoc .none _, rfl⟩
  rcases h_step_m with ⟨bs, h_eval_m⟩
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState] at h_eval_m ⊢
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt]
    dsimp only
    rw [h_eval_m]
    exact h_next { m with borrows := bs } (ModularRootMemory.withBorrows hm bs)

/-- 1-step `goto` terminator rule for `PureMirModularConverges`. -/
theorem PureMirModularConverges.step_goto
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {targetBb : BasicBlockIdx}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .goto targetBb)
    (h_next :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := ps.env } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    exact h_next m hm

private theorem resolveCalleeBodyAndArgs?_nil
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (traitImpls : List TraitImplEntry) :
    resolveCalleeBodyAndArgs? [] defPath typeArgs traitImpls = none := by
  have h_nonparam (fa : RigidTy) (ra : List RigidTy) :
      (let allTraitImpls := traitImpls ++ flatMapTraitImpls []
       let matchedImpls := collectMatchingTraitImpls [] allTraitImpls defPath (fa :: ra)
       match matchedImpls with
       | [] =>
         match findCallee? [] defPath with
         | none => none
         | some c =>
           match Bool.and (hasTraitImplForDefPath allTraitImpls defPath)
               (Bool.not (allParamsInCallerLayouts 0 fa)) with
           | true => none
           | false => some (c, fa :: ra)
       | _ :: _ =>
         match filterMostSpecificTraitImpls matchedImpls matchedImpls with
         | (winnerEntry, some implTypeArgs) :: [] =>
           match findCallee? [] winnerEntry.implPath with
           | some c =>
             let effectiveTypeArgs :=
               match stringEq winnerEntry.implPath defPath with
               | true => fa :: ra
               | false => implTypeArgs
             if effectiveTypeArgs.length == c.typeParamCount then
               some (c, effectiveTypeArgs)
             else none
           | none => none
         | _ => none) = (none : Option (CapturedMir × List RigidTy)) := by
    dsimp only
    cases h_m : collectMatchingTraitImpls []
        (traitImpls ++ flatMapTraitImpls []) defPath (fa :: ra) with
    | nil => rfl
    | cons hd tl =>
      dsimp only
      cases filterMostSpecificTraitImpls (hd :: tl) (hd :: tl) with
      | nil => rfl
      | cons w wtl =>
        rcases w with ⟨_, wargs⟩
        cases wargs <;> cases wtl <;> rfl
  unfold resolveCalleeBodyAndArgs?
  cases typeArgs with
  | nil => rfl
  | cons firstArg restArgs =>
    cases firstArg with
    | param _ _ => rfl
    | bool => exact h_nonparam _ _
    | char => exact h_nonparam _ _
    | int _ => exact h_nonparam _ _
    | uint _ => exact h_nonparam _ _
    | float _ => exact h_nonparam _ _
    | never => exact h_nonparam _ _
    | str => exact h_nonparam _ _
    | tuple _ => exact h_nonparam _ _
    | array _ _ => exact h_nonparam _ _
    | slice _ => exact h_nonparam _ _
    | ref _ _ => exact h_nonparam _ _
    | rawPtr _ _ => exact h_nonparam _ _
    | adt _ _ => exact h_nonparam _ _
    | fnDef _ _ => exact h_nonparam _ _
    | fnPtr _ _ _ _ => exact h_nonparam _ _
    | closure _ _ => exact h_nonparam _ _
    | dynamic _ => exact h_nonparam _ _
    | foreign _ => exact h_nonparam _ _
    | alias _ _ => exact h_nonparam _ _
    | other _ => exact h_nonparam _ _

/--
Looking up any callee in an empty `callees` list returns `none` for any
`traitImpls`.
-/
@[simp]
theorem lookupCallee_nil
    (layouts : LayoutTable)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (traitImpls : List TraitImplEntry) :
    lookupCallee [] layouts defPath typeArgs traitImpls = none := by
  unfold lookupCallee
  rw [resolveCalleeBodyAndArgs?_nil]

/--
Compositional 1-step modular call rule (`PureMirModularConverges.call_modular`,
`FF-2.2` Section 2 & 4):
when block `bb` ends with `TerminatorKind.call func argOps destination (.some
targetBb) unwind`
targeting an un-inlined callee `(defPath, typeArgs)` covered by `contract`
(such as `#[external_spec]`, `polyExternalSpecCallContract`, or
`pureRustIntrinsicContract`), the caller steps directly in **1 compositional
step** to `{ bb := targetBb, stmtIdx := 0, env := updatedEnv }` in `PureState`
for every normal return value `retVal` satisfying `calleePost retVal`.
-/
theorem PureMirModularConverges.call_modular
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        contract.pre
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        contract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        ModularRootMemory body callees traitImpls retMem ∧ calleePost retVal)
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ contract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem))
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        contract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = [])
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (resumeExternalCall (ps.toMachineState m) envAfterArgs
            destination targetBb unwind) := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_not_exact]
      dsimp only [evalDirectRustIntrinsic?]
      rw [h_not_intrinsic]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  refine ⟨h_contract_pre m hm, fun ans h_cpost => ?_⟩
  cases ans with
  | aborted =>
    dsimp only [resumeExternalCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    rcases h_contract_panic with rfl | rfl | h_no_panic
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [h_panic_stack m panicMem hm h_cpost]
      dsimp only [unwindFromCallStack]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · exact False.elim (h_no_panic m panicMem hm h_cpost)
  | returned retVal retMem =>
    rcases h_contract_ret m retMem retVal hm h_cpost with ⟨h_mod_ret, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr, h_next⟩
    dsimp only [resumeExternalCall]
    rw [writePlaceValue_pure_eq envAfterArgs retMem.borrows destination retVal h_dst_pure]
    unfold writePurePlaceValue at h_wr
    rw [h_wr]
    exact h_next retMem h_mod_ret

/--
1-step specialization of `PureMirModularConverges.call_modular` for polymorphic
`#[external_spec]` call contracts (`polyExternalSpecCallContract`).
-/
theorem PureMirModularConverges.call_poly_external_spec
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_targs : extractCalleeTypeArgs func = expectedTypeArgs)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨ unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false)
    (h_after :
      ∀ (retVal : Value),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges
            (polyExternalSpecCallContract targetDefPath expectedTypeArgs
              sidecarBody extraPre extraPost)
            body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges
      (polyExternalSpecCallContract targetDefPath expectedTypeArgs
        sidecarBody extraPre extraPost)
      body callees ps post traitImpls := by
  refine PureMirModularConverges.call_modular
    h_phase h_bb h_end h_term h_dst_pure h_args_pure h_def h_args
    (by rw [h_targs]; exact h_lookup)
    h_not_exact
    (fun _ _ => ⟨rfl, h_targs, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m retMem retVal hm hp =>
      ⟨ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1, hp.2⟩)
    ?_
    (fun m panicMem hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])
    h_after
    h_not_intrinsic
  rcases h_unwind with hu | hu | h_nu
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · refine Or.inr (Or.inr (fun _ _ _ hp => ?_))
    dsimp only [polyExternalSpecCallContract] at hp
    rw [h_nu] at hp
    exact hp

/--
1-step specialization of `PureMirModularConverges.call_modular` for monomorphic
`#[external_spec]` call contracts (`externalSpecCallContract`, when
`traitImpls = []` and `body.traitImpls = []`, or via `combineMirCallContracts`).
-/
theorem PureMirModularConverges.call_external_spec
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨ unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false)
    (h_after :
      ∀ (retVal : Value) (tr' : List TraitImplEntry),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges
            (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
            body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post tr')
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
      body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := targetDefPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (resumeExternalCall (ps.toMachineState m) envAfterArgs
            destination targetBb unwind) := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_not_exact]
      dsimp only [evalDirectRustIntrinsic?]
      rw [h_not_intrinsic]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  refine ⟨⟨rfl, h_arity, h_param_tys, h_extra_pre⟩, fun ans hp => ?_⟩
  cases ans with
  | aborted =>
    dsimp only [resumeExternalCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    dsimp only [externalSpecCallContract] at hp
    rcases h_unwind with rfl | rfl | h_nu
    · cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · dsimp only [resumeExternalCall, applyUnwindAction]
        rw [hp.2.1, hm.2.2.1]
        dsimp only [unwindFromCallStack]
        rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
        trivial
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · rw [h_nu] at hp
      exact False.elim hp
  | returned retVal retMem =>
    rcases hp with ⟨h_fp, h_ret_ty, h_ep⟩
    rcases h_after retVal retMem.traitImpls ⟨h_ret_ty, h_ep⟩ with ⟨updEnv, h_wr, h_next⟩
    dsimp only [resumeExternalCall]
    rw [writePlaceValue_pure_eq envAfterArgs retMem.borrows destination retVal h_dst_pure]
    unfold writePurePlaceValue at h_wr
    rw [h_wr]
    have hm_ret : ModularRootMemory body callees retMem.traitImpls retMem := by
      rcases h_fp with ⟨hc', hcs', hac', hap', _⟩
      exact ⟨by rw [hc', hm.1], rfl, by rw [hcs', hm.2.2.1],
        by rw [hac']; exact hm.2.2.2.1, by rw [hap', hm.2.2.2.2]⟩
    exact h_next retMem hm_ret

/--
1-step specialization of `PureMirModularConverges.call_modular` for pure
`CallConv.rustIntrinsic` calls under `pureRustIntrinsicContract`.
-/
theorem PureMirModularConverges.call_intrinsic
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {kind : PureRustIntrinsicKind}
    {envAfterArgs updatedEnv : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind
        (extractCalleeTypeArgs func) argVals pointerBytes ubChecksEnabled =
        some retVal)
    (h_wr : writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv)
    (h_after :
      PureMirModularConverges
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges
      (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
      body callees ps post traitImpls := by
  refine PureMirModularConverges.call_modular
    (calleePost := (· = retVal))
    h_phase h_bb h_end h_term h_dst_pure h_args_pure h_def h_args h_lookup
    h_not_exact
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m retMem rv hm hp => by
      rcases hp with ⟨rfl, k', hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      exact ⟨hm, hrv_eq.symm⟩)
    (Or.inr (Or.inr (fun _ _ _ hp => hp)))
    (fun _ _ _ hp => False.elim hp)
    (fun rv h_eq => by
      subst h_eq
      exact ⟨updatedEnv, h_wr, h_after⟩)
    h_not_intrinsic

/--
1-step modular call rule parameterized by a subsumed sub-contract `subContract`
(`h_sub : subContract.Subsumes contract`), enabling a single modular caller to
mix `call_intrinsic_sub`, `call_poly_external_spec_sub`, and
`call_external_spec_sub` steps while keeping the continuation in `contract`.
-/
theorem PureMirModularConverges.call_modular_sub
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        ModularRootMemory body callees traitImpls retMem ∧ calleePost retVal)
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem))
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = [])
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  refine PureMirModularConverges.call_modular
    h_phase h_bb h_end h_term h_dst_pure h_args_pure h_def h_args h_lookup
    h_not_exact
    (fun m hm => (h_sub _ (h_contract_pre m hm)).1)
    (fun m retMem retVal hm hp =>
      h_contract_ret m retMem retVal hm
        ((h_sub _ (h_contract_pre m hm)).2 _ hp))
    ?_
    (fun m panicMem hm hp =>
      h_panic_stack m panicMem hm ((h_sub _ (h_contract_pre m hm)).2 _ hp))
    h_after
    h_not_intrinsic
  rcases h_contract_panic with hu | hu | h_np
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (fun m panicMem hm hp =>
      h_np m panicMem hm ((h_sub _ (h_contract_pre m hm)).2 _ hp)))

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` call rule inside modular
callers (`PureMirModularConverges.call_poly_external_spec_sub`), usable directly
under `combineMirCallContracts` via `MirCallContract.Subsumes`.
-/
theorem PureMirModularConverges.call_poly_external_spec_sub
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_targs : extractCalleeTypeArgs func = expectedTypeArgs)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨ unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false)
    (h_after :
      ∀ (retVal : Value),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  refine PureMirModularConverges.call_modular_sub h_sub
    h_phase h_bb h_end h_term h_dst_pure h_args_pure h_def h_args
    (by rw [h_targs]; exact h_lookup)
    h_not_exact
    (fun _ _ => ⟨rfl, h_targs, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ _ hm hp =>
      ⟨ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1, hp.2⟩)
    ?_
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])
    h_after
    h_not_intrinsic
  rcases h_unwind with hu | hu | h_nu
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · refine Or.inr (Or.inr (fun _ _ _ hp => ?_))
    dsimp only [polyExternalSpecCallContract] at hp
    rw [h_nu] at hp
    exact hp

/--
Subsumption-aware 1-step monomorphic `#[external_spec]` call rule inside modular
callers (`PureMirModularConverges.call_external_spec_sub`), usable directly
under `combineMirCallContracts` via `MirCallContract.Subsumes`.
-/
theorem PureMirModularConverges.call_external_spec_sub
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨ unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false)
    (h_after :
      ∀ (retVal : Value) (tr' : List TraitImplEntry),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post tr')
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := targetDefPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (resumeExternalCall (ps.toMachineState m) envAfterArgs
            destination targetBb unwind) := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_not_exact]
      dsimp only [evalDirectRustIntrinsic?]
      rw [h_not_intrinsic]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  have h_sub_pre :
      (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost).pre
        { defPath := targetDefPath
          typeArgs := extractCalleeTypeArgs func
          args := argVals
          memory := m } := ⟨rfl, h_arity, h_param_tys, h_extra_pre⟩
  rcases h_sub _ h_sub_pre with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    dsimp only [externalSpecCallContract] at hp
    rcases h_unwind with rfl | rfl | h_nu
    · cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · dsimp only [resumeExternalCall, applyUnwindAction]
        rw [hp.2.1, hm.2.2.1]
        dsimp only [unwindFromCallStack]
        rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
        trivial
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · rw [h_nu] at hp
      exact False.elim hp
  | returned retVal retMem =>
    rcases hp with ⟨h_fp, h_ret_ty, h_ep⟩
    rcases h_after retVal retMem.traitImpls ⟨h_ret_ty, h_ep⟩ with ⟨updEnv, h_wr, h_next⟩
    dsimp only [resumeExternalCall]
    rw [writePlaceValue_pure_eq envAfterArgs retMem.borrows destination retVal h_dst_pure]
    unfold writePurePlaceValue at h_wr
    rw [h_wr]
    have hm_ret : ModularRootMemory body callees retMem.traitImpls retMem := by
      rcases h_fp with ⟨hc', hcs', hac', hap', _⟩
      exact ⟨by rw [hc', hm.1], rfl, by rw [hcs', hm.2.2.1],
        by rw [hac']; exact hm.2.2.2.1, by rw [hap', hm.2.2.2.2]⟩
    exact h_next retMem hm_ret

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` call rule inside modular
callers (`PureMirModularConverges.call_intrinsic_sub`), usable directly under
`combineMirCallContracts` via `MirCallContract.Subsumes` for external intrinsic
aliases (`classifyRustIntrinsic? defPath = none`, e.g. `std::intrinsics::*`).
-/
theorem PureMirModularConverges.call_intrinsic_sub
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {kind : PureRustIntrinsicKind}
    {envAfterArgs updatedEnv : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind
        (extractCalleeTypeArgs func) argVals pointerBytes ubChecksEnabled =
        some retVal)
    (h_wr : writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv)
    (h_after :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  refine PureMirModularConverges.call_modular_sub
    (calleePost := (· = retVal))
    h_sub h_phase h_bb h_end h_term h_dst_pure h_args_pure h_def h_args h_lookup
    h_not_exact
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ _ hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      exact ⟨hm, hrv_eq.symm⟩)
    (Or.inr (Or.inr (fun _ _ _ hp => hp)))
    (fun _ _ _ hp => False.elim hp)
    (fun rv h_eq => by
      subst h_eq
      exact ⟨updatedEnv, h_wr, h_after⟩)
    h_not_intrinsic

private theorem bswapLoop_eq_pureBswapLoop (n b a : Nat) :
    bswapLoop n b a = pureBswapLoop n b a := by
  induction n generalizing b a with
  | zero => rfl
  | succ n ih =>
    dsimp only [bswapLoop, pureBswapLoop]
    exact ih _ _

private theorem ctpopLoop_eq_pureCtpopLoop (n b : Nat) :
    ctpopLoop n b = pureCtpopLoop n b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    dsimp only [ctpopLoop, pureCtpopLoop]
    rw [ih]

private theorem wrapScalarBits_u32_of_lt {v : Nat} (hv : v < 4294967296) :
    wrapScalarBits v (scalarModulus 4) = v := by
  have hm : scalarModulus 4 = 4294967296 := rfl
  rw [hm]
  unfold wrapScalarBits
  cases h : Nat.ble 4294967296 v with
  | false => rfl
  | true =>
    have hle := Nat.le_of_ble_eq_true h
    omega

private theorem evalBswap_u32_eq {v : Nat} (hv : v < 4294967296) :
    evalBswap ⟨v, 4⟩ = some ⟨pureBswapLoop 4 v 0, 4⟩ := by
  unfold evalBswap
  dsimp only
  rw [wrapScalarBits_u32_of_lt hv, bswapLoop_eq_pureBswapLoop]

private theorem evalCtpop_u32_eq {v : Nat} (hv : v < 4294967296) :
    evalCtpop ⟨v, 4⟩ = some ⟨pureCtpopLoop 32 v, 4⟩ := by
  unfold evalCtpop
  dsimp only
  rw [wrapScalarBits_u32_of_lt hv, ctpopLoop_eq_pureCtpopLoop]
  rfl

private theorem evalDirectRustIntrinsic_bswap_u32
    (s : MachineState) (curBody : Option CapturedMir)
    (typeArgs : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List SlotState)
    (dst : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    {v : Nat} (hv : v < 4294967296) :
    evalDirectRustIntrinsic? s curBody
      { defPath := "core::intrinsics::bswap", typeArgs := typeArgs, fnSig := .none, isIndirect := false }
      decls layouts argOps [.scalar ⟨v, 4⟩] locals' dst targetBb unwind =
    some (writeIntrinsicReturn s locals' dst targetBb (.scalar ⟨pureBswapLoop 4 v 0, 4⟩)) := by
  rw [evalDirectRustIntrinsic?_nonSelect _ _ _ _ _ _ _ _ _ _ _ (rk := .bswap) rfl (by rintro ⟨⟩)]
  change some (writeIntrinsicScalarResult s locals' dst targetBb (evalBswap ⟨v, 4⟩)) = _
  rw [evalBswap_u32_eq hv]

private theorem evalDirectRustIntrinsic_ctpop_u32
    (s : MachineState) (curBody : Option CapturedMir)
    (typeArgs : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List SlotState)
    (dst : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    {v : Nat} (hv : v < 4294967296) :
    evalDirectRustIntrinsic? s curBody
      { defPath := "core::intrinsics::ctpop", typeArgs := typeArgs, fnSig := .none, isIndirect := false }
      decls layouts argOps [.scalar ⟨v, 4⟩] locals' dst targetBb unwind =
    some (writeIntrinsicReturn s locals' dst targetBb (.scalar ⟨pureCtpopLoop 32 v, 4⟩)) := by
  rw [evalDirectRustIntrinsic?_nonSelect _ _ _ _ _ _ _ _ _ _ _ (rk := .ctpop) rfl (by rintro ⟨⟩)]
  change some (writeIntrinsicScalarResult s locals' dst targetBb (evalCtpop ⟨v, 4⟩)) = _
  rw [evalCtpop_u32_eq hv]

private theorem evalDirectRustIntrinsic_constEvalSelect_ctpop_u32
    (s : MachineState) (curBody : Option CapturedMir)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (op0 op1 rtOp : Operand) (locals' : List SlotState)
    (dst : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    {sc : ScalarInt}
    (h_rt_def : extractCalleeDefPath? rtOp = some "core::intrinsics::ctpop")
    (h_rt_targs : extractCalleeTypeArgs rtOp = [.uint .u32])
    (h_rt_lk :
      lookupCallee s.memory.callees layouts "core::intrinsics::ctpop"
        [.uint .u32] s.memory.traitImpls = none)
    (h_sz : sc.sizeBytes = 4)
    (h_lt : sc.bits < 4294967296) :
    evalDirectRustIntrinsic? s curBody
      { defPath := "core::intrinsics::const_eval_select"
        typeArgs := [
          .tuple [.uint .u32],
          .fnDef "core::intrinsics::ctpop" [.uint .u32],
          .fnDef "core::intrinsics::ctpop" [.uint .u32],
          .uint .u32
        ]
        fnSig := .none
        isIndirect := false }
      decls layouts [op0, op1, rtOp] [.aggregate 0 [.scalar sc], .unit, .unit]
      locals' dst targetBb unwind =
    some (writeIntrinsicReturn s locals' dst targetBb
      (.scalar ⟨pureCtpopLoop 32 sc.bits, 4⟩)) := by
  rcases sc with ⟨v, sz⟩
  dsimp only at h_sz h_lt ⊢
  subst h_sz
  have hc_sel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = some .constEvalSelect := rfl
  have hc_pop : classifyRustIntrinsic? "core::intrinsics::ctpop" = some .ctpop := rfl
  have h_unp :
      unpackConstEvalSelectArgs? (.aggregate 0 [.scalar ⟨v, 4⟩]) (some (.tuple [.uint .u32])) =
        some [.scalar ⟨v, 4⟩] := rfl
  have h_res :
      resolveConstEvalSelectTarget? s
        { defPath := "core::intrinsics::const_eval_select"
          typeArgs := [
            .tuple [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .uint .u32
          ]
          fnSig := .none
          isIndirect := false }
        decls layouts (some rtOp) .unit 1 =
      some { defPath := "core::intrinsics::ctpop"
             typeArgs := [.uint .u32]
             fnSig := .none
             isIndirect := false } := by
    unfold resolveConstEvalSelectTarget?
    dsimp only
    rw [h_rt_def, h_rt_targs]
  rw [evalDirectRustIntrinsic?_constEvalSelect_three _ _ _ _ _ _ _ _ _ _ _ _ _ hc_sel]
  unfold evalConstEvalSelectThree
  dsimp only [selectTupleTyOpt, selectRtFnOpOpt]
  rw [h_unp]
  dsimp only [length]
  rw [h_res]
  dsimp only
  rw [h_rt_lk]
  dsimp only [isDirectExactDivTarget]
  have h_ne : stringEq "core::intrinsics::ctpop" "core::intrinsics::exact_div" = false := by decide
  rw [h_ne]
  dsimp only
  rw [hc_pop]
  change some (writeIntrinsicScalarResult s locals' dst targetBb (evalCtpop ⟨v, 4⟩)) = _
  rw [evalCtpop_u32_eq h_lt]

/--
1-step inline `CallConv.rustIntrinsic` `.call` rule for `PureMirModularConverges`
when `evalDirectRustIntrinsic?` evaluates inline to `writeIntrinsicReturn`
(covering all 22 inline scalar/layout intrinsics as well as `const_eval_select`
dispatching to an unlinked inline intrinsic, for any modular `contract`).
-/
theorem PureMirModularConverges.call_inline_intrinsic
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs updatedEnv : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_eval :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        evalDirectRustIntrinsic? (ps.toMachineState m) (some body)
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            fnSig := .none
            isIndirect := false }
          body.localDecls body.layouts argOps argVals envAfterArgs
          destination targetBb unwind =
          some (writeIntrinsicReturn (ps.toMachineState m) envAfterArgs
            destination targetBb retVal))
    (h_wr : writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv)
    (h_after :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.step
          (({ bb := targetBb, stmtIdx := 0, env := updatedEnv } : PureState).toMachineState m) := by
    have h_ev := h_eval m hm
    dsimp only [PureState.toMachineState] at h_ev
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_not_exact]
      dsimp only
      rw [h_ev]
      dsimp only [writeIntrinsicReturn]
      rw [writePlaceValue_pure_eq envAfterArgs m.borrows destination retVal h_dst_pure]
      unfold writePurePlaceValue at h_wr
      rw [h_wr]
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  exact h_after m hm

private def SameCallFrameAndTraits (m₁ m₂ : Memory) : Prop :=
  m₂.callees = m₁.callees ∧
  m₂.traitImpls = m₁.traitImpls ∧
  m₂.callStack = m₁.callStack ∧
  m₂.activeCallee = m₁.activeCallee ∧
  m₂.activeProtectors = m₁.activeProtectors

private def ModularCalleeOutMemory
    (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (m : Memory) : Prop :=
  m.callees = callees ∧
  m.traitImpls = traitImpls ∧
  m.callStack = [] ∧
  m.activeProtectors = []

private theorem sameExceptBorrows_step_noCall
    {fuel : Nat} {body : CapturedMir} {callees : List CapturedMir}
    {traitImpls : List TraitImplEntry}
    {st₁ st₂ : MirExecState} {P : Value → Prop}
    (h_inv :
      match st₁ with
      | .running s₁ =>
        PureCalleeMachineInv callees traitImpls body s₁ ∧
        ∀ f ∈ s₁.memory.callStack, isPurePlace f.destination = true
      | _ => True)
    (h_rel :
      match st₁, st₂ with
      | .running s₁, .running s₂ =>
        s₂.frame = s₁.frame ∧
        SameCallFrameAndTraits s₁.memory s₂.memory
      | .halted (.normal (v₁, m₁)), .halted (.normal (v₂, m₂)) =>
        v₂ = v₁ ∧ SameCallFrameAndTraits m₁ m₂
      | .halted .panic, .halted .panic => True
      | .halted .abort, .halted .abort => True
      | .faulted fk₁, .faulted fk₂ => fk₂ = fk₁
      | _, _ => False)
    (h_wp :
      wpMirExecNoCallSym fuel body st₁
        (mirNormalPost
          (fun retVal mem' =>
            ActiveRootMemory body
              (pureCalleeMemory callees traitImpls) mem' ∧ P retVal))) :
    wpMirExecNoCallSym fuel body st₂
      (mirNormalPost
        (fun retVal mem' =>
          ModularCalleeOutMemory callees traitImpls mem' ∧ P retVal)) := by
  induction fuel generalizing st₁ st₂ with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    have ih_run {ns₁ ns₂ : MachineState}
        (hi :
          PureCalleeMachineInv callees traitImpls body ns₁ ∧
          ∀ f ∈ ns₁.memory.callStack, isPurePlace f.destination = true)
        (hr : ns₂.frame = ns₁.frame ∧ SameCallFrameAndTraits ns₁.memory ns₂.memory)
        (hw :
          wpMirExecNoCallSym fuel' body (.running ns₁)
            (mirNormalPost
              (fun retVal mem' =>
                ActiveRootMemory body
                  (pureCalleeMemory callees traitImpls) mem' ∧ P retVal))) :
        wpMirExecNoCallSym fuel' body (.running ns₂)
          (mirNormalPost
            (fun retVal mem' =>
              ModularCalleeOutMemory callees traitImpls mem' ∧ P retVal)) :=
      ih (st₁ := .running ns₁) (st₂ := .running ns₂) hi hr hw
    unfold wpMirExecNoCallSym at h_wp ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval] at h_wp ⊢
    cases st₁ with
    | faulted _ => exact False.elim h_wp
    | halted out₁ =>
      cases out₁ with
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
      | normal rv₁ =>
        rcases rv₁ with ⟨v₁, m₁⟩
        cases st₂ with
        | running _ => exact False.elim h_rel
        | faulted _ => exact False.elim h_rel
        | halted out₂ =>
          cases out₂ with
          | panic => exact False.elim h_rel
          | abort => exact False.elim h_rel
          | normal rv₂ =>
            rcases rv₂ with ⟨v₂, m₂⟩
            rcases h_rel with ⟨rfl, hc, ht, hcs, _, hap⟩
            rcases h_wp with ⟨h_act₁, hp₁⟩
            refine ⟨?_, hp₁⟩
            dsimp only [ModularCalleeOutMemory]
            rw [hc, ht, hcs, hap]
            rcases h_act₁ with rfl | ⟨_, rfl⟩ <;>
              exact ⟨rfl, rfl, rfl, rfl⟩
    | running s₁ =>
      cases st₂ with
      | halted _ => exact False.elim h_rel
      | faulted _ => exact False.elim h_rel
      | running s₂ =>
        rcases h_rel with ⟨h_fr, h_meq⟩
        rcases h_meq with ⟨mf_cal, mf_tr, mf_cs, mf_ac, mf_ap⟩
        have h_meq : SameCallFrameAndTraits s₁.memory s₂.memory :=
          ⟨mf_cal, mf_tr, mf_cs, mf_ac, mf_ap⟩
        rcases h_inv with ⟨h_p_inv, h_dst_stk⟩
        rcases h_p_inv with ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
        have h_inv_full : PureCalleeMachineInv callees traitImpls body s₁ :=
          ⟨h_bor, h_glob, h_cloc, h_ap, h_cal, h_tr, h_act, h_stack⟩
        dsimp only [stepMirState] at h_wp ⊢
        rw [stepMirFn_eq_ite] at h_wp
        rw [stepMirFn_eq_ite]
        dsimp only at h_wp ⊢
        rw [mf_ac, h_fr]
        cases h_ph : isOtherPhase (s₁.memory.activeCallee.getD body).phase with
        | true =>
          simp only [h_ph, ite_true] at h_wp
          exact False.elim h_wp
        | false =>
          simp only [h_ph, Bool.false_eq_true, ite_false] at h_wp ⊢
          cases h_bb : get? (s₁.memory.activeCallee.getD body).basicBlocks s₁.frame.blockIdx with
          | none =>
            rw [h_bb] at h_wp
            exact False.elim h_wp
          | some bb =>
            rw [h_bb] at h_wp
            dsimp only at h_wp ⊢
            have ⟨h_stmts, h_term⟩ := IsPureWithCalleesAtSomeDepth.block h_act h_bb
            cases h_stmt : get? bb.statements s₁.frame.stmtIdx with
            | some stmt =>
              rw [h_stmt] at h_wp
              dsimp only at h_wp ⊢
              have h_s := list_all_of_get? h_stmts h_stmt
              have h_inv_next :=
                evalStmt_preserves_pureCalleeMachineInv
                  (localDecls := (s₁.memory.activeCallee.getD body).localDecls)
                  (layouts := (s₁.memory.activeCallee.getD body).layouts)
                  h_s h_inv_full
              have h_adv (locs : List LocalSlot) :
                  (advanceStmt s₂ locs).frame = (advanceStmt s₁ locs).frame := by
                dsimp only [advanceStmt]; rw [h_fr]
              have h_adv_m (locs : List LocalSlot) (m₁ m₂ : Memory) :
                  (advanceStmt s₂ locs m₂).frame = (advanceStmt s₁ locs m₁).frame := by
                dsimp only [advanceStmt]; rw [h_fr]
              rcases stmt with ⟨skind, sspan⟩
              cases skind with
              | nop =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
              | coverage =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
              | constEvalCounter =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
              | placeMention p =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                cases h_g : get? s₁.frame.locals p.local_ with
                | none => rw [h_g] at h_wp; exact False.elim h_wp
                | some sl =>
                  rw [h_g] at h_wp h_inv_next
                  cases sl with
                  | dead => exact False.elim h_wp
                  | uninit =>
                    dsimp only at h_wp h_inv_next ⊢
                    cases h_ok : placeMentionOperandsInit s₁.frame.locals .uninit p.projection with
                    | false => rw [h_ok] at h_wp; exact False.elim h_wp
                    | true =>
                      rw [h_ok] at h_wp h_inv_next
                      exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                  | init v =>
                    dsimp only at h_wp h_inv_next ⊢
                    cases h_ok : placeMentionOperandsInit s₁.frame.locals (.init v) p.projection with
                    | false => rw [h_ok] at h_wp; exact False.elim h_wp
                    | true =>
                      rw [h_ok] at h_wp h_inv_next
                      exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
              | storageLive loc =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                cases h_g : get? s₁.frame.locals loc with
                | none => rw [h_g] at h_wp; exact False.elim h_wp
                | some _ =>
                  rw [h_g] at h_wp h_inv_next
                  cases h_set : set? s₁.frame.locals loc .uninit with
                  | none => rw [h_set] at h_wp; exact False.elim h_wp
                  | some _ =>
                    rw [h_set] at h_wp h_inv_next
                    exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv_m _ _ _, h_meq⟩ h_wp
              | storageDead loc =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                cases h_g : get? s₁.frame.locals loc with
                | none => rw [h_g] at h_wp; exact False.elim h_wp
                | some _ =>
                  rw [h_g] at h_wp h_inv_next
                  cases h_set : set? s₁.frame.locals loc .dead with
                  | none => rw [h_set] at h_wp; exact False.elim h_wp
                  | some _ =>
                    rw [h_set] at h_wp h_inv_next
                    rw [h_ap] at h_wp h_inv_next
                    have h_ap2 : s₂.memory.activeProtectors = [] := by
                      rw [mf_ap, h_ap]
                    rw [h_ap2]
                    exact ih_run ⟨h_inv_next, h_dst_stk⟩
                      ⟨h_adv_m _ _ _, ⟨mf_cal, mf_tr, mf_cs, mf_ac, rfl⟩⟩ h_wp
              | deinit p =>
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                rcases p with ⟨loc, proj⟩
                cases proj with
                | nil =>
                  dsimp only at h_wp h_inv_next ⊢
                  cases h_g : get? s₁.frame.locals loc with
                  | none => rw [h_g] at h_wp; exact False.elim h_wp
                  | some sl =>
                    rw [h_g] at h_wp h_inv_next
                    cases sl with
                    | dead => exact False.elim h_wp
                    | uninit =>
                      cases h_set : set? s₁.frame.locals loc .uninit with
                      | none => rw [h_set] at h_wp; exact False.elim h_wp
                      | some _ =>
                        rw [h_set] at h_wp h_inv_next
                        exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                    | init _ =>
                      cases h_set : set? s₁.frame.locals loc .uninit with
                      | none => rw [h_set] at h_wp; exact False.elim h_wp
                      | some _ =>
                        rw [h_set] at h_wp h_inv_next
                        exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                | cons hd tl =>
                  dsimp only at h_wp h_inv_next ⊢
                  cases h_g : get? s₁.frame.locals loc with
                  | none => rw [h_g] at h_wp; exact False.elim h_wp
                  | some sl =>
                    rw [h_g] at h_wp h_inv_next
                    cases sl with
                    | uninit => exact False.elim h_wp
                    | dead => exact False.elim h_wp
                    | init rv =>
                      dsimp only at h_wp h_inv_next ⊢
                      cases h_rd : readProjectedValue s₁.frame.locals rv (hd :: tl) with
                      | ub => rw [h_rd] at h_wp; exact False.elim h_wp
                      | unsupported => rw [h_rd] at h_wp; exact False.elim h_wp
                      | ok _ =>
                        rw [h_rd] at h_wp h_inv_next
                        exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
              | intrinsic intr =>
                cases intr with
                | copyNonOverlapping _ _ _ => cases h_s
                | assume op =>
                  dsimp only [isPureStatement] at h_s
                  dsimp only [evalStmt] at h_wp h_inv_next ⊢
                  rw [h_fr]
                  rw [evalOperand_pure_eq s₁.frame.locals op s₂.memory.borrows
                    s₂.memory.globals (s₁.memory.activeCallee.getD body).layouts
                    s₂.memory.callerLocals h_s]
                  rw [evalOperand_pure_eq s₁.frame.locals op s₁.memory.borrows
                    s₁.memory.globals (s₁.memory.activeCallee.getD body).layouts
                    s₁.memory.callerLocals h_s] at h_wp h_inv_next
                  cases h_op : evalOperand s₁.frame.locals op [] []
                      (s₁.memory.activeCallee.getD body).layouts [] with
                  | ub => rw [h_op] at h_wp; exact False.elim h_wp
                  | unsupported => rw [h_op] at h_wp; exact False.elim h_wp
                  | ok v l' =>
                    rw [h_op] at h_wp h_inv_next
                    cases v with
                    | scalar sc =>
                      dsimp only at h_wp h_inv_next ⊢
                      cases h_ok : Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
                      | false => rw [h_ok] at h_wp; exact False.elim h_wp
                      | true =>
                        rw [h_ok] at h_wp h_inv_next
                        exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                    | _ => exact False.elim h_wp
              | retag _ _ => cases h_s
              | backwardIncompatibleDropHint _ => cases h_s
              | setDiscriminant p varIdx =>
                dsimp only [isPureStatement] at h_s
                have h_op_p : isPureOperand (.copy p) = true := h_s
                dsimp only [evalStmt] at h_wp h_inv_next ⊢
                rw [h_fr]
                rcases p with ⟨loc, proj⟩
                cases proj with
                | nil =>
                  dsimp only at h_wp h_inv_next ⊢
                  cases h_g : get? s₁.frame.locals loc with
                  | none => rw [h_g] at h_wp; exact False.elim h_wp
                  | some sl =>
                    rw [h_g] at h_wp h_inv_next
                    cases sl with
                    | uninit => exact False.elim h_wp
                    | dead => exact False.elim h_wp
                    | init v =>
                      cases v with
                      | aggregate _ flds =>
                        dsimp only at h_wp h_inv_next ⊢
                        cases h_set : set? s₁.frame.locals loc (.init (.aggregate varIdx flds)) with
                        | none => rw [h_set] at h_wp; exact False.elim h_wp
                        | some _ =>
                          rw [h_set] at h_wp h_inv_next
                          exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                      | _ => exact False.elim h_wp
                | cons hd tl =>
                  dsimp only at h_wp h_inv_next ⊢
                  rw [evalOperand_pure_eq s₁.frame.locals
                    (.copy { local_ := loc, projection := hd :: tl })
                    s₂.memory.borrows s₂.memory.globals
                    (s₁.memory.activeCallee.getD body).layouts
                    s₂.memory.callerLocals h_op_p]
                  rw [evalOperand_pure_eq s₁.frame.locals
                    (.copy { local_ := loc, projection := hd :: tl })
                    s₁.memory.borrows s₁.memory.globals
                    (s₁.memory.activeCallee.getD body).layouts
                    s₁.memory.callerLocals h_op_p] at h_wp h_inv_next
                  cases h_ev : evalOperand s₁.frame.locals
                      (.copy { local_ := loc, projection := hd :: tl }) [] []
                      (s₁.memory.activeCallee.getD body).layouts [] with
                  | ub => rw [h_ev] at h_wp; exact False.elim h_wp
                  | unsupported => rw [h_ev] at h_wp; exact False.elim h_wp
                  | ok v l1 =>
                    rw [h_ev] at h_wp h_inv_next
                    cases v with
                    | aggregate _ flds =>
                      dsimp only at h_wp h_inv_next ⊢
                      rw [writePlaceValue_pure_eq l1 s₂.memory.borrows
                        { local_ := loc, projection := hd :: tl }
                        (.aggregate varIdx flds) h_s]
                      rw [writePlaceValue_pure_eq l1 s₁.memory.borrows
                        { local_ := loc, projection := hd :: tl }
                        (.aggregate varIdx flds) h_s] at h_wp h_inv_next
                      cases h_w : writePlaceValue l1 []
                          { local_ := loc, projection := hd :: tl }
                          (.aggregate varIdx flds) with
                      | ub => rw [h_w] at h_wp; exact False.elim h_wp
                      | unsupported => rw [h_w] at h_wp; exact False.elim h_wp
                      | ok _ =>
                        rw [h_w] at h_wp h_inv_next
                        exact ih_run ⟨h_inv_next, h_dst_stk⟩ ⟨h_adv _, h_meq⟩ h_wp
                    | _ => exact False.elim h_wp
              | assign dst rv =>
                simp only [isPureStatement, Bool.and_eq_true] at h_s
                rcases h_s with ⟨h_dst, h_rv⟩
                rw [evalStmt_assign_eq] at h_wp h_inv_next
                rw [evalStmt_assign_eq]
                rw [h_fr]
                rw [evalRvalue_pure_eq_withMem s₁.frame.locals rv s₂.memory
                  (s₁.memory.activeCallee.getD body).localDecls
                  (s₁.memory.activeCallee.getD body).layouts h_rv]
                rw [evalRvalue_pure_eq_withMem s₁.frame.locals rv s₁.memory
                  (s₁.memory.activeCallee.getD body).localDecls
                  (s₁.memory.activeCallee.getD body).layouts h_rv] at h_wp h_inv_next
                cases h_ev : evalRvalue s₁.frame.locals rv emptyMemory
                    (s₁.memory.activeCallee.getD body).localDecls
                    (s₁.memory.activeCallee.getD body).layouts with
                | ub => rw [h_ev] at h_wp; exact False.elim h_wp
                | unsupported => rw [h_ev] at h_wp; exact False.elim h_wp
                | ok val l1 _ =>
                  rw [h_ev] at h_wp h_inv_next
                  dsimp only [RvalueEvalResult.withMem] at h_wp h_inv_next ⊢
                  rcases dst with ⟨dstLoc, dstProj⟩
                  cases dstProj with
                  | nil =>
                    unfold evalAssignDst at h_wp h_inv_next ⊢
                    dsimp only at h_wp h_inv_next ⊢
                    cases h_g : get? l1 dstLoc with
                    | none => rw [h_g] at h_wp; exact False.elim h_wp
                    | some sl =>
                      rw [h_g] at h_wp h_inv_next
                      cases sl with
                      | dead => exact False.elim h_wp
                      | uninit =>
                        cases h_set : set? l1 dstLoc (.init val) with
                        | none => rw [h_set] at h_wp; exact False.elim h_wp
                        | some l2 =>
                          rw [h_set] at h_wp h_inv_next
                          dsimp only at h_wp h_inv_next ⊢
                          rw [h_ap] at h_wp h_inv_next
                          rw [mf_ap, h_ap]
                          exact ih_run ⟨h_inv_next, by
                            rw [h_bor]; exact h_dst_stk⟩
                            ⟨h_adv_m _ _ _, ⟨mf_cal, mf_tr, mf_cs, mf_ac, rfl⟩⟩ h_wp
                      | init _ =>
                        cases h_set : set? l1 dstLoc (.init val) with
                        | none => rw [h_set] at h_wp; exact False.elim h_wp
                        | some l2 =>
                          rw [h_set] at h_wp h_inv_next
                          dsimp only at h_wp h_inv_next ⊢
                          rw [h_ap] at h_wp h_inv_next
                          rw [mf_ap, h_ap]
                          exact ih_run ⟨h_inv_next, by
                            rw [h_bor]; exact h_dst_stk⟩
                            ⟨h_adv_m _ _ _, ⟨mf_cal, mf_tr, mf_cs, mf_ac, rfl⟩⟩ h_wp
                  | cons hd tl =>
                    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_dst
                    have h_nd := ne_deref_of_isPureProjElem h_dst.1
                    rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd] at h_wp h_inv_next
                    rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ h_nd]
                    unfold evalAssignNonDeref at h_wp h_inv_next ⊢
                    dsimp only at h_wp h_inv_next ⊢
                    cases h_g : get? l1 dstLoc with
                    | none => rw [h_g] at h_wp; exact False.elim h_wp
                    | some sl =>
                      rw [h_g] at h_wp h_inv_next
                      cases sl with
                      | uninit => exact False.elim h_wp
                      | dead => exact False.elim h_wp
                      | init rootVal =>
                        dsimp only at h_wp h_inv_next ⊢
                        generalize writeProjectedValue l1 rootVal _ val = wpvRes at h_wp h_inv_next ⊢
                        cases wpvRes with
                        | ub => exact False.elim h_wp
                        | unsupported => exact False.elim h_wp
                        | ok rootVal' =>
                          dsimp only at h_wp h_inv_next ⊢
                          cases h_set : set? l1 dstLoc (.init rootVal') with
                          | none => rw [h_set] at h_wp; exact False.elim h_wp
                          | some l2 =>
                            rw [h_set] at h_wp h_inv_next
                            dsimp only at h_wp h_inv_next ⊢
                            rw [h_ap] at h_wp h_inv_next
                            rw [mf_ap, h_ap]
                            exact ih_run ⟨h_inv_next, by
                              rw [h_bor]; exact h_dst_stk⟩
                              ⟨h_adv_m _ _ _, ⟨mf_cal, mf_tr, mf_cs, mf_ac, rfl⟩⟩ h_wp
            | none =>
              rw [h_stmt] at h_wp
              dsimp only at h_wp ⊢
              by_cases h_len : (s₁.frame.stmtIdx == length bb.statements) = true
              · simp only [h_len, ite_true] at h_wp ⊢
                rcases bb with ⟨stmts, ⟨tkind, tspan⟩, isCl⟩
                dsimp only at h_term
                have ⟨h_step_inv, _⟩ :=
                  stepMirFn_pureCallee_step_and_replaceRoot
                    (mem₀ := pureCalleeMemory callees traitImpls)
                    h_inv_full rfl rfl rfl
                rw [stepMirFn_eq_ite] at h_step_inv
                dsimp only at h_step_inv
                simp only [h_ph, Bool.false_eq_true, ite_false] at h_step_inv
                rw [h_bb] at h_step_inv
                dsimp only at h_step_inv
                rw [h_stmt] at h_step_inv
                dsimp only at h_step_inv
                simp only [h_len, ite_true] at h_step_inv
                have h_unw_eq :
                    ∀ (cs : List SavedCallerFrame) (m₁ m₂ : Memory),
                      SameCallFrameAndTraits m₁ m₂ →
                      (∀ f ∈ cs, isPurePlace f.destination = true) →
                      match unwindFromCallStack cs m₁, unwindFromCallStack cs m₂ with
                      | .running ns₁, .running ns₂ =>
                        ns₂.frame = ns₁.frame ∧
                        SameCallFrameAndTraits ns₁.memory ns₂.memory ∧
                        ∀ f ∈ ns₁.memory.callStack, isPurePlace f.destination = true
                      | .halted o₁, .halted o₂ =>
                        o₂ = o₁ ∧ (o₁ = .panic ∨ o₁ = .abort)
                      | .faulted f₁, .faulted f₂ => f₂ = f₁
                      | _, _ => False := by
                  intro cs
                  induction cs with
                  | nil => intros; exact ⟨rfl, Or.inl rfl⟩
                  | cons c rest ih_cs =>
                    intro m₁ m₂ hm_eq hd_cs
                    have hd_tl : ∀ f ∈ rest, isPurePlace f.destination = true :=
                      fun f hf => hd_cs f (List.Mem.tail c hf)
                    dsimp only [unwindFromCallStack]
                    cases c.returnUnwind with
                    | unreachable => rfl
                    | terminate => exact ⟨rfl, Or.inr rfl⟩
                    | cleanup _ =>
                      exact ⟨rfl, ⟨hm_eq.1, hm_eq.2.1, rfl, rfl, rfl⟩, hd_tl⟩
                    | continue_ =>
                      exact ih_cs _ _ ⟨hm_eq.1, hm_eq.2.1, rfl, rfl, rfl⟩ hd_tl
                by_cases h_pt : isPureTerminator tkind = true
                · cases tkind with
                  | goto target =>
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [h_fr]
                    exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                  | unreachable => exact False.elim h_wp
                  | unwindTerminate => exact False.elim h_wp
                  | inlineAsm => cases h_pt
                  | call _ _ _ _ _ => cases h_pt
                  | tailCall _ _ => cases h_pt
                  | drop p target unwind =>
                    rcases p with ⟨pLoc, pProj⟩
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [h_fr]
                    cases h_g : get? s₁.frame.locals pLoc with
                    | none => rw [h_g] at h_wp; exact False.elim h_wp
                    | some sl =>
                      rw [h_g] at h_wp h_step_inv
                      cases sl with
                      | dead => exact False.elim h_wp
                      | uninit =>
                        dsimp only at h_wp h_step_inv ⊢
                        cases pProj with
                        | nil =>
                          dsimp only at h_wp h_step_inv ⊢
                          cases h_s : set? s₁.frame.locals pLoc .uninit with
                          | none => rw [h_s] at h_wp; exact False.elim h_wp
                          | some _ =>
                            rw [h_s] at h_wp h_step_inv
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                        | cons _ _ => exact False.elim h_wp
                      | init rv =>
                        dsimp only at h_wp h_step_inv ⊢
                        cases pProj with
                        | nil =>
                          dsimp only at h_wp h_step_inv ⊢
                          cases h_s : set? s₁.frame.locals pLoc .uninit with
                          | none => rw [h_s] at h_wp; exact False.elim h_wp
                          | some _ =>
                            rw [h_s] at h_wp h_step_inv
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                        | cons hd tl =>
                          dsimp only at h_wp h_step_inv ⊢
                          cases h_rd : readProjectedValue s₁.frame.locals rv (hd :: tl) with
                          | ub => rw [h_rd] at h_wp; exact False.elim h_wp
                          | unsupported => rw [h_rd] at h_wp; exact False.elim h_wp
                          | ok _ =>
                            rw [h_rd] at h_wp h_step_inv
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                  | unwindResume =>
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [mf_cs]
                    have hu := h_unw_eq s₁.memory.callStack s₁.memory s₂.memory h_meq h_dst_stk
                    cases h_u1 : unwindFromCallStack s₁.memory.callStack s₁.memory <;>
                      cases h_u2 : unwindFromCallStack s₁.memory.callStack s₂.memory <;>
                      rw [h_u1, h_u2] at hu <;>
                      try exact False.elim hu
                    · rw [h_u1] at h_wp h_step_inv
                      rcases hu with ⟨hfr', hmeq', hdst'⟩
                      exact ih_run ⟨h_step_inv, hdst'⟩ ⟨hfr', hmeq'⟩ h_wp
                    · rw [h_u1] at h_wp
                      rcases hu with ⟨_, rfl | rfl⟩ <;> exact False.elim h_wp
                    · rw [h_u1] at h_wp
                      exact False.elim h_wp
                  | return_ =>
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [h_fr, mf_cs]
                    cases h_g : get? s₁.frame.locals 0 with
                    | none => rw [h_g] at h_wp; exact False.elim h_wp
                    | some sl =>
                      rw [h_g] at h_wp h_step_inv
                      cases sl with
                      | uninit => exact False.elim h_wp
                      | dead => exact False.elim h_wp
                      | init retVal =>
                        dsimp only at h_wp h_step_inv ⊢
                        cases h_cs : s₁.memory.callStack with
                        | nil =>
                          rw [h_cs] at h_wp
                          dsimp only [MirStepNode.retNormal, evalNodeNoCallWP, mirNormalPost] at h_wp ⊢
                          rcases h_wp with ⟨h_act₁, hp₁⟩
                          refine ⟨?_, hp₁⟩
                          dsimp only [ModularCalleeOutMemory]
                          rw [mf_cal, mf_tr, mf_cs, mf_ap, h_cs]
                          rcases h_act₁ with h_eq1 | ⟨_, h_eq1⟩ <;>
                            (have hc := congrArg Memory.callees h_eq1;
                             have ht := congrArg Memory.traitImpls h_eq1;
                             have hap := congrArg Memory.activeProtectors h_eq1;
                             rw [hc, ht, hap];
                             exact ⟨rfl, rfl, rfl, rfl⟩)
                        | cons caller rest =>
                          rw [h_cs] at h_wp h_step_inv h_dst_stk
                          dsimp only at h_wp h_step_inv ⊢
                          cases h_div : caller.isDiverging with
                          | true =>
                            rw [h_div] at h_wp
                            exact False.elim h_wp
                          | false =>
                            rw [h_div] at h_wp h_step_inv
                            dsimp only at h_wp h_step_inv ⊢
                            have h_cdst : isPurePlace caller.destination = true :=
                              h_dst_stk caller (List.Mem.head rest)
                            rw [writePlaceValue_pure_eq caller.frame.locals
                              s₂.memory.borrows caller.destination retVal h_cdst]
                            rw [writePlaceValue_pure_eq caller.frame.locals
                              s₁.memory.borrows caller.destination retVal h_cdst] at h_wp h_step_inv
                            cases h_w : writePlaceValue caller.frame.locals []
                                caller.destination retVal with
                            | ub => rw [h_w] at h_wp; exact False.elim h_wp
                            | unsupported => rw [h_w] at h_wp; exact False.elim h_wp
                            | ok updL =>
                              rw [h_w] at h_wp h_step_inv
                              exact ih_run ⟨h_step_inv, fun f hf =>
                                h_dst_stk f (List.Mem.tail caller hf)⟩
                                ⟨rfl, mf_cal, mf_tr, rfl, rfl, rfl⟩ h_wp
                  | switchInt discr targets =>
                    dsimp only [isPureTerminator] at h_pt
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [h_fr]
                    rw [evalOperand_pure_eq s₁.frame.locals discr s₂.memory.borrows
                      s₂.memory.globals (s₁.memory.activeCallee.getD body).layouts
                      s₂.memory.callerLocals h_pt]
                    rw [evalOperand_pure_eq s₁.frame.locals discr s₁.memory.borrows
                      s₁.memory.globals (s₁.memory.activeCallee.getD body).layouts
                      s₁.memory.callerLocals h_pt] at h_wp h_step_inv
                    cases h_ev : evalOperand s₁.frame.locals discr [] []
                        (s₁.memory.activeCallee.getD body).layouts [] with
                    | ub => rw [h_ev] at h_wp; exact False.elim h_wp
                    | unsupported => rw [h_ev] at h_wp; exact False.elim h_wp
                    | ok val l' =>
                      rw [h_ev] at h_wp h_step_inv
                      cases val with
                      | scalar sc =>
                        exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                      | _ => exact False.elim h_wp
                  | assert cond expected target unwind =>
                    dsimp only [isPureTerminator] at h_pt
                    dsimp only [evalTerminator] at h_wp h_step_inv ⊢
                    rw [h_fr]
                    rw [evalOperand_pure_eq s₁.frame.locals cond s₂.memory.borrows
                      s₂.memory.globals (s₁.memory.activeCallee.getD body).layouts
                      s₂.memory.callerLocals h_pt]
                    rw [evalOperand_pure_eq s₁.frame.locals cond s₁.memory.borrows
                      s₁.memory.globals (s₁.memory.activeCallee.getD body).layouts
                      s₁.memory.callerLocals h_pt] at h_wp h_step_inv
                    cases h_ev : evalOperand s₁.frame.locals cond [] []
                        (s₁.memory.activeCallee.getD body).layouts [] with
                    | ub => rw [h_ev] at h_wp; exact False.elim h_wp
                    | unsupported => rw [h_ev] at h_wp; exact False.elim h_wp
                    | ok val l' =>
                      rw [h_ev] at h_wp h_step_inv
                      cases val with
                      | scalar sc =>
                        have h_unw_branch :
                            (evalNodeNoCallWP
                              (fun st' =>
                                wpMirExecNoCallSym fuel' body st'
                                  (mirNormalPost fun retVal mem' =>
                                    ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
                                    P retVal))
                              (mirNormalPost fun retVal mem' =>
                                ActiveRootMemory body (pureCalleeMemory callees traitImpls) mem' ∧
                                P retVal)
                              (match applyUnwindAction s₁ l' s₁.memory unwind with
                               | .running ns => MirStepNode.step ns
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk)) →
                            pureNodeStepInv callees traitImpls body
                              (match applyUnwindAction s₁ l' s₁.memory unwind with
                               | .running ns => MirStepNode.step ns
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) →
                            evalNodeNoCallWP
                              (fun st' =>
                                wpMirExecNoCallSym fuel' body st'
                                  (mirNormalPost fun retVal mem' =>
                                    ModularCalleeOutMemory callees traitImpls mem' ∧ P retVal))
                              (mirNormalPost fun retVal mem' =>
                                ModularCalleeOutMemory callees traitImpls mem' ∧ P retVal)
                              (match applyUnwindAction s₂ l' s₂.memory unwind with
                               | .running ns => MirStepNode.step ns
                               | .halted out => MirStepNode.retOutcome out
                               | .faulted fk => MirStepNode.fail fk) := by
                          intro h_wp_u h_inv_u
                          dsimp only [applyUnwindAction] at h_wp_u h_inv_u ⊢
                          cases unwind with
                          | unreachable => exact False.elim h_wp_u
                          | terminate => exact False.elim h_wp_u
                          | cleanup _ =>
                            exact ih_run ⟨h_inv_u, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp_u
                          | continue_ =>
                            rw [mf_cs]
                            have hu := h_unw_eq s₁.memory.callStack s₁.memory s₂.memory h_meq h_dst_stk
                            cases h_u1 : unwindFromCallStack s₁.memory.callStack s₁.memory <;>
                              cases h_u2 : unwindFromCallStack s₁.memory.callStack s₂.memory <;>
                              rw [h_u1, h_u2] at hu <;>
                              try exact False.elim hu
                            · rw [h_u1] at h_wp_u h_inv_u
                              rcases hu with ⟨hfr', hmeq', hdst'⟩
                              exact ih_run ⟨h_inv_u, hdst'⟩ ⟨hfr', hmeq'⟩ h_wp_u
                            · rw [h_u1] at h_wp_u
                              rcases hu with ⟨_, rfl | rfl⟩ <;> exact False.elim h_wp_u
                            · rw [h_u1] at h_wp_u
                              exact False.elim h_wp_u
                        cases expected <;> dsimp only [BEq.beq] at h_wp h_step_inv ⊢
                        · revert h_wp h_step_inv
                          cases Nat.beq sc.bits 0 with
                          | true =>
                            intro h_step_inv h_wp
                            dsimp only at h_wp h_step_inv ⊢
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                          | false =>
                            intro h_step_inv h_wp
                            dsimp only at h_wp h_step_inv ⊢
                            exact h_unw_branch h_wp h_step_inv
                        · revert h_wp h_step_inv
                          cases Nat.beq sc.bits 1 with
                          | true =>
                            intro h_step_inv h_wp
                            dsimp only at h_wp h_step_inv ⊢
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                          | false =>
                            intro h_step_inv h_wp
                            dsimp only at h_wp h_step_inv ⊢
                            exact h_unw_branch h_wp h_step_inv
                      | _ => exact False.elim h_wp
                · unfold checkPureTerminatorWith at h_term
                  simp only [h_pt, Bool.false_eq_true, ↓reduceIte] at h_term
                  cases tkind with
                  | call func argOps destination targetOpt unwind =>
                    simp only [Bool.and_eq_true] at h_term
                    rcases h_term with ⟨⟨h_dst, h_args⟩, h_ext⟩
                    cases h_def : extractPureCalleeTarget?
                        (s₁.memory.activeCallee.getD body).localDecls
                        (s₁.memory.activeCallee.getD body).layouts func with
                    | none => rw [h_def] at h_ext; exact False.elim (Bool.false_ne_true h_ext)
                    | some dt =>
                      rcases dt with ⟨defPath, typeArgs⟩
                      rw [h_def] at h_ext
                      dsimp only at h_ext
                      simp only [evalTerminator_call_eq_unified] at h_wp h_step_inv ⊢
                      dsimp only [evalCallTerminatorUnified,
                        bodyLocalDeclsOf] at h_wp h_step_inv ⊢
                      have h_res₂ :=
                        resolveCallTarget_eq_of_extractPureCalleeTarget
                          s₂ func (length argOps)
                          (s₁.memory.activeCallee.getD body).localDecls
                          (s₁.memory.activeCallee.getD body).layouts h_def
                      have h_res₁ :=
                        resolveCallTarget_eq_of_extractPureCalleeTarget
                          s₁ func (length argOps)
                          (s₁.memory.activeCallee.getD body).localDecls
                          (s₁.memory.activeCallee.getD body).layouts h_def
                      rw [h_fr] at h_res₂
                      rw [h_res₂]
                      rw [h_res₁] at h_wp h_step_inv
                      cases h_rp : resolvePureCalleeTarget s₁.frame.locals func
                          defPath typeArgs
                          (s₁.memory.activeCallee.getD body).layouts with
                      | ub =>
                        rw [h_rp] at h_wp
                        exact False.elim h_wp
                      | unsupported =>
                        rw [h_rp] at h_wp
                        exact False.elim h_wp
                      | ok rTarget localsAfterFunc =>
                        rw [h_rp] at h_wp h_step_inv
                        have h_rt := resolvePureCalleeTarget_ok_target h_rp
                        subst h_rt
                        dsimp only at h_wp h_step_inv ⊢
                        rw [evalOperands_pure_eq localsAfterFunc argOps s₂.memory.borrows
                          s₂.memory.globals (s₁.memory.activeCallee.getD body).layouts
                          s₂.memory.callerLocals h_args]
                        rw [evalOperands_pure_eq localsAfterFunc argOps s₁.memory.borrows
                          s₁.memory.globals (s₁.memory.activeCallee.getD body).layouts
                          s₁.memory.callerLocals h_args] at h_wp h_step_inv
                        cases h_ev : evalOperands localsAfterFunc argOps [] []
                            (s₁.memory.activeCallee.getD body).layouts [] with
                        | ub =>
                          rw [h_ev] at h_wp
                          cases targetOpt <;> exact False.elim h_wp
                        | unsupported =>
                          rw [h_ev] at h_wp
                          cases targetOpt <;> exact False.elim h_wp
                        | ok argVals locals' =>
                          rw [h_ev] at h_wp h_step_inv
                          cases targetOpt with
                          | none =>
                            dsimp only at h_wp h_step_inv ⊢
                            rw [h_cal, h_tr] at h_wp h_step_inv
                            rw [mf_cal, mf_tr, h_cal, h_tr]
                            cases h_lk : lookupCallee callees
                                (s₁.memory.activeCallee.getD body).layouts defPath
                                typeArgs traitImpls with
                            | some calleeBody =>
                              rw [h_lk] at h_wp h_step_inv
                              dsimp only [checkCalleeTargetCompatible,
                                pushDivergingCalleeFrame] at h_wp h_step_inv ⊢
                              refine ih_run ⟨h_step_inv, ?_⟩ ⟨rfl, ?_⟩ h_wp
                              · intro f hf
                                cases hf with
                                | head => exact h_dst
                                | tail _ hm => exact h_dst_stk f hm
                              · exact ⟨mf_cal, mf_tr, by dsimp only; rw [h_fr, mf_ap, mf_cs], rfl, mf_ap⟩
                            | none =>
                              rw [h_lk] at h_ext h_wp h_step_inv
                              dsimp only at h_ext h_wp h_step_inv ⊢
                              cases h_unr : isUnreachableCallTarget defPath with
                              | true => rw [h_unr] at h_wp; exact False.elim h_wp
                              | false =>
                                rw [h_unr] at h_ext h_wp h_step_inv
                                dsimp only at h_wp h_step_inv ⊢
                                cases h_ab : isAbortingPanicDefPath defPath with
                                | true => rw [h_ab] at h_wp; exact False.elim h_wp
                                | false =>
                                  rw [h_ab] at h_ext h_wp h_step_inv
                                  simp only [Bool.false_or] at h_ext
                                  dsimp only at h_wp h_step_inv ⊢
                                  rw [h_ext] at h_wp h_step_inv ⊢
                                  dsimp only [applyUnwindAction] at h_wp h_step_inv ⊢
                                  cases unwind with
                                  | unreachable => exact False.elim h_wp
                                  | terminate => exact False.elim h_wp
                                  | cleanup _ =>
                                    exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                                  | continue_ =>
                                    rw [mf_cs]
                                    have hu := h_unw_eq s₁.memory.callStack s₁.memory s₂.memory h_meq h_dst_stk
                                    cases h_u1 : unwindFromCallStack s₁.memory.callStack s₁.memory <;>
                                      cases h_u2 : unwindFromCallStack s₁.memory.callStack s₂.memory <;>
                                      rw [h_u1, h_u2] at hu <;>
                                      try exact False.elim hu
                                    · rw [h_u1] at h_wp h_step_inv
                                      rcases hu with ⟨hfr', hmeq', hdst'⟩
                                      exact ih_run ⟨h_step_inv, hdst'⟩ ⟨hfr', hmeq'⟩ h_wp
                                    · rw [h_u1] at h_wp
                                      rcases hu with ⟨_, rfl | rfl⟩ <;> exact False.elim h_wp
                                    · rw [h_u1] at h_wp
                                      exact False.elim h_wp
                          | some targetBb =>
                            dsimp only at h_wp h_step_inv ⊢
                            rw [h_cal, h_tr] at h_wp h_step_inv
                            rw [mf_cal, mf_tr, h_cal, h_tr]
                            cases h_lk : lookupCallee callees
                                (s₁.memory.activeCallee.getD body).layouts defPath
                                typeArgs traitImpls with
                            | some calleeBody =>
                              rw [h_lk] at h_wp h_step_inv
                              dsimp only [checkCalleeTargetCompatible,
                                pushCalleeFrame] at h_wp h_step_inv ⊢
                              refine ih_run ⟨h_step_inv, ?_⟩ ⟨rfl, ?_⟩ h_wp
                              · intro f hf
                                cases hf with
                                | head => exact h_dst
                                | tail _ hm => exact h_dst_stk f hm
                              · exact ⟨mf_cal, mf_tr, by dsimp only; rw [h_fr, mf_ap, mf_cs], rfl, mf_ap⟩
                            | none =>
                              rw [h_lk] at h_ext h_wp h_step_inv
                              dsimp only at h_ext
                              dsimp only [isDirectExactDivTarget] at h_wp h_step_inv ⊢
                              rw [h_ext] at h_wp h_step_inv ⊢
                              dsimp only at h_wp h_step_inv ⊢
                              cases argVals with
                              | nil => exact False.elim h_wp
                              | cons v1 vs1 =>
                                cases v1 with
                                | scalar lhsSc =>
                                  cases vs1 with
                                  | nil => exact False.elim h_wp
                                  | cons v2 vs2 =>
                                    cases v2 with
                                    | scalar rhsSc =>
                                      cases vs2 with
                                      | cons _ _ => exact False.elim h_wp
                                      | nil =>
                                        dsimp only at h_wp h_step_inv ⊢
                                        cases h_sgn : resolveIntrinsicIsSigned
                                            { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
                                            (s₁.memory.activeCallee.getD body).localDecls
                                            (s₁.memory.activeCallee.getD body).layouts
                                            argOps with
                                        | none => rw [h_sgn] at h_wp; exact False.elim h_wp
                                        | some isSigned =>
                                          rw [h_sgn] at h_wp h_step_inv
                                          dsimp only at h_wp h_step_inv ⊢
                                          cases h_d : evalExactDiv lhsSc rhsSc isSigned with
                                          | none => rw [h_d] at h_wp; exact False.elim h_wp
                                          | some retSc =>
                                            rw [h_d] at h_wp h_step_inv
                                            dsimp only at h_wp h_step_inv ⊢
                                            rw [writePlaceValue_pure_eq locals'
                                              s₂.memory.borrows destination
                                              (.scalar retSc) h_dst]
                                            rw [writePlaceValue_pure_eq locals'
                                              s₁.memory.borrows destination
                                              (.scalar retSc) h_dst] at h_wp h_step_inv
                                            cases h_w : writePlaceValue locals' []
                                                destination (.scalar retSc) with
                                            | ub => rw [h_w] at h_wp; exact False.elim h_wp
                                            | unsupported => rw [h_w] at h_wp; exact False.elim h_wp
                                            | ok updL =>
                                              rw [h_w] at h_wp h_step_inv
                                              exact ih_run ⟨h_step_inv, h_dst_stk⟩ ⟨rfl, h_meq⟩ h_wp
                                    | _ => exact False.elim h_wp
                                | _ => exact False.elim h_wp
                  | tailCall func argOps =>
                    simp only [Bool.and_eq_true] at h_term
                    rcases h_term with ⟨h_args, h_ext⟩
                    cases h_def : extractPureCalleeTarget?
                        (s₁.memory.activeCallee.getD body).localDecls
                        (s₁.memory.activeCallee.getD body).layouts func with
                    | none => rw [h_def] at h_ext; exact False.elim (Bool.false_ne_true h_ext)
                    | some dt =>
                      rcases dt with ⟨defPath, typeArgs⟩
                      rw [h_def] at h_ext
                      dsimp only at h_ext
                      dsimp only [evalTerminator, evalTailCallTerminator,
                        bodyLocalDeclsOf] at h_wp h_step_inv ⊢
                      have h_res₂ :=
                        resolveCallTarget_eq_of_extractPureCalleeTarget
                          s₂ func (length argOps)
                          (s₁.memory.activeCallee.getD body).localDecls
                          (s₁.memory.activeCallee.getD body).layouts h_def
                      have h_res₁ :=
                        resolveCallTarget_eq_of_extractPureCalleeTarget
                          s₁ func (length argOps)
                          (s₁.memory.activeCallee.getD body).localDecls
                          (s₁.memory.activeCallee.getD body).layouts h_def
                      rw [h_fr] at h_res₂
                      rw [h_res₂]
                      rw [h_res₁] at h_wp h_step_inv
                      cases h_rp : resolvePureCalleeTarget s₁.frame.locals func
                          defPath typeArgs
                          (s₁.memory.activeCallee.getD body).layouts with
                      | ub => rw [h_rp] at h_wp; exact False.elim h_wp
                      | unsupported => rw [h_rp] at h_wp; exact False.elim h_wp
                      | ok rTarget localsAfterFunc =>
                        rw [h_rp] at h_wp h_step_inv
                        have h_rt := resolvePureCalleeTarget_ok_target h_rp
                        subst h_rt
                        dsimp only at h_wp h_step_inv ⊢
                        rw [evalOperands_pure_eq localsAfterFunc argOps s₂.memory.borrows
                          s₂.memory.globals (s₁.memory.activeCallee.getD body).layouts
                          s₂.memory.callerLocals h_args]
                        rw [evalOperands_pure_eq localsAfterFunc argOps s₁.memory.borrows
                          s₁.memory.globals (s₁.memory.activeCallee.getD body).layouts
                          s₁.memory.callerLocals h_args] at h_wp h_step_inv
                        cases h_ev : evalOperands localsAfterFunc argOps [] []
                            (s₁.memory.activeCallee.getD body).layouts [] with
                        | ub => rw [h_ev] at h_wp; exact False.elim h_wp
                        | unsupported => rw [h_ev] at h_wp; exact False.elim h_wp
                        | ok argVals _ =>
                          rw [h_ev] at h_wp h_step_inv
                          dsimp only at h_wp h_step_inv ⊢
                          rw [h_cal, h_tr] at h_wp h_step_inv
                          rw [mf_cal, mf_tr, h_cal, h_tr]
                          cases h_lk : lookupCallee callees
                              (s₁.memory.activeCallee.getD body).layouts defPath
                              typeArgs traitImpls with
                          | none =>
                            rw [h_lk] at h_ext
                            exact False.elim (Bool.false_ne_true h_ext)
                          | some calleeBody =>
                            rw [h_lk] at h_wp h_step_inv
                            dsimp only [checkCalleeTargetCompatible,
                              enterTailCalleeFrame] at h_wp h_step_inv ⊢
                            exact ih_run ⟨h_step_inv, h_dst_stk⟩
                              ⟨rfl, mf_cal, mf_tr, mf_cs, rfl, mf_ap⟩ h_wp
                  | _ => exact False.elim (Bool.false_ne_true h_term)
              · simp only [h_len] at h_wp
                exact False.elim h_wp

/--
Compositional 1-step inlined-callee summary rule inside modular callers
(`PureMirModularConverges.call_summary`, `FF-2.2` Section 2 & 4):
resolves direct or polymorphic `(defPath, typeArgs)` callees in `callees`
using an established `PureMirConvergesWithCallees` summary (with
`checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true`)
and advances the modular caller directly to `{ bb := targetBb, stmtIdx := 0, env
:= updatedEnv }`
in **1 compositional step**, even when `m.borrows` is non-empty after a prior
`#[external_spec]` call.
-/
theorem PureMirModularConverges.call_summary
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls =
        some calleeBody)
    (h_callee_pure :
      checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  let _ := h_depth
  intro m hm
  let s0 := ps.toMachineState m
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step
          (pushCalleeFrame s0 body envAfterArgs destination targetBb
            calleeBody argVals unwind) := by
    unfold stepMirFn
    dsimp only [s0, PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf,
        resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      rfl
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_callee_m :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ModularCalleeOutMemory callees traitImpls memOut ∧
            calleePost retVal)) :=
    ⟨fuel_c, sameExceptBorrows_step_noCall
      (st₁ := .running ((initPureState calleeBody argVals).toMachineState
        (pureCalleeMemory callees traitImpls)))
      ⟨PureCalleeMachineInv.init (initPureState calleeBody argVals)
        ⟨maxCallDepth, h_callee_pure⟩, fun _ hf => nomatch hf⟩
      ⟨rfl, hm.1, hm.2.1, rfl, rfl, hm.2.2.2.2⟩
      h_wp_c⟩
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) (.running s0)) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  dsimp only [MirStepNode.step, Trusted.ITree.ITreeF.map]
  refine dwp_modular_bind_steps
    (mid := fun s' =>
      ∃ (updatedEnv : List SlotState) (m' : Memory),
        s' = PureState.toMachineState { bb := targetBb, stmtIdx := 0, env := updatedEnv } m' ∧
        ModularRootMemory body callees traitImpls m' ∧
        PureMirModularConverges contract body callees
          { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    ?_ ?_
  · refine wpMirExecNoCallSym_pushCalleeFrame
      (outerBody := body) (callerBody := body) (calleeBody := calleeBody)
      (s := s0) h_callee_m hm.2.2.2.2 ?_
    intro retVal memOut ⟨h_mod_out, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr_pure, h_next_mod⟩
    refine ⟨updEnv, ?_, ⟨updEnv,
      { memOut with
        callStack := s0.memory.callStack
        activeCallee := some body
        activeProtectors := [] },
      ?_, ?_, h_next_mod⟩⟩
    · rw [writePlaceValue_pure_eq envAfterArgs memOut.borrows destination retVal h_dst_pure]
      exact h_wr_pure
    · rfl
    · exact ⟨h_mod_out.1, h_mod_out.2.1, hm.2.2.1, Or.inr rfl, rfl⟩
  · rintro s' ⟨updEnv, m', rfl, hm', h_next_mod⟩
    exact h_next_mod m' hm'

/--
Compositional 1-step inlined-callee `tailCall` summary rule inside modular
callers (`PureMirModularConverges.tailCall_summary`):
resolves direct or polymorphic `(defPath, typeArgs)` callees in `callees`
using an established `PureMirConvergesWithCallees` summary and converges in
**1 compositional step**, even when `m.borrows` is non-empty after a prior
`#[external_spec]` call.
-/
theorem PureMirModularConverges.tailCall_summary
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls =
        some calleeBody)
    (h_callee_pure :
      checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_imp : ∀ retVal : Value, calleePost retVal → post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  let _ := h_depth
  intro m hm
  let s0 := ps.toMachineState m
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step (enterTailCalleeFrame m calleeBody argVals) := by
    unfold stepMirFn
    dsimp only [s0, PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf,
        resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      rfl
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_callee_m :
      wpMirExecNoCallSym fuel_c calleeBody
        (.running (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none }))
        (mirNormalPost
          (fun retVal memOut =>
            ModularCalleeOutMemory callees traitImpls memOut ∧
            calleePost retVal)) :=
    sameExceptBorrows_step_noCall
      (st₁ := .running ((initPureState calleeBody argVals).toMachineState
        (pureCalleeMemory callees traitImpls)))
      ⟨PureCalleeMachineInv.init (initPureState calleeBody argVals)
        ⟨maxCallDepth, h_callee_pure⟩, fun _ hf => nomatch hf⟩
      ⟨rfl, hm.1, hm.2.1, rfl, rfl, hm.2.2.2.2⟩
      h_wp_c
  have h_pushed :=
    wpMirExecNoCallSym_pushBaseStack_nil_outer (outerBody := body) h_callee_m
  have h_state_eq :
      MirExecState.pushBaseStack calleeBody []
        (.running (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none })) =
      .running (enterTailCalleeFrame m calleeBody argVals) := by
    have h_cs := hm.2.2.1
    cases m
    dsimp only at h_cs ⊢
    subst h_cs
    rfl
  rw [h_state_eq] at h_pushed
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) (.running s0)) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  dsimp only [MirStepNode.step, Trusted.ITree.ITreeF.map]
  refine dwp_modular_of_noCallWp ⟨fuel_c, wpMirExecNoCallSym_mono_post ?_ h_pushed⟩
  intro out h_out
  cases out with
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out
  | normal rv =>
    rcases rv with ⟨retVal, _⟩
    rcases h_out with ⟨_, _, _, h_cp⟩
    exact h_imp retVal h_cp

/-- 1-step `switchInt` terminator rule for `PureMirModularConverges`. -/
theorem PureMirModularConverges.step_switchInt
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {discr : Operand} {targets : SwitchTargets}
    {sc : ScalarInt} {env' : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .switchInt discr targets)
    (h_pure : isPureOperand discr = true)
    (h_eval : evalPureOperand ps.env discr body.layouts = .ok (.scalar sc) env')
    (h_next :
      PureMirModularConverges contract body callees
        { bb := lookupSwitchTarget sc.bits targets.branches targets.otherwise
          stmtIdx := 0
          env := env' }
        post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator]
    rw [evalOperand_pure_eq ps.env discr m.borrows m.globals body.layouts
      m.callerLocals h_pure]
    unfold evalPureOperand at h_eval
    rw [h_eval]
    exact h_next m hm

/--
1-step `assert` terminator rule for `PureMirModularConverges`: handles both
passing assertions (`sc.bits == expectedBit`, stepping to `targetBb`) and
runtime-panicking/aborting/cleanup assertions (`sc.bits != expectedBit` under
`mirSafePost`).
-/
theorem PureMirModularConverges.step_assert
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {cond : Operand} {expected : Bool}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {sc : ScalarInt} {env' : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .assert cond expected targetBb unwind)
    (h_pure : isPureOperand cond = true)
    (h_eval : evalPureOperand ps.env cond body.layouts = .ok (.scalar sc) env')
    (h_pass :
      Nat.beq sc.bits (if expected then 1 else 0) = true →
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := env' } post traitImpls)
    (h_fail :
      Nat.beq sc.bits (if expected then 1 else 0) = false →
      unwind = .continue_ ∨
      unwind = .terminate ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := env' } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator]
    rw [evalOperand_pure_eq ps.env cond m.borrows m.globals body.layouts
      m.callerLocals h_pure]
    unfold evalPureOperand at h_eval
    rw [h_eval]
    cases expected <;> dsimp only at h_pass h_fail ⊢
    all_goals
      cases h_cond : Nat.beq sc.bits _ with
      | true =>
        exact h_pass h_cond m hm
      | false =>
        rcases h_fail h_cond with rfl | rfl | ⟨cleanupBb, rfl, h_clean⟩
        · dsimp only [applyUnwindAction]
          rw [hm.2.2.1]
          dsimp only [unwindFromCallStack, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction]
          exact h_clean m hm

/--
1-step `drop` terminator rule for `PureMirModularConverges` (valid even when
`m.borrows` is non-empty after a prior `#[external_spec]` call).
-/
theorem PureMirModularConverges.step_drop
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {place : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {s_emp : MachineState} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .drop place targetBb unwind)
    (h_eval :
      evalTerminator (ps.toMachineState emptyMemory) bb.terminator (some body) =
        MirStepNode.step s_emp)
    (h_next :
      PureMirModularConverges contract body callees
        (PureState.ofMachineState s_emp) post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_drop_m :
      evalTerminator (ps.toMachineState m) bb.terminator (some body) =
        MirStepNode.step ((PureState.ofMachineState s_emp).toMachineState m) := by
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    rcases place with ⟨loc, proj⟩
    dsimp only at h_term
    subst h_term
    unfold evalTerminator at h_eval ⊢
    dsimp only [PureState.toMachineState] at h_eval ⊢
    cases h_g : get? ps.env loc with
    | none => rw [h_g] at h_eval; nomatch h_eval
    | some sl =>
      rw [h_g] at h_eval
      cases sl with
      | dead => nomatch h_eval
      | uninit =>
        cases proj with
        | nil =>
          dsimp only at h_eval ⊢
          cases h_s : set? ps.env loc .uninit with
          | none => rw [h_s] at h_eval; nomatch h_eval
          | some _ =>
            rw [h_s] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
        | cons _ _ => nomatch h_eval
      | init rv =>
        cases proj with
        | nil =>
          dsimp only at h_eval ⊢
          cases h_s : set? ps.env loc .uninit with
          | none => rw [h_s] at h_eval; nomatch h_eval
          | some _ =>
            rw [h_s] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
        | cons hd tl =>
          dsimp only at h_eval ⊢
          cases h_rd : readProjectedValue ps.env rv (hd :: tl) with
          | ub => rw [h_rd] at h_eval; nomatch h_eval
          | unsupported => rw [h_rd] at h_eval; nomatch h_eval
          | ok _ =>
            rw [h_rd] at h_eval
            dsimp only at h_eval ⊢
            injection h_eval with h_se
            injection h_se with h_eq
            subst h_eq
            rfl
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState] at h_drop_m ⊢
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rw [h_drop_m]
    exact h_next m hm

/--
1-step inline `core::intrinsics::exact_div` call rule for
`PureMirModularConverges` (when `"core::intrinsics::exact_div"` is un-shadowed
in `callees`).
-/
theorem PureMirModularConverges.call_exact_div
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {func : Operand}
    {argOps : List Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {defPath : DefPath} {lhs rhs retScalar : ScalarInt}
    {isSigned : Bool}
    {envAfterArgs updatedEnv : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_exact_path : stringEq defPath "core::intrinsics::exact_div" = true := by decide)
    (h_args :
      evalPureOperands ps.env argOps body.layouts =
        .ok [.scalar lhs, .scalar rhs] envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_signed :
      resolveIntrinsicIsSigned
        { defPath := defPath
          typeArgs := extractCalleeTypeArgs func
          fnSig := .none
          isIndirect := false }
        body.localDecls body.layouts argOps = some isSigned := by rfl)
    (h_div : evalExactDiv lhs rhs isSigned = some retScalar)
    (h_wr :
      writePurePlaceValue envAfterArgs destination (.scalar retScalar) =
        .ok updatedEnv)
    (h_next :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.step
          (({ bb := targetBb, stmtIdx := 0, env := updatedEnv } : PureState).toMachineState m) := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_exact_path]
      dsimp only
      rw [h_signed]
      dsimp only
      rw [h_div]
      dsimp only
      rw [writePlaceValue_pure_eq envAfterArgs m.borrows destination
        (.scalar retScalar) h_dst_pure]
      unfold writePurePlaceValue at h_wr
      rw [h_wr]
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  exact h_next m hm

/--
Generalized 1-step inlined-callee summary rule inside modular callers
(`PureMirModularConverges.call_summary_resolved`): supports any call target
resolved via `resolveCallTarget` (including capture-free closures, local ZST
function items, and `checkCalleeTargetCompatible` validation) without requiring
`extractCalleeDefPath? func = some _`.
-/
theorem PureMirModularConverges.call_summary_resolved
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_pure :
      checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  let _ := h_depth
  intro m hm
  let s0 := ps.toMachineState m
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step
          (pushCalleeFrame s0 body envAfterArgs destination targetBb
            calleeBody argVals unwind) := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [s0, PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      rw [h_compat]
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_callee_m :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ModularCalleeOutMemory callees traitImpls memOut ∧
            calleePost retVal)) :=
    ⟨fuel_c, sameExceptBorrows_step_noCall
      (st₁ := .running ((initPureState calleeBody argVals).toMachineState
        (pureCalleeMemory callees traitImpls)))
      ⟨PureCalleeMachineInv.init (initPureState calleeBody argVals)
        ⟨maxCallDepth, h_callee_pure⟩, fun _ hf => nomatch hf⟩
      ⟨rfl, hm.1, hm.2.1, rfl, rfl, hm.2.2.2.2⟩
      h_wp_c⟩
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) (.running s0)) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  dsimp only [MirStepNode.step, Trusted.ITree.ITreeF.map]
  refine dwp_modular_bind_steps
    (mid := fun s' =>
      ∃ (updatedEnv : List SlotState) (m' : Memory),
        s' = PureState.toMachineState { bb := targetBb, stmtIdx := 0, env := updatedEnv } m' ∧
        ModularRootMemory body callees traitImpls m' ∧
        PureMirModularConverges contract body callees
          { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    ?_ ?_
  · refine wpMirExecNoCallSym_pushCalleeFrame
      (outerBody := body) (callerBody := body) (calleeBody := calleeBody)
      (s := s0) h_callee_m hm.2.2.2.2 ?_
    intro retVal memOut ⟨h_mod_out, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr_pure, h_next_mod⟩
    refine ⟨updEnv, ?_, ⟨updEnv,
      { memOut with
        callStack := s0.memory.callStack
        activeCallee := some body
        activeProtectors := [] },
      rfl, ⟨h_mod_out.1, h_mod_out.2.1, hm.2.2.1, Or.inr rfl, rfl⟩, h_next_mod⟩⟩
    rw [writePlaceValue_pure_eq envAfterArgs memOut.borrows destination retVal h_dst_pure]
    exact h_wr_pure
  · rintro s' ⟨updEnv, m', rfl, hm', h_next_mod⟩
    exact h_next_mod m' hm'

/--
1-step inlined-callee summary rule for `core::intrinsics::const_eval_select`
inside modular callers (`PureMirModularConverges.call_const_eval_select_summary`):
when `const_eval_select` is un-shadowed in `callees` (`lookupCallee = none`) and
its runtime target `rtTarget` resolves in `callees` (`lookupCallee = some calleeBody`),
`evalDirectRustIntrinsic?` steps via `pushCalleeFrame` and composes with
`calleeBody`'s `PureMirConvergesWithCallees` summary in 1 step.
-/
theorem PureMirModularConverges.call_const_eval_select_summary
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {tupleArgVal ctFnVal rtFnVal : Value}
    {unpackedArgs : List Value}
    {rtTarget : ResolvedCallTarget}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_select_path : classifyRustIntrinsic? defPath = some .constEvalSelect := by rfl)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_args :
      evalPureOperands ps.env argOps body.layouts =
        .ok [tupleArgVal, ctFnVal, rtFnVal] envAfterArgs)
    (h_lookup_select :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_unpack :
      unpackConstEvalSelectArgs? tupleArgVal
        (selectTupleTyOpt (extractCalleeTypeArgs func)) = .some unpackedArgs)
    (h_resolve_rt :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveConstEvalSelectTarget? (ps.toMachineState m)
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            fnSig := .none
            isIndirect := false }
          body.localDecls body.layouts
          (selectRtFnOpOpt argOps)
          rtFnVal (length unpackedArgs) = .some rtTarget)
    (h_lookup_rt :
      lookupCallee callees body.layouts rtTarget.defPath rtTarget.typeArgs traitImpls =
        some calleeBody)
    (h_compat_rt :
      Bool.and (Nat.beq calleeBody.argCount (length unpackedArgs))
        (Bool.and (Bool.not (callConvEq calleeBody.fnAbi.conv .rustIntrinsic))
          (checkCalleeTargetCompatible rtTarget calleeBody (length unpackedArgs))) = true := by rfl)
    (h_callee_pure :
      checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody unpackedArgs) calleePost traitImpls)
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  let _ := h_depth
  intro m hm
  let s0 := ps.toMachineState m
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step
          (pushCalleeFrame s0 body envAfterArgs destination targetBb
            calleeBody unpackedArgs unwind) := by
    have h_res_rt_m := h_resolve_rt m hm
    dsimp only [PureState.toMachineState] at h_res_rt_m
    unfold stepMirFn
    dsimp only [s0, PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf, resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup_select]
      dsimp only [isDirectExactDivTarget]
      rw [h_not_exact]
      dsimp only
      rw [evalDirectRustIntrinsic?_constEvalSelect_three _ _ _ _ _ _ _ _ _ _ _ _ _ h_select_path]
      unfold evalConstEvalSelectThree
      dsimp only
      rw [h_unpack]
      dsimp only
      rw [h_res_rt_m]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup_rt]
      dsimp only
      rw [h_compat_rt]
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_callee_m :
      MirNoCallWpConverges calleeBody
        (initMachineStateWithMemory calleeBody unpackedArgs
          { m with callStack := [], activeCallee := none })
        (mirNormalPost
          (fun retVal memOut =>
            ModularCalleeOutMemory callees traitImpls memOut ∧
            calleePost retVal)) :=
    ⟨fuel_c, sameExceptBorrows_step_noCall
      (st₁ := .running ((initPureState calleeBody unpackedArgs).toMachineState
        (pureCalleeMemory callees traitImpls)))
      ⟨PureCalleeMachineInv.init (initPureState calleeBody unpackedArgs)
        ⟨maxCallDepth, h_callee_pure⟩, fun _ hf => nomatch hf⟩
      ⟨rfl, hm.1, hm.2.1, rfl, rfl, hm.2.2.2.2⟩
      h_wp_c⟩
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) (.running s0)) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  dsimp only [MirStepNode.step, Trusted.ITree.ITreeF.map]
  refine dwp_modular_bind_steps
    (mid := fun s' =>
      ∃ (updatedEnv : List SlotState) (m' : Memory),
        s' = PureState.toMachineState { bb := targetBb, stmtIdx := 0, env := updatedEnv } m' ∧
        ModularRootMemory body callees traitImpls m' ∧
        PureMirModularConverges contract body callees
          { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    ?_ ?_
  · refine wpMirExecNoCallSym_pushCalleeFrame
      (outerBody := body) (callerBody := body) (calleeBody := calleeBody)
      (s := s0) h_callee_m hm.2.2.2.2 ?_
    intro retVal memOut ⟨h_mod_out, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr_pure, h_next_mod⟩
    refine ⟨updEnv, ?_, ⟨updEnv,
      { memOut with
        callStack := s0.memory.callStack
        activeCallee := some body
        activeProtectors := [] },
      rfl, ⟨h_mod_out.1, h_mod_out.2.1, hm.2.2.1, Or.inr rfl, rfl⟩, h_next_mod⟩⟩
    rw [writePlaceValue_pure_eq envAfterArgs memOut.borrows destination retVal h_dst_pure]
    exact h_wr_pure
  · rintro s' ⟨updEnv, m', rfl, hm', h_next_mod⟩
    exact h_next_mod m' hm'

/--
Discharge a `ModularVerificationResult` with non-empty linked `callees` against
`contract.holdsOn` from `PureMirModularConverges` (`FF-2.2` Section 2 & 4).
-/
theorem verifyModularMirWithCallees_of_pureModularExec
    (contract : MirCallContract)
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_nonempty : callees ≠ [] := by decide)
    (h_frame :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨ mem.activeCallee = some body) ∧
        mem.activeProtectors = [])
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        PureMirModularConverges contract body callees
          (initPureState body args)
          (fun retVal => ∀ mem', post args mem retVal mem')
          body.traitImpls) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post
        callees := callees } := by
  refine Anneal.Rustc.V2026_06_01.Lower.verifyModularContractWithCalleesByDWLP
    contract body callees pre post (fun args mem h_pre => ?_)
  rcases h_frame args mem h_pre with ⟨h_cs, h_ac, h_ap⟩
  let initSt :=
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem callees
  have h_st_eq :
      initSt = (initPureState body args).toMachineState initSt.memory := by
    dsimp only [initSt,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory, PureState.toMachineState, initPureState]
  have h_mod : ModularRootMemory body callees body.traitImpls initSt.memory := by
    dsimp only [initSt,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : callees with
    | nil => exact False.elim (h_nonempty hc)
    | cons _ _ => exact ⟨rfl, rfl, h_cs, h_ac, h_ap⟩
  have hdwp := h_wp args mem h_pre initSt.memory h_mod
  change Anneal.ITreeWP.DWLP _ (mirTree body initSt) _ _
  rw [h_st_eq]
  refine Anneal.ITreeWP.DWLP.mono ?_ hdwp.toDWLP
  intro out _ h_out retVal mem' h_eq
  subst h_eq
  exact h_out mem'

/--
Discharge a `ModularVerificationResult` (with `callees = []`, e.g. pure
`#[external_spec]` or `CallConv.rustIntrinsic` callers) against
`contract.holdsOn` from `PureMirModularConverges`.
-/
theorem verifyModularMir_of_pureModularExec
    (contract : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_frame :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        mem.callees = [] ∧
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨ mem.activeCallee = some body) ∧
        mem.activeProtectors = [])
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        PureMirModularConverges contract body []
          (initPureState body args)
          (fun retVal => ∀ mem', post args mem retVal mem')
          mem.traitImpls) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } := by
  refine Anneal.Rustc.V2026_06_01.Lower.verifyModularContractByDWLP
    contract body pre post (fun args mem h_pre => ?_)
  rcases h_frame args mem h_pre with ⟨h_cal, h_cs, h_ac, h_ap⟩
  have h_mod : ModularRootMemory body [] mem.traitImpls mem :=
    ⟨h_cal, rfl, h_cs, h_ac, h_ap⟩
  have hdwp := h_wp args mem h_pre mem h_mod
  change Anneal.ITreeWP.DWLP _
    (mirTree body ((initPureState body args).toMachineState mem)) _ _
  refine Anneal.ITreeWP.DWLP.mono ?_ hdwp.toDWLP
  intro out _ h_out retVal mem' h_eq
  subst h_eq
  exact h_out mem'

/--
Generalized 1-step inlined-callee `tailCall` summary rule inside modular callers
(`PureMirModularConverges.tailCall_summary_resolved`): supports any call target
resolved via `resolveCallTarget` (including capture-free closures, local ZST
function items, and `checkCalleeTargetCompatible` validation) without requiring
`extractCalleeDefPath? func = some _`.
-/
theorem PureMirModularConverges.tailCall_summary_resolved
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleeBody : CapturedMir}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    {maxCallDepth : Nat}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_depth : 0 < maxCallDepth := by
      first | decide | exact Nat.zero_lt_succ 31)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = some calleeBody)
    (h_compat :
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true := by rfl)
    (h_callee_pure :
      checkPureMirWithCallees callees calleeBody maxCallDepth traitImpls = true)
    (h_callee_summary :
      PureMirConvergesWithCallees calleeBody callees
        (initPureState calleeBody argVals) calleePost traitImpls)
    (h_imp : ∀ retVal : Value, calleePost retVal → post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  let _ := h_depth
  intro m hm
  let s0 := ps.toMachineState m
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body s0 =
        MirStepNode.step (enterTailCalleeFrame m calleeBody argVals) := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [s0, PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      rw [h_compat]
  rcases h_callee_summary with ⟨fuel_c, h_wp_c⟩
  have h_callee_m :
      wpMirExecNoCallSym fuel_c calleeBody
        (.running (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none }))
        (mirNormalPost
          (fun retVal memOut =>
            ModularCalleeOutMemory callees traitImpls memOut ∧
            calleePost retVal)) :=
    sameExceptBorrows_step_noCall
      (st₁ := .running ((initPureState calleeBody argVals).toMachineState
        (pureCalleeMemory callees traitImpls)))
      ⟨PureCalleeMachineInv.init (initPureState calleeBody argVals)
        ⟨maxCallDepth, h_callee_pure⟩, fun _ hf => nomatch hf⟩
      ⟨rfl, hm.1, hm.2.1, rfl, rfl, hm.2.2.2.2⟩
      h_wp_c
  have h_pushed :=
    wpMirExecNoCallSym_pushBaseStack_nil_outer (outerBody := body) h_callee_m
  have h_state_eq :
      MirExecState.pushBaseStack calleeBody []
        (.running (initMachineStateWithMemory calleeBody argVals
          { m with callStack := [], activeCallee := none })) =
      .running (enterTailCalleeFrame m calleeBody argVals) := by
    have h_cs := hm.2.2.1
    cases m
    dsimp only at h_cs ⊢
    subst h_cs
    rfl
  rw [h_state_eq] at h_pushed
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) (.running s0)) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  dsimp only [MirStepNode.step, Trusted.ITree.ITreeF.map]
  refine dwp_modular_of_noCallWp ⟨fuel_c, wpMirExecNoCallSym_mono_post ?_ h_pushed⟩
  intro out h_out
  cases out with
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out
  | normal rv =>
    rcases rv with ⟨retVal, _⟩
    rcases h_out with ⟨_, _, _, h_cp⟩
    exact h_imp retVal h_cp

/--
Compositional 1-step external `tailCall` rule (`PureMirModularConverges.tailCall_modular`):
when block `bb` ends with `TerminatorKind.tailCall func argOps` targeting an
un-inlined callee `(defPath, typeArgs)` covered by `contract` (`lookupCallee =
none`), any returned value satisfying `contract.post` with `retMem.callStack =
[]` halts normally with `post retVal` (and unwinding with `panicMem.callStack =
[]` or aborting satisfies `mirSafePost`).
-/
theorem PureMirModularConverges.tailCall_modular
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        contract.pre
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        contract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        retMem.callStack = [] ∧ post retVal)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        contract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          resumeExternalTailCall := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf,
        resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  refine ⟨h_contract_pre m hm, fun ans h_cpost => ?_⟩
  cases ans with
  | aborted =>
    dsimp only [resumeExternalTailCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    dsimp only [resumeExternalTailCall]
    rw [h_panic_stack m panicMem hm h_cpost]
    dsimp only [unwindFromCallStack]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | returned retVal retMem =>
    rcases h_contract_ret m retMem retVal hm h_cpost with ⟨h_cs, h_post_ret⟩
    dsimp only [resumeExternalTailCall]
    rw [h_cs]
    dsimp only
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    exact h_post_ret

/--
Subsumption-aware 1-step external `tailCall` rule
(`PureMirModularConverges.tailCall_modular_sub`).
-/
theorem PureMirModularConverges.tailCall_modular_sub
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        retMem.callStack = [] ∧ post retVal)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls :=
  PureMirModularConverges.tailCall_modular
    h_phase h_bb h_end h_term h_args_pure h_def h_args h_lookup
    (fun m hm => (h_sub _ (h_contract_pre m hm)).1)
    (fun m retMem retVal hm hp =>
      h_contract_ret m retMem retVal hm
        ((h_sub _ (h_contract_pre m hm)).2 _ hp))
    (fun m panicMem hm hp =>
      h_panic_stack m panicMem hm
        ((h_sub _ (h_contract_pre m hm)).2 _ hp))

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` `tailCall` rule
(`PureMirModularConverges.tailCall_poly_external_spec_sub`).
-/
theorem PureMirModularConverges.tailCall_poly_external_spec_sub
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_targs : extractCalleeTypeArgs func = expectedTypeArgs)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_imp :
      ∀ retVal : Value,
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls :=
  PureMirModularConverges.tailCall_modular_sub h_sub
    h_phase h_bb h_end h_term h_args_pure h_def h_args
    (by rw [h_targs]; exact h_lookup)
    (fun _ _ => ⟨rfl, h_targs, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ retVal hm hp =>
      ⟨(ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1).2.2.1,
        h_imp retVal hp.2⟩)
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])

/--
Subsumption-aware 1-step monomorphic `#[external_spec]` `tailCall` rule
(`PureMirModularConverges.tailCall_external_spec_sub`).
-/
theorem PureMirModularConverges.tailCall_external_spec_sub
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (externalSpecCallContract targetDefPath sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some targetDefPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_imp :
      ∀ retVal : Value,
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls :=
  PureMirModularConverges.tailCall_modular_sub h_sub
    h_phase h_bb h_end h_term h_args_pure h_def h_args h_lookup
    (fun _ _ => ⟨rfl, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ retVal hm hp =>
      ⟨by rw [hp.1.2.1, hm.2.2.1], h_imp retVal hp.2⟩)
    (fun m _ hm hp => by
      dsimp only [externalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.2.1, hm.2.2.1])

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` `tailCall` rule
(`PureMirModularConverges.tailCall_intrinsic_sub`).
-/
theorem PureMirModularConverges.tailCall_intrinsic_sub
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {kind : PureRustIntrinsicKind}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind
        (extractCalleeTypeArgs func) argVals pointerBytes ubChecksEnabled =
        some retVal)
    (h_post : post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls :=
  PureMirModularConverges.tailCall_modular_sub h_sub
    h_phase h_bb h_end h_term h_args_pure h_def h_args h_lookup
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ rv hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      subst hrv_eq
      exact ⟨hm.2.2.1, h_post⟩)
    (fun _ _ _ hp => False.elim hp)

/--
1-step specialization of `PureMirModularConverges.tailCall_intrinsic_sub` to
`pureRustIntrinsicContract` directly.
-/
theorem PureMirModularConverges.tailCall_intrinsic
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {kind : PureRustIntrinsicKind}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath
        (extractCalleeTypeArgs func) traitImpls = none)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind
        (extractCalleeTypeArgs func) argVals pointerBytes ubChecksEnabled =
        some retVal)
    (h_post : post retVal) :
    PureMirModularConverges
      (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
      body callees ps post traitImpls :=
  PureMirModularConverges.tailCall_intrinsic_sub
    (MirCallContract.Subsumes.refl _)
    h_phase h_bb h_end h_term h_args_pure h_def h_args h_lookup h_kind h_eval
    h_post

/--
1-step diverging standard panic/abort call rule (`target = .none`) for
`PureMirModularConverges`: discharges un-shadowed `isAbortingPanicDefPath`
entrypoints directly and `isUnwindingPanicDefPath` entrypoints under
`.continue_`, `.terminate`, or `.cleanup cleanupBb`.
-/
theorem PureMirModularConverges.call_diverging_panic
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination .none unwind)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_unreach : isUnreachableCallTarget defPath = false := by decide)
    (h_panic :
      isAbortingPanicDefPath defPath = true ∨
      (isUnwindingPanicDefPath defPath = true ∧
        (unwind = .continue_ ∨
         unwind = .terminate ∨
         ∃ cleanupBb : BasicBlockIdx,
           unwind = .cleanup cleanupBb ∧
           PureMirModularConverges contract body callees
             { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
             post traitImpls))) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, bodyLocalDeclsOf,
      resolveCallTarget]
    rw [h_def]
    dsimp only
    rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
      m.callerLocals h_args_pure]
    unfold evalPureOperands at h_args
    rw [h_args]
    dsimp only
    rw [hm.1, hm.2.1, h_lookup]
    dsimp only
    rw [h_not_unreach]
    dsimp only
    cases h_ab : isAbortingPanicDefPath defPath with
    | true =>
      dsimp only [MirStepNode.retOutcome, Trusted.ITree.ITreeF.map]
      trivial
    | false =>
      dsimp only
      rcases h_panic with h_ab_true | ⟨h_unw_path, h_unw_act⟩
      · rw [h_ab] at h_ab_true; nomatch h_ab_true
      · rw [h_unw_path]
        dsimp only
        rcases h_unw_act with rfl | rfl | ⟨cleanupBb, rfl, h_clean⟩
        · dsimp only [applyUnwindAction]
          rw [hm.2.2.1]
          dsimp only [unwindFromCallStack, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction]
          exact h_clean m hm

/--
Subsumption-aware 1-step external diverging call rule (`target = .none`) for
`PureMirModularConverges` (for `-> !` callees whose `subContract.post` forbids
normal `.returned` answers).
-/
theorem PureMirModularConverges.call_diverging_modular_sub
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination .none unwind)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_def : extractCalleeDefPath? func = some defPath)
    (h_args : evalPureOperands ps.env argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath (extractCalleeTypeArgs func) traitImpls = none)
    (h_not_unreach : isUnreachableCallTarget defPath = false := by decide)
    (h_not_abort : isAbortingPanicDefPath defPath = false := by decide)
    (h_not_unwind : isUnwindingPanicDefPath defPath = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m })
    (h_no_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.returned retVal retMem))
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      (∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem)) ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        (∀ (m panicMem : Memory),
          ModularRootMemory body callees traitImpls m →
          subContract.post
            { defPath := defPath
              typeArgs := extractCalleeTypeArgs func
              args := argVals
              memory := m }
            (.panicked panicMem) →
          ModularRootMemory body callees traitImpls panicMem) ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := defPath
            typeArgs := extractCalleeTypeArgs func
            args := argVals
            memory := m }
          (resumeExternalDivergingCall (ps.toMachineState m) envAfterArgs unwind) := by
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf,
        resolveCallTarget]
      rw [h_def]
      dsimp only
      rw [evalOperands_pure_eq ps.env argOps m.borrows m.globals body.layouts
        m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      rw [h_not_unreach, h_not_abort, h_not_unwind]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  rcases h_sub _ (h_contract_pre m hm) with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalDivergingCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | returned retVal retMem =>
    exact False.elim (h_no_ret m retMem retVal hm hp)
  | panicked panicMem =>
    rcases h_contract_panic with rfl | rfl | h_no_panic | ⟨cleanupBb, rfl, h_mod_p, h_clean⟩
    · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
      rw [h_panic_stack m panicMem hm hp]
      dsimp only [unwindFromCallStack]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · exact False.elim (h_no_panic m panicMem hm hp)
    · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
      exact h_clean panicMem (h_mod_p m panicMem hm hp)

/--
Unified `ModularVerificationResult` gate (`verifyModularMir_of_pureModularExec_any`)
for `PureMirModularConverges` that seamlessly handles both non-empty
`c.callees ≠ []` (using `c.body.traitImpls`) and empty `c.callees = []` (when
`c.pre` pins `mem.callees = []`, allowing arbitrary `mem.traitImpls`).
-/
theorem verifyModularMir_of_pureModularExec_any
    (contract : MirCallContract)
    (c : ModularClaim)
    (h_env : c.envAssumed = contract.holdsOn := by rfl)
    (h_callees :
      c.callees ≠ [] ∨
      ∀ args mem, c.pre args mem → mem.callees = [])
    (h_frame :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨ mem.activeCallee = some c.body) ∧
        mem.activeProtectors = [])
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirModularConverges contract c.body c.callees
          (initPureState c.body args)
          (fun retVal => ∀ mem', c.post args mem retVal mem')
          (if c.callees.isEmpty then mem.traitImpls else c.body.traitImpls)) :
    ModularVerificationResult c := by
  rcases c with ⟨body, envAssumed, pre, post, callees⟩
  dsimp only at h_env h_callees h_frame h_wp
  subst h_env
  refine Anneal.Rustc.V2026_06_01.Lower.verifyModularContractWithCalleesByDWLP
    contract body callees pre post (fun args mem h_pre => ?_)
  rcases h_frame args mem h_pre with ⟨h_cs, h_ac, h_ap⟩
  let initSt :=
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem callees
  have h_st_eq :
      initSt = (initPureState body args).toMachineState initSt.memory := by
    dsimp only [initSt,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory, PureState.toMachineState, initPureState]
  have h_mod :
      ModularRootMemory body callees
        (if callees.isEmpty then mem.traitImpls else body.traitImpls)
        initSt.memory := by
    dsimp only [initSt,
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees,
      initMachineStateWithMemory]
    cases hc : callees with
    | cons _ _ => exact ⟨rfl, rfl, h_cs, h_ac, h_ap⟩
    | nil =>
      rcases h_callees with h_ne | h_emp
      · exact False.elim (h_ne hc)
      · exact ⟨h_emp args mem h_pre, rfl, h_cs, h_ac, h_ap⟩
  have hdwp := h_wp args mem h_pre initSt.memory h_mod
  change Anneal.ITreeWP.DWLP _ (mirTree body initSt) _ _
  rw [h_st_eq]
  refine Anneal.ITreeWP.DWLP.mono ?_ hdwp.toDWLP
  intro out _ h_out retVal mem' h_eq
  subst h_eq
  exact h_out mem'

/--
1-step `unwindResume` terminator rule for `PureMirModularConverges`: in any root
modular caller (`m.callStack = []`), completing a cleanup landing pad (`isCleanup
= true`) via `TerminatorKind.unwindResume` halts cleanly with `.halted .panic`,
satisfying `mirSafePost`.
-/
theorem PureMirModularConverges.step_unwindResume
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .unwindResume) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator]
    rw [hm.2.2.1]
    dsimp only [unwindFromCallStack, MirStepNode.retOutcome,
      Trusted.ITree.ITreeF.map]
    trivial

/--
1-step `unwindTerminate` terminator rule for `PureMirModularConverges`:
halting via `TerminatorKind.unwindTerminate` produces `.halted .abort`,
satisfying `mirSafePost`.
-/
theorem PureMirModularConverges.step_unwindTerminate
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .unwindTerminate) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, MirStepNode.retOutcome, Trusted.ITree.ITreeF.map]
    trivial

/--
Generalized subsumption-aware 1-step external modular call rule
(`PureMirModularConverges.call_modular_resolved`):
supports arbitrary call-target resolution via `resolveCallTarget` (including
local/projected zero-sized `RigidTy.fnDef` slots with `Operand.move` slot
invalidation and indirect `FnPtrEntry` targets) AND full `.cleanup cleanupBb`
unwind landing-pad recovery alongside `.continue_`, `.terminate`, and
non-unwinding contracts.
-/
theorem PureMirModularConverges.call_modular_resolved
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {calleePost : Value → Prop}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = none)
    (h_not_exact : isDirectExactDivTarget resolvedTarget = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        ModularRootMemory body callees traitImpls retMem ∧ calleePost retVal)
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      (∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem)) ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        (∀ (m panicMem : Memory),
          ModularRootMemory body callees traitImpls m →
          subContract.post
            { defPath := resolvedTarget.defPath
              typeArgs := resolvedTarget.typeArgs
              args := argVals
              memory := m }
            (.panicked panicMem) →
          ModularRootMemory body callees traitImpls panicMem) ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = [])
    (h_after :
      ∀ (retVal : Value),
        calleePost retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic :
      resolvedTarget.isIndirect = true ∨
      classifyRustIntrinsic? resolvedTarget.defPath = none := by
      first | exact Or.inr (by decide) | exact Or.inl (by decide)) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (resumeExternalCall (ps.toMachineState m) envAfterArgs
            destination targetBb unwind) := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      rw [h_not_exact]
      dsimp only
      cases h_ind : resolvedTarget.isIndirect with
      | true => rfl
      | false =>
        rcases h_not_intrinsic with h_ind_t | h_ni
        · rw [h_ind] at h_ind_t
          exact False.elim (Bool.false_ne_true h_ind_t)
        · dsimp only [evalDirectRustIntrinsic?]
          rw [h_ni]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  rcases h_sub _ (h_contract_pre m hm) with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    rcases h_contract_panic with
      rfl | rfl | h_no_panic | ⟨cleanupBb, rfl, h_mod_p, h_clean⟩
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [h_panic_stack m panicMem hm hp]
      dsimp only [unwindFromCallStack]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · dsimp only [resumeExternalCall, applyUnwindAction]
      rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
      trivial
    · exact False.elim (h_no_panic m panicMem hm hp)
    · dsimp only [resumeExternalCall, applyUnwindAction]
      exact h_clean panicMem (h_mod_p m panicMem hm hp)
  | returned retVal retMem =>
    rcases h_contract_ret m retMem retVal hm hp with ⟨h_mod_ret, h_cp⟩
    rcases h_after retVal h_cp with ⟨updEnv, h_wr, h_next⟩
    dsimp only [resumeExternalCall]
    rw [writePlaceValue_pure_eq envAfterArgs retMem.borrows destination retVal h_dst_pure]
    unfold writePurePlaceValue at h_wr
    rw [h_wr]
    exact h_next retMem h_mod_ret

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` call rule supporting
both constant and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`) AND `.cleanup
cleanupBb` unwind landing-pad recovery.
-/
theorem PureMirModularConverges.call_poly_external_spec_pureTarget
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (targetDefPath, expectedTypeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func targetDefPath expectedTypeArgs
        body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_not_exact : stringEq targetDefPath "core::intrinsics::exact_div" = false := by decide)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_unwind :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      sidecarTargetCanUnwind sidecarBody = false ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_after :
      ∀ (retVal : Value),
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        ∃ updatedEnv : List SlotState,
          writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv ∧
          PureMirModularConverges contract body callees
            { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? targetDefPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  refine PureMirModularConverges.call_modular_resolved
    (resolvedTarget := { defPath := targetDefPath, typeArgs := expectedTypeArgs, fnSig := .none, isIndirect := false })
    h_sub h_phase h_bb h_end h_term h_dst_pure h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup h_not_exact
    (fun _ _ => ⟨rfl, rfl, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ _ hm hp =>
      ⟨ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1, hp.2⟩)
    ?_
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])
    h_after
    (Or.inr h_not_intrinsic)
  rcases h_unwind with hu | hu | h_nu | ⟨cleanupBb, h_cl, h_clean_wp⟩
  · exact Or.inl hu
  · exact Or.inr (Or.inl hu)
  · refine Or.inr (Or.inr (Or.inl (fun _ _ _ hp => ?_)))
    dsimp only [polyExternalSpecCallContract] at hp
    rw [h_nu] at hp
    exact hp
  · refine Or.inr (Or.inr (Or.inr ⟨cleanupBb, h_cl, ?_, h_clean_wp⟩))
    intro m panicMem hm hp
    dsimp only [polyExternalSpecCallContract] at hp
    cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
    · exact False.elim hp
    · exact ModularRootMemory.of_callFrameAndTraitsPreserved hm hp

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` call rule supporting
both constant and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.call_intrinsic_pureTarget
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {kind : PureRustIntrinsicKind}
    {envAfterFunc envAfterArgs updatedEnv : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_not_exact : stringEq defPath "core::intrinsics::exact_div" = false := by decide)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind typeArgs argVals pointerBytes
        ubChecksEnabled = some retVal)
    (h_wr : writePurePlaceValue envAfterArgs destination retVal = .ok updatedEnv)
    (h_after :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls)
    (h_not_intrinsic : classifyRustIntrinsic? defPath = none := by decide) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  refine PureMirModularConverges.call_modular_resolved
    (resolvedTarget := { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false })
    (calleePost := (· = retVal))
    h_sub h_phase h_bb h_end h_term h_dst_pure h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup h_not_exact
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ rv hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      exact ⟨hm, hrv_eq.symm⟩)
    (Or.inr (Or.inr (Or.inl (fun _ _ _ hp => hp))))
    (fun _ _ _ hp => False.elim hp)
    (fun rv h_eq => by
      subst h_eq
      exact ⟨updatedEnv, h_wr, h_after⟩)
    (Or.inr h_not_intrinsic)

/--
1-step inline `core::intrinsics::exact_div` call rule supporting both constant
and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.call_exact_div_pureTarget
    {contract : MirCallContract} {body : CapturedMir}
    {callees : List CapturedMir} {ps : PureState}
    {bb : BasicBlockData} {func : Operand}
    {argOps : List Operand} {destination : Place}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {defPath : DefPath} {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {lhs rhs retScalar : ScalarInt} {isSigned : Bool}
    {envAfterFunc envAfterArgs updatedEnv : List SlotState}
    {post : Value → Prop} {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination (.some targetBb) unwind)
    (h_dst_pure : isPurePlace destination = true)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_exact_path : stringEq defPath "core::intrinsics::exact_div" = true := by decide)
    (h_args :
      evalPureOperands envAfterFunc argOps body.layouts =
        .ok [.scalar lhs, .scalar rhs] envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_signed :
      resolveIntrinsicIsSigned
        { defPath := defPath
          typeArgs := typeArgs
          fnSig := .none
          isIndirect := false }
        body.localDecls body.layouts argOps = some isSigned := by rfl)
    (h_div : evalExactDiv lhs rhs isSigned = some retScalar)
    (h_wr :
      writePurePlaceValue envAfterArgs destination (.scalar retScalar) =
        .ok updatedEnv)
    (h_next :
      PureMirModularConverges contract body callees
        { bb := targetBb, stmtIdx := 0, env := updatedEnv } post traitImpls) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.step
          (({ bb := targetBb, stmtIdx := 0, env := updatedEnv } : PureState).toMachineState m) := by
    have h_res_m :
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts =
          .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
            envAfterFunc := by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps)
        body.localDecls body.layouts h_ext]
      exact h_res_pure
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only [isDirectExactDivTarget]
      rw [h_exact_path]
      dsimp only
      rw [h_signed]
      dsimp only
      rw [h_div]
      dsimp only
      rw [writePlaceValue_pure_eq envAfterArgs m.borrows destination
        (.scalar retScalar) h_dst_pure]
      unfold writePurePlaceValue at h_wr
      rw [h_wr]
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step_eq]
  exact h_next m hm

/--
Generalized subsumption-aware 1-step external `tailCall` rule
(`PureMirModularConverges.tailCall_modular_resolved`):
supports arbitrary call-target resolution via `resolveCallTarget` (including
local/projected zero-sized `RigidTy.fnDef` slots and indirect `FnPtrEntry`
targets).
-/
theorem PureMirModularConverges.tailCall_modular_resolved
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_resolve :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        resolveCallTarget (ps.toMachineState m) func (length argOps)
          body.localDecls body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts resolvedTarget.defPath
        resolvedTarget.typeArgs traitImpls = none)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m })
    (h_contract_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.returned retVal retMem) →
        retMem.callStack = [] ∧ post retVal)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  have h_step_eq :
      stepMirFn body (ps.toMachineState m) =
        MirStepNode.extCall
          { defPath := resolvedTarget.defPath
            typeArgs := resolvedTarget.typeArgs
            args := argVals
            memory := m }
          resumeExternalTailCall := by
    have h_res_m := h_resolve m hm
    dsimp only [PureState.toMachineState] at h_res_m
    unfold stepMirFn
    dsimp only [PureState.toMachineState]
    rw [ModularRootMemory.activeCallee_getD hm]
    cases h_ph : body.phase with
    | other tag => exact False.elim (h_phase tag h_ph)
    | _ =>
      rw [h_bb]
      dsimp only
      rw [h_stmt_none]
      dsimp only
      have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
      simp only [h_beq, ite_true]
      rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
      dsimp only at h_term
      rw [h_term]
      dsimp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf]
      rw [h_res_m]
      dsimp only
      rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals
        body.layouts m.callerLocals h_args_pure]
      unfold evalPureOperands at h_args
      rw [h_args]
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
  rw [h_step_eq]
  dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP,
    MirCallContract.toCallContract]
  rcases h_sub _ (h_contract_pre m hm) with ⟨h_cpre, h_cpost_imp⟩
  refine ⟨h_cpre, fun ans hp_sup => ?_⟩
  have hp := h_cpost_imp ans hp_sup
  cases ans with
  | aborted =>
    dsimp only [resumeExternalTailCall]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | panicked panicMem =>
    dsimp only [resumeExternalTailCall]
    rw [h_panic_stack m panicMem hm hp]
    dsimp only [unwindFromCallStack]
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    trivial
  | returned retVal retMem =>
    rcases h_contract_ret m retMem retVal hm hp with ⟨h_cs, h_post_ret⟩
    dsimp only [resumeExternalTailCall]
    rw [h_cs]
    dsimp only
    rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
    exact h_post_ret

/--
Subsumption-aware 1-step polymorphic `#[external_spec]` `tailCall` rule
supporting both constant and local/projected zero-sized `RigidTy.fnDef`
operands (`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.tailCall_poly_external_spec_pureTarget
    {contract : MirCallContract}
    {targetDefPath : DefPath}
    {expectedTypeArgs : List RigidTy}
    {sidecarBody : CapturedMir}
    {extraPre : List Value → Prop}
    {extraPost : List Value → Value → Prop}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (polyExternalSpecCallContract targetDefPath expectedTypeArgs
          sidecarBody extraPre extraPost)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (targetDefPath, expectedTypeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func targetDefPath expectedTypeArgs
        body.layouts = .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup :
      lookupCallee callees body.layouts targetDefPath expectedTypeArgs traitImpls = none)
    (h_arity : length argVals = sidecarBody.argCount)
    (h_param_tys : argsMatchCalleeParamTys sidecarBody argVals)
    (h_extra_pre : extraPre argVals)
    (h_imp :
      ∀ retVal : Value,
        retMatchesCalleeReturnTy sidecarBody retVal ∧ extraPost argVals retVal →
        post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  exact PureMirModularConverges.tailCall_modular_resolved
    (subContract := polyExternalSpecCallContract targetDefPath expectedTypeArgs
      sidecarBody extraPre extraPost)
    (resolvedTarget := { defPath := targetDefPath, typeArgs := expectedTypeArgs, fnSig := .none, isIndirect := false })
    h_sub
    h_phase h_bb h_end h_term h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup
    (fun _ _ => ⟨rfl, rfl, h_arity, h_param_tys, h_extra_pre⟩)
    (fun m _ retVal hm hp =>
      ⟨(ModularRootMemory.of_callFrameAndTraitsPreserved hm hp.1).2.2.1,
        h_imp retVal hp.2⟩)
    (fun m _ hm hp => by
      dsimp only [polyExternalSpecCallContract] at hp
      cases h_u : sidecarTargetCanUnwind sidecarBody <;> rw [h_u] at hp
      · exact False.elim hp
      · rw [hp.1.2.1, hm.2.2.1])

/--
Subsumption-aware 1-step pure `CallConv.rustIntrinsic` `tailCall` rule
supporting both constant and local/projected zero-sized `RigidTy.fnDef`
operands (`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.tailCall_intrinsic_pureTarget
    {contract : MirCallContract}
    {pointerBytes : Nat}
    {ubChecksEnabled : Bool}
    {rtEval : DefPath → List RigidTy → List Value → Option Value}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {kind : PureRustIntrinsicKind}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {retVal : Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub :
      MirCallContract.Subsumes
        (pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
        contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .tailCall func argOps)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_kind : classifyPureRustIntrinsic? defPath = some kind)
    (h_eval :
      evalPureRustIntrinsicWithRuntime rtEval kind typeArgs argVals pointerBytes
        ubChecksEnabled = some retVal)
    (h_post : post retVal) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  exact PureMirModularConverges.tailCall_modular_resolved
    (subContract := pureRustIntrinsicContract pointerBytes ubChecksEnabled rtEval)
    (resolvedTarget := { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false })
    h_sub
    h_phase h_bb h_end h_term h_args_pure
    (fun m _ => by
      rw [resolveCallTarget_eq_of_extractPureCalleeTarget
        (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
        h_ext]
      exact h_res_pure)
    h_args h_lookup
    (fun _ _ => ⟨kind, retVal, h_kind, h_eval⟩)
    (fun m _ rv hm hp => by
      rcases hp with ⟨rfl, _, hk', hev'⟩
      rw [h_kind] at hk'
      injection hk' with hk_eq
      subst hk_eq
      rw [h_eval] at hev'
      injection hev' with hrv_eq
      subst hrv_eq
      exact ⟨hm.2.2.1, h_post⟩)
    (fun _ _ _ hp => False.elim hp)

/--
1-step diverging standard panic/abort call rule (`target = .none`) supporting
both constant and local/projected zero-sized `RigidTy.fnDef` operands
(`extractPureCalleeTarget?` + `resolvePureCalleeTarget`).
-/
theorem PureMirModularConverges.call_diverging_panic_pureTarget
    {contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination .none unwind)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_not_unreach : isUnreachableCallTarget defPath = false := by decide)
    (h_panic :
      isAbortingPanicDefPath defPath = true ∨
      (isUnwindingPanicDefPath defPath = true ∧
        (unwind = .continue_ ∨
         unwind = .terminate ∨
         ∃ cleanupBb : BasicBlockIdx,
           unwind = .cleanup cleanupBb ∧
           PureMirModularConverges contract body callees
             { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
             post traitImpls))) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_res_m :
      resolveCallTarget (ps.toMachineState m) func (length argOps)
        body.localDecls body.layouts =
        .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
          envAfterFunc := by
    rw [resolveCallTarget_eq_of_extractPureCalleeTarget
      (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
      h_ext]
    exact h_res_pure
  dsimp only [PureState.toMachineState] at h_res_m
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, bodyLocalDeclsOf]
    rw [h_res_m]
    dsimp only
    rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals body.layouts
      m.callerLocals h_args_pure]
    unfold evalPureOperands at h_args
    rw [h_args]
    dsimp only
    rw [hm.1, hm.2.1, h_lookup]
    dsimp only
    rw [h_not_unreach]
    dsimp only
    cases h_ab : isAbortingPanicDefPath defPath with
    | true =>
      dsimp only [MirStepNode.retOutcome, Trusted.ITree.ITreeF.map]
      trivial
    | false =>
      dsimp only
      rcases h_panic with h_ab_true | ⟨h_unw_path, h_unw_act⟩
      · rw [h_ab] at h_ab_true; nomatch h_ab_true
      · rw [h_unw_path]
        dsimp only
        rcases h_unw_act with rfl | rfl | ⟨cleanupBb, rfl, h_clean⟩
        · dsimp only [applyUnwindAction]
          rw [hm.2.2.1]
          dsimp only [unwindFromCallStack, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction, MirStepNode.retOutcome,
            Trusted.ITree.ITreeF.map]
          trivial
        · dsimp only [applyUnwindAction]
          exact h_clean m hm

theorem PureMirModularConverges.call_diverging_modular_sub_pureTarget
    {subContract contract : MirCallContract}
    {body : CapturedMir}
    {callees : List CapturedMir}
    {ps : PureState}
    {bb : BasicBlockData}
    {func : Operand}
    {argOps : List Operand}
    {destination : Place}
    {unwind : UnwindAction}
    {defPath : DefPath}
    {typeArgs : List RigidTy}
    {resolvedTarget : ResolvedCallTarget}
    {envAfterFunc envAfterArgs : List SlotState}
    {argVals : List Value}
    {post : Value → Prop}
    {traitImpls : List TraitImplEntry}
    (h_sub : MirCallContract.Subsumes subContract contract)
    (h_phase : ∀ tag, body.phase ≠ .other tag)
    (h_bb : get? body.basicBlocks ps.bb = some bb)
    (h_end : ps.stmtIdx = length bb.statements)
    (h_term : bb.terminator.kind = .call func argOps destination .none unwind)
    (h_args_pure : argOps.all isPureOperand = true)
    (h_ext :
      extractPureCalleeTarget? body.localDecls body.layouts func =
        some (defPath, typeArgs))
    (h_res_pure :
      resolvePureCalleeTarget ps.env func defPath typeArgs body.layouts =
        .ok resolvedTarget envAfterFunc)
    (h_args : evalPureOperands envAfterFunc argOps body.layouts = .ok argVals envAfterArgs)
    (h_lookup : lookupCallee callees body.layouts defPath typeArgs traitImpls = none)
    (h_not_unreach : isUnreachableCallTarget defPath = false := by decide)
    (h_not_abort : isAbortingPanicDefPath defPath = false := by decide)
    (h_not_unwind : isUnwindingPanicDefPath defPath = false := by decide)
    (h_contract_pre :
      ∀ m : Memory,
        ModularRootMemory body callees traitImpls m →
        subContract.pre
          { defPath := defPath
            typeArgs := typeArgs
            args := argVals
            memory := m })
    (h_no_ret :
      ∀ (m retMem : Memory) (retVal : Value),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := defPath
            typeArgs := typeArgs
            args := argVals
            memory := m }
          (.returned retVal retMem))
    (h_contract_panic :
      unwind = .continue_ ∨
      unwind = .terminate ∨
      (∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        ¬ subContract.post
          { defPath := defPath
            typeArgs := typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem)) ∨
      ∃ cleanupBb : BasicBlockIdx,
        unwind = .cleanup cleanupBb ∧
        (∀ (m panicMem : Memory),
          ModularRootMemory body callees traitImpls m →
          subContract.post
            { defPath := defPath
              typeArgs := typeArgs
              args := argVals
              memory := m }
            (.panicked panicMem) →
          ModularRootMemory body callees traitImpls panicMem) ∧
        PureMirModularConverges contract body callees
          { bb := cleanupBb, stmtIdx := 0, env := envAfterArgs }
          post traitImpls)
    (h_panic_stack :
      ∀ (m panicMem : Memory),
        ModularRootMemory body callees traitImpls m →
        subContract.post
          { defPath := defPath
            typeArgs := typeArgs
            args := argVals
            memory := m }
          (.panicked panicMem) →
        panicMem.callStack = []) :
    PureMirModularConverges contract body callees ps post traitImpls := by
  have h_rt := resolvePureCalleeTarget_ok_target h_res_pure
  subst h_rt
  intro m hm
  have h_stmt_none : get? bb.statements ps.stmtIdx = none := by
    rw [h_end]; exact get?_length_eq_none bb.statements
  have h_res_m :
      resolveCallTarget (ps.toMachineState m) func (length argOps)
        body.localDecls body.layouts =
        .ok { defPath := defPath, typeArgs := typeArgs, fnSig := .none, isIndirect := false }
          envAfterFunc := by
    rw [resolveCallTarget_eq_of_extractPureCalleeTarget
      (ps.toMachineState m) func (length argOps) body.localDecls body.layouts
      h_ext]
    exact h_res_pure
  dsimp only [PureState.toMachineState] at h_res_m
  change Anneal.ITreeWP.DWP _ (Trusted.ITree.ITree.cofix (stepMirState body) _) _ _
  rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
  dsimp only [stepMirState]
  unfold stepMirFn
  dsimp only [PureState.toMachineState]
  rw [ModularRootMemory.activeCallee_getD hm]
  cases h_ph : body.phase with
  | other tag => exact False.elim (h_phase tag h_ph)
  | _ =>
    rw [h_bb]
    dsimp only
    rw [h_stmt_none]
    dsimp only
    have h_beq : (ps.stmtIdx == length bb.statements) = true := by simp [h_end]
    simp only [h_beq, ite_true]
    rcases bb with ⟨stmts, ⟨tk, tsp⟩, isCl⟩
    dsimp only at h_term
    rw [h_term]
    dsimp only [evalTerminator, bodyLocalDeclsOf]
    rw [h_res_m]
    dsimp only
    rw [evalOperands_pure_eq envAfterFunc argOps m.borrows m.globals body.layouts
      m.callerLocals h_args_pure]
    unfold evalPureOperands at h_args
    cases h_ev : evalOperands envAfterFunc argOps [] [] body.layouts [] with
    | ub => rw [h_ev] at h_args; nomatch h_args
    | unsupported => rw [h_ev] at h_args; nomatch h_args
    | ok vals env' =>
      rw [h_ev] at h_args; injection h_args with h_v h_e
      subst h_v h_e
      dsimp only
      rw [hm.1, hm.2.1, h_lookup]
      dsimp only
      have h_unr : isUnreachableCallTarget defPath = false := h_not_unreach
      rw [h_unr]
      dsimp only
      have h_ab : isAbortingPanicDefPath defPath = false := h_not_abort
      rw [h_ab]
      dsimp only
      have h_not_unw : isUnwindingPanicDefPath defPath = false := h_not_unwind
      rw [h_not_unw]
      dsimp only [MirStepNode.extCall, Trusted.ITree.ITreeF.map, mirModularWP, MirCallContract.toCallContract]
      rcases h_sub _ (h_contract_pre m hm) with ⟨h_cpre, h_cpost_imp⟩
      refine ⟨h_cpre, fun ans hp_sup => ?_⟩
      have hp := h_cpost_imp ans hp_sup
      cases ans with
      | aborted =>
        dsimp only [resumeExternalDivergingCall]
        rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
        trivial
      | returned retVal retMem =>
        exact False.elim (h_no_ret m retMem retVal hm hp)
      | panicked panicMem =>
        rcases h_contract_panic with rfl | rfl | h_no_panic | ⟨cleanupBb, rfl, h_mod_p, h_clean⟩
        · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
          rw [h_panic_stack m panicMem hm hp]
          dsimp only [unwindFromCallStack]
          rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
          trivial
        · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
          rw [Anneal.ITreeWP.DWP.unfold_eq, Trusted.ITree.ITree.observe_cofix]
          trivial
        · exact False.elim (h_no_panic m panicMem hm hp)
        · dsimp only [resumeExternalDivergingCall, applyUnwindAction]
          exact h_clean panicMem (h_mod_p m panicMem hm hp)

/-!
## 10. Concrete Multi-Callee, Polymorphic, Intrinsic, & `#[external_spec]`
Witnesses
-/

/-- Generic parameter `T` (`idx := 0`, dedicated layout slot `0`). -/
def polyParamTTy : Ty :=
  { kind := .param 0 "T", layoutIdx := 0 }

/-- Generic tuple `(T, T)` (dedicated compound layout slot `1`). -/
def polyPairTTy : Ty :=
  { kind := .tuple [.param 0 "T", .param 0 "T"], layoutIdx := 1 }

/-- `u64` type (`8` bytes). -/
def pureU64Ty : Ty :=
  { kind := .uint .u64, layoutIdx := 0 }

/-- Concrete `64`-bit layout for `(u32, u32)`. -/
def pairU32Layout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [u32Layout] [] none (.tuple [.uint .u32, .uint .u32]))
    u32Layout

/-- Concrete `64`-bit layout for `u64`. -/
def u64Layout : TypeLayout :=
  Option.getD (RigidTy.computeLayout 64 [] [] none (.uint .u64)) u32Layout

/-- Concrete `64`-bit layout for `(u64, u64)`. -/
def pairU64Layout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [u64Layout] [] none (.tuple [.uint .u64, .uint .u64]))
    u64Layout

/-- Zero-sized function-item constant `Operand` for `(defPath, typeArgs)`. -/
def fnItemOperand (defPath : DefPath) (typeArgs : List RigidTy := []) : Operand :=
  .constant
    { ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
      val := .zeroSized }

/-- Compile-time `u32` scalar constant `Operand`. -/
def u32ConstOperand (n : Nat) : Operand :=
  .constant
    { ty := pureU32Ty
      val := .scalar (.int { bits := n, sizeBytes := 4 }) }

/--
Polymorphic helper `demo::poly_swap_pair<T>` (`typeParamCount := 1`,
`genericParams := [{ idx := 0, name := "T" }]`, `argCount := 1`):
takes `_1 : (T, T)` and returns `(_1.1, _1.0) : (T, T)`.
Slot `0` holds the placeholder for `T` and slot `1` holds `(T, T)` so
`CapturedMir.instantiate` substitutes `T`'s layout and recomputes `(T, T)`'s
compound layout cleanly at any concrete scalar type `T`.
-/
def polySwapPairBody : CapturedMir where
  defPath := "demo::poly_swap_pair"
  phase := .runtimePostCleanup
  role := .subject
  typeParamCount := 1
  genericParams := [{ idx := 0, name := "T" }]
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := polyPairTTy, debugName := some "_0" },
    { mutability := .not, ty := polyPairTTy, debugName := some "pair" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 1, projection := [.field 1 polyParamTTy] },
              .copy { local_ := 1, projection := [.field 0 polyParamTTy] }
            ])
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [u32Layout, pairU32Layout]
  }
  allocations := []

/--
Caller layout table shared by `u32`-pair callers (`[u32Layout, pairU32Layout]`).
-/
def demoCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout]

/--
Monomorphized `demo::poly_swap_pair::<u32>` body produced by
`CapturedMir.instantiate`.
-/
def polySwapPairU32Body : CapturedMir :=
  polySwapPairBody.instantiate [(.uint .u32, u32Layout)]

/--
Monomorphized `demo::poly_swap_pair::<u64>` body produced by
`CapturedMir.instantiate`.
-/
def polySwapPairU64Body : CapturedMir :=
  polySwapPairBody.instantiate [(.uint .u64, u64Layout)]

/--
Polymorphic `(defPath, typeArgs)` resolution at `T = u32` via `lookupCallee`
instantiates `polySwapPairBody` to `polySwapPairU32Body`.
-/
theorem lookupCallee_polySwapPair_u32 :
    lookupCallee [polySwapPairBody] demoCallerLayouts
      "demo::poly_swap_pair" [.uint .u32] [] =
      some polySwapPairU32Body := rfl

/--
Polymorphic `(defPath, typeArgs)` resolution at `T = u64` via `lookupCallee`
instantiates `polySwapPairBody` to `polySwapPairU64Body` with recomputed
`u64` / `(u64, u64)` layouts.
-/
theorem lookupCallee_polySwapPair_u64 :
    lookupCallee [polySwapPairBody] demoCallerLayouts
      "demo::poly_swap_pair" [.uint .u64] [] =
      some polySwapPairU64Body := rfl

/-- `checkPureMir` holds on monomorphized `polySwapPairU32Body`. -/
theorem checkPureMir_polySwapPairU32Body :
    checkPureMir polySwapPairU32Body = true := by
  decide

/-- `checkPureMir` holds on monomorphized `polySwapPairU64Body`. -/
theorem checkPureMir_polySwapPairU64Body :
    checkPureMir polySwapPairU64Body = true := by
  decide

/--
Call-free `PureMirConverges` summary for `polySwapPairU32Body` (`T = u32`),
swapping `(a, b)` to `(b, a)`.
-/
theorem polySwapPairU32_pureConverges (a b : Value) :
    PureMirConverges polySwapPairU32Body
      (initPureState polySwapPairU32Body [.aggregate 0 [a, b]])
      (· = .aggregate 0 [b, a]) :=
  ⟨4, rfl⟩

/--
Call-free `PureMirConverges` summary for `polySwapPairU64Body` (`T = u64`),
swapping `(a, b)` to `(b, a)`.
-/
theorem polySwapPairU64_pureConverges (a b : Value) :
    PureMirConverges polySwapPairU64Body
      (initPureState polySwapPairU64Body [.aggregate 0 [a, b]])
      (· = .aggregate 0 [b, a]) :=
  ⟨4, rfl⟩

/--
Intermediate helper `demo::scale_swap_and_div` (`argCount := 1`):
- Input `_1 : (u32, u32) = (x, y)` (with `x < 2^31`).
- `bb0`: calls polymorphic `demo::poly_swap_pair::<u32>(_1)` -> `_2 = (y, x)`,
  jumping to `bb1`.
- `bb1`: computes `_3 = _2.1 * 2` (`BinOp.mul`), then calls inline intrinsic
  `core::intrinsics::exact_div::<u32>(_3, 2)` -> `_4 = x`, jumping to `bb2`.
- `bb2`: computes `_5 = _2.0 + 1` (`BinOp.add`), writes `_0 = (_5, _4)`, and
  returns `((y + 1) % 2^32, x)`.
-/
def scaleSwapAndDivBody : CapturedMir where
  defPath := "demo::scale_swap_and_div"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "doubled_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "halved_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_y" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = demo::poly_swap_pair::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: StorageLive(_3, _4); _3 = _2.1 * 2; _4 = exact_div::<u32>(_3, 2) ->
    -- bb2
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.binaryOp .mul
              (.copy { local_ := 2, projection := [.field 1 pureU32Ty] })
              (u32ConstOperand 2))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::exact_div" [.uint .u32])
          [.copy { local_ := 3, projection := [] }, u32ConstOperand 2]
          { local_ := 4, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: StorageLive(_5); _5 = _2.0 + 1; _0 = (_5, _4); return
    { statements := [
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .assign
            { local_ := 5, projection := [] }
            (.binaryOp .add
              (.copy { local_ := 2, projection := [.field 0 pureU32Ty] })
              (u32ConstOperand 1))
          span := pureAdtSpan },
        { kind := .assign
            { local_ := 0, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 5, projection := [] },
              .copy { local_ := 4, projection := [] }
            ])
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Outer caller `demo::caller_two_nested` (`argCount := 1`) invoking 2 nested
helper functions in `demoCallees := [polySwapPairBody, scaleSwapAndDivBody]`:
- `bb0`: `StorageLive(_2)`; calls `demo::scale_swap_and_div(_1)` (which
  internally invokes polymorphic `demo::poly_swap_pair::<u32>` and inline
  `core::intrinsics::exact_div::<u32>`), writing `_2 = ((y + 1) % 2^32, x)`.
- `bb1`: calls polymorphic `demo::poly_swap_pair::<u32>(_2)`, writing
  `_0 = (x, (y + 1) % 2^32)`.
- `bb2`: `return`.
-/
def nestedMultiCalleeCallerBody : CapturedMir where
  defPath := "demo::caller_two_nested"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "mid" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = demo::scale_swap_and_div(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::scale_swap_and_div" [])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _0 = demo::poly_swap_pair::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/-- Linked callee table with 2 nested pure helper functions. -/
def demoCallees : List CapturedMir :=
  [polySwapPairBody, scaleSwapAndDivBody]

/--
Expected pair output `(x, (y + 1) % 2^32)` of `nestedMultiCalleeCallerBody`.
-/
def nestedCallerExpected (x y : Nat) : Value :=
  .aggregate 0 [
    .scalar { bits := x, sizeBytes := 4 },
    .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 }
  ]

private theorem wrapScalarBits_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  have h_ble : Nat.ble modulus val = false := by
    cases hb : Nat.ble modulus val with
    | false => rfl
    | true =>
      have h_le : modulus ≤ val := Nat.le_of_ble_eq_true hb
      omega
  rw [h_ble]

private theorem evalExactDiv_double_u32 {x : Nat} (hx : x < 2147483648) :
    evalExactDiv ⟨wrapScalarBits (Nat.mul x 2) (scalarModulus 4), 4⟩ ⟨2, 4⟩ false =
      some ⟨x, 4⟩ := by
  have hm : scalarModulus 4 = 4294967296 := rfl
  have h_mul : Nat.mul x 2 = x * 2 := rfl
  have h_w1 : wrapScalarBits (Nat.mul x 2) (scalarModulus 4) = x * 2 := by
    rw [hm, h_mul]
    exact wrapScalarBits_lt (by omega)
  have h_w2 : wrapScalarBits (x * 2) (scalarModulus 4) = x * 2 := by
    rw [hm]
    exact wrapScalarBits_lt (by omega)
  have h_b2 : wrapScalarBits 2 (scalarModulus 4) = 2 := rfl
  have h_mod : Nat.beq (Nat.mod (x * 2) 2) 0 = true := by
    rw [Nat.beq_eq]
    change (x * 2) % 2 = 0
    omega
  have h_div : Nat.div (x * 2) 2 = x := by
    change (x * 2) / 2 = x
    omega
  dsimp only [evalExactDiv]
  rw [h_w1, h_w2, h_b2]
  dsimp only
  rw [h_mod]
  dsimp only
  rw [h_div]
  rfl

/-!
### 10A. Proof Path A — Compositional 1-Step Callee Summaries
(`PureMirConverges.call_summary`)
-/

/--
Compositional summary for `scaleSwapAndDivBody`: resolves polymorphic
`demo::poly_swap_pair::<u32>` in 1 compositional step via
`PureMirConverges.call_leaf_summary` and inline `core::intrinsics::exact_div`
in 1 step via `PureMirConvergesWithCallees.call_exact_div`.
-/
theorem scaleSwapAndDiv_compositional
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees scaleSwapAndDivBody demoCallees
      (initPureState scaleSwapAndDivBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 },
        .scalar { bits := x, sizeBytes := 4 }
      ])
      [] := by
  -- bb0 stmt 0 (StorageLive(_2)), then 1-step compositional call to
  -- poly_swap_pair::<u32>
  have h_init :
      initPureState scaleSwapAndDivBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] = {
        bb := 0
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .dead, .dead, .dead, .dead
        ]
      } := rfl
  rw [h_init]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 64)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1 stmts (StorageLive(_3), StorageLive(_4), _3 = _2.1 * 2)
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb1 terminator: 1-step inline core::intrinsics::exact_div(_3, 2)
  refine PureMirConvergesWithCallees.call_exact_div
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (evalExactDiv_double_u32 hx) rfl ?_
  -- bb2 stmts (StorageLive(_5), _5 = _2.0 + 1, _0 = (_5, _4)) and return_
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirConvergesWithCallees.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  exact PureMirConvergesWithCallees.step ⟨Or.inl rfl, rfl⟩

/--
Headline compositional 2-nested-callee proof (`FF-2.2` Section 4):
proves `nestedMultiCalleeCallerBody` using **2 compositional `call_summary`
steps**
(1 step for `demo::scale_swap_and_div`, reusing `scaleSwapAndDiv_compositional`
without re-stepping any of its basic blocks or guessing fuel, and 1 step for
polymorphic `demo::poly_swap_pair::<u32>`) plus `StorageLive(_2)` and `return_`.
-/
theorem nestedMultiCalleeCaller_compositional
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees nestedMultiCalleeCallerBody demoCallees
      (initPureState nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = nestedCallerExpected x y)
      [] := by
  -- bb0: StorageLive(_2), then 1 compositional step for
  -- demo::scale_swap_and_div
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConverges.call_summary
    (maxCallDepth := 64)
    (calleeBody := scaleSwapAndDivBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    (scaleSwapAndDiv_compositional x y hx)
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1: 1 compositional step for polymorphic demo::poly_swap_pair::<u32>
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 64)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 })
      (.scalar { bits := x, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb2: return_
  exact PureMirConvergesWithCallees.step ⟨Or.inl rfl, rfl⟩

/--
`checkPureMirWithCallees` succeeds on `nestedMultiCalleeCallerBody` at exact
call depth `maxCallDepth = 2` (`caller -> scale_swap_and_div ->
poly_swap_pair`).
-/
theorem checkPureMirWithCallees_nestedCaller_depth2 :
    checkPureMirWithCallees demoCallees nestedMultiCalleeCallerBody 2 [] = true := by
  decide

/--
Tightness of `maxCallDepth` in `checkPureMirWithCallees`: depth `1` rejects
`nestedMultiCalleeCallerBody` because `scale_swap_and_div` makes a nested call
at depth `2`.
-/
theorem checkPureMirWithCallees_nestedCaller_depth1_false :
    checkPureMirWithCallees demoCallees nestedMultiCalleeCallerBody 1 [] = false := by
  decide

/--
Transport the compositional 1-step-per-call
`nestedMultiCalleeCaller_compositional`
proof directly to `MirWpConverges` on `initMachineStateWithCallees`.
-/
theorem nestedMultiCalleeCaller_wpConverges_compositional
    (x y : Nat) (hx : x < 2147483648) :
    MirWpConverges nestedMultiCalleeCallerBody
      (initMachineStateWithCallees nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] demoCallees)
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory nestedMultiCalleeCallerBody
            (initMachineStateWithCallees nestedMultiCalleeCallerBody [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] demoCallees).memory mem' ∧
          retVal = nestedCallerExpected x y)) :=
  mirWpConverges_of_pureExecWithCallees_init
    checkPureMirWithCallees_nestedCaller_depth2
    (nestedMultiCalleeCaller_compositional x y hx)

/-!
### 10B. Proof Path B — Inline `checkPureMirWithCallees` Execution & Trusted
Certificates
-/

private def runPureTauSteps : Nat → CapturedMir → MachineState → Option MachineState
  | 0, _, s => some s
  | n + 1, body, s =>
    match stepMirFn body s with
    | .tau (.running s') => runPureTauSteps n body s'
    | _ => none

private theorem wpMirExecNoCallSym_of_runPureTauSteps
    {n fuel : Nat} {body : CapturedMir} {s s' : MachineState}
    {post : _ → Prop}
    (h_run : runPureTauSteps n body s = some s')
    (h_rest : wpMirExecNoCallSym fuel body (.running s') post) :
    wpMirExecNoCallSym (n + fuel) body (.running s) post := by
  induction n generalizing s with
  | zero =>
    injection h_run with h_eq
    subst h_eq
    simpa only [Nat.zero_add] using h_rest
  | succ k ih =>
    dsimp only [runPureTauSteps] at h_run
    cases h_sf : stepMirFn body s with
    | ret _ => rw [h_sf] at h_run; nomatch h_run
    | vis _ _ => rw [h_sf] at h_run; nomatch h_run
    | tau st =>
      rw [h_sf] at h_run
      cases st with
      | halted _ => nomatch h_run
      | faulted _ => nomatch h_run
      | running nxt =>
        have h_sub := ih h_run
        rw [Nat.succ_add]
        unfold wpMirExecNoCallSym
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
        dsimp only [stepMirState]
        rw [h_sf]
        exact h_sub

private theorem wpMirExecNoCallSym_of_step_eq
    {fuel : Nat} {body : CapturedMir} {s s' : MachineState}
    {post : _ → Prop}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_rest : wpMirExecNoCallSym fuel body (.running s') post) :
    wpMirExecNoCallSym (fuel + 1) body (.running s) post := by
  unfold wpMirExecNoCallSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_rest

private theorem wpMirExecNoCallSym_of_retNormal
    {body : CapturedMir} {s : MachineState} {retVal : Value} {memOut : Memory}
    {post : _ → Prop}
    (h_step : stepMirFn body s = .ret (.normal (retVal, memOut)))
    (h_post : post (.normal (retVal, memOut))) :
    wpMirExecNoCallSym 1 body (.running s) post := by
  unfold wpMirExecNoCallSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_post

/--
Inline multi-frame `PureMirConvergesWithCallees` proof for
`nestedMultiCalleeCallerBody` (`FF-2.2` Section 4), executing directly across
`pushCalleeFrame`, 2-deep `callStack`, polymorphic `poly_swap_pair::<u32>`,
inline `exact_div`, and `activeCallee` restoration in
`wpPureMirExecWithCallees`.
-/
theorem nestedMultiCalleeCaller_inline
    (x y : Nat) (hx : x < 2147483648) :
    PureMirConvergesWithCallees nestedMultiCalleeCallerBody demoCallees
      (initPureState nestedMultiCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = nestedCallerExpected x y)
      [] := by
  let pairXY : Value :=
    .aggregate 0 [
      .scalar { bits := x, sizeBytes := 4 },
      .scalar { bits := y, sizeBytes := 4 }
    ]
  let pairYX : Value :=
    .aggregate 0 [
      .scalar { bits := y, sizeBytes := 4 },
      .scalar { bits := x, sizeBytes := 4 }
    ]
  let baseMem := pureCalleeMemory demoCallees []
  let s0 := (initPureState nestedMultiCalleeCallerBody [pairXY]).toMachineState baseMem
  let callerSaved : SavedCallerFrame := {
    callerBody := nestedMultiCalleeCallerBody
    frame := {
      blockIdx := 0
      stmtIdx := 1
      locals := [.uninit, .init pairXY, .uninit]
    }
    destination := { local_ := 2, projection := [] }
    returnTarget := 1
    calleeProtectors := []
    returnUnwind := .continue_
    isDiverging := false
  }
  let s9 : MachineState := {
    frame := {
      blockIdx := 1
      stmtIdx := 3
      locals := [
        .uninit,
        .init pairXY,
        .init pairYX,
        .init (.scalar { bits := wrapScalarBits (Nat.mul x 2) (scalarModulus 4), sizeBytes := 4 }),
        .uninit,
        .dead
      ]
    }
    memory := {
      baseMem with
      callStack := [callerSaved]
      activeCallee := some scaleSwapAndDivBody
    }
  }
  let s10 : MachineState := {
    frame := {
      blockIdx := 2
      stmtIdx := 0
      locals := [
        .uninit,
        .init pairXY,
        .init pairYX,
        .init (.scalar { bits := wrapScalarBits (Nat.mul x 2) (scalarModulus 4), sizeBytes := 4 }),
        .init (.scalar { bits := x, sizeBytes := 4 }),
        .dead
      ]
    }
    memory := s9.memory
  }
  let midPair : Value :=
    .aggregate 0 [
      .scalar { bits := wrapScalarBits (Nat.add y 1) (scalarModulus 4), sizeBytes := 4 },
      .scalar { bits := x, sizeBytes := 4 }
    ]
  let s17 : MachineState := {
    frame := {
      blockIdx := 2
      stmtIdx := 0
      locals := [.init (nestedCallerExpected x y), .init pairXY, .init midPair]
    }
    memory := {
      baseMem with
      activeCallee := some nestedMultiCalleeCallerBody
    }
  }
  have h_step10 : stepMirFn nestedMultiCalleeCallerBody s9 = .tau (.running s10) := by
    change
      (match evalExactDiv ⟨wrapScalarBits (Nat.mul x 2) (scalarModulus 4), 4⟩ ⟨2, 4⟩ false with
       | some retScalar =>
         match writePlaceValue s9.frame.locals s9.memory.borrows
             { local_ := 4, projection := [] } (.scalar retScalar) with
         | .ok updatedLocals =>
           MirStepNode.step {
             frame := { s9.frame with blockIdx := 2, stmtIdx := 0, locals := updatedLocals }
             memory := s9.memory
           }
         | .ub => MirStepNode.fail .ub
         | .unsupported => MirStepNode.unsupported
       | none => MirStepNode.fail .ub) = .tau (.running s10)
    rw [evalExactDiv_double_u32 hx]
    rfl
  have h_run9 : runPureTauSteps 9 nestedMultiCalleeCallerBody s0 = some s9 := rfl
  have h_run7 : runPureTauSteps 7 nestedMultiCalleeCallerBody s10 = some s17 := rfl
  have h_ret17 :
      stepMirFn nestedMultiCalleeCallerBody s17 =
        .ret (.normal (nestedCallerExpected x y, s17.memory)) := rfl
  refine ⟨18, ?_⟩
  unfold wpPureMirExecWithCallees
  exact wpMirExecNoCallSym_of_runPureTauSteps (n := 9) (fuel := 9) h_run9
    (wpMirExecNoCallSym_of_step_eq (fuel := 8) h_step10
      (wpMirExecNoCallSym_of_runPureTauSteps (n := 7) (fuel := 1) h_run7
        (wpMirExecNoCallSym_of_retNormal h_ret17 ⟨Or.inr ⟨_, rfl⟩, rfl⟩)))

/-- Stateless `Claim` for `nestedMultiCalleeCallerBody` with `demoCallees`. -/
def nestedMultiCalleeStatelessClaim : Claim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre args :=
    ∃ (x y : Nat),
      x < 2147483648 ∧
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ]
  post args retVal :=
    ∀ (x y : Nat),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] →
      retVal = nestedCallerExpected x y

/-- Non-vacuity witness for `nestedMultiCalleeStatelessClaim.pre`. -/
theorem nestedMultiCalleeStatelessClaim_nonVacuous :
    NonVacuousPre nestedMultiCalleeStatelessClaim.pre :=
  ⟨[.aggregate 0 [.scalar { bits := 21, sizeBytes := 4 }, .scalar { bits := 99, sizeBytes := 4 }]],
   21, 99, by decide, rfl⟩

private theorem pairU32Args_inj
    {x y x' y' : Nat}
    (h :
      ([Value.aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]] : List Value) =
      [Value.aggregate 0 [
          .scalar { bits := x', sizeBytes := 4 },
          .scalar { bits := y', sizeBytes := 4 }
        ]]) :
    x = x' ∧ y = y' := by
  injection h with h_hd _
  injection h_hd with _ h_flds
  injection h_flds with h_x h_tl
  injection h_tl with h_y _
  injection h_x with h_sx
  injection h_y with h_sy
  injection h_sx with hx_eq _
  injection h_sy with hy_eq _
  exact ⟨hx_eq, hy_eq⟩

/--
Stateless `VerificationResult` for `nestedMultiCalleeStatelessClaim`, discharged
via `verifyMirNoPanic_of_pureExecWithCallees` and
`nestedMultiCalleeCaller_inline`.
-/
theorem verify_nestedMultiCalleeStatelessClaim :
    VerificationResult nestedMultiCalleeStatelessClaim := by
  refine verifyMirNoPanic_of_pureExecWithCallees
    nestedMultiCalleeStatelessClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (fun args h_pre => ?_)
  rcases h_pre with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_inline x y hx)
  intro retVal h_ret x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/--
Stateful `StatefulClaim` for `nestedMultiCalleeCallerBody` requiring full
`ActiveRootMemory` preservation (`allocs`, `borrows`, `provenanceMap`,
`globals`,
`fnPtrs`, `callees`, `traitImpls`, `callStack = []`) across arbitrary heap
state.
-/
def nestedMultiCalleeStatefulClaim : StatefulClaim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre args mem₀ :=
    (∃ (x y : Nat),
      x < 2147483648 ∧
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ]) ∧
    RootActiveMemory mem₀
  post args mem₀ retVal mem' :=
    ActiveRootMemory nestedMultiCalleeCallerBody
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        nestedMultiCalleeCallerBody args mem₀ demoCallees).memory mem' ∧
    ∀ (x y : Nat),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] →
      retVal = nestedCallerExpected x y

/-- Non-vacuity witness for `nestedMultiCalleeStatefulClaim.pre`. -/
theorem nestedMultiCalleeStatefulClaim_nonVacuous :
    NonVacuousStatefulPre nestedMultiCalleeStatefulClaim.pre :=
  ⟨[.aggregate 0 [.scalar { bits := 21, sizeBytes := 4 }, .scalar { bits := 99, sizeBytes := 4 }]],
   emptyMemory,
   ⟨21, 99, by decide, rfl⟩,
   rootActiveMemory_emptyMemory⟩

/--
Stateful `StatefulVerificationResult` for `nestedMultiCalleeStatefulClaim`,
discharged via `verifyStatefulMirNoPanic_of_pureExecWithCallees`.
-/
theorem verify_nestedMultiCalleeStatefulClaim :
    StatefulVerificationResult nestedMultiCalleeStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExecWithCallees
    nestedMultiCalleeStatefulClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_compositional x y hx)
  intro retVal h_ret mem' h_act
  refine ⟨h_act, fun x' y' h_eq => ?_⟩
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/--
Total-correctness `TotalClaim` for `nestedMultiCalleeCallerBody`
(`demoCallees`).
-/
def nestedMultiCalleeTotalClaim : TotalClaim where
  body := nestedMultiCalleeCallerBody
  callees := demoCallees
  pre := nestedMultiCalleeStatefulClaim.pre
  post := nestedMultiCalleeStatefulClaim.post

/-- Non-vacuity witness for `nestedMultiCalleeTotalClaim.pre`. -/
theorem nestedMultiCalleeTotalClaim_nonVacuous :
    NonVacuousStatefulPre nestedMultiCalleeTotalClaim.pre :=
  nestedMultiCalleeStatefulClaim_nonVacuous

/--
Total-correctness `TotalVerificationResult` (`TreeSafe`, `Productive`,
`¬ MayDiverge`, no panic/abort) for `nestedMultiCalleeTotalClaim`.
-/
theorem verify_nestedMultiCalleeTotalClaim :
    TotalVerificationResult nestedMultiCalleeTotalClaim := by
  refine verifyTotalMir_of_pureExecWithCallees
    nestedMultiCalleeTotalClaim
    checkPureMirWithCallees_nestedCaller_depth2
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirConvergesWithCallees.mono ?_ (nestedMultiCalleeCaller_compositional x y hx)
  intro retVal h_ret mem' h_act
  refine ⟨h_act, fun x' y' h_eq => ?_⟩
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-! ### 10C. Pure `CallConv.rustIntrinsic` & UB-Rejection Witnesses -/

/--
`ctlz::<u8>(0) = 8`, whereas `ctlz_nonzero::<u8>(0) = none` (UB rejected).
-/
theorem evalPureScalarIntrinsic_ctlz_and_nonzero_ub :
    evalPureScalarIntrinsic .ctlz [.uint .u8] [.scalar ⟨0, 1⟩] =
      some (.scalar ⟨8, 4⟩) ∧
    evalPureScalarIntrinsic .ctlzNonzero [.uint .u8] [.scalar ⟨0x10, 1⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .ctlzNonzero [.uint .u8] [.scalar ⟨0, 1⟩] = none :=
  ⟨rfl, rfl, rfl⟩

/--
`cttz::<u8>(0) = 8`, whereas `cttz_nonzero::<u8>(0) = none` (UB rejected).
-/
theorem evalPureScalarIntrinsic_cttz_and_nonzero_ub :
    evalPureScalarIntrinsic .cttz [.uint .u8] [.scalar ⟨0, 1⟩] =
      some (.scalar ⟨8, 4⟩) ∧
    evalPureScalarIntrinsic .cttzNonzero [.uint .u8] [.scalar ⟨0x18, 1⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .cttzNonzero [.uint .u8] [.scalar ⟨0, 1⟩] = none :=
  ⟨rfl, rfl, rfl⟩

/-- `ctpop`, `bswap`, and `bitreverse` pure evaluation witnesses. -/
theorem evalPureScalarIntrinsic_bitops :
    evalPureScalarIntrinsic .ctpop [.uint .u32] [.scalar ⟨0x10101, 4⟩] =
      some (.scalar ⟨3, 4⟩) ∧
    evalPureScalarIntrinsic .bswap [.uint .u32] [.scalar ⟨0x12345678, 4⟩] =
      some (.scalar ⟨0x78563412, 4⟩) ∧
    evalPureScalarIntrinsic .bitreverse [.uint .u8] [.scalar ⟨0x81, 1⟩] =
      some (.scalar ⟨0x81, 1⟩) :=
  ⟨rfl, rfl, rfl⟩

/--
`wrapping_add/sub/mul` and unsigned/signed `saturating_add/sub` witnesses.
-/
theorem evalPureScalarIntrinsic_wrapping_and_saturating :
    evalPureScalarIntrinsic .wrappingAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = some (.scalar ⟨4, 1⟩) ∧
    evalPureScalarIntrinsic .wrappingSub [.uint .u8]
      [.scalar ⟨3, 1⟩, .scalar ⟨5, 1⟩] = some (.scalar ⟨254, 1⟩) ∧
    evalPureScalarIntrinsic .wrappingMul [.uint .u8]
      [.scalar ⟨16, 1⟩, .scalar ⟨16, 1⟩] = some (.scalar ⟨0, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = some (.scalar ⟨255, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingAdd [.int .i8]
      [.scalar ⟨120, 1⟩, .scalar ⟨20, 1⟩] = some (.scalar ⟨127, 1⟩) ∧
    evalPureScalarIntrinsic .saturatingSub [.int .i8]
      [.scalar ⟨136, 1⟩, .scalar ⟨20, 1⟩] = some (.scalar ⟨128, 1⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
UB-guarded `unchecked_add`, `unchecked_shl`, and `exact_div` witnesses:
valid inputs evaluate to `some`, while overflow (`250 + 10` on `u8`),
out-of-range
shift (`1 << 8` on `u8`), non-exact division (`7 / 2`), and signed `i8::MIN ÷
-1`
(`128 ÷ 255` on `i8`) evaluate to `none`.
-/
theorem evalPureScalarIntrinsic_ub_guards :
    evalPureScalarIntrinsic .uncheckedAdd [.uint .u8]
      [.scalar ⟨200, 1⟩, .scalar ⟨50, 1⟩] = some (.scalar ⟨250, 1⟩) ∧
    evalPureScalarIntrinsic .uncheckedAdd [.uint .u8]
      [.scalar ⟨250, 1⟩, .scalar ⟨10, 1⟩] = none ∧
    evalPureScalarIntrinsic .uncheckedShl [.uint .u8, .uint .u32]
      [.scalar ⟨3, 1⟩, .scalar ⟨2, 4⟩] = some (.scalar ⟨12, 1⟩) ∧
    evalPureScalarIntrinsic .uncheckedShl [.uint .u8, .uint .u32]
      [.scalar ⟨3, 1⟩, .scalar ⟨8, 4⟩] = none ∧
    evalPureScalarIntrinsic .exactDiv [.uint .u8]
      [.scalar ⟨7, 1⟩, .scalar ⟨2, 1⟩] = none ∧
    evalPureScalarIntrinsic .exactDiv [.int .i8]
      [.scalar ⟨128, 1⟩, .scalar ⟨255, 1⟩] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `three_way_compare`, `ub_checks`, and `const_eval_select` witnesses. -/
theorem evalPureRustIntrinsic_misc_and_constEvalSelect :
    evalPureScalarIntrinsic .threeWayCompare [.int .i8]
      [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩] = some (.scalar ⟨255, 1⟩) ∧
    evalPureScalarIntrinsic .ubChecks [] [] 8 false = some (.scalar ⟨0, 1⟩) ∧
    evalPureRustIntrinsicWithRuntime
      (fun dp targs unpacked =>
        if dp == "demo::rt_add" then
          match targs, unpacked with
          | [.uint .u32], [.scalar a, .scalar b] =>
            some (.scalar ⟨a.bits + b.bits, 4⟩)
          | _, _ => none
        else none)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_add" [.uint .u32],
       .fnDef "demo::rt_add" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨19, 4⟩, .scalar ⟨23, 4⟩], .unit, .unit] =
      some (.scalar ⟨42, 4⟩) :=
  ⟨rfl, rfl, rfl⟩

/-!
### 10D. Modular `CallConv.rustIntrinsic` & `#[external_spec]` Caller
Witnesses
-/

/--
Caller `demo::intrinsic_bswap_pop` invoking two `CallConv.rustIntrinsic`
operations (`core::intrinsics::bswap::<u32>` followed by
`core::intrinsics::ctpop::<u32>`) on `_1 : u32`.
-/
def pureIntrinsicCallerBody : CapturedMir where
  defPath := "demo::intrinsic_bswap_pop"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "swapped" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2); _2 = core::intrinsics::bswap::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::bswap" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _0 = core::intrinsics::ctpop::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::ctpop" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Default 64-bit runtime `pureRustIntrinsicContract` instance (`pointerBytes =
8`).
-/
abbrev defaultPureRustIntrinsicContract : MirCallContract :=
  pureRustIntrinsicContract 8 true (fun _ _ _ => none)

/--
Expected return value `ctpop::<u32>(bswap::<u32>(x))` of
`pureIntrinsicCallerBody`.
-/
@[irreducible]
def expectedBswapPopU32 (x : Nat) : Value :=
  .scalar ⟨pureCtpopLoop 32 (pureBswapLoop 4 x 0), 4⟩

private theorem expectedBswapPopU32_def (x : Nat) :
    (Value.scalar ⟨pureCtpopLoop 32 (pureBswapLoop 4 x 0), 4⟩) =
      expectedBswapPopU32 x := by
  unfold expectedBswapPopU32
  rfl

private theorem isCanonicalScalarOfSize_four {v : Nat} (hv : v < 4294967296) :
    isCanonicalScalarOfSize { bits := v, sizeBytes := 4 } 4 = true := by
  change decide (v < 4294967296) = true
  exact decide_eq_true hv

/--
Compositional modular convergence for `pureIntrinsicCallerBody` under
`defaultPureRustIntrinsicContract` on any canonical `x < 2^32` and arbitrary
`traitImpls`.
-/
theorem pureIntrinsicCaller_modularConverges
    (x : Nat) (hx : x < 4294967296)
    (traitImpls : List TraitImplEntry := []) :
    PureMirModularConverges
      defaultPureRustIntrinsicContract
      pureIntrinsicCallerBody []
      (initPureState pureIntrinsicCallerBody [.scalar { bits := x, sizeBytes := 4 }])
      (· = expectedBswapPopU32 x)
      traitImpls := by
  have h_canon_x :
      isCanonicalScalarOfSize { bits := x, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four hx
  have h_step (v a bound : Nat) (ha : a < bound) :
      a * 256 + Nat.mod v 256 < bound * 256 := by
    have hm : Nat.mod v 256 < 256 := Nat.mod_lt v (by decide)
    omega
  have h_bswap_lt : pureBswapLoop 4 x 0 < 4294967296 := by
    dsimp only [pureBswapLoop]
    have h1 := h_step x 0 1 (by decide)
    have h2 := h_step (Nat.div x 256) _ 256 h1
    have h3 := h_step (Nat.div (Nat.div x 256) 256) _ 65536 h2
    exact h_step (Nat.div (Nat.div (Nat.div x 256) 256) 256) _ 16777216 h3
  have h_canon_bs :
      isCanonicalScalarOfSize
        { bits := pureBswapLoop 4 x 0, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four h_bswap_lt
  -- bb0: StorageLive(_2), then 1-step inline intrinsic bswap::<u32>(_1)
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := .scalar ⟨pureBswapLoop 4 x 0, 4⟩)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _) (by decide)
    (fun _ _ => evalDirectRustIntrinsic_bswap_u32 _ _ _ _ _ _ _ _ _ _ hx)
    rfl ?_
  -- bb1: 1-step inline intrinsic ctpop::<u32>(_2)
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := expectedBswapPopU32 x)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _) (by decide)
    (fun _ _ => by
      rw [← expectedBswapPopU32_def x]
      exact evalDirectRustIntrinsic_ctpop_u32 _ _ _ _ _ _ _ _ _ _ h_bswap_lt)
    rfl ?_
  exact PureMirModularConverges.return_ (fun _ h => nomatch h) rfl rfl rfl rfl rfl

/-- Modular precondition for `pureIntrinsicCallerBody`. -/
def pureIntrinsicCallerPre (args : List Value) (mem : Memory) : Prop :=
  (∃ x : Nat, x < 4294967296 ∧ args = [.scalar { bits := x, sizeBytes := 4 }]) ∧
  mem.callees = [] ∧
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨ mem.activeCallee = some pureIntrinsicCallerBody) ∧
  mem.activeProtectors = []

/-- Modular postcondition for `pureIntrinsicCallerBody`. -/
def pureIntrinsicCallerPost
    (args : List Value) (_ : Memory) (retVal : Value) (_ : Memory) : Prop :=
  ∀ x : Nat,
    args = [.scalar { bits := x, sizeBytes := 4 }] →
    retVal = expectedBswapPopU32 x

/-- Non-vacuity witness for `pureIntrinsicCallerBody`'s modular precondition. -/
theorem pureIntrinsicCaller_modularPre_nonVacuous :
    NonVacuousStatefulPre pureIntrinsicCallerPre :=
  ⟨[.scalar { bits := 0x12345678, sizeBytes := 4 }],
   emptyMemory,
   ⟨0x12345678, by decide, rfl⟩,
   rfl, rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `pureIntrinsicCallerBody` against
`defaultPureRustIntrinsicContract.holdsOn`.
-/
theorem verify_pureIntrinsicCallerModular :
    ModularVerificationResult
      { body := pureIntrinsicCallerBody
        envAssumed := defaultPureRustIntrinsicContract.holdsOn
        pre := pureIntrinsicCallerPre
        post := pureIntrinsicCallerPost } := by
  refine verifyModularMir_of_pureModularExec
    defaultPureRustIntrinsicContract
    pureIntrinsicCallerBody
    pureIntrinsicCallerPre
    pureIntrinsicCallerPost
    (fun _ _ h_pre => h_pre.2)
    (fun args mem h_pre => ?_)
  rcases h_pre.1 with ⟨x, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (pureIntrinsicCaller_modularConverges x hx mem.traitImpls)
  intro retVal h_ret _ x' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with hx_eq _
  subst hx_eq
  exact h_ret

/--
Sidecar stub body for a polymorphic `#[external_spec]` target
`ext::checked_inc<T>(x: u32) -> u32` (monomorphized at `T = u32`).
-/
def extCheckedIncSidecarBody : CapturedMir where
  defPath := "ext::checked_inc_spec"
  phase := .runtimePostCleanup
  role := .externalSpec "ext::checked_inc"
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Polymorphic `#[external_spec]` contract for `ext::checked_inc::<u32>`:
requires `x < 2^32 - 1` and returns `x + 1`.
-/
def extCheckedIncContract : MirCallContract :=
  polyExternalSpecCallContract
    "ext::checked_inc"
    [.uint .u32]
    extCheckedIncSidecarBody
    (fun args => ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })

/--
Hybrid caller `demo::external_spec_and_poly_callee` (`argCount := 1`,
input `_1 : (u32, u32) = (x, y)` with `x < 2^32 - 1`):
- `bb0`: `StorageLive(_2, _3)`; calls `#[external_spec]` target
  `ext::checked_inc::<u32>(_1.0)` -> `_2 = x + 1`.
- `bb1`: constructs `_3 = (_2, _1.1) = (x + 1, y)`, then calls linked
  polymorphic
  callee `demo::poly_swap_pair::<u32>(_3)` in `demoCallees` -> `_0 = (y, x +
  1)`.
- `bb2`: `return`.
-/
def externalSpecAndPolyCalleeCallerBody : CapturedMir where
  defPath := "demo::external_spec_and_poly_callee"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_x" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "tmp_pair" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2, _3); _2 = ext::checked_inc::<u32>(_1.0) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "ext::checked_inc" [.uint .u32])
          [.copy { local_ := 1, projection := [.field 0 pureU32Ty] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _3 = (_2, _1.1); _0 = demo::poly_swap_pair::<u32>(_3) -> bb2
    { statements := [
        { kind := .assign
            { local_ := 3, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 2, projection := [] },
              .copy { local_ := 1, projection := [.field 1 pureU32Ty] }
            ])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 3, projection := [] }]
          { local_ := 0, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: return
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Compositional modular proof combining a 1-step `#[external_spec]` call
(`PureMirModularConverges.call_poly_external_spec`) with a 1-step linked
polymorphic callee summary (`PureMirModularConverges.call_summary`), even after
the external call may have mutated `m.borrows` or `m.globals`.
-/
theorem externalSpecAndPolyCallee_modularConverges
    (x y : Nat) (hx : x < 4294967295) :
    PureMirModularConverges
      extCheckedIncContract
      externalSpecAndPolyCalleeCallerBody
      [polySwapPairBody]
      (initPureState externalSpecAndPolyCalleeCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := y, sizeBytes := 4 },
        .scalar { bits := x + 1, sizeBytes := 4 }
      ])
      [] := by
  -- bb0: StorageLive(_2), StorageLive(_3), then 1-step #[external_spec] call
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  refine PureMirModularConverges.call_poly_external_spec
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide) rfl
    ⟨⟨x, by dsimp [scalarModulus]; omega, rfl⟩, trivial⟩
    ⟨x, hx, rfl⟩
    (Or.inl rfl)
    ?_
  rintro retVal ⟨_, h_ext_post⟩
  have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
    h_ext_post x rfl
  subst h_rv
  refine ⟨_, rfl, ?_⟩
  -- bb1 stmt 0: _3 = (_2, _1.1)
  refine PureMirModularConverges.step_stmt
    (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb1 terminator: 1-step linked polymorphic callee summary
  -- demo::poly_swap_pair::<u32>
  refine PureMirModularConverges.call_summary
    (maxCallDepth := 1)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
    (by decide)
    (PureMirConvergesWithCallees.of_pureMirConverges
      checkPureMir_polySwapPairU32Body
      (polySwapPairU32_pureConverges
        (.scalar { bits := x + 1, sizeBytes := 4 })
        (.scalar { bits := y, sizeBytes := 4 })))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb2: return_
  exact PureMirModularConverges.return_ (fun _ h => nomatch h) rfl rfl rfl rfl rfl

/--
Non-vacuity witness for `externalSpecAndPolyCalleeCallerBody`'s precondition.
-/
theorem externalSpecAndPolyCallee_modularPre_nonVacuous :
    NonVacuousStatefulPre
      (fun args mem =>
        (∃ (x y : Nat),
          x < 4294967295 ∧
          args = [
            .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              .scalar { bits := y, sizeBytes := 4 }
            ]
          ]) ∧
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨
         mem.activeCallee = some externalSpecAndPolyCalleeCallerBody) ∧
        mem.activeProtectors = []) :=
  ⟨[.aggregate 0 [.scalar { bits := 41, sizeBytes := 4 }, .scalar { bits := 7, sizeBytes := 4 }]],
   emptyMemory,
   ⟨41, 7, by decide, rfl⟩,
   rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `externalSpecAndPolyCalleeCallerBody`
with linked `[polySwapPairBody]` and external `extCheckedIncContract.holdsOn`.
-/
theorem verify_externalSpecAndPolyCalleeModular :
    ModularVerificationResult
      { body := externalSpecAndPolyCalleeCallerBody
        callees := [polySwapPairBody]
        envAssumed := extCheckedIncContract.holdsOn
        pre := fun args mem =>
          (∃ (x y : Nat),
            x < 4294967295 ∧
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ]) ∧
          mem.callStack = [] ∧
          (mem.activeCallee = none ∨
           mem.activeCallee = some externalSpecAndPolyCalleeCallerBody) ∧
          mem.activeProtectors = []
        post := fun args _ retVal _ =>
          ∀ (x y : Nat),
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] →
            retVal = .aggregate 0 [
              .scalar { bits := y, sizeBytes := 4 },
              .scalar { bits := x + 1, sizeBytes := 4 }
            ] } := by
  refine verifyModularMirWithCallees_of_pureModularExec
    extCheckedIncContract
    externalSpecAndPolyCalleeCallerBody
    [polySwapPairBody]
    _ _
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (externalSpecAndPolyCallee_modularConverges x y hx)
  intro retVal h_ret _ x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-!
### 10E. Combined Modular Pipeline Witness — `combineMirCallContracts`
(`#[external_spec]` + `bswap` + `const_eval_select(ctpop)` + `assert` +
`exact_div` + Linked Polymorphic `tailCall`)
-/

/--
Combined rely contract pairing `defaultPureRustIntrinsicContract` and
`extCheckedIncContract` via `combineMirCallContracts`.
-/
def combinedIntrinsicAndExtContract : MirCallContract :=
  combineMirCallContracts defaultPureRustIntrinsicContract extCheckedIncContract

/--
Combined modular caller `demo::combined_modular_pipeline` (`argCount := 1`,
input `_1 : (u32, u32) = (x, y)` with `x < 2^31`):
- `bb0`: `StorageLive(_2.._9)`; calls `#[external_spec]` target
  `ext::checked_inc::<u32>(_1.0)` -> `_2 = x + 1`.
- `bb1`: calls `core::intrinsics::bswap::<u32>(_2)` -> `_3`.
- `bb2`: packs `_5 = (_3,)` and calls `core::intrinsics::const_eval_select`
  selecting `core::intrinsics::ctpop::<u32>` at runtime -> `_4 =
  ctpop::<u32>(bswap::<u32>(x + 1))`.
- `bb3`: computes `_6 = (_2 == _2)` and executes `TerminatorKind.assert` ->
  `bb4`.
- `bb4`: computes `_7 = _1.0 * 2` and calls inline
  `core::intrinsics::exact_div::<u32>(_7, 2)` -> `_8 = x`.
- `bb5`: constructs `_9 = (_4, _8)` and executes `TerminatorKind.tailCall` to
  linked polymorphic `demo::poly_swap_pair::<u32>(_9)` -> `(x,
  ctpop::<u32>(bswap::<u32>(x + 1)))`.
-/
def combinedModularPipelineBody : CapturedMir where
  defPath := "demo::combined_modular_pipeline"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "bswap_inc" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "pop_val" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32], layoutIdx := 0 }, debugName := some "arg_tup" },
    { mutability := .mut, ty := { kind := .bool, layoutIdx := 0 }, debugName := some "cond" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "doubled_x" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "halved_x" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "final_pair" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_2.._9); _2 = ext::checked_inc::<u32>(_1.0) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .storageLive 6, span := pureAdtSpan },
        { kind := .storageLive 7, span := pureAdtSpan },
        { kind := .storageLive 8, span := pureAdtSpan },
        { kind := .storageLive 9, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "ext::checked_inc" [.uint .u32])
          [.copy { local_ := 1, projection := [.field 0 pureU32Ty] }]
          { local_ := 2, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _3 = core::intrinsics::bswap::<u32>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::bswap" [.uint .u32])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 3, projection := [] }
          (.some 2)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: _5 = (_3,); _4 = const_eval_select((_3,), ctpop::<u32>,
    -- ctpop::<u32>) -> bb3
    { statements := [
        { kind := .assign
            { local_ := 5, projection := [] }
            (.aggregate .tuple [.copy { local_ := 3, projection := [] }])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::const_eval_select" [
            .tuple [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .fnDef "core::intrinsics::ctpop" [.uint .u32],
            .uint .u32
          ])
          [ .copy { local_ := 5, projection := [] },
            fnItemOperand "core::intrinsics::ctpop" [.uint .u32],
            fnItemOperand "core::intrinsics::ctpop" [.uint .u32] ]
          { local_ := 4, projection := [] }
          (.some 3)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: _6 = (_2 == _2); assert(_6 == true) -> bb4
    { statements := [
        { kind := .assign
            { local_ := 6, projection := [] }
            (.binaryOp .eq
              (.copy { local_ := 2, projection := [] })
              (.copy { local_ := 2, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .assert
          (.copy { local_ := 6, projection := [] })
          true
          4
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb4: _7 = _1.0 * 2; _8 = core::intrinsics::exact_div::<u32>(_7, 2) -> bb5
    { statements := [
        { kind := .assign
            { local_ := 7, projection := [] }
            (.binaryOp .mul
              (.copy { local_ := 1, projection := [.field 0 pureU32Ty] })
              (u32ConstOperand 2))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::exact_div" [.uint .u32])
          [.copy { local_ := 7, projection := [] }, u32ConstOperand 2]
          { local_ := 8, projection := [] }
          (.some 5)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb5: _9 = (_4, _8); tailCall demo::poly_swap_pair::<u32>(_9)
    { statements := [
        { kind := .assign
            { local_ := 9, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 4, projection := [] },
              .copy { local_ := 8, projection := [] }
            ])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .tailCall
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 9, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

@[irreducible]
private def bswapScalarU32 (v : Nat) : ScalarInt :=
  ⟨pureBswapLoop 4 v 0, 4⟩

private theorem bswapScalarU32_def (v : Nat) :
    ({ bits := pureBswapLoop 4 v 0, sizeBytes := 4 } : ScalarInt) =
      bswapScalarU32 v := by
  unfold bswapScalarU32
  rfl

private theorem evalConstEvalSelect_ctpop_u32 (v : ScalarInt)
    (hv : isCanonicalScalarOfSize v 4 = true) :
    evalPureRustIntrinsicWithRuntime (fun _ _ _ => none) .constEvalSelect
      [.tuple [.uint .u32],
       .fnDef "core::intrinsics::ctpop" [.uint .u32],
       .fnDef "core::intrinsics::ctpop" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar v], .unit, .unit] 8 true =
      some (.scalar ⟨pureCtpopLoop 32 v.bits, 4⟩) := by
  have h_unp :
      unpackConstEvalSelectWithElemTys?
        [.tuple [.uint .u32],
         .fnDef "core::intrinsics::ctpop" [.uint .u32],
         .fnDef "core::intrinsics::ctpop" [.uint .u32],
         .uint .u32]
        [.aggregate 0 [.scalar v], .unit, .unit] =
      some ([.uint .u32], "core::intrinsics::ctpop", [.uint .u32], [.scalar v]) := rfl
  have h_cls : classifyPureRustIntrinsic? "core::intrinsics::ctpop" = some .ctpop := rfl
  dsimp only [evalPureRustIntrinsicWithRuntime]
  rw [h_unp]
  dsimp only
  rw [h_cls]
  change (if isCanonicalScalarOfSize v 4 then some (Value.scalar ⟨pureCtpopLoop 32 v.bits, 4⟩) else none) = _
  rw [hv]
  rfl

private theorem pureBswapLoop_four_lt (v : Nat) :
    pureBswapLoop 4 v 0 < 4294967296 := by
  have h_step (u a bound : Nat) (ha : a < bound) :
      a * 256 + Nat.mod u 256 < bound * 256 := by
    have hm : Nat.mod u 256 < 256 := Nat.mod_lt u (by decide)
    omega
  dsimp only [pureBswapLoop]
  have h1 := h_step v 0 1 (by decide)
  have h2 := h_step (Nat.div v 256) _ 256 h1
  have h3 := h_step (Nat.div (Nat.div v 256) 256) _ 65536 h2
  exact h_step (Nat.div (Nat.div (Nat.div v 256) 256) 256) _ 16777216 h3

private theorem checkPureMirWithCallees_polySwapPairU32 :
    checkPureMirWithCallees [polySwapPairBody] polySwapPairU32Body 1 [] = true := by
  decide

private theorem combinedModularPipeline_from_bb3
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      { bb := 3
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .init (.scalar { bits := x + 1, sizeBytes := 4 }),
          .init (.scalar (bswapScalarU32 (x + 1))),
          .init (expectedBswapPopU32 (x + 1)),
          .init (.aggregate 0 [.scalar (bswapScalarU32 (x + 1))]),
          .uninit,
          .uninit,
          .uninit,
          .uninit
        ] }
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  -- bb3 stmt 0: _6 = (_2 == _2) (evaluates to bool true = 1)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb3 terminator: assert(_6 == true) -> bb4
  refine PureMirModularConverges.step_assert
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl
    (fun _ => ?_)
    (fun _ => Or.inl rfl)
  -- bb4 stmt 0: _7 = _1.0 * 2
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb4 terminator: inline core::intrinsics::exact_div::<u32>(_7, 2) -> bb5
  refine PureMirModularConverges.call_exact_div
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl
    (evalExactDiv_double_u32 hx) rfl ?_
  -- bb5 stmt 0: _9 = (_4, _8)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb5 terminator: linked polymorphic tailCall demo::poly_swap_pair::<u32>(_9)
  refine PureMirModularConverges.tailCall_summary
    (maxCallDepth := 1)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMirWithCallees_polySwapPairU32
    (PureMirConvergesWithCallees.of_pureMirConverges
      checkPureMir_polySwapPairU32Body
      (polySwapPairU32_pureConverges
        (expectedBswapPopU32 (x + 1))
        (.scalar { bits := x, sizeBytes := 4 })))
    (fun _ h => h)

private theorem combinedModularPipeline_from_bb2
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      { bb := 2
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .init (.scalar { bits := x + 1, sizeBytes := 4 }),
          .init (.scalar (bswapScalarU32 (x + 1))),
          .uninit,
          .uninit,
          .uninit,
          .uninit,
          .uninit,
          .uninit
        ] }
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  -- bb2 stmt 0: _5 = (_3,)
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  -- bb2 terminator: const_eval_select((_3,), ctpop::<u32>, ctpop::<u32>)
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := expectedBswapPopU32 (x + 1))
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (fun m hm => by
      have h_sz_bs : (bswapScalarU32 (x + 1)).sizeBytes = 4 := by
        rw [← bswapScalarU32_def]
      have h_bits_bs : (bswapScalarU32 (x + 1)).bits = pureBswapLoop 4 (x + 1) 0 := by
        rw [← bswapScalarU32_def]
      have h_lt_bs : (bswapScalarU32 (x + 1)).bits < 4294967296 := by
        rw [h_bits_bs]
        exact pureBswapLoop_four_lt (x + 1)
      rw [← expectedBswapPopU32_def (x + 1), ← h_bits_bs]
      exact evalDirectRustIntrinsic_constEvalSelect_ctpop_u32
        _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        (by dsimp only [PureState.toMachineState]; rw [hm.1, hm.2.1]; rfl)
        h_sz_bs h_lt_bs)
    rfl
    (combinedModularPipeline_from_bb3 x y hx)

/--
Compositional modular proof for `combinedModularPipelineBody`, combining
`call_poly_external_spec_sub`, `call_inline_intrinsic` (`bswap` +
`const_eval_select(ctpop)`), `step_assert`, `call_exact_div`, and
`tailCall_summary` in a single caller under `combinedIntrinsicAndExtContract`.
-/
theorem combinedModularPipeline_modularConverges
    (x y : Nat) (hx : x < 2147483648) :
    PureMirModularConverges
      combinedIntrinsicAndExtContract
      combinedModularPipelineBody
      [polySwapPairBody]
      (initPureState combinedModularPipelineBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        expectedBswapPopU32 (x + 1)
      ])
      [] := by
  have hx1_lt : x + 1 < 4294967296 :=
    Nat.lt_trans (Nat.succ_lt_succ hx) (by decide)
  -- bb0: StorageLive(_2.._9)
  have h_init :
      initPureState combinedModularPipelineBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] = {
        bb := 0
        stmtIdx := 0
        env := [
          .uninit,
          .init (.aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ]),
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
        ]
      } := rfl
  rw [h_init]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb0 terminator: ext::checked_inc::<u32>(_1.0) via call_poly_external_spec_sub
  refine PureMirModularConverges.call_poly_external_spec_sub
    (targetDefPath := "ext::checked_inc")
    (expectedTypeArgs := [.uint .u32])
    (sidecarBody := extCheckedIncSidecarBody)
    (extraPre := fun args =>
      ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (extraPost := fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })
    (MirCallContract.Subsumes.combine_right
      defaultPureRustIntrinsicContract extCheckedIncContract)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨⟨x, Nat.lt_trans hx (by decide), rfl⟩, trivial⟩
    ⟨x, Nat.lt_trans hx (by decide), rfl⟩
    (Or.inl rfl)
    ?_
    rfl
  rintro retVal ⟨_, h_ext_post⟩
  have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
    h_ext_post x rfl
  subst h_rv
  refine ⟨_, rfl, ?_⟩
  -- bb1: core::intrinsics::bswap::<u32>(_2) via call_inline_intrinsic
  refine PureMirModularConverges.call_inline_intrinsic
    (retVal := .scalar (bswapScalarU32 (x + 1)))
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    ?_
    rfl
    (combinedModularPipeline_from_bb2 x y hx)
  intro _ _
  rw [← bswapScalarU32_def]
  exact evalDirectRustIntrinsic_bswap_u32 _ _ _ _ _ _ _ _ _ _ hx1_lt

/-- Non-vacuity witness for `combinedModularPipelineBody`'s precondition. -/
theorem combinedModularPipeline_modularPre_nonVacuous :
    NonVacuousStatefulPre
      (fun args mem =>
        (∃ (x y : Nat),
          x < 2147483648 ∧
          args = [
            .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              .scalar { bits := y, sizeBytes := 4 }
            ]
          ]) ∧
        mem.callStack = [] ∧
        (mem.activeCallee = none ∨
         mem.activeCallee = some combinedModularPipelineBody) ∧
        mem.activeProtectors = []) :=
  ⟨[.aggregate 0 [.scalar { bits := 19, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]],
   emptyMemory,
   ⟨19, 3, by decide, rfl⟩,
   rfl, Or.inl rfl, rfl⟩

/--
Audited `ModularVerificationResult` for `combinedModularPipelineBody` against
`combinedIntrinsicAndExtContract.holdsOn`.
-/
theorem verify_combinedModularPipeline :
    ModularVerificationResult
      { body := combinedModularPipelineBody
        callees := [polySwapPairBody]
        envAssumed := combinedIntrinsicAndExtContract.holdsOn
        pre := fun args mem =>
          (∃ (x y : Nat),
            x < 2147483648 ∧
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ]) ∧
          mem.callStack = [] ∧
          (mem.activeCallee = none ∨
           mem.activeCallee = some combinedModularPipelineBody) ∧
          mem.activeProtectors = []
        post := fun args _ retVal _ =>
          ∀ (x y : Nat),
            args = [
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] →
            retVal = .aggregate 0 [
              .scalar { bits := x, sizeBytes := 4 },
              expectedBswapPopU32 (x + 1)
            ] } := by
  refine verifyModularMirWithCallees_of_pureModularExec
    combinedIntrinsicAndExtContract
    combinedModularPipelineBody
    [polySwapPairBody]
    _ _
    (by decide)
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (combinedModularPipeline_modularConverges x y hx)
  intro retVal h_ret _ x' y' h_eq
  rcases pairU32Args_inj h_eq with ⟨rfl, rfl⟩
  exact h_ret

/-!
### 10F. `TraitImplEntry` Dispatch, Multi-Monomorphization (`u32` + `u64`),
Linked `tailCall`, & Computable `evalPureMirWithCallees` Witness
-/

/--
Concrete `u32` trait-method implementation body `demo::u32_step_impl`
(`<u32 as demo::StepTrait>::step`), returning `_1 + 1` (wrapping modulo `2^32`).
-/
def u32StepImplBody : CapturedMir where
  defPath := "demo::u32_step_impl"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.binaryOp .add
              (.copy { local_ := 1, projection := [] })
              (u32ConstOperand 1))
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Registered `TraitImplEntry` associating `<u32 as demo::StepTrait>::step` with
`demo::u32_step_impl`.
-/
def demoStepTraitImpl : TraitImplEntry where
  traitRef := { defPath := "demo::StepTrait::step", args := [.uint .u32] }
  implPath := "demo::u32_step_impl"

theorem checkPureMir_u32StepImplBody : checkPureMir u32StepImplBody = true := by
  decide

theorem u32StepImpl_pureConverges (x : Nat) :
    PureMirConverges u32StepImplBody
      (initPureState u32StepImplBody [.scalar { bits := x, sizeBytes := 4 }])
      (· = .scalar { bits := wrapScalarBits (Nat.add x 1) (scalarModulus 4), sizeBytes := 4 }) :=
  ⟨4, rfl⟩

/--
Layout table supporting both `(u32, u32)` and `(u64, u64)` pairs in a single
caller (`[u32Layout, pairU32Layout, u64Layout, pairU64Layout]`).
-/
def multiMonoCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout, u64Layout, pairU64Layout]

/--
Caller `demo::trait_and_tail_multi_mono_caller` (`argCount := 2`,
`_1 : (u32, u32) = (x, y)`, `_2 : (u64, u64) = (z, w)`, with
`traitImpls := [demoStepTraitImpl]`):
- `bb0`: calls `demo::poly_swap_pair::<u32>(_1)` -> `_3 = (y, x)`.
- `bb1`: calls `demo::poly_swap_pair::<u64>(_2)` -> `_4 = (w, z)` (second
  monomorphization of `polySwapPairBody` in the same caller!).
- `bb2`: dispatches trait method `demo::StepTrait::step::<u32>(_3.1)` via
  `TraitImplEntry` (`demoStepTraitImpl` -> `demo::u32_step_impl`) -> `_5 =
  (x + 1) % 2^32`.
- `bb3`: executes `TerminatorKind.tailCall` to trait method
  `demo::StepTrait::step::<u32>(_5)` -> `((x + 1) % 2^32 + 1) % 2^32`.
-/
def traitAndTailMultiMonoCallerBody : CapturedMir where
  defPath := "demo::trait_and_tail_multi_mono_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair32" },
    { mutability := .not, ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 3 }, debugName := some "pair64" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "sw32" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 3 }, debugName := some "sw64" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "step1" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_3, _4, _5); _3 = demo::poly_swap_pair::<u32>(_1) -> bb1
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u32])
          [.copy { local_ := 1, projection := [] }]
          { local_ := 3, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _4 = demo::poly_swap_pair::<u64>(_2) -> bb2
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::poly_swap_pair" [.uint .u64])
          [.copy { local_ := 2, projection := [] }]
          { local_ := 4, projection := [] }
          (.some 2)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: _5 = <u32 as demo::StepTrait>::step(_3.1) -> bb3
    { statements := []
      terminator := {
        kind := .call
          (fnItemOperand "demo::StepTrait::step" [.uint .u32])
          [.copy { local_ := 3, projection := [.field 1 pureU32Ty] }]
          { local_ := 5, projection := [] }
          (.some 3)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: tailCall <u32 as demo::StepTrait>::step(_5)
    { statements := []
      terminator := {
        kind := .tailCall
          (fnItemOperand "demo::StepTrait::step" [.uint .u32])
          [.copy { local_ := 5, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := pairU32Layout, mode := .direct },
      { layout := pairU64Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := multiMonoCallerLayouts
  allocations := []
  traitImpls := [demoStepTraitImpl]

def traitMultiMonoCallees : List CapturedMir :=
  [polySwapPairBody, u32StepImplBody]

theorem checkPureMirWithCallees_traitAndTailMultiMono :
    checkPureMirWithCallees traitMultiMonoCallees
      traitAndTailMultiMonoCallerBody 2 [demoStepTraitImpl] = true := by
  decide

/--
Compositional 4-step proof of `traitAndTailMultiMonoCallerBody` exercising
`u32` + `u64` multi-monomorphization of `polySwapPairBody`, `TraitImplEntry`
dispatch (`<u32 as demo::StepTrait>::step -> demo::u32_step_impl`), and
`PureMirConverges.tailCall_leaf_summary`.
-/
theorem traitAndTailMultiMonoCaller_compositional (x y z w : Nat) :
    PureMirConvergesWithCallees traitAndTailMultiMonoCallerBody
      traitMultiMonoCallees
      (initPureState traitAndTailMultiMonoCallerBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate 0 [
          .scalar { bits := z, sizeBytes := 8 },
          .scalar { bits := w, sizeBytes := 8 }
        ]
      ])
      (· = .scalar {
        bits := wrapScalarBits
          (Nat.add (wrapScalarBits (Nat.add x 1) (scalarModulus 4)) 1)
          (scalarModulus 4)
        sizeBytes := 4
      })
      [demoStepTraitImpl] := by
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  -- 1. demo::poly_swap_pair::<u32>(_1)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 2. demo::poly_swap_pair::<u64>(_2)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU64Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU64Body
    (polySwapPairU64_pureConverges
      (.scalar { bits := z, sizeBytes := 8 })
      (.scalar { bits := w, sizeBytes := 8 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 3. TraitImplEntry dispatch <u32 as demo::StepTrait>::step(_3.1)
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := u32StepImplBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_u32StepImplBody
    (u32StepImpl_pureConverges x)
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- 4. TraitImplEntry tailCall <u32 as demo::StepTrait>::step(_5)
  exact PureMirConverges.tailCall_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := u32StepImplBody)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_u32StepImplBody
    (u32StepImpl_pureConverges (wrapScalarBits (Nat.add x 1) (scalarModulus 4)))
    (fun _ h => h)

/--
Zero-step computable evaluation witness for `traitAndTailMultiMonoCallerBody`
via `pureMirConvergesWithCallees_of_evalPureMirWithCallees` (`x = 40` -> `42`).
-/
theorem traitAndTailMultiMonoCaller_evalConcrete :
    PureMirConvergesWithCallees traitAndTailMultiMonoCallerBody
      traitMultiMonoCallees
      (initPureState traitAndTailMultiMonoCallerBody [
        .aggregate 0 [
          .scalar { bits := 40, sizeBytes := 4 },
          .scalar { bits := 7, sizeBytes := 4 }
        ],
        .aggregate 0 [
          .scalar { bits := 100, sizeBytes := 8 },
          .scalar { bits := 200, sizeBytes := 8 }
        ]
      ])
      (· = .scalar { bits := 42, sizeBytes := 4 })
      [demoStepTraitImpl] :=
  pureMirConvergesWithCallees_of_evalPureMirWithCallees
    checkPureMirWithCallees_traitAndTailMultiMono
    (fuel := 32)
    rfl

/-!
### 10G. Higher-Order Local Zero-Sized Function-Item & Callee-Backed
`const_eval_select` + Diverging Panic + External Intrinsic `tailCall` Witnesses
-/

/-- Zero-sized layout (`0` bytes) for function-item types (`RigidTy.fnDef`). -/
def zstFnItemLayout : TypeLayout :=
  Option.getD
    (RigidTy.computeLayout 64 [] [] none (.fnDef "demo::poly_swap_pair" [.uint .u32]))
    u32Layout

/-- Function-item `Ty` for `demo::poly_swap_pair::<u32>` at layout slot `2`. -/
def polySwapU32FnItemTy : Ty :=
  { kind := .fnDef "demo::poly_swap_pair" [.uint .u32], layoutIdx := 2 }

/--
Caller layout table `[u32Layout, pairU32Layout, zstFnItemLayout]` supporting
`u32`, `(u32, u32)`, and zero-sized `fnDef` local variables.
-/
def higherOrderCallerLayouts : LayoutTable where
  pointerBits := 64
  isLittleEndian := true
  entries := [u32Layout, pairU32Layout, zstFnItemLayout]

/--
Higher-order caller `demo::higher_order_fn_item_caller` (`argCount := 2`):
- `_1` has zero-sized function-item type `RigidTy.fnDef "demo::poly_swap_pair"
  [.uint .u32]` (`Value.unit`),
- `_2` has type `(u32, u32)`,
- `bb0` copies `_1` into local `_3` and invokes `TerminatorKind.call` via
  `Operand.move _3` (`extractCalleeDefPath? = none`!), writing `_4 = (y, x)`,
- `bb1` invokes `TerminatorKind.tailCall` via `Operand.copy _1`
  (`extractCalleeDefPath? = none`!), returning `(x, y)`.
-/
def higherOrderFnItemCallerBody : CapturedMir where
  defPath := "demo::higher_order_fn_item_caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "_0" },
    { mutability := .not, ty := polySwapU32FnItemTy, debugName := some "f" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := polySwapU32FnItemTy, debugName := some "f_local" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_3); StorageLive(_4); _3 = Copy(_1);
    --      _4 = (Move(_3))(_2) -> bb1
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.use (.copy { local_ := 1, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (.move { local_ := 3, projection := [] })
          [.copy { local_ := 2, projection := [] }]
          { local_ := 4, projection := [] }
          (.some 1)
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: tailcall (Copy(_1))(_4)
    { statements := []
      terminator := {
        kind := .tailCall
          (.copy { local_ := 1, projection := [] })
          [.copy { local_ := 4, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := pairU32Layout, mode := .direct }
    ]
    ret := { layout := pairU32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
`checkPureMirWithCallees` accepts `higherOrderFnItemCallerBody` at `maxCallDepth =
2` even though both `call` and `tailCall` invoke local `Operand.move` /
`Operand.copy` function-item slots (`extractCalleeDefPath? = none`).
-/
theorem checkPureMirWithCallees_higherOrderFnItemCaller :
    checkPureMirWithCallees [polySwapPairBody] higherOrderFnItemCallerBody 2 [] =
      true := by
  decide

/--
Symbolic compositional proof for `higherOrderFnItemCallerBody` across all
`x y : Nat`, discharging the `Operand.move _3` call via
`PureMirConverges.call_leaf_summary` and the `Operand.copy _1` tail call via
`PureMirConverges.tailCall_leaf_summary`.
-/
theorem higherOrderFnItemCaller_compositional (x y : Nat) :
    PureMirConvergesWithCallees higherOrderFnItemCallerBody [polySwapPairBody]
      (initPureState higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := x, sizeBytes := 4 },
        .scalar { bits := y, sizeBytes := 4 }
      ])
      [] := by
  -- bb0: StorageLive(_3), StorageLive(_4), _3 = Copy(_1)
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  refine PureMirConvergesWithCallees.step ⟨rfl, ?_⟩
  -- bb0 terminator: (Move(_3))(_2) -> polySwapPairU32Body
  refine PureMirConverges.call_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := x, sizeBytes := 4 })
      (.scalar { bits := y, sizeBytes := 4 }))
    ?_
  rintro _ rfl
  refine ⟨_, rfl, ?_⟩
  -- bb1 terminator: tailCall (Copy(_1))(_4) -> polySwapPairU32Body
  exact PureMirConverges.tailCall_leaf_summary
    (maxCallDepth := 2)
    (calleeBody := polySwapPairU32Body)
    (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl
    checkPureMir_polySwapPairU32Body
    (polySwapPairU32_pureConverges
      (.scalar { bits := y, sizeBytes := 4 })
      (.scalar { bits := x, sizeBytes := 4 }))
    (fun _ h => h)

/--
Operational `MirWpConverges` witness on `initMachineStateWithCallees` for
`higherOrderFnItemCallerBody`.
-/
theorem higherOrderFnItemCaller_mirWpConverges (x y : Nat) :
    MirWpConverges higherOrderFnItemCallerBody
      (initMachineStateWithCallees higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ]
      ] [polySwapPairBody])
      (mirNormalPost
        (fun retVal mem' =>
          ActiveRootMemory higherOrderFnItemCallerBody
            (initMachineStateWithCallees higherOrderFnItemCallerBody [
              .unit,
              .aggregate 0 [
                .scalar { bits := x, sizeBytes := 4 },
                .scalar { bits := y, sizeBytes := 4 }
              ]
            ] [polySwapPairBody]).memory mem' ∧
          retVal = .aggregate 0 [
            .scalar { bits := x, sizeBytes := 4 },
            .scalar { bits := y, sizeBytes := 4 }
          ])) :=
  mirWpConverges_of_pureExecWithCallees_init
    checkPureMirWithCallees_higherOrderFnItemCaller
    (higherOrderFnItemCaller_compositional x y)

/--
Zero-step concrete evaluation witness for `higherOrderFnItemCallerBody` via
`pureMirConvergesWithCallees_of_evalPureMirWithCallees`.
-/
theorem higherOrderFnItemCaller_evalConcrete :
    PureMirConvergesWithCallees higherOrderFnItemCallerBody [polySwapPairBody]
      (initPureState higherOrderFnItemCallerBody [
        .unit,
        .aggregate 0 [
          .scalar { bits := 17, sizeBytes := 4 },
          .scalar { bits := 99, sizeBytes := 4 }
        ]
      ])
      (· = .aggregate 0 [
        .scalar { bits := 17, sizeBytes := 4 },
        .scalar { bits := 99, sizeBytes := 4 }
      ])
      [] :=
  pureMirConvergesWithCallees_of_evalPureMirWithCallees
    checkPureMirWithCallees_higherOrderFnItemCaller
    (fuel := 16)
    rfl

/--
Modular caller `demo::callee_const_eval_and_intrinsic_tail` (`argCount := 1`):
- Input `_1 : (u32, u32) = (x, y)`.
- `bb0`: invokes `core::intrinsics::const_eval_select` selecting polymorphic
  Rust helper `demo::poly_swap_pair::<u32>` on `(_1,)` (unpacked via `((u32,
  u32),)` 1-tuple), evaluated through `calleeRuntimeEval` -> `_3 = (y, x)`.
- `bb1`: `switchInt(_3.0)` (testing whether `y == 0`):
  - `y == 0` (`bb2`): invokes diverging `core::panicking::panic` (`target =
    .none`, `unwind = .continue_`), discharged via `call_diverging_panic`.
  - `y != 0` (`bb3`): invokes external `TerminatorKind.tailCall` to
    `core::intrinsics::ctpop::<u32>(_3.0)`, discharged via
    `tailCall_intrinsic_sub`.
-/
def calleeBackedConstEvalAndIntrinsicTailBody : CapturedMir where
  defPath := "demo::callee_const_eval_and_intrinsic_tail"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "pair" },
    { mutability := .mut, ty := { kind := .tuple [.tuple [.uint .u32, .uint .u32]], layoutIdx := 1 }, debugName := some "arg_tup" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 1 }, debugName := some "swapped" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "first" },
    { mutability := .mut, ty := { kind := .never, layoutIdx := 2 }, debugName := some "never_dst" }
  ]
  basicBlocks := [
    -- bb0: _2 = (_1,); _3 = const_eval_select(_2, poly_swap_pair::<u32>,
    --      poly_swap_pair::<u32>) -> bb1
    { statements := [
        { kind := .storageLive 2, span := pureAdtSpan },
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .assign
            { local_ := 2, projection := [] }
            (.aggregate .tuple [.copy { local_ := 1, projection := [] }])
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::intrinsics::const_eval_select" [
            .tuple [.tuple [.uint .u32, .uint .u32]],
            .fnDef "demo::poly_swap_pair" [.uint .u32],
            .fnDef "demo::poly_swap_pair" [.uint .u32],
            .tuple [.uint .u32, .uint .u32]
          ])
          [
            .copy { local_ := 2, projection := [] },
            fnItemOperand "demo::poly_swap_pair" [.uint .u32],
            fnItemOperand "demo::poly_swap_pair" [.uint .u32]
          ]
          { local_ := 3, projection := [] }
          (.some 1)
          .unreachable
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: _4 = Copy(_3.0); switchInt(_4) [0 -> bb2, otherwise -> bb3]
    { statements := [
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 0 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .switchInt
          (.copy { local_ := 4, projection := [] })
          { branches := [(0, 2)], otherwise := 3 }
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2: diverging panic guard core::panicking::panic() -> !
    { statements := [
        { kind := .storageLive 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (fnItemOperand "core::panicking::panic" [])
          []
          { local_ := 5, projection := [] }
          .none
          .continue_
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb3: external intrinsic tailCall core::intrinsics::ctpop::<u32>(_4)
    { statements := []
      terminator := {
        kind := .tailCall
          (fnItemOperand "core::intrinsics::ctpop" [.uint .u32])
          [.copy { local_ := 4, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Combined modular contract pairing `calleeRuntimeEval` over `[polySwapPairBody]`
inside `pureRustIntrinsicContract` with `extCheckedIncContract`.
-/
def calleeBackedModularContract : MirCallContract :=
  combineMirCallContracts
    (pureRustIntrinsicContract 8 true
      (calleeRuntimeEval 16 [polySwapPairBody] higherOrderCallerLayouts [] 2))
    extCheckedIncContract

/--
Precondition for `calleeBackedConstEvalAndIntrinsicTailBody` on concrete pair
`(7, 0x0F0F0005)` (where swapped first element `y = 0x0F0F0005` has popcount
`10`), plus arbitrary `(x, 0)` exercising the diverging `panic` branch.
-/
def calleeBackedModularPre (args : List Value) (mem : Memory) : Prop :=
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨
    mem.activeCallee = some calleeBackedConstEvalAndIntrinsicTailBody) ∧
  mem.activeProtectors = [] ∧
  ((args = [.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
    ]]) ∨
   (args = [.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0, sizeBytes := 4 }
    ]]))

/-- Non-vacuity witness for `calleeBackedModularPre`. -/
theorem calleeBackedConstEval_modularPre_nonVacuous :
    NonVacuousStatefulPre calleeBackedModularPre :=
  ⟨[.aggregate 0 [
      .scalar { bits := 7, sizeBytes := 4 },
      .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
    ]],
   emptyMemory,
   ⟨rfl, Or.inl rfl, rfl, Or.inl rfl⟩⟩

/--
End-to-end audited `ModularVerificationResult` certificate via
`verifyModularMir_of_pureModularExec_any` exercising:
1. `calleeRuntimeEval` inside `const_eval_select` resolving polymorphic
   `demo::poly_swap_pair::<u32>`,
2. `PureMirModularConverges.step_switchInt`,
3. `PureMirModularConverges.call_diverging_panic` on the `y = 0` guard branch,
4. `PureMirModularConverges.tailCall_intrinsic_sub` (`ctpop::<u32>`) on the
   `y = 0x0F0F0005` branch (returning popcount `10`).
-/
theorem verify_calleeBackedConstEvalAndIntrinsicTail :
    ModularVerificationResult
      { body := calleeBackedConstEvalAndIntrinsicTailBody
        envAssumed := calleeBackedModularContract.holdsOn
        pre := calleeBackedModularPre
        post := fun args _ retVal _ =>
          args = [.aggregate 0 [
            .scalar { bits := 7, sizeBytes := 4 },
            .scalar { bits := 0x0F0F0005, sizeBytes := 4 }
          ]] →
          retVal = .scalar { bits := 10, sizeBytes := 4 }
        callees := [polySwapPairBody] } := by
  refine verifyModularMir_of_pureModularExec_any
    calleeBackedModularContract _ rfl (Or.inl (by decide))
    (fun _ _ hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun args _ hp => ?_)
  simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  rcases hp.2.2.2 with rfl | rfl
  · -- Case 1: y = 0x0F0F0005 -> const_eval_select -> switchInt -> tailCall ctpop = 10
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.call_const_eval_select_summary
      (maxCallDepth := 1)
      (calleeBody := polySwapPairU32Body)
      (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl (by decide)
      rfl rfl rfl (fun _ _ => rfl) rfl rfl (by decide)
      (PureMirConvergesWithCallees.of_pureMirConverges
        checkPureMir_polySwapPairU32Body
        (polySwapPairU32_pureConverges
          (.scalar { bits := 7, sizeBytes := 4 })
          (.scalar { bits := 0x0F0F0005, sizeBytes := 4 })))
      ?_
    rintro _ rfl
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_switchInt
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl ?_
    exact PureMirModularConverges.tailCall_intrinsic_sub
      (MirCallContract.Subsumes.combine_left _ _)
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ => rfl)
  · -- Case 2: y = 0 -> const_eval_select -> switchInt -> diverging panic guard
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.call_const_eval_select_summary
      (maxCallDepth := 1)
      (calleeBody := polySwapPairU32Body)
      (fun _ h => nomatch h) rfl rfl rfl (by decide) rfl rfl rfl rfl (by decide)
      rfl rfl rfl (fun _ _ => rfl) rfl rfl (by decide)
      (PureMirConvergesWithCallees.of_pureMirConverges
        checkPureMir_polySwapPairU32Body
        (polySwapPairU32_pureConverges
          (.scalar { bits := 7, sizeBytes := 4 })
          (.scalar { bits := 0, sizeBytes := 4 })))
      ?_
    rintro _ rfl
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    refine PureMirModularConverges.step_switchInt
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl ?_
    refine PureMirModularConverges.step_stmt
      (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
    exact PureMirModularConverges.call_diverging_panic
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl
      (Or.inr ⟨rfl, Or.inl rfl⟩)

/-!
### 10H. Capture-Free Closure & Arity-Validated `const_eval_select` +
Higher-Order Modular `fnDef` & `.cleanup` Unwind Landing-Pad Witnesses
-/

/--
Capture-free closure body `demo::closure_first` (`|x: u32, _y: u32| -> u32 { x }`,
`argCount := 3`):
- `_1` is the zero-sized closure environment `RigidTy.closure "demo::closure_first" []`
  (`Value.unit`),
- `_2` is parameter `x : u32`,
- `_3` is parameter `y : u32`,
- `bb0` returns `Copy(_2)` (`x`), distinguishing exact `(.unit :: unpackedArgs)`
  closure frame layout from off-by-one `unpackedArgs` misalignment.
-/
def captureFreeFirstClosureBody : CapturedMir where
  defPath := "demo::closure_first"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not,
      ty := { kind := .closure "demo::closure_first" [], layoutIdx := 2 },
      debugName := some "_env" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .not, ty := pureU32Ty, debugName := some "y" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 2, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := u32Layout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Kernel-checked regression witnesses for `const_eval_select` + `calleeRuntimeEval`:
1. Invoking capture-free closure `captureFreeFirstClosureBody` on `(10, 99)`
   prepends `Value.unit` for `_1` and returns `10` (`_2`), not `99` (`_3`).
2. Capturing closures (`upvars ≠ []`) are rejected (`none`) by
   `extractZeroSizedCallableTy?` ( both as `rtFnTy` and as `constFnTy`).
3. Arity-mismatched `const_eval_select` calls (e.g., passing a 2-element tuple
   to 1-parameter `u32StepImplBody`) fail closed (`none`) instead of corrupting
   temporary locals.
-/
theorem constEvalSelect_closure_and_arity_witnesses :
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_first" [],
       .closure "demo::closure_first" [],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] =
      some (.scalar ⟨10, 4⟩) ∧
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .fnDef "demo::ct_first" [],
       .closure "demo::closure_first" [.uint .u32],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] = none ∧
    evalPureRustIntrinsicWithRuntime
      (calleeRuntimeEval 8 [captureFreeFirstClosureBody] higherOrderCallerLayouts [] 1)
      .constEvalSelect
      [.tuple [.uint .u32, .uint .u32],
       .tuple [],
       .closure "demo::closure_first" [],
       .uint .u32]
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩], .unit, .unit] = none ∧
    calleeRuntimeEval 8 [u32StepImplBody] demoCallerLayouts [] 1
      "demo::u32_step_impl" [] [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Operational `MirWpConverges` soundness certificate for `calleeRuntimeEval` on
capture-free closure `captureFreeFirstClosureBody` via `calleeRuntimeEval_sound`.
-/
theorem captureFreeFirstClosure_calleeRuntimeEval_sound :
    ∃ (calleeBody : CapturedMir) (callArgs : List Value),
      lookupCallee [captureFreeFirstClosureBody] higherOrderCallerLayouts
        "demo::closure_first" [] [] = some calleeBody ∧
      effectiveConstEvalCalleeArgs? calleeBody
        [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] = some callArgs ∧
      MirWpConverges calleeBody
        (initMachineStateWithMemory calleeBody callArgs
          (pureCalleeMemory [captureFreeFirstClosureBody] []))
        (mirNormalPost
          (fun rv mem' =>
            ActiveRootMemory calleeBody
              (pureCalleeMemory [captureFreeFirstClosureBody] []) mem' ∧
            rv = .scalar ⟨10, 4⟩)) :=
  calleeRuntimeEval_sound (fuel := 8) (maxCallDepth := 1)
    (mem₀ := pureCalleeMemory [captureFreeFirstClosureBody] []) rfl

/--
Unwinding `#[external_spec]` sidecar stub `ext::unwinding_inc<T>(x: u32) -> u32`
with `fnAbi.canUnwind := true` (`sidecarTargetCanUnwind = true`), so callers
passing `unwind = .cleanup cleanupBb` must genuinely prove cleanup landing-pad
convergence.
-/
def extUnwindingIncSidecarBody : CapturedMir where
  defPath := "ext::unwinding_inc_spec"
  phase := .runtimePostCleanup
  role := .externalSpec "ext::unwinding_inc"
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" }
  ]
  basicBlocks := [
    { statements := []
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false }
  ]
  fnAbi := {
    args := [{ layout := u32Layout, mode := .direct }]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := demoCallerLayouts
  allocations := []

/--
Polymorphic unwinding `#[external_spec]` contract for `ext::unwinding_inc::<u32>`:
requires `x < 2^32 - 1` and returns `x + 1` on normal return, while permitting
frame-preserving panics (`sidecarTargetCanUnwind = true`).
-/
def extUnwindingIncContract : MirCallContract :=
  polyExternalSpecCallContract
    "ext::unwinding_inc"
    [.uint .u32]
    extUnwindingIncSidecarBody
    (fun args => ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })

/-- Zero-sized function-item `Ty` for `ext::unwinding_inc::<u32>`. -/
def extUnwindingIncU32FnTy : Ty :=
  { kind := .fnDef "ext::unwinding_inc" [.uint .u32], layoutIdx := 2 }

/-- Zero-sized function-item `Ty` for `core::intrinsics::ctpop::<u32>`. -/
def ctpopU32FnTy : Ty :=
  { kind := .fnDef "core::intrinsics::ctpop" [.uint .u32], layoutIdx := 2 }

/--
Combined modular contract pairing `defaultPureRustIntrinsicContract` with
unwinding `extUnwindingIncContract`.
-/
def localFnItemAndCleanupContract : MirCallContract :=
  combineMirCallContracts
    defaultPureRustIntrinsicContract
    extUnwindingIncContract

/--
Higher-order modular caller `demo::local_fn_item_and_cleanup_modular`
(`argCount := 3`, `_1 : u32`, `_2 : fnDef("ext::unwinding_inc", [u32])`,
`_3 : fnDef("core::intrinsics::ctpop", [u32])`):
- `bb0`: copies `_1` into `_4` and calls `(Move(_2))(_4)` (`Operand.move` local
  `fnDef` slot!) with `unwind := .cleanup 2`.
- `bb1`: on normal return `_5 = x + 1`, tail-calls `(Copy(_3))(_5)`
  (`Operand.copy` local intrinsic `fnDef` slot!), returning `ctpop::<u32>(x + 1)`.
- `bb2` (`isCleanup := true`): on unwind from `ext::unwinding_inc`, runs
  `StorageDead(_5)` and `drop(_4) -> bb3`.
- `bb3` (`isCleanup := true`): runs `StorageDead(_4)` and `unwindResume`.
-/
def localFnItemAndCleanupModularBody : CapturedMir where
  defPath := "demo::local_fn_item_and_cleanup_modular"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 3
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := pureU32Ty, debugName := some "x" },
    { mutability := .mut, ty := extUnwindingIncU32FnTy, debugName := some "ext_f" },
    { mutability := .not, ty := ctpopU32FnTy, debugName := some "intr_f" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "guard_tmp" },
    { mutability := .mut, ty := pureU32Ty, debugName := some "inc_out" }
  ]
  basicBlocks := [
    -- bb0: StorageLive(_4, _5); _4 = Copy(_1);
    --      _5 = (Move(_2))(_4) -> [return: bb1, unwind: cleanup(bb2)]
    { statements := [
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .storageLive 5, span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.use (.copy { local_ := 1, projection := [] }))
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .call
          (.move { local_ := 2, projection := [] })
          [.copy { local_ := 4, projection := [] }]
          { local_ := 5, projection := [] }
          (.some 1)
          (.cleanup 2)
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: tailcall (Copy(_3))(_5)
    { statements := []
      terminator := {
        kind := .tailCall
          (.copy { local_ := 3, projection := [] })
          [.copy { local_ := 5, projection := [] }]
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb2 (cleanup): StorageDead(_5); drop(_4) -> [return: bb3, unwind: terminate]
    { statements := [
        { kind := .storageDead 5, span := pureAdtSpan }
      ]
      terminator := {
        kind := .drop
          { local_ := 4, projection := [] }
          3
          .terminate
        span := pureAdtSpan
      }
      isCleanup := true
    },
    -- bb3 (cleanup): StorageDead(_4); unwindResume
    { statements := [
        { kind := .storageDead 4, span := pureAdtSpan }
      ]
      terminator := {
        kind := .unwindResume
        span := pureAdtSpan
      }
      isCleanup := true
    }
  ]
  fnAbi := {
    args := [
      { layout := u32Layout, mode := .direct },
      { layout := zstFnItemLayout, mode := .ignore },
      { layout := zstFnItemLayout, mode := .ignore }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := higherOrderCallerLayouts
  allocations := []

/--
Precondition for `localFnItemAndCleanupModularBody` over all `x < 2^32 - 1` and
unconstrained `mem.traitImpls` (with `mem.callees = []`).
-/
def localFnItemAndCleanupPre (args : List Value) (mem : Memory) : Prop :=
  (∃ x : Nat,
    x < 4294967295 ∧
    args = [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit]) ∧
  mem.callees = [] ∧
  mem.callStack = [] ∧
  (mem.activeCallee = none ∨
    mem.activeCallee = some localFnItemAndCleanupModularBody) ∧
  mem.activeProtectors = []

/-- Non-vacuity witness for `localFnItemAndCleanupPre`. -/
theorem localFnItemAndCleanup_modularPre_nonVacuous :
    NonVacuousStatefulPre localFnItemAndCleanupPre :=
  ⟨[.scalar { bits := 41, sizeBytes := 4 }, .unit, .unit],
   emptyMemory,
   ⟨41, by decide, rfl⟩,
   rfl, rfl, Or.inl rfl, rfl⟩

@[irreducible]
def expectedCtpopU32 (v : Nat) : Value := .scalar ⟨pureCtpopLoop 32 v, 4⟩

private theorem expectedCtpopU32_def (v : Nat) :
    (Value.scalar ⟨pureCtpopLoop 32 v, 4⟩) = expectedCtpopU32 v := by
  unfold expectedCtpopU32
  rfl

/--
Symbolic modular convergence across all `x < 2^32 - 1` and arbitrary
`traitImpls` for `localFnItemAndCleanupModularBody`, exercising:
1. `PureMirModularConverges.call_poly_external_spec_pureTarget` on `Operand.move
   _2` (`_2` becomes `.uninit`) with `unwind = .cleanup 2`,
2. Cleanup landing-pad recovery in `bb2 -> bb3` via `step_stmt` + `step_drop` +
   `step_unwindResume`,
3. `PureMirModularConverges.tailCall_intrinsic_pureTarget` on `Operand.copy _3`
   (`ctpop::<u32>(x + 1)`).
-/
theorem localFnItemAndCleanup_modularConverges
    (x : Nat) (hx : x < 4294967295)
    (traitImpls : List TraitImplEntry := []) :
    PureMirModularConverges
      localFnItemAndCleanupContract
      localFnItemAndCleanupModularBody
      []
      (initPureState localFnItemAndCleanupModularBody
        [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit])
      (· = expectedCtpopU32 (x + 1))
      traitImpls := by
  have hx1_lt : x + 1 < 4294967296 := Nat.succ_lt_succ hx
  have h_canon_x1 :
      isCanonicalScalarOfSize { bits := x + 1, sizeBytes := 4 } 4 = true :=
    isCanonicalScalarOfSize_four hx1_lt
  -- bb0: StorageLive(_4), StorageLive(_5), _4 = Copy(_1)
  have h_init :
      initPureState localFnItemAndCleanupModularBody
        [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit] =
        { bb := 0
          stmtIdx := 0
          env := [.uninit, .init (.scalar { bits := x, sizeBytes := 4 }),
            .init .unit, .init .unit, .dead, .dead] } := rfl
  rw [h_init]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
  dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set, Nat.add]
  -- bb0 terminator: (Move(_2))(_4) -> [return: bb1, unwind: cleanup(bb2)]
  refine PureMirModularConverges.call_poly_external_spec_pureTarget
    (targetDefPath := "ext::unwinding_inc")
    (expectedTypeArgs := [.uint .u32])
    (sidecarBody := extUnwindingIncSidecarBody)
    (extraPre := fun args =>
      ∃ x : Nat, x < 4294967295 ∧ args = [.scalar { bits := x, sizeBytes := 4 }])
    (extraPost := fun args retVal =>
      ∀ x : Nat,
        args = [.scalar { bits := x, sizeBytes := 4 }] →
        retVal = .scalar { bits := x + 1, sizeBytes := 4 })
    (MirCallContract.Subsumes.combine_right
      defaultPureRustIntrinsicContract extUnwindingIncContract)
    (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl rfl
    (lookupCallee_nil _ _ _ _)
    rfl rfl
    ⟨⟨x, Nat.lt_trans hx (by decide), rfl⟩, trivial⟩
    ⟨x, hx, rfl⟩
    (Or.inr (Or.inr (Or.inr ⟨2, rfl, ?_⟩)))
    ?_
    rfl
  · -- Cleanup landing pad bb2 -> bb3: StorageDead(_5), drop(_4), StorageDead(_4), unwindResume
    refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set]
    refine PureMirModularConverges.step_drop (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    refine PureMirModularConverges.step_stmt (fun _ h => nomatch h) rfl rfl rfl rfl ?_
    dsimp only [PureState.ofMachineState, PureState.toMachineState, advanceStmt, set?, List.set]
    exact PureMirModularConverges.step_unwindResume
      (fun _ h => nomatch h) rfl rfl rfl
  · -- Normal return path bb1: tailCall (Copy(_3))(_5) -> ctpop::<u32>(x + 1)
    rintro retVal ⟨_, h_ext_post⟩
    have h_rv : retVal = .scalar { bits := x + 1, sizeBytes := 4 } :=
      h_ext_post x rfl
    subst h_rv
    refine ⟨_, rfl, ?_⟩
    refine PureMirModularConverges.tailCall_intrinsic_pureTarget
      (pointerBytes := 8)
      (ubChecksEnabled := true)
      (rtEval := fun _ _ _ => none)
      (kind := .ctpop)
      (retVal := expectedCtpopU32 (x + 1))
      (MirCallContract.Subsumes.combine_left
        defaultPureRustIntrinsicContract extUnwindingIncContract)
      (fun _ h => nomatch h) rfl rfl rfl rfl rfl rfl rfl
      (lookupCallee_nil _ _ _ _)
      rfl
      ?_
      rfl
    dsimp only [evalPureRustIntrinsicWithRuntime, evalPureScalarIntrinsic,
      intrinsicScalarTyInfo?]
    rw [h_canon_x1]
    exact congrArg some (expectedCtpopU32_def (x + 1))

/--
Audited `ModularVerificationResult` for `localFnItemAndCleanupModularBody` via
`verifyModularMir_of_pureModularExec_any` with `callees = []` and unconstrained
`mem.traitImpls`.
-/
theorem verify_localFnItemAndCleanupModular :
    ModularVerificationResult
      { body := localFnItemAndCleanupModularBody
        envAssumed := localFnItemAndCleanupContract.holdsOn
        pre := localFnItemAndCleanupPre
        post := fun args _ retVal _ =>
          ∀ x : Nat,
            args = [.scalar { bits := x, sizeBytes := 4 }, .unit, .unit] →
            retVal = expectedCtpopU32 (x + 1)
        callees := [] } := by
  refine verifyModularMir_of_pureModularExec_any
    localFnItemAndCleanupContract _ rfl
    (Or.inr (fun _ _ hp => hp.2.1))
    (fun _ _ hp => hp.2.2)
    (fun args mem hp => ?_)
  rcases hp.1 with ⟨x, hx, rfl⟩
  refine PureMirModularConverges.mono ?_
    (localFnItemAndCleanup_modularConverges x hx mem.traitImpls)
  intro retVal h_ret _ x' h_eq
  injection h_eq with h_hd _
  injection h_hd with h_sc
  injection h_sc with hx_eq _
  subst hx_eq
  exact h_ret

end Anneal.PureMirExec
