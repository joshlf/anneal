-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Attributes
import Trusted.Refinement
import Trusted.StepResult
import Trusted.MirAst

/-!
# Trusted MIR Operational Semantics (`Trusted/MirSemantics.lean`)

This module defines the small-step operational semantics `MirSem` for the
minimal MIR fragment (`Trusted/MirAst.lean`).

Every declaration in this file that models a Rust execution rule explains the
correspondence and both quotes and cites the normative Rust Reference or `rustc`
documentation at the repository's pinned revisions
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

This module belongs to `trusted/lean/` and contains only definitions and
structures (zero theorems). All proofs (`TotalStep`, `InhabitedDemonic`,
adequacy canaries, and `id` verification lemmas) live in
`theory/Anneal/MirLemmas.lean`.
-/

namespace Trusted

/-- Instantaneous execution state of a `MirBody`, recording the contents of
    each local slot (`none` when uninitialized or deallocated, `some v` when
    holding an initialized `MirVal`), the active basic block index, and the
    statement index within that basic block. -/
@[candidate mir_semantics]
structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat

/-- Update local slot `target` in a local store `locals`, leaving all other
    local indices unchanged. -/
@[candidate mir_semantics]
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Dynamic type-validity relation matching an initialized `MirVal` against a
    `MirTy`.

    Corresponds to Rust's value validity requirement that every produced scalar
    value be initialized and match its static type:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L117 -/
@[candidate mir_semantics]
def MirVal.hasTy (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .unit, .unit => True
  | _, _ => False

/-- Entry initialization condition for function arguments and non-argument
    locals.

    Starting at local `1` at function entry, each parameter type in `argTys`
    holds an initialized `MirVal` matching its `MirTy`, while remaining locals
    start uninitialized (`none`):

    > "Starting at local 1, `arg_count` locals will be provided by the caller
    > and can be assumed to be initialized."
    >
    > "At any point during the execution of a function, each local is either
    > allocated or unallocated. Except as noted below, all locals except
    > function parameters are initially unallocated."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L245-L249
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L366-L368 -/
@[candidate mir_semantics]
def argsMatchLocals (argTys : List MirTy) (locals : Nat → Option MirVal) : Prop :=
  -- Fold across `argTys` starting at local index `k = 1`: each parameter slot
  -- `k` must hold `some v` with `v.hasTy ty`, and every index `j` past the last
  -- parameter (`1 + argTys.length ≤ j`) must be `none`.
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ v.hasTy ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

/-- Entry state predicate for a `MirBody`: execution starts at basic block `0`,
    statement `0`, with the return place `_0` uninitialized and argument locals
    `1 ..= argTys.length` initialized to type-valid values.

    Corresponds to function body entry in the Rust Reference and `rustc` MIR:

    > "The body block of a function is conceptually wrapped in another block
    > that first binds the argument patterns and then `return`s the value of
    > the function's body."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/functions.md#L114-L116 -/
@[candidate mir_semantics]
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals body.argTys s.locals

/-- Single-step operational evaluation of a MIR statement.

    Models `Operand::Copy`, `Operand::Move`, `Rvalue::Use`,
    `StatementKind::Assign`, `StatementKind::StorageLive`,
    `StatementKind::StorageDead`, and `StatementKind::Nop`:
    - Reading an uninitialized local via `Operand.copy` or `Operand.move`
      triggers immediate Undefined Behavior (`.failed`), matching
      `r[undefined.invalid]` and `r[undefined.validity.scalar]`.
    - `Operand.copy` preserves the source local, whereas `Operand.move`
      deinitializes the source local before storing the value into `dst`,
      matching `r[expr.move.copy]` and `r[expr.move.deinitialization]`:

    > "* Producing an [invalid value][invalid-values]. "Producing" a value
    > happens any time a value is assigned to or read from a place, passed to a
    > function/primitive operation or returned from a function/primitive
    > operation."
    >
    > "If the type of that value implements [`Copy`], then the value will be
    > copied."
    >
    > "After moving out of a place expression that evaluates to a local
    > variable, the location is deinitialized and cannot be read from again
    > until it is reinitialized."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L54-L55
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions.md#L199-L215 -/
@[candidate mir_semantics]
def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match op with
    | .copy src =>
      -- `Copy` reads `src` without deinitializing it; reading an uninitialized
      -- local (`none`) is immediate UB.
      match s.locals src.index with
      | some v =>
        .step () {
          locals := updateLocal s.locals dst.index (some v)
          block := s.block
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    | .move src =>
      -- `Move` reads `src`, deinitializes `src` (`none`), and writes `v` to
      -- `dst`. Deinitializing `src` before writing `dst` ensures that a
      -- self-move (`_x = move _x`) still leaves `_x` initialized with `v`.
      match s.locals src.index with
      | some v =>
        let deinitLocals := updateLocal s.locals src.index none
        .step () {
          locals := updateLocal deinitLocals dst.index (some v)
          block := s.block
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    | .constVal v =>
      .step () {
        locals := updateLocal s.locals dst.index (some v)
        block := s.block
        stmtIdx := s.stmtIdx + 1
      }
  | .storageLive loc =>
    -- Entering a live storage range starts `loc` in an uninitialized state.
    .step () {
      locals := updateLocal s.locals loc.index none
      block := s.block
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    -- Ending a live storage range deallocates/deinitializes `loc`.
    .step () {
      locals := updateLocal s.locals loc.index none
      block := s.block
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

/-- Single-step operational evaluation of a MIR basic-block terminator.

    Models `TerminatorKind::Return`, `TerminatorKind::Goto`, and
    `TerminatorKind::Unreachable`:
    - `Terminator.return_` reads the return place `_0` (`s.locals 0`) and
      completes with `.terminated (.normal retVal)` if initialized, or triggers
      `.failed` if `_0` is uninitialized (`r[undefined.invalid]`).
    - `Terminator.goto target` transfers control to statement `0` of
      `target.index`.
    - `Terminator.unreachable` triggers immediate `.failed`:

    > "Block has one successor; we continue execution there."
    >
    > "Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L684-L731 -/
@[candidate mir_semantics]
def evalMirTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some retVal => .terminated (.normal retVal)
    | none => .failed
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed

/-- Single-step transition function of a `MirBody`: executes the statement at
    `s.stmtIdx` in block `s.block`, or the block's terminator once all
    statements in `s.block` have completed. Jumping to an out-of-bounds basic
    block index triggers `.failed`. -/
@[candidate mir_semantics]
def evalMirStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

/-- Small-step operational machine for `MirBody`. -/
@[candidate mir_semantics]
def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStep body s

/-- Operational language of Rust MIR (`MirMachine.toLanguage`). -/
@[candidate mir_semantics]
def MirLang : Language :=
  MirMachine.toLanguage

/-- Operational behavior of a `MirBody`: the query-indexed partial behavior
    (`ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop)`) induced by
    `MirMachine`. -/
@[candidate mir_semantics]
abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-- Postcondition specification for a safe function asserting that:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`MirLang.WellFormed`), and
    - `val`: any normal return value equals the initial value of argument local
      `argLocal` (`1` for the first parameter `_1`). -/
@[candidate mir_semantics]
def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.locals argLocal = some ret)

end Trusted
