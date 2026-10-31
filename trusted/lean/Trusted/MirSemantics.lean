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
# Trusted MIR Semantics and Crate Theorem (`Trusted/MirSemantics.lean`)

This module defines the small-step operational semantics `MirSem` for the MIR
fragment in `Trusted/MirAst.lean`, Post-Monomorphization Error (PME) admission
(`RequiresConst`, `ConstSucceeds`, `MonoAdmitted`), the library representation
invariant and API boundary contract (`LibInv`, `AdmissibleLibInv`, `FnKind`,
`UnsafeImplObligation`), and the top-level crate verification obligation
`Trusted.CrateTheorem`.

Every declaration in this file that models a Rust execution rule or library
soundness obligation explains the correspondence and both quotes and cites the
normative Rust Reference or `rustc` documentation at the repository's pinned
revisions (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

This module belongs to `trusted/lean/` and contains only definitions,
structures, inductives, and opaque interfaces (zero theorems). All proofs
(`TotalStep`, `InhabitedDemonic`, adequacy canaries, PME extraction lemmas, and
library verification theorems) live in `theory/Anneal/MirLemmas.lean`.
-/

namespace Trusted

/-- Saved caller activation frame pushed onto `MirState.stack` by a static
    `Terminator.call1` and popped by the callee's `Terminator.return_`. -/
@[candidate mir_semantics]
structure StackFrame where
  callerBody : MirBody
  callerLocals : Nat → Option MirVal
  retDst : LocalId
  retBlock : Nat

/-- Instantaneous execution state of a `MirBody`, recording:
    - `locals`: the contents of each local slot (`none` when uninitialized or
      deallocated, `some v` when holding an initialized `MirVal`),
    - `block`: the active basic block index,
    - `stmtIdx`: the statement index within that basic block,
    - `tySizes`: the monomorphization environment mapping each type parameter
      index (`MirTy.param idx`) to its concrete byte size,
    - `curBody`: `none` when executing the root `MirBody`, or `some callee` when
      executing inside a static `Terminator.call1` frame, and
    - `stack`: saved caller activation frames. -/
@[candidate mir_semantics]
structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option MirBody := none
  stack : List StackFrame := []

/-- Update local slot `target` in a local store `locals`, leaving all other
    local indices unchanged. -/
@[candidate mir_semantics]
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Byte size of a `MirTy` under a monomorphization type-size assignment
    `tySizes` (`core::mem::size_of::<T>()`):
    - `usize`, single-field `usize` wrapper ADTs, and thin shared references
      (`&T`) are 8 bytes on a 64-bit target,
    - `bool` is 1 byte (`r[type.bool.layout]`),
    - `()` is 0 bytes, and
    - `MirTy.param idx` has byte size `tySizes idx`.

    > "The size of a value is the offset in bytes between successive elements
    > in an array with that item type including alignment padding."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/type-layout.md#L16-L18 -/
@[candidate mir_semantics]
def evalTyByteSize (tySizes : Nat → Nat) (ty : MirTy) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .refParam _ => 8

/-- Dynamic language-level type-validity relation (`V_lang`) matching an
    initialized `MirVal` against a `MirTy` under `tySizes`.

    Corresponds to Rust's value validity requirement that every produced scalar
    or aggregate value be initialized and match its static type layout:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L117 -/
@[candidate mir_semantics]
def MirVal.hasTy (tySizes : Nat → Nat) (v : MirVal) (ty : MirTy) : Prop :=
  match ty, v with
  | .usize, .usize _ => True
  | .bool, .bool _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.usize _) => vId = tyId
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .ref _ => True
  | _, _ => False

/-- Entry initialization condition for function arguments and non-argument
    locals under `tySizes`.

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
def argsMatchLocals (tySizes : Nat → Nat) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  -- Fold across `argTys` starting at local index `k = 1`: each parameter slot
  -- `k` must hold `some v` with `v.hasTy tySizes ty`, and every index `j` past
  -- the last parameter (`1 + argTys.length ≤ j`) must be `none`.
  argTys.foldr
    (fun ty rest k =>
      (∃ v, locals k = some v ∧ v.hasTy tySizes ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

/-- Entry state predicate for a `MirBody`: execution starts at basic block `0`,
    statement `0`, at the root frame (`curBody = none`, `stack = []`), with the
    return place `_0` uninitialized and argument locals `1 ..= argTys.length`
    initialized to type-valid values.

    Corresponds to function body entry in the Rust Reference and `rustc` MIR:

    > "The body block of a function is conceptually wrapped in another block
    > that first binds the argument patterns and then `return`s the value of
    > the function's body."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/functions.md#L114-L116 -/
@[candidate mir_semantics]
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.locals 0 = none ∧
  argsMatchLocals s.tySizes body.argTys s.locals

/-- Evaluate a MIR `Operand`, returning the loaded `MirVal` and the updated
    local store (or `none` if the operand reads an uninitialized local).

    - `Operand.copy` preserves the source local (`r[expr.move.copy]`).
    - `Operand.move` deinitializes the source local
      (`r[expr.move.deinitialization]`).
    - `Operand.constVal` yields its constant directly. -/
@[candidate mir_semantics]
def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some v => some (v, updateLocal locals src.index none)
    | none => none
  | .constVal v => some (v, locals)

/-- Evaluate a binary comparison `BinOp` on two initialized `MirVal`
    operands. -/
@[candidate mir_semantics]
def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | _, _, _ => none

/-- Single-step operational evaluation of a MIR statement.

    Models `Operand::Copy`, `Operand::Move`, `Rvalue::Use`, `Rvalue::BinaryOp`,
    `Rvalue::Aggregate`, field projection, shared borrow/reborrow,
    `StatementKind::Assign`, `StatementKind::StorageLive`,
    `StatementKind::StorageDead`, and `StatementKind::Nop`:
    - Reading an uninitialized local triggers immediate Undefined Behavior
      (`.failed .ub`), matching `r[undefined.invalid]`.
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
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some outVal =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some outVal)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .assign dst (.aggregate adtId op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some (.adt adtId v))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.field0 src) =>
    match s.locals src.index with
    | some (.adt _ inner) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some inner)
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.ref src) =>
    match s.locals src.index with
    | some _ =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.ref src))
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.reborrow src) =>
    match s.locals src.index with
    | some (.ref target) =>
      match s.locals target.index with
      | some _ =>
        .step () { s with
          locals := updateLocal s.locals dst.index (some (.ref target))
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .storageLive loc =>
    -- Entering a live storage range starts `loc` in an uninitialized state.
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    -- Ending a live storage range deallocates/deinitializes `loc`.
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

/-- Operational evaluation of `core::mem::transmute_copy::<srcTy, dstTy>(&src)`:
    requires `srcTy` and `dstTy` to have equal byte size under `tySizes` and
    `argVal` to be a valid reference `.ref target` to an initialized byte value
    of size `evalTyByteSize tySizes srcTy`; otherwise returns `none` (immediate
    Undefined Behavior).

    Corresponds to `core::mem::transmute_copy` in the Rust standard library:

    > "It is undefined behavior to call this function if `Src` is smaller than
    > `Dst` (`size_of::<Src>() < size_of::<Dst>()`)."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/mem/mod.rs#L1180-L1209 -/
@[candidate mir_semantics]
def evalTransmuteCopy (tySizes : Nat → Nat) (locals : Nat → Option MirVal)
    (srcTy dstTy : MirTy) (argVal : MirVal) : Option MirVal :=
  let srcSz := evalTyByteSize tySizes srcTy
  let dstSz := evalTyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match argVal with
    | .ref target =>
      match locals target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

/-- Single-step operational evaluation of a MIR basic-block terminator.

    Models `TerminatorKind::Return`, `TerminatorKind::Goto`,
    `TerminatorKind::Unreachable`, `TerminatorKind::SwitchInt`, and
    `TerminatorKind::Call` (`panic`, `size_of`, `transmute_copy`, and static
    single-argument calls):
    - `Terminator.return_` reads the return place `_0` (`s.locals 0`). At the
      root frame (`s.stack = []`), it completes with
      `.terminated (.normal retVal)` if initialized (or `.failed .ub` if
      uninitialized). Inside a callee frame (`frame :: restStack`), it pops
      `frame`, writes `retVal` to `frame.retDst` in `frame.callerLocals`, and
      resumes at `frame.retBlock`.
    - `Terminator.goto target` transfers control to statement `0` of
      `target.index`.
    - `Terminator.unreachable` triggers immediate `.failed .ub`.
    - `Terminator.panic` terminates execution via unwinding
      (`.terminated .unwind`).
    - `Terminator.switchInt discr falseTarget trueTarget` branches on a boolean
      discriminant (`false` -> `falseTarget`; `true` -> `trueTarget`).
    - `Terminator.callSizeOf dst ty target` writes `evalTyByteSize s.tySizes ty`
      to `dst` and jumps to `target`.
    - `Terminator.callTransmuteCopy dst srcTy dstTy op target` evaluates
      `evalTransmuteCopy`, writing the transmuted value to `dst` or failing with
      `.failed .ub` if the byte sizes disagree.
    - `Terminator.call1 dst callee arg target` evaluates `arg` and pushes a
      `StackFrame` to execute `callee` at block `0`, statement `0`.

    > "Block has one successor; we continue execution there."
    >
    > "Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."
    >
    > "Indicates a terminator that can never be reached.
    >
    > Executing this terminator is UB."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L684-L798 -/
@[candidate mir_semantics]
def evalMirTerminator (activeBody : MirBody) (s : MirState)
    (term : Terminator) : StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | none => .failed .ub
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          locals := updateLocal frame.callerLocals frame.retDst.index (some retVal)
          block := frame.retBlock
          stmtIdx := 0
          tySizes := s.tySizes
          curBody := if restStack.isEmpty then none else some frame.callerBody
          stack := restStack
        }
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed .ub
  | .panic =>
    .terminated .unwind
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with locals := locals', block := falseTarget.index, stmtIdx := 0 }
    | some (.bool true, locals') =>
      .step () { s with locals := locals', block := trueTarget.index, stmtIdx := 0 }
    | _ => .failed .ub
  | .callSizeOf dst ty target =>
    let sz := evalTyByteSize s.tySizes ty
    .step () { s with
      locals := updateLocal s.locals dst.index (some (.usize sz))
      block := target.index
      stmtIdx := 0
    }
  | .callTransmuteCopy dst srcTy dstTy op target =>
    match evalOperand s.locals op with
    | some (argVal, locals') =>
      match evalTransmuteCopy s.tySizes locals' srcTy dstTy argVal with
      | some outVal =>
        .step () { s with
          locals := updateLocal locals' dst.index (some outVal)
          block := target.index
          stmtIdx := 0
        }
      | none => .failed .ub
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalOperand s.locals arg with
    | some (argVal, callerLocals') =>
      let calleeLocals : Nat → Option MirVal :=
        updateLocal (fun _ => none) 1 (some argVal)
      let frame : StackFrame := {
        callerBody := activeBody
        callerLocals := callerLocals'
        retDst := dst
        retBlock := target.index
      }
      .step () {
        locals := calleeLocals
        block := 0
        stmtIdx := 0
        tySizes := s.tySizes
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed .ub

/-- Single-step transition function of a `MirBody`: executes the statement at
    `s.stmtIdx` in block `s.block` of the active `MirBody` (`s.curBody.getD
    rootBody`), or the block's terminator once all statements in `s.block` have
    completed. Jumping to an out-of-bounds basic block index triggers
    `.failed .ub`. -/
@[candidate mir_semantics]
def evalMirStep (rootBody : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator active s bb.terminator

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

/-!
## Post-Monomorphization Error (PME) Admission
-/

/-- Inductive reachability of compile-time constant `MirBody` items required
    for monomorphization of `body` (`Body::required_consts` collected across
    `body` and its static `Terminator.call1` callees).

    Corresponds to `collect_used_items` and `required_consts` evaluation in
    `rustc_monomorphize::collector`:

    > "Constants that are required to evaluate successfully for this `Body`
    > to be well-formed. Wait until monomorphization to evaluate them."
    >
    > "Collect all monomorphized items reachable from the root and evaluate
    > their `required_consts`."

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L279-L285
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1185-L1207 -/
@[candidate mir_semantics]
inductive RequiresConst : MirBody → MirBody → Prop where
  /-- Direct PME constant referenced in `body.requiredConsts`. -/
  | direct {body c : MirBody} :
      c ∈ body.requiredConsts →
      RequiresConst body c
  /-- Transitive PME constant required by a constant `c'` in
      `body.requiredConsts`. -/
  | nested {body c' c : MirBody} :
      c' ∈ body.requiredConsts →
      RequiresConst c' c →
      RequiresConst body c
  /-- Transitive PME constant required by a static `Terminator.call1` callee
      in `body.blocks`. -/
  | call1 {body callee c : MirBody} {bb : BasicBlock}
      {dst : LocalId} {arg : Operand} {target : BlockId} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target →
      RequiresConst callee c →
      RequiresConst body c

/-- Compile-Time Function Evaluation (CTFE) success predicate for a constant
    `MirBody` `c` under monomorphization type sizes `tySizes`: there exists a
    valid entry state `s₀` with `s₀.tySizes = tySizes` from which `MirMachine`
    reaches normal termination `.terminated (.normal v)` in `n` steps.

    If `c` panics (`.terminated .unwind`), triggers UB (`.failed .ub`), or
    diverges, `ConstSucceeds tySizes c` is `False` and `rustc` rejects the
    monomorphization with a Post-Monomorphization Error (`E0080`):

    > "A constant expression is evaluated at compile time. If evaluation fails
    > (for example, due to a panic or integer overflow), compilation fails."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/const_eval.md#L1-L25 -/
@[candidate mir_semantics]
def ConstSucceeds (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∃ (s₀ : MirState) (n : Nat) (tr : List Unit) (v : MirVal),
    s₀.tySizes = tySizes ∧
    initMirState c s₀ ∧
    ReachesPrefix MirMachine c s₀ n s₀ tr (.terminated (.normal v))

/-- Monomorphization admission predicate for `body` under `tySizes`: every
    compile-time constant `c` satisfying `RequiresConst body c` (including those
    of static `Terminator.call1` callees) evaluates to normal completion without
    panicking or triggering UB. -/
@[candidate mir_semantics]
def MonoAdmitted (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConst body c → ConstSucceeds tySizes c

/-!
## Library Representation Invariants and Boundary Promises
-/

/-- Library representation invariant map (`I_lib`): assigns a semantic validity
    predicate to every `MirTy` and `MirVal` under a monomorphization environment
    `tySizes`.

    Corresponds to Rust's distinction between language-level validity invariants
    and library-level safety invariants required for sound interaction with safe
    downstream code:

    > "`unsafe` code may trust that *safe* code cannot violate library-level
    > invariants when interacting only through the public safe API."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/unsafety.md#L1-L35 -/
@[candidate mir_semantics]
abbrev LibInv := (Nat → Nat) → MirTy → MirVal → Prop

/-- Default library representation invariant equating library validity with
    language-level type validity (`MirVal.hasTy`). -/
@[candidate mir_semantics]
def defaultLibInv : LibInv :=
  fun tySizes ty v => v.hasTy tySizes ty

/-- Standard library representation invariant for a crate whose ADT `0`
    (`NonZeroUsize`) encapsulates a private non-zero `usize` field
    (`val != 0`). -/
@[candidate mir_semantics]
def nonZeroLibInv (tySizes : Nat → Nat) (ty : MirTy) (v : MirVal) : Prop :=
  match ty, v with
  | .usize, .usize _ => True
  | .bool, .bool _ => True
  | .unit, .unit => True
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .ref _ => True
  | .adt 0, .adt 0 (.usize n) => n ≠ 0
  | _, _ => False

/-- Standard `# Safety` precondition for `pub unsafe fn new_unchecked(x: usize)
    -> NonZeroUsize`: the caller guarantees that argument `_1` is non-zero. -/
@[candidate mir_semantics]
def newUncheckedSafetyPre (q : ExecQuery MirState) : Prop :=
  ∀ n, q.init.locals 1 = some (.usize n) → n ≠ 0

/-- Admissibility of a library representation invariant `libInv` for a crate's
    ADT declarations `adts`:
    1. **Refines language validity (`I_lib -> V_lang`):** every value satisfying
       `libInv tySizes ty v` satisfies `v.hasTy tySizes ty`.
    2. **Primitives and `Copy` byte parameters are open:** every language-valid
       `.usize`, `.bool`, `.unit`, or `.param idx` value satisfies `libInv`,
       because safe downstream callers can construct arbitrary scalar values.
    3. **Public-safe field closure (`r[expr.struct.safety]`):** for any ADT
       `decl ∈ adts` whose fields are all `pubSafe` (and not
       `#[non_exhaustive]`), wrapping any field value `v` satisfying
       `libInv tySizes .usize v` must satisfy
       `libInv tySizes (.adt decl.id) (.adt decl.id v)`—preventing a library
       from claiming a restricted invariant on a struct that safe downstream
       code can construct directly via struct literal syntax.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/struct-expr.md#L58-L65 -/
@[candidate mir_semantics]
def AdmissibleLibInv (adts : List AdtDecl) (libInv : LibInv) : Prop :=
  (∀ tySizes ty v, libInv tySizes ty v → v.hasTy tySizes ty) ∧
  (∀ tySizes n, libInv tySizes .usize (.usize n)) ∧
  (∀ tySizes b, libInv tySizes .bool (.bool b)) ∧
  (∀ tySizes, libInv tySizes .unit .unit) ∧
  (∀ tySizes idx bits, libInv tySizes (.param idx) (.bytes (tySizes idx) bits)) ∧
  (∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ tySizes v, libInv tySizes .usize v →
      libInv tySizes (.adt decl.id) (.adt decl.id v))

/-- Entry condition asserting that each caller argument local
    `1 ..= argTys.length` satisfies the crate's library representation invariant
    `libInv`. -/
@[candidate mir_semantics]
def argsSatisfyLibInv (libInv : LibInv) (tySizes : Nat → Nat)
    (argTys : List MirTy) (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, locals k = some v ∧ libInv tySizes ty v) ∧ rest (k + 1))
    (fun _ => True)
    1

/-- Mandatory postcondition specification for public library functions: on every
    query `q` satisfying `pre q`, the function is free of UB
    (`defined := pre q`) and any normal return value `ret` satisfies
    `libInv q.init.tySizes retTy ret`. -/
@[candidate mir_semantics]
def EnsuresRetLibInv (libInv : LibInv) (retTy : MirTy)
    (pre : ExecQuery MirState → Prop) : MirLang.Behavior :=
  MirLang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

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

/-- Abstract type of compiled target artifacts produced by `rustc`.

    Its constructor is marked `private` so external modules can only obtain a
    `TargetArtifact` through the opaque `rustc` lowering function. -/
@[candidate mir_semantics]
structure TargetArtifact where
  private mk ::
  unit : Unit

/-- Abstract `rustc` lowering from a `MirBody` to a `TargetArtifact`.

    Declared `opaque` so that proofs cannot unfold target compilation and must
    instead discharge target refinement via the audited `TCBItem.rustcLowering`
    assumption in the crate's TCB list. -/
@[candidate mir_semantics]
opaque rustc : MirBody → TargetArtifact := fun _ => { unit := () }

/-- Abstract operational behavior of a compiled `TargetArtifact`.

    Declared `opaque` so that no theorem can rely on an implementation artifact
    of `TargetSem`; any property of `TargetSem (rustc body)` must be derived
    from `RustcCompiler.SoundOn body` and `MirSem body`. -/
@[candidate mir_semantics]
opaque TargetSem :
    TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

/-- Target language of compiled `TargetArtifact`s. -/
@[candidate mir_semantics]
def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := TargetSem

/-- Abstract compiler behavior mapping from MIR behaviors to target behaviors.

    Declared `opaque` so that monotonicity (`Monotone π_c`) comes solely from
    `RustcCompiler.SoundOn` via `TCBItem.rustcLowering`. -/
@[candidate mir_semantics]
opaque π_c : MirLang.Behavior → TargetLang.Behavior :=
  fun b => b

/-- `rustc` compiler lowering from `MirLang` to `TargetLang` under `π_c`. -/
@[candidate mir_semantics]
def RustcCompiler : Compiler MirLang TargetLang where
  compile := rustc
  π := π_c

/-- Audited assumption category in a crate's Trusted Computing Base. -/
@[candidate mir_semantics]
inductive TCBItem where
  /-- Standard compiler lowering assumption for a function: `RustcCompiler` is
      sound on `body` (`RustcCompiler.SoundOn body`). Tagged with
      `@[candidate rustc_capture]` because this assumption is emitted by the
      `anneal-rustc-capture` pipeline when lowering a captured function. -/
  | @[candidate rustc_capture] rustcLowering (fnName : String) (body : MirBody)
  /-- Explicit user-supplied axiom assumption (`#[anneal::axiom]`). -/
  | userAxiom (name : String) (prop : Prop)

/-- Semantic meaning of each Rust `TCBItem` as a `TrustedAssumption`. -/
@[candidate mir_semantics]
instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => RustcCompiler.SoundOn body
    | .userAxiom _ prop => prop

/-- Default trust policy: standard `rustc` lowering assumptions are permitted;
    unapproved user axioms are rejected (`False`). -/
@[candidate mir_semantics]
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True
    | .userAxiom _ _ => False

/-- Rust visibility and safety role of a captured function, determining what the
    function may assume at entry and what it must guarantee to downstream
    callers (`r[unsafety]`):
    - `pubSafe traitLaws`: a public safe function (`pub fn`). Cannot attach an
      unchecked caller precondition; must be UB-free and preserve `libInv` on
      every monomorphization-admitted call whose arguments satisfy `libInv` and
      whose generic `unsafe trait` bounds (`traitLaws`) hold.
    - `pubUnsafe traitLaws safetyPre`: a public unsafe function
      (`pub unsafe fn`). May additionally assume its documented `# Safety`
      precondition `safetyPre`.
    - `priv pre`: a crate-private function (`fn`). Not callable by downstream
      crates; may use an internal precondition `pre` discharged at internal
      call sites.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/unsafety.md#L1-L35 -/
@[candidate mir_semantics]
inductive FnKind where
  | pubSafe (traitLaws : Prop := True)
  | pubUnsafe (traitLaws : Prop := True) (safetyPre : ExecQuery MirState → Prop)
  | priv (pre : ExecQuery MirState → Prop := fun _ => True)

/-- Captured MIR function pairing its identifier (`name`), lowered `MirBody`
    (`prog`), visibility/safety role (`kind`, defaulting to `.pubSafe True`),
    and additional functional specifications (`specs`, defaulting to `[]`). -/
@[candidate mir_semantics]
structure CapturedFn where
  name : String
  prog : MirBody
  kind : FnKind := .pubSafe True
  specs : List MirLang.Behavior := []

/-- Canonical entry precondition of `fn` under the crate's library invariant
    `libInv`:
    1. All Post-Monomorphization Error constants transitively required by
       `fn.prog` succeed (`MonoAdmitted q.init.tySizes fn.prog`).
    2. For `pubSafe`, generic `unsafe trait` laws hold and all arguments satisfy
       `libInv`.
    3. For `pubUnsafe`, generic `unsafe trait` laws hold, all arguments satisfy
       `libInv`, and the caller satisfies `safetyPre q`.
    4. For `priv`, the internal precondition `internalPre q` holds. -/
@[candidate mir_semantics]
def CapturedFn.effectivePre (libInv : LibInv) (fn : CapturedFn)
    (q : ExecQuery MirState) : Prop :=
  MonoAdmitted q.init.tySizes fn.prog ∧
  match fn.kind with
  | .pubSafe traitLaws =>
    traitLaws ∧
    argsSatisfyLibInv libInv q.init.tySizes fn.prog.argTys q.init.locals
  | .pubUnsafe traitLaws safetyPre =>
    traitLaws ∧
    argsSatisfyLibInv libInv q.init.tySizes fn.prog.argTys q.init.locals ∧
    safetyPre q
  | .priv internalPre =>
    internalPre q

/-- Canonical specification list of `fn` under `libInv`: public functions
    (`.pubSafe` and `.pubUnsafe`) automatically require `EnsuresRetLibInv` in
    addition to user-supplied `fn.specs`. -/
@[candidate mir_semantics]
def CapturedFn.effectiveSpecs (libInv : LibInv) (fn : CapturedFn) :
    List MirLang.Behavior :=
  let pre := fn.effectivePre libInv
  match fn.kind with
  | .pubSafe _ | .pubUnsafe _ _ =>
    EnsuresRetLibInv libInv fn.prog.retTy pre :: fn.specs
  | .priv _ =>
    fn.specs

/-- Proof obligation for an `unsafe impl` of an `unsafe trait` (or `unsafe impl
    Copy`/`Clone` for a type with `unsafe` fields): under the `impl`'s generic
    `where` bounds and PME admission (`whereBounds`), the crate's representation
    invariant `libInv` satisfies the trait's semantic law `traitLaw libInv`.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/implementations.md#L120-L135 -/
@[candidate mir_semantics]
structure UnsafeImplObligation where
  implName : String
  whereBounds : Prop := True
  traitLaw : LibInv → Prop

/-- Captured Rust crate bundling its ADT declarations (`adts`), library
    representation invariant (`libInv`, defaulting to `defaultLibInv`),
    `unsafe impl` obligations (`unsafeImpls`), captured functions (`functions`),
    and TCB audit log (`tcb`). -/
@[candidate mir_semantics]
structure Crate where
  adts : List AdtDecl := []
  libInv : LibInv := defaultLibInv
  unsafeImpls : List UnsafeImplObligation := []
  functions : List CapturedFn
  tcb : List TCBItem

/-- Top-level theorem required of every verified Rust crate:
    1. The crate contains at least one captured function (`c.functions ≠ []`).
    2. The crate's representation invariant is admissible (`AdmissibleLibInv
       c.adts c.libInv`): it refines language validity and respects public-safe
       struct field construction.
    3. Every `unsafe impl` in `c.unsafeImpls` satisfies its `unsafe trait` law
       relative to `c.libInv`.
    4. Every captured function `fn ∈ c.functions` satisfies
       `VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog
       (fn.effectivePre c.libInv) (fn.effectiveSpecs c.libInv)`
       —proving that `c.tcb` complies with `defaultTrustPolicy` and, assuming
       the meaning of every item in `c.tcb`, proving `RustcCompiler.Verified
       fn.prog` on the non-empty specification list
       `MirLang.WellFormedOn (fn.effectivePre c.libInv) ::
       fn.effectiveSpecs c.libInv`. -/
@[candidate mir_semantics]
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AdmissibleLibInv c.adts c.libInv ∧
  AllHold (c.unsafeImpls.map (fun u => u.whereBounds → u.traitLaw c.libInv)) ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog
      (fn.effectivePre c.libInv) (fn.effectiveSpecs c.libInv)))

end Trusted
