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
invariant and API boundary contract (`AdtInv`, `MirVal.satisfiesBaseInv`,
`MirVal.satisfiesInv`, `AdmissibleAdtInv`, `FnKind`, `UnsafeImplObligation`),
and the top-level crate verification obligation `Trusted.CrateTheorem`.

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
  callerLocalGens : Nat → Nat := fun _ => 0
  callerTySizes : Nat → Nat := fun _ => 0
  retDst : LocalId
  retBlock : Nat

/-- Instantaneous execution state of a `MirBody`, recording:
    - `locals`: the contents of each local slot (`none` when uninitialized or
      deallocated, `some v` when holding an initialized `MirVal`),
    - `localGens`: per-local storage-liveness generation counter incremented on
      each `Stmt.storageLive` and `Stmt.storageDead`,
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
  localGens : Nat → Nat := fun _ => 0
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

/-- Increment the storage-liveness generation counter of local `target` in
    `gens` by `1`, leaving all other local indices unchanged. -/
@[candidate mir_semantics]
def bumpGen (gens : Nat → Nat) (target : Nat) : Nat → Nat :=
  fun i => if i == target then gens i + 1 else gens i

/-- Look up element `idx` in `xs` via `List.foldr`. -/
@[candidate mir_semantics]
def lookupAt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr
    (fun x rest i =>
      match i with
      | 0 => some x
      | k + 1 => rest k)
    (fun _ => none)
    idx

/-- Look up an `AdtDecl` by its crate-local identifier `id`. -/
@[candidate mir_semantics]
def findAdtDecl (adts : List AdtDecl) (id : Nat) : Option AdtDecl :=
  adts.find? (fun d => d.id == id)

/-- Fuel-bounded byte-size computation for a `MirTy` across `adts` and
    `tySizes`. Returns `none` if `ty` references an undeclared `AdtId` or a
    recursive ADT cycle exceeding `fuel`. -/
@[candidate mir_semantics]
def evalTyByteSizeFuel (fuel : Nat) (adts : List AdtDecl)
    (tySizes : Nat → Nat) (ty : MirTy) : Option Nat :=
  @Nat.rec (fun _ => MirTy → Option Nat)
    (fun _ => none)
    (fun _ ih t =>
      match t with
      | .usize => some 8
      | .bool => some 1
      | .unit => some 0
      | .param idx => some (tySizes idx)
      | .ref _ => some 8
      | .adt id =>
        match findAdtDecl adts id with
        | some decl =>
          decl.fields.foldl
            (fun accOpt f =>
              match accOpt, ih f.ty with
              | some acc, some sz => some (acc + sz)
              | _, _ => none)
            (some 0)
        | none => none)
    fuel ty

/-- Byte size of a `MirTy` under ADT declarations `adts` and monomorphization
    type-size assignment `tySizes` (`core::mem::size_of::<T>()`):
    - `usize` and thin shared references (`&T`) are 8 bytes on a 64-bit target,
    - `bool` is 1 byte (`r[type.bool.layout]`),
    - `()` is 0 bytes,
    - `MirTy.param idx` has byte size `tySizes idx`, and
    - `MirTy.adt id` sums the byte sizes of `decl.fields` for `decl ∈ adts`
      (or returns `none` if `id` is undeclared in `adts`).

    > "The size of a value is the offset in bytes between successive elements
    > in an array with that item type including alignment padding."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/type-layout.md#L16-L18 -/
@[candidate mir_semantics]
def evalTyByteSize (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) : Option Nat :=
  evalTyByteSizeFuel (adts.length + 1) adts tySizes ty

/-- Check whether `ty` (including the pointee type of a reference) only
    references declared, non-cyclic ADTs in `adts`. -/
@[candidate mir_semantics]
def MirTy.wfInAdts (adts : List AdtDecl) (ty : MirTy) : Bool :=
  match ty with
  | .ref inner => (evalTyByteSize adts (fun _ => 0) inner).isSome
  | _ => (evalTyByteSize adts (fun _ => 0) ty).isSome

/-- Substitute concrete call-site or const-use `typeArgs` into the caller's
    type-size environment `tySizes`: parameter index `idx` resolves to
    `(evalTyByteSize adts tySizes ty).getD 0` when `lookupAt typeArgs idx =
    some ty`, and falls back to `tySizes idx` when `typeArgs` is empty or `idx`
    is beyond `typeArgs.length`. -/
@[candidate mir_semantics]
def substTySizes (adts : List AdtDecl) (tySizes : Nat → Nat)
    (typeArgs : List MirTy) (idx : Nat) : Nat :=
  match lookupAt typeArgs idx with
  | some ty => (evalTyByteSize adts tySizes ty).getD 0
  | none => tySizes idx

/-- Retrieve the caller `StackFrame` at call-stack depth `depth` (`0` for the
    root caller frame at the bottom of `frames`). -/
@[candidate mir_semantics]
def getFrameAtDepth (frames : List StackFrame) (depth : Nat) :
    Option StackFrame :=
  if depth < frames.length then
    lookupAt frames (frames.length - 1 - depth)
  else
    none

/-- Resolve a shared reference `.ref depth gen loc` in state `s`, verifying that
    `depth` designates a live frame (`depth ≤ s.stack.length`), the target
    local's storage generation matches `gen`, and the target slot holds an
    initialized `MirVal`.

    Corresponds to Rust's prohibition against dangling or lifetime-expired
    references (`r[undefined.validity.reference]`):

    > "A reference or `Box<T>` must be aligned and non-null, it cannot be
    > dangling (it must point to a valid allocation of at least the size of the
    > pointee type `T`), and it must point to a valid value of type `T`."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L120-L125 -/
@[candidate mir_semantics]
def resolveRef (s : MirState) (depth gen : Nat) (loc : LocalId) :
    Option MirVal :=
  if depth == s.stack.length then
    if s.localGens loc.index == gen then
      s.locals loc.index
    else
      none
  else if depth < s.stack.length then
    match getFrameAtDepth s.stack depth with
    | some frame =>
      if frame.callerLocalGens loc.index == gen then
        frame.callerLocals loc.index
      else
        none
    | none => none
  else
    none

/-- Check whether a reference `.ref d _ loc` escapes frame depth
    `returningDepth` (whose root frame has `rootLocalCount` locals). -/
@[candidate mir_semantics]
def checkEscapingRef (returningDepth : Nat) (rootLocalCount : Nat)
    (d : Nat) (loc : LocalId) : Bool :=
  if returningDepth == 0 then
    decide (0 < d || loc.index < rootLocalCount)
  else
    decide (returningDepth ≤ d)

/-- Check whether returning `v` from frame depth `returningDepth` (whose local
    frame has `rootLocalCount` locals) would allow a reference to a frame-local
    variable to escape its defining stack frame (`0 < d || loc.index <
    rootLocalCount` at root depth `0`, or `returningDepth ≤ d` when returning
    from a callee frame at depth `returningDepth > 0`). Caller-owned referent
    slots at `d = 0 ∧ rootLocalCount ≤ loc.index` are permitted to return to the
    caller. -/
@[candidate mir_semantics]
def MirVal.hasEscapingRef (returningDepth : Nat) (rootLocalCount : Nat) :
    MirVal → Bool
  | .ref d _ loc => checkEscapingRef returningDepth rootLocalCount d loc
  | .adt _ (.ref d _ loc) =>
    checkEscapingRef returningDepth rootLocalCount d loc
  | _ => false

/-- Library-level representation invariant on user-defined ADT values
    (`AdtInv`): assigns a semantic validity predicate to each ADT identifier
    `adtId` and inner field value `MirVal`.

    Corresponds to Rust's distinction between language-level validity invariants
    and library-level safety invariants required for sound interaction with safe
    downstream code:

    > "`unsafe` code may trust that *safe* code cannot violate library-level
    > invariants when interacting only through the public safe API."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/unsafety.md#L1-L35 -/
@[candidate mir_semantics]
abbrev AdtInv := Nat → MirVal → Prop

/-- Default ADT representation invariant permitting any language-valid inner
    field value (`fun _ _ => True`). -/
@[candidate mir_semantics]
def defaultAdtInv : AdtInv :=
  fun _ _ => True

/-- Stage-1 structural value-validity relation on non-reference values (`v :
    MirVal`), supporting scalars, generic byte parameters, and 0-field,
    single-field, and multi-field ADTs declared in `adts`. -/
@[candidate mir_semantics]
def MirVal.satisfiesBaseInv (adts : List AdtDecl) (adtInv : AdtInv)
    (tySizes : Nat → Nat) (v : MirVal) (ty : MirTy) : Prop :=
  @MirVal.rec (fun _ => MirTy → Prop)
    (fun _ t => match t with | .usize => True | _ => False)
    (fun _ t => match t with | .bool => True | _ => False)
    (fun t => match t with | .unit => True | _ => False)
    (fun vId inner ih t =>
      match t with
      | .adt tyId =>
        vId = tyId ∧
        adtInv tyId inner ∧
        match findAdtDecl adts tyId with
        | some decl =>
          match decl.fields with
          | [] => inner = .unit
          | [f] => ih f.ty
          | f :: _ :: _ =>
            evalTyByteSize adts tySizes (.adt tyId) ≠ none ∧
            ih f.ty
        | none => False
      | _ => False)
    (fun sz _ t => match t with | .param idx => sz = tySizes idx | _ => False)
    (fun _ _ _ _ => False)
    v ty

/-- Stage-2 parameterized value-validity relation matching an initialized
    `MirVal` against a `MirTy` in state `s` under `adts` and ADT representation
    invariant `adtInv`:
    - For `.ref depth gen loc` against `.ref innerTy`, resolves the reference
      via `resolveRef s depth gen loc` and recursively verifies the pointee
      value against `innerTy`.
    - For non-reference types, delegates to `MirVal.satisfiesBaseInv`.

    Corresponds to Rust's value validity requirement that every produced scalar,
    aggregate, or reference value be initialized, live, and match its static
    type layout:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L117 -/
@[candidate mir_semantics]
def MirVal.satisfiesInv (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (v : MirVal) (ty : MirTy) : Prop :=
  @MirTy.rec (fun _ => MirVal → Prop)
    (fun w => w.satisfiesBaseInv adts adtInv s.tySizes .usize)
    (fun w => w.satisfiesBaseInv adts adtInv s.tySizes .bool)
    (fun w => w.satisfiesBaseInv adts adtInv s.tySizes .unit)
    (fun id w => w.satisfiesBaseInv adts adtInv s.tySizes (.adt id))
    (fun idx w => w.satisfiesBaseInv adts adtInv s.tySizes (.param idx))
    (fun _ ih w =>
      match w with
      | .ref depth gen loc =>
        match resolveRef s depth gen loc with
        | some pointeeVal => ih pointeeVal
        | none => False
      | _ => False)
    ty v

/-- Dynamic language-level type-validity relation (`V_lang`) matching an
    initialized `MirVal` against a `MirTy` in state `s`
    (`v.satisfiesInv adts defaultAdtInv s ty`). -/
@[candidate mir_semantics]
abbrev MirVal.hasTy (adts : List AdtDecl := []) (s : MirState)
    (v : MirVal) (ty : MirTy) : Prop :=
  v.satisfiesInv adts defaultAdtInv s ty

/-- Entry initialization condition for function arguments and non-argument
    locals under `adts` and `adtInv`.

    Starting at local `1` at function entry, each parameter type in `argTys`
    holds an initialized `MirVal` satisfying `v.satisfiesInv adts adtInv s ty`,
    while remaining frame-local slots `1 + argTys.length ≤ j < localCount` start
    uninitialized (`none`). Slots `j ≥ localCount` at root depth `0` are left
    unconstrained to model caller-owned referents for reference parameters:

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
def argsMatchInv (adts : List AdtDecl := []) (adtInv : AdtInv)
    (localCount : Nat) (s : MirState) (argTys : List MirTy) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, s.locals k = some v ∧ v.satisfiesInv adts adtInv s ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → j < localCount → s.locals j = none)
    1

/-- Language-level argument initialization condition (`argsMatchInv adts
    defaultAdtInv`). -/
@[candidate mir_semantics]
abbrev argsMatchLocals (adts : List AdtDecl := []) (localCount : Nat)
    (s : MirState) (argTys : List MirTy) : Prop :=
  argsMatchInv adts defaultAdtInv localCount s argTys

/-- Structural entry state predicate for a `MirBody` (prior to
    Post-Monomorphization Error admission): execution starts at basic block `0`,
    statement `0`, at the root frame (`curBody = none`, `stack = []`,
    `localGens = fun _ => 0`), with the return place `_0` uninitialized,
    `1 + body.argTys.length ≤ body.localCount`, well-formed argument and return
    types in `adts`, and argument locals `1 ..= argTys.length` initialized to
    language-valid values.

    Corresponds to function body entry in the Rust Reference and `rustc` MIR:

    > "The body block of a function is conceptually wrapped in another block
    > that first binds the argument patterns and then `return`s the value of
    > the function's body."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/functions.md#L114-L116 -/
@[candidate mir_semantics]
def initEntryState (adts : List AdtDecl := []) (body : MirBody)
    (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.localGens = (fun _ => 0) ∧
  s.locals 0 = none ∧
  1 + body.argTys.length ≤ body.localCount ∧
  body.argTys.all (MirTy.wfInAdts adts) = true ∧
  body.retTy.wfInAdts adts = true ∧
  argsMatchLocals adts body.localCount s body.argTys

/-- Evaluate a MIR `Operand` within a frame of `localCount` locals, returning
    the loaded `MirVal` and the updated local store (or `none` if the operand
    accesses an out-of-bounds or uninitialized local).

    - `Operand.copy` preserves the source local (`r[expr.move.copy]`).
    - `Operand.move` deinitializes the source local
      (`r[expr.move.deinitialization]`).
    - `Operand.constVal` yields its constant directly. -/
@[candidate mir_semantics]
def evalOperand (localCount : Nat) (locals : Nat → Option MirVal)
    (op : Operand) : Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    if src.index < localCount then
      match locals src.index with
      | some v => some (v, locals)
      | none => none
    else
      none
  | .move src =>
    if src.index < localCount then
      match locals src.index with
      | some v => some (v, updateLocal locals src.index none)
      | none => none
    else
      none
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

/-- Single-step operational evaluation of a MIR statement inside `activeBody`.

    Models `Operand::Copy`, `Operand::Move`, `Rvalue::Use`, `Rvalue::BinaryOp`,
    `Rvalue::Aggregate`, field projection, shared borrow/reborrow, dereference
    copy, `StatementKind::Assign`, `StatementKind::StorageLive`,
    `StatementKind::StorageDead`, and `StatementKind::Nop`:
    - Reading an uninitialized or out-of-bounds local, or reborrowing/reading
      through a dead reference, triggers immediate Undefined Behavior
      (`.failed`), matching `r[undefined.invalid]`.
    - Both `Stmt.storageLive` and `Stmt.storageDead` clear the local slot to
      `none` and increment `s.localGens loc.index` so any pre-existing reference
      to `loc` is invalidated across storage range boundaries:

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
def evalMirStmt (activeBody : MirBody) (s : MirState)
    (stmt : Stmt) : StepResult MirState Empty MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    if dst.index < activeBody.localCount then
      match evalOperand activeBody.localCount s.locals op with
      | some (v, locals') =>
        .silent { s with
          locals := updateLocal locals' dst.index (some v)
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    else
      .failed
  | .assign dst (.binaryOp op lhs rhs) =>
    if dst.index < activeBody.localCount then
      match evalOperand activeBody.localCount s.locals lhs with
      | some (v1, locals1) =>
        match evalOperand activeBody.localCount locals1 rhs with
        | some (v2, locals2) =>
          match evalBinOp op v1 v2 with
          | some outVal =>
            .silent { s with
              locals := updateLocal locals2 dst.index (some outVal)
              stmtIdx := s.stmtIdx + 1
            }
          | none => .failed
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign dst (.aggregate adtId op) =>
    if dst.index < activeBody.localCount then
      match evalOperand activeBody.localCount s.locals op with
      | some (v, locals') =>
        .silent { s with
          locals := updateLocal locals' dst.index (some (.adt adtId v))
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    else
      .failed
  | .assign dst (.field0 src) =>
    if dst.index < activeBody.localCount &&
       src.index < activeBody.localCount then
      match s.locals src.index with
      | some (.adt _ inner) =>
        .silent { s with
          locals := updateLocal s.locals dst.index (some inner)
          stmtIdx := s.stmtIdx + 1
        }
      | _ => .failed
    else
      .failed
  | .assign dst (.ref src) =>
    if dst.index < activeBody.localCount &&
       src.index < activeBody.localCount then
      match s.locals src.index with
      | some _ =>
        .silent { s with
          locals := updateLocal s.locals dst.index
            (some (.ref s.stack.length (s.localGens src.index) src))
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed
    else
      .failed
  | .assign dst (.reborrow src) =>
    if dst.index < activeBody.localCount &&
       src.index < activeBody.localCount then
      match s.locals src.index with
      | some (.ref depth gen target) =>
        match resolveRef s depth gen target with
        | some _ =>
          .silent { s with
            locals := updateLocal s.locals dst.index
              (some (.ref depth gen target))
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed
      | _ => .failed
    else
      .failed
  | .assign dst (.copyDeref src) =>
    if dst.index < activeBody.localCount &&
       src.index < activeBody.localCount then
      match s.locals src.index with
      | some (.ref depth gen target) =>
        match resolveRef s depth gen target with
        | some v =>
          .silent { s with
            locals := updateLocal s.locals dst.index (some v)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed
      | _ => .failed
    else
      .failed
  | .storageLive loc | .storageDead loc =>
    if loc.index < activeBody.localCount then
      .silent { s with
        locals := updateLocal s.locals loc.index none
        localGens := bumpGen s.localGens loc.index
        stmtIdx := s.stmtIdx + 1
      }
    else
      .failed
  | .nop =>
    .silent { s with stmtIdx := s.stmtIdx + 1 }

/-- Extract the byte size and bit payload of a transmutable source `MirVal`. -/
@[candidate mir_semantics]
def extractTransmuteBits : MirVal → Option (Nat × Nat)
  | .bytes vSz bits => some (vSz, bits)
  | .usize bits => some (8, bits)
  | .bool b => some (1, if b then 1 else 0)
  | .unit => some (0, 0)
  | .adt _ (.usize bits) => some (8, bits)
  | _ => none

/-- Operational evaluation of `core::mem::transmute_copy::<srcTy, dstTy>(&src)`:
    requires `srcTy` and `dstTy` to have equal defined byte size under `adts`
    and `s.tySizes`, `argVal` to be a live reference `.ref depth gen target`
    resolving via `resolveRef` to a pointee whose byte size equals `srcSz`, and
    `dstTy` to admit arbitrary bit patterns of that size (including `.adt id`
    only when `decl` has a single `pubSafe` `.usize` field and is not
    `#[non_exhaustive]`).

    Corresponds to `core::mem::transmute_copy` in the Rust standard library:

    > "It is undefined behavior to call this function if `Src` is smaller than
    > `Dst` (`size_of::<Src>() < size_of::<Dst>()`)."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/mem/mod.rs#L1180-L1209 -/
@[candidate mir_semantics]
def evalTransmuteCopy (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (argVal : MirVal) : Option MirVal :=
  match evalTyByteSize adts s.tySizes srcTy,
        evalTyByteSize adts s.tySizes dstTy, argVal with
  | some srcSz, some dstSz, .ref depth gen target =>
    if decide (srcSz = dstSz) then
      match resolveRef s depth gen target with
      | some pointee =>
        match extractTransmuteBits pointee with
        | some (vSz, bits) =>
          if decide (vSz = srcSz) then
            match dstTy with
            | .param _ => some (.bytes dstSz bits)
            | .usize => if dstSz == 8 then some (.usize bits) else none
            | .unit => if dstSz == 0 then some .unit else none
            | .adt id =>
              match findAdtDecl adts id with
              | some decl =>
                match decl.allFieldsPubSafe, decl.fields with
                | true, [{ ty := .usize, access := .pubSafe }] =>
                  if dstSz == 8 then some (.adt id (.usize bits)) else none
                | _, _ => none
              | none => none
            | _ => none
          else
            none
        | none => none
      | none => none
    else
      none
  | _, _, _ => none

/-- Single-step operational evaluation of a MIR basic-block terminator.

    Models `TerminatorKind::Return`, `TerminatorKind::Goto`,
    `TerminatorKind::Unreachable`, `TerminatorKind::SwitchInt`, and
    `TerminatorKind::Call` (`panic`, `size_of`, `transmute_copy`, and static
    single-argument calls):
    - `Terminator.return_` reads `_0` (`s.locals 0`) and rejects escaping
      frame-local references via `MirVal.hasEscapingRef`. At the root frame
      (`s.stack = []`), it completes with `.terminated (.normal retVal)`. Inside
      a callee frame (`frame :: restStack`), it pops `frame`, restores
      `frame.callerLocalGens` and `frame.callerTySizes`, writes `retVal` to
      `frame.retDst` in `frame.callerLocals`, and resumes at `frame.retBlock`.
    - `Terminator.goto target` verifies
      `target.index < activeBody.blocks.length` and transfers control to
      statement `0` of `target.index`.
    - `Terminator.unreachable` triggers immediate `.failed`.
    - `Terminator.panic` terminates execution via unwinding
      (`.terminated .unwind`).
    - `Terminator.switchInt discr falseTarget trueTarget` branches on a boolean
      discriminant (`false` -> `falseTarget`; `true` -> `trueTarget`).
    - `Terminator.callSizeOf dst ty target` evaluates
      `evalTyByteSize adts s.tySizes ty`, writing the byte size to `dst` and
      jumping to `target` (or failing if `ty` has no defined size).
    - `Terminator.callTransmuteCopy dst srcTy dstTy op target` evaluates
      `evalTransmuteCopy`, writing the transmuted value to `dst` or failing with
      `.failed` if the byte sizes or pointee validity checks fail.
    - `Terminator.call1 dst callee arg target typeArgs` verifies call-site arity
      (`callee.argTys.length == 1`) and bounds, evaluates `arg`, substitutes
      `typeArgs` into `s.tySizes` via `substTySizes`, and pushes a `StackFrame`
      to execute `callee` at block `0`, statement `0`.

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
def evalMirTerminator (adts : List AdtDecl) (activeBody : MirBody)
    (s : MirState) (term : Terminator) : StepResult MirState Empty MirVal :=
  match term with
  | .return_ =>
    if 0 < activeBody.localCount then
      match s.locals 0 with
      | none => .failed
      | some retVal =>
        if retVal.hasEscapingRef s.stack.length activeBody.localCount then
          .failed
        else
          match s.stack with
          | [] => .terminated (.normal retVal)
          | frame :: restStack =>
            if frame.retDst.index < frame.callerBody.localCount &&
               frame.retBlock < frame.callerBody.blocks.length then
              .silent {
                locals := updateLocal frame.callerLocals
                  frame.retDst.index (some retVal)
                localGens := frame.callerLocalGens
                block := frame.retBlock
                stmtIdx := 0
                tySizes := frame.callerTySizes
                curBody :=
                  if restStack.isEmpty then none else some frame.callerBody
                stack := restStack
              }
            else
              .failed
    else
      .failed
  | .goto target =>
    if target.index < activeBody.blocks.length then
      .silent { s with block := target.index, stmtIdx := 0 }
    else
      .failed
  | .unreachable =>
    .failed
  | .panic =>
    .terminated .unwind
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand activeBody.localCount s.locals discr with
    | some (.bool false, locals') =>
      if falseTarget.index < activeBody.blocks.length then
        .silent {
          s with locals := locals', block := falseTarget.index, stmtIdx := 0
        }
      else
        .failed
    | some (.bool true, locals') =>
      if trueTarget.index < activeBody.blocks.length then
        .silent {
          s with locals := locals', block := trueTarget.index, stmtIdx := 0
        }
      else
        .failed
    | _ => .failed
  | .callSizeOf dst ty target =>
    if dst.index < activeBody.localCount &&
       target.index < activeBody.blocks.length then
      match evalTyByteSize adts s.tySizes ty with
      | some sz =>
        .silent { s with
          locals := updateLocal s.locals dst.index (some (.usize sz))
          block := target.index
          stmtIdx := 0
        }
      | none => .failed
    else
      .failed
  | .callTransmuteCopy dst srcTy dstTy op target =>
    if dst.index < activeBody.localCount &&
       target.index < activeBody.blocks.length then
      match evalOperand activeBody.localCount s.locals op with
      | some (argVal, locals') =>
        match evalTransmuteCopy adts { s with locals := locals' }
            srcTy dstTy argVal with
        | some outVal =>
          .silent { s with
            locals := updateLocal locals' dst.index (some outVal)
            block := target.index
            stmtIdx := 0
          }
        | none => .failed
      | none => .failed
    else
      .failed
  | .call1 dst callee arg target typeArgs =>
    if dst.index < activeBody.localCount &&
       target.index < activeBody.blocks.length &&
       callee.argTys.length == 1 &&
       2 ≤ callee.localCount &&
       0 < callee.blocks.length then
      match evalOperand activeBody.localCount s.locals arg with
      | some (argVal, callerLocals') =>
        let calleeLocals : Nat → Option MirVal :=
          updateLocal (fun _ => none) 1 (some argVal)
        let frame : StackFrame := {
          callerBody := activeBody
          callerLocals := callerLocals'
          callerLocalGens := s.localGens
          callerTySizes := s.tySizes
          retDst := dst
          retBlock := target.index
        }
        .silent {
          locals := calleeLocals
          localGens := fun _ => 0
          block := 0
          stmtIdx := 0
          tySizes := substTySizes adts s.tySizes typeArgs
          curBody := some callee
          stack := frame :: s.stack
        }
      | none => .failed
    else
      .failed

/-- Single-step transition function of a `MirBody` under ADT declarations
    `adts`: executes the statement at `s.stmtIdx` in block `s.block` of the
    active `MirBody` (`s.curBody.getD rootBody`), or the block's terminator once
    all statements in `s.block` have completed. Jumping to an out-of-bounds
    basic block or statement index triggers `.failed`. -/
@[candidate mir_semantics]
def evalMirStep (adts : List AdtDecl := []) (rootBody : MirBody)
    (s : MirState) : StepResult MirState Empty MirVal :=
  let active := s.curBody.getD rootBody
  match lookupAt active.blocks s.block with
  | none => .failed
  | some bb =>
    match lookupAt bb.stmts s.stmtIdx with
    | some stmt => evalMirStmt active s stmt
    | none =>
      if s.stmtIdx == bb.stmts.length then
        evalMirTerminator adts active s bb.terminator
      else
        .failed

/-- Relational step transition of a `MirBody` (`r = evalMirStep adts body
    s`). -/
@[candidate mir_semantics]
abbrev MirStep (adts : List AdtDecl := []) (body : MirBody) (s : MirState)
    (r : StepResult MirState Empty MirVal) : Prop :=
  r = evalMirStep adts body s

/-!
## Post-Monomorphization Error (PME) Admission
-/

/-- Inductive reachability of compile-time constant `(tySizes', c)` obligations
    required for monomorphization of `(tySizes, body)` (`Body::required_consts`
    collected across `body` and its static `Terminator.call1` callees under
    their substituted `typeArgs`).

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
inductive RequiresConst (adts : List AdtDecl := []) :
    (Nat → Nat) → MirBody → (Nat → Nat) → MirBody → Prop where
  /-- Direct PME constant `(c, typeArgs)` in `body.requiredConsts`, evaluated
      under `substTySizes adts tySizes typeArgs`. -/
  | direct {tySizes : Nat → Nat} {body c : MirBody} {typeArgs : List MirTy} :
      (c, typeArgs) ∈ body.requiredConsts →
      RequiresConst adts tySizes body (substTySizes adts tySizes typeArgs) c
  /-- Transitive PME constant required by a constant `(c', typeArgs)` in
      `body.requiredConsts`. -/
  | nested {tySizes tySizes' : Nat → Nat} {body c' c : MirBody}
      {typeArgs : List MirTy} :
      (c', typeArgs) ∈ body.requiredConsts →
      RequiresConst adts (substTySizes adts tySizes typeArgs) c' tySizes' c →
      RequiresConst adts tySizes body tySizes' c
  /-- Transitive PME constant required by a static `Terminator.call1` callee
      in `body.blocks`, evaluated under the substituted type-size environment
      `substTySizes adts tySizes typeArgs`. -/
  | call1 {tySizes tySizes' : Nat → Nat} {body callee c : MirBody}
      {bb : BasicBlock} {dst : LocalId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target typeArgs →
      RequiresConst adts (substTySizes adts tySizes typeArgs) callee
        tySizes' c →
      RequiresConst adts tySizes body tySizes' c

/-- Canonical initial state for evaluating a zero-argument compile-time constant
    `MirBody` under monomorphization type sizes `tySizes`. -/
@[candidate mir_semantics]
def constEntryState (tySizes : Nat → Nat) : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0
  tySizes := tySizes

/-- Compile-Time Function Evaluation (CTFE) success predicate for a constant
    `MirBody` `c` under `adts` and monomorphization type sizes `tySizes`: `c`
    takes zero arguments (`c.argTys = []`) and reaches normal termination
    `.terminated (.normal v)` from `constEntryState tySizes`.

    If `c` panics (`.terminated .unwind`), triggers UB (`.failed`), or
    diverges, `ConstSucceeds adts tySizes c` is `False` and `rustc` rejects the
    monomorphization with a Post-Monomorphization Error (`E0080`):

    > "A constant expression is evaluated at compile time. If evaluation fails
    > (for example, due to a panic or integer overflow), compilation fails."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/const_eval.md#L1-L25 -/
@[candidate mir_semantics]
def ConstSucceeds (adts : List AdtDecl := []) (tySizes : Nat → Nat)
    (c : MirBody) : Prop :=
  c.argTys = [] ∧
  ∃ n v,
    ReachesPrefix (MirStep adts) c n (constEntryState tySizes) []
      (.terminated (.normal v))

/-- Monomorphization admission predicate for `body` under `adts` and `tySizes`:
    every compile-time constant `(tySizes', c)` satisfying
    `RequiresConst adts tySizes body tySizes' c` (including those of static
    `Terminator.call1` callees under their substituted `typeArgs`) evaluates to
    normal completion without panicking or triggering UB. -/
@[candidate mir_semantics]
def MonoAdmitted (adts : List AdtDecl := []) (tySizes : Nat → Nat)
    (body : MirBody) : Prop :=
  ∀ tySizes' c,
    RequiresConst adts tySizes body tySizes' c →
    ConstSucceeds adts tySizes' c

/-- Full initial state predicate of `MirMachine` for `body`: `s` is a valid
    structural entry state (`initEntryState adts body s`) and `body` is admitted
    by monomorphization under `s.tySizes` (`MonoAdmitted adts s.tySizes body`).

    When a monomorphization fails a Post-Monomorphization Error
    (`¬ MonoAdmitted adts s.tySizes body`), `initMirState adts body s` is
    `False`, so `EventualBehaviorOf (MirMachine adts) body` at `s` has
    `defined := True` and `val := ∅` (the bottom element `⊥` of
    `Partial (Out → Prop)`), accurately modeling that a rejected
    monomorphization has no runtime execution in either `MirLang` or
    `TargetLang`. -/
@[candidate mir_semantics]
def initMirState (adts : List AdtDecl := []) (body : MirBody)
    (s : MirState) : Prop :=
  initEntryState adts body s ∧ MonoAdmitted adts s.tySizes body

/-- Small-step operational machine for `MirBody` under ADT declarations
    `adts`. -/
@[candidate mir_semantics]
def MirMachine (adts : List AdtDecl := []) :
    SmallStepMachine MirBody MirState Empty MirVal where
  initState := initMirState adts
  step := MirStep adts

/-- Operational language of Rust MIR (`(MirMachine adts).toLanguage`). -/
@[candidate mir_semantics]
def MirLang (adts : List AdtDecl := []) :
    Language (EventualOut Empty MirVal) :=
  (MirMachine adts).toLanguage

/-- Operational behavior of a `MirBody`: the state-indexed partial behavior
    (`MirState → Partial (EventualOut Empty MirVal → Prop)`) induced by
    `MirMachine adts`. -/
@[candidate mir_semantics]
abbrev MirSem (adts : List AdtDecl := []) (body : MirBody) :
    (MirLang adts).Behavior :=
  (MirLang adts).sem body

/-!
## Library Representation Invariants and Boundary Promises
-/

/-- Admissibility of an ADT representation invariant `adtInv` for a crate's ADT
    declarations `adts` (`r[expr.struct.safety]`):
    1. Declared ADT identifiers are pairwise distinct (`NoDupIds`).
    2. Every declared ADT `decl ∈ adts` is inhabited by at least one valid value
       satisfying `v.satisfiesInv adts adtInv s (.adt decl.id)`.
    3. For any ADT `decl ∈ adts` whose fields are all `pubSafe` (and not
       `#[non_exhaustive]`), every language-valid field payload (`inner = .unit`
       or `inner.satisfiesBaseInv adts defaultAdtInv tySizes f.ty` for
       `f ∈ decl.fields`) satisfies `adtInv decl.id inner`—preventing a library
       from claiming a restricted invariant on a struct that safe downstream
       code can construct directly via struct literal syntax.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/struct-expr.md#L58-L65 -/
@[candidate mir_semantics]
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  AllHold (adts.map (fun decl =>
    ∃ (s : MirState) (v : MirVal),
      v.satisfiesInv adts adtInv s (.adt decl.id))) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (tySizes : Nat → Nat) (inner : MirVal),
      (inner = .unit ∨
       ∃ f, f ∈ decl.fields ∧
         inner.satisfiesBaseInv adts defaultAdtInv tySizes f.ty) →
      adtInv decl.id inner

/-- Mandatory postcondition specification for public library functions: on every
    initial state `s` satisfying `pre s`, the function is free of UB
    (`defined := pre s`) and any normal return value `ret` satisfies
    `ret.satisfiesInv adts adtInv s retTy`. -/
@[candidate mir_semantics]
def EnsuresRetLibInv (adts : List AdtDecl := []) (adtInv : AdtInv)
    (retTy : MirTy) (pre : MirState → Prop) : (MirLang adts).Behavior :=
  (MirLang adts).SpecOn pre (fun s out =>
    ∀ tr ret, out = .terminated tr (.normal ret) →
      ret.satisfiesInv adts adtInv s retTy)

/-- Postcondition specification for a safe function asserting that:
    - `defined := True`: every finite execution prefix is free of UB and stuck
      states (`(MirLang adts).WellFormed`), and
    - `val`: any normal return value equals the initial value of argument local
      `argLocal` (`1` for the first parameter `_1`). -/
@[candidate mir_semantics]
def EnsuresEqArg (argLocal : Nat) (adts : List AdtDecl := []) :
    (MirLang adts).Behavior :=
  (MirLang adts).Spec (fun s out =>
    ∀ tr ret, out = .terminated tr (.normal ret) →
      s.locals argLocal = some ret)

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
    waiver in the crate's TCB list. -/
@[candidate mir_semantics]
opaque rustc : MirBody → TargetArtifact := fun _ => { unit := () }

/-- Abstract operational behavior of a compiled `TargetArtifact`.

    Declared `opaque` so that no theorem can rely on an implementation artifact
    of `TargetSem`; any property of `TargetSem (rustc body)` must be derived
    from `ProductiveCompiles (MirLang adts) TargetLang (rustcCodec adts) body
    (rustc body)` and `MirSem adts body`. -/
@[candidate mir_semantics]
opaque TargetSem :
    TargetArtifact → MirState → Partial (EventualOut Empty MirVal → Prop) :=
  fun _ _ => Partial.ub

/-- Target language of compiled `TargetArtifact`s sharing the observable spine
    `EventualOut Empty MirVal` with `MirLang`. -/
@[candidate mir_semantics]
def TargetLang : Language (EventualOut Empty MirVal) :=
  Language.mkSimple TargetArtifact MirState (EventualOut Empty MirVal) TargetSem

/-- Canonical spine-preserving representation codec between `MirLang adts` and
    `TargetLang`. -/
@[candidate mir_semantics]
def rustcCodec (adts : List AdtDecl := []) :
    BehaviorCodec (MirLang adts) TargetLang where
  encodeQuery s := s
  decodeQuery s := s
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut o₂ _ h      :=
    congrArg (fun x => match x with | some v => v | none => o₂) h

/-- Audited obligation identifier in a crate's verification unit. -/
@[candidate mir_semantics]
inductive TCBItem where
  /-- Standard compiler lowering obligation for a function: `rustc` lowers
      `body` soundly under `rustcCodec`
      (`ProductiveCompiles (MirLang adts) TargetLang (rustcCodec adts) body
      (rustc body)`). Tagged with `@[candidate rustc_capture]` because this
      waiver is emitted by the `anneal-rustc-capture` pipeline when lowering a
      captured function. -/
  | @[candidate rustc_capture] rustcLowering (fnName : String) (body : MirBody)
  /-- Non-capture compilation obligation identifier for hand-written MIR crates
      whose `tcb` waiver list does not use `rustcLowering`. -/
  | fnCompiles (fnName : String) (body : MirBody)
  /-- Behavioral verification obligation for a captured function `fnName`:
      `MirSem adts body` refines its baseline UB-freedom obligation and all
      effective specifications. Disallowed in `defaultTrustPolicy` so it can
      never be waived. -/
  | fnVerified (fnName : String) (body : MirBody)
  /-- Explicit user-supplied axiom assumption (`#[anneal::axiom]`). -/
  | userAxiom (name : String) (prop : Prop)

/-- Default trust policy: standard `rustc` lowering waivers are permitted
    (guarded under `Trusted.candidate "rustc_capture"`); function verification
    obligations and unapproved user axioms cannot be waived (`False`). -/
@[candidate mir_semantics]
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => Trusted.candidate "rustc_capture" True
    | _ => False

/-- Select the compilation obligation identifier from the head of `c.tcb`,
    wrapping `.rustcLowering` in `Trusted.candidate "rustc_capture"` so crates
    that do not use `rustcLowering` do not activate
    `candidate:rustc_capture`. -/
@[candidate mir_semantics]
def TCBItem.compileIdFromItem (fnName : String) (body : MirBody) :
    TCBItem → TCBItem
  | .rustcLowering _ _ =>
    Trusted.candidate "rustc_capture" (.rustcLowering fnName body)
  | _ => .fnCompiles fnName body

/-- Select the compilation obligation identifier for `(fnName, body)` given the
    crate's `tcb` waiver list. -/
@[candidate mir_semantics]
def TCBItem.compileId (fnName : String) (body : MirBody) :
    List TCBItem → TCBItem
  | item :: _ => TCBItem.compileIdFromItem fnName body item
  | [] => .fnCompiles fnName body

/-- Rust visibility and safety role of a captured function, determining what the
    function may assume at entry and what it must guarantee to downstream
    callers (`r[unsafety]`):
    - `pubSafe traitLaws`: a public safe function (`pub fn`). Cannot attach an
      unchecked caller precondition; must be UB-free and preserve `adtInv` on
      every monomorphization-admitted call whose arguments satisfy `adtInv` and
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
  | pubUnsafe (traitLaws : Prop := True) (safetyPre : MirState → Prop)
  | priv (pre : MirState → Prop := fun _ => True)

/-- Captured MIR function pairing its identifier (`name`), lowered `MirBody`
    (`prog`), visibility/safety role (`kind`, defaulting to `.pubSafe True`),
    and additional functional specifications (`specs`, defaulting to `[]`). -/
@[candidate mir_semantics]
structure CapturedFn where
  name : String
  prog : MirBody
  kind : FnKind := .pubSafe True
  specs : List (Behavior MirState (EventualOut Empty MirVal)) := []

/-- Canonical entry precondition of `fn` under `adts` and the crate's ADT
    representation invariant `adtInv`:
    - Conjoins `initMirState adts fn.prog s` so that `effectivePre` is bounded
      to valid, monomorphization-admitted entry states for all function kinds
      (including `.priv`).
    - For `pubSafe`, generic `unsafe trait` laws hold and all arguments satisfy
      `adtInv` (`argsMatchInv adts adtInv`).
    - For `pubUnsafe`, generic `unsafe trait` laws hold, all arguments satisfy
      `adtInv`, and the caller satisfies `safetyPre s`.
    - For `priv`, the internal precondition `internalPre s` holds. -/
@[candidate mir_semantics]
def CapturedFn.effectivePre (adts : List AdtDecl := []) (adtInv : AdtInv)
    (fn : CapturedFn) (s : MirState) : Prop :=
  initMirState adts fn.prog s ∧
  match fn.kind with
  | .pubSafe traitLaws =>
    traitLaws ∧
    argsMatchInv adts adtInv fn.prog.localCount s fn.prog.argTys
  | .pubUnsafe traitLaws safetyPre =>
    traitLaws ∧
    argsMatchInv adts adtInv fn.prog.localCount s fn.prog.argTys ∧
    safetyPre s
  | .priv internalPre =>
    internalPre s

/-- Canonical specification list of `fn` under `adts` and `adtInv`: public
    functions (`.pubSafe` and `.pubUnsafe`) automatically require
    `EnsuresRetLibInv` in addition to user-supplied `fn.specs`. -/
@[candidate mir_semantics]
def CapturedFn.effectiveSpecs (adts : List AdtDecl := []) (adtInv : AdtInv)
    (fn : CapturedFn) : List (MirLang adts).Behavior :=
  let pre := fn.effectivePre adts adtInv
  match fn.kind with
  | .pubSafe _ | .pubUnsafe _ _ =>
    EnsuresRetLibInv adts adtInv fn.prog.retTy pre :: fn.specs
  | .priv _ =>
    fn.specs

/-- Per-function obligation inventory under `adts`, `adtInv`, and `tcb`:
    1. `TCBItem.compileId fn.name fn.prog tcb`: `rustc` lowers `fn.prog` soundly
       to `TargetLang` (`ProductiveCompiles (MirLang adts) TargetLang
       (rustcCodec adts) fn.prog (rustc fn.prog)`), and
    2. `.fnVerified fn.name fn.prog`: `MirSem adts fn.prog` satisfies
       `(MirLang adts).Verified (fn.effectivePre adts adtInv) (fun _ _ => True)`
       and refines baseline `(MirLang adts).WellFormedOn` and every
       specification in `fn.effectiveSpecs adts adtInv`. -/
@[candidate mir_semantics]
def CapturedFn.obligations (adts : List AdtDecl := []) (adtInv : AdtInv)
    (tcb : List TCBItem := []) (fn : CapturedFn) :
    List (Obligation TCBItem) :=
  [
    Obligation.compiles (TCBItem.compileId fn.name fn.prog tcb)
      (MirLang adts) TargetLang (rustcCodec adts) fn.prog (rustc fn.prog),
    Obligation.wellFormedAndSpecsOn (.fnVerified fn.name fn.prog)
      (MirLang adts) (fn.effectivePre adts adtInv)
      (fn.effectiveSpecs adts adtInv) fn.prog
  ]

/-- Proof obligation for an `unsafe impl` of an `unsafe trait` (or `unsafe impl
    Copy`/`Clone` for a type with `unsafe` fields): both the `impl`'s
    monomorphization/where-clause admission (`whereBounds`) and the trait's
    semantic law (`traitLaw adtInv`) must hold.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/items/implementations.md#L120-L135 -/
@[candidate mir_semantics]
structure UnsafeImplObligation where
  implName : String
  whereBounds : Prop := True
  traitLaw : AdtInv → Prop

/-- Captured Rust crate bundling its ADT declarations (`adts`), ADT
    representation invariant (`adtInv`, defaulting to `defaultAdtInv`),
    `unsafe impl` obligations (`unsafeImpls`), captured functions (`functions`),
    TCB waiver list (`tcb`), and `.olean`-bound source artifacts
    (`artifacts`). -/
@[candidate mir_semantics]
structure Crate where
  adts : List AdtDecl := []
  adtInv : AdtInv := defaultAdtInv
  unsafeImpls : List UnsafeImplObligation := []
  functions : List CapturedFn
  tcb : List TCBItem
  artifacts : List EmittedArtifact := []

/-- Top-level theorem required of every verified Rust crate:
    1. The crate contains at least one captured function (`c.functions ≠ []`).
    2. Captured function names are pairwise distinct (`NoDupIds`).
    3. The crate's ADT representation invariant is admissible (`AdmissibleAdtInv
       c.adts c.adtInv`).
    4. Every `unsafe impl` in `c.unsafeImpls` satisfies both `u.whereBounds` and
       `u.traitLaw c.adtInv`.
    5. `c.artifacts` includes `"src/lib.rs"` and every artifact satisfies
       `EmittedArtifact.holds`.
    6. Every captured function `fn ∈ c.functions` satisfies
       `VerificationResult defaultTrustPolicy c.tcb (fn.obligations c.adts
       c.adtInv c.tcb)`. -/
@[candidate mir_semantics]
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.unsafeImpls.map (fun u => u.whereBounds ∧ u.traitLaw c.adtInv)) ∧
  (∃ a, a ∈ c.artifacts ∧ a.path = "src/lib.rs") ∧
  AllHold (c.artifacts.map EmittedArtifact.holds) ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.adtInv c.tcb)))

end Trusted
