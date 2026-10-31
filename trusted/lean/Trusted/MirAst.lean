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

/-!
# Trusted MIR Abstract Syntax Tree (`Trusted/MirAst.lean`)

This module defines the owned representation of `rustc`'s
`MirPhase::Runtime(RuntimePhase::PostCleanup)` Mid-level Intermediate
Representation (MIR) for scalar, aggregate (ADT), and polymorphic functions,
including `Body::required_consts` for Post-Monomorphization Error (PME)
constant-evaluation obligations.

Every declaration in this file that models a `rustc` MIR construct or Rust
type/value concept explains the correspondence and both quotes and cites its
normative source at the repository's pinned revisions
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

This module belongs to `trusted/lean/` and contains only data definitions
(zero theorems).
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...).

    Corresponds to `rustc_middle::mir::Local` indexing into `Body::local_decls`,
    where local `0` (`_0`) is the return place, `1 ..= arg_count` (`_1`, ...)
    are caller-initialized function arguments, and higher indices are
    user-declared variables and temporaries:

    > "The first local is the return value pointer, followed by `arg_count`
    > locals for the function arguments, followed by any user-declared
    > variables and temporaries."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L235-L240 -/
@[candidate mir_ast]
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) within a MIR body.

    Corresponds to `rustc_middle::mir::BasicBlock` indexing into
    `Body::basic_blocks`:

    > "A list of basic blocks. References to basic block use a newtyped index
    > type [`BasicBlock`] that indexes into this vector."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
@[candidate mir_ast]
structure BlockId where
  index : Nat

/-- Visibility and safety classification of a struct/ADT field, determining
    whether safe downstream crates can construct or mutate the field directly.

    Corresponds to `rustc_middle::ty::FieldDef::vis` (`Visibility::Public` vs.
    restricted/private visibility) and `FieldDef::safety` (`Safety::Safe` vs.
    `Safety::Unsafe` under `#![feature(unsafe_fields)]`, RFC 3458):

    > "Visibility of the field (mostly matters for structs)."
    >
    > "Safety of the field (only `Unsafe` under `feature(unsafe_fields)`)."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/adt.rs#L114-L120 -/
@[candidate mir_ast]
inductive FieldAccess where
  /-- Public safe field (`pub f: T`). -/
  | pubSafe
  /-- Module-private or restricted field (`f: T`). -/
  | priv
  /-- Unsafe field (`pub unsafe f: T` or `unsafe f: T`). -/
  | unsafeField

/-- MIR type grammar for scalar, aggregate (ADT), and polymorphic types.

    - `MirTy.usize` models Rust's pointer-sized unsigned integer type `usize`.
    - `MirTy.bool` models Rust's boolean type `bool` (`false` / `true`).
    - `MirTy.unit` models Rust's unit type `()` (an empty tuple).
    - `MirTy.adt id` models a user-defined struct (`TyKind::Adt`) identified by
      its crate-local index `id`.
    - `MirTy.param idx` models a generic type parameter (`TyKind::Param`, e.g.,
      `Src` at index `0`, `Dst` at index `1`) whose concrete byte size is
      resolved at monomorphization time via `MirState.tySizes idx`.
    - `MirTy.ref inner` models an immutable shared reference `&T`
      (`TyKind::Ref`) to pointee type `inner`.

    > "The `usize` type is an unsigned integer type with the same number of
    > bits as the platform's pointer type. It can represent every memory
    > address in the process."
    >
    > "The boolean type or bool is a primitive data type that can take on one
    > of two values, called `true` and `false`."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/boolean.md#L6-L7
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_type_ir/src/ty_kind.rs#L106-L165 -/
@[candidate mir_ast]
inductive MirTy where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)

/-- Single field declaration inside an ADT (`rustc_middle::ty::FieldDef`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/adt.rs#L108-L121 -/
@[candidate mir_ast]
structure FieldDecl where
  ty : MirTy
  access : FieldAccess

/-- Captured ADT (struct) declaration recording its crate-local identifier,
    field declarations, and `#[non_exhaustive]` attribute status.

    Corresponds to `rustc_middle::ty::AdtDefData` and `VariantDef`:

    > "If `true`, this variant has the `#[non_exhaustive]` attribute, which
    > prevents external crates from constructing it or matching on it
    > exhaustively."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/adt.rs#L140-L176 -/
@[candidate mir_ast]
structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  nonExhaustive : Bool := false

/-- Whether an ADT's fields can all be constructed and mutated directly by safe
    downstream code via struct literal syntax (`Adt { ... }`) without `unsafe`.

    In Rust (`r[expr.struct.safety]`), constructing a struct literal in safe
    code outside the defining module is permitted if and only if the struct is
    not `#[non_exhaustive]` and every field is visible (`pub`) and safe (not
    marked `unsafe`):

    > "A struct expression can only be used if all fields are visible in the
    > current scope, and the struct is not marked `#[non_exhaustive]` in
    > another crate."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/struct-expr.md#L58-L65 -/
@[candidate mir_ast]
def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  !decl.nonExhaustive &&
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv | .unsafeField => false)

/-- Initialized runtime value.

    In Rust, scalar and aggregate values must be initialized when produced;
    uninitialized locals are represented in `MirState` (`Trusted.MirSemantics`)
    by `Option.none` rather than a `MirVal` constructor:

    > "The Rust compiler assumes that all values produced during program
    > execution are "valid", and producing an invalid value is hence immediate
    > UB."
    >
    > "* An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer
    > must be initialized, i.e., must not be obtained from uninitialized
    > memory."
    >
    > "* A `bool` must be initialized, and must have the value `0` (`false`) or
    > `1` (`true`)."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L132 -/
@[candidate mir_ast]
inductive MirVal where
  /-- Initialized `usize` scalar with bit value `bits`. -/
  | usize (bits : Nat)
  /-- Initialized `bool` scalar (`false` or `true`). -/
  | bool (b : Bool)
  /-- Unit value `()`. -/
  | unit
  /-- Single-field ADT value wrapping `inner`. -/
  | adt (id : Nat) (inner : MirVal)
  /-- Initialized byte representation of a `Copy` type parameter of byte size
      `sz` and bit content `bits`. -/
  | bytes (sz : Nat) (bits : Nat)
  /-- Shared reference (`&T`) pointing to live local variable `loc`. -/
  | ref (loc : LocalId)

/-- MIR operand evaluated to produce a value in an `Rvalue` or terminator.

    Corresponds to `rustc_middle::mir::Operand` (`Copy`, `Move`, `Constant`)
    specialized to unprojected local places (`Place { local, projection: [] }`):
    - `copy src`: loads the value in `src` without modifying `src`.
    - `move src`: loads the value in `src` and deinitializes `src` so a
      subsequent read before re-initialization is Undefined Behavior.
    - `constVal val`: yields the constant `val` directly.

    > "Creates a value by loading the given place.
    >
    > Before drop elaboration, the type of the place must be `Copy`. After drop
    > elaboration there is no such requirement."
    >
    > "Creates a value by performing loading the place, just like the `Copy`
    > operand.
    >
    > This *may* additionally overwrite the place with `uninit` bytes,
    > depending on how we decide in [UCG#188]. You should not emit MIR that may
    > attempt a subsequent second load of this place without first
    > re-initializing it."
    >
    > "Constants are already semantically values, and remain unchanged."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310 -/
@[candidate mir_ast]
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

/-- Binary comparison operator in `Rvalue.binaryOp`.

    Corresponds to `rustc_middle::mir::BinOp::Eq`:

    > "The `==` operator (equality)"

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1686-L1716 -/
@[candidate mir_ast]
inductive BinOp where
  | eq

/-- Right-hand side value computation of a MIR assignment statement.

    Corresponds to `rustc_middle::mir::Rvalue` (`Use`, `BinaryOp`,
    `Aggregate(AggregateKind::Adt, ...)`, field projection `(_x.0: T)`, shared
    borrow `&_x`, and shared reborrow `&(*_x)`):

    > "Yields the operand unchanged, except for a potential retag."
    >
    > "Creates a pointer/reference to the given place."
    >
    > "Applies the binary operation to the twoOperands."
    >
    > "Creates an aggregate value, like a tuple or struct."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1340-L1435 -/
@[candidate mir_ast]
inductive Rvalue where
  /-- `Rvalue::Use(op)`. -/
  | use (op : Operand)
  /-- `Rvalue::BinaryOp(op, Box<(lhs, rhs)>)`. -/
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  /-- `Rvalue::Aggregate(Box<AggregateKind::Adt(adtId, ...)>, [op])`. -/
  | aggregate (adtId : Nat) (op : Operand)
  /-- Copy of field `0` from an ADT local (`copy (_src.0: T)`). -/
  | field0 (src : LocalId)
  /-- Shared borrow `&_src` (`Rvalue::Ref(_, BorrowKind::Shared, _src)`). -/
  | ref (src : LocalId)
  /-- Shared reborrow `&(*_src)` (`Rvalue::Ref` of a dereferenced reference
      local). -/
  | reborrow (src : LocalId)

/-- Sequential statement inside a MIR basic block.

    Corresponds to `rustc_middle::mir::StatementKind` (`Assign`, `StorageLive`,
    `StorageDead`, and `Nop`):
    - `assign dst rv`: evaluates `rv` and writes the resulting value to `dst`.
    - `storageLive loc` / `storageDead loc`: marks the start or end of a local's
      live storage range, leaving `loc` uninitialized.
    - `nop`: advances to the next statement without modifying locals (also used
      for `ConstEvalCounter` statements in CTFE MIR bodies).

    > "Assign statements roughly correspond to an assignment in Rust proper
    > (`x = ...`) except without the possibility of dropping the previous value
    > (that must be done separately, if at all). The *exact* way this works is
    > undecided. It probably does something like evaluating the LHS to a place,
    > then the RHS to a value, and then storing the value to the place."
    >
    > "`StorageLive` and `StorageDead` statements mark the live range of a
    > local."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385 -/
@[candidate mir_ast]
inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

mutual
  /-- Control-flow transfer at the end of a MIR basic block.

      Corresponds to `rustc_middle::mir::TerminatorKind` (`Return`, `Goto`,
      `Unreachable`, `SwitchInt`, and `Call`):
      - `return_`: returns the value currently stored in the return place `_0`.
      - `goto target`: branches unconditionally to the start of `target`.
      - `unreachable`: marks an unreachable control-flow point (including
        `core::hint::unreachable_unchecked()`) whose execution is immediate
        Undefined Behavior.
      - `panic`: diverging call to `core::panicking::panic(...)`, which
        terminates execution via unwinding (and causes CTFE of a
        `requiredConsts` entry to fail with a Post-Monomorphization Error).
      - `switchInt discr falseTarget trueTarget`: branches on a boolean
        discriminant (`0` / `false` jumps to `falseTarget`; `otherwise` / `true`
        jumps to `trueTarget`).
      - `callSizeOf dst ty target`: call to `core::mem::size_of::<ty>()`,
        storing the byte size of `ty` in `dst` and continuing at `target`.
      - `callTransmuteCopy dst srcTy dstTy op target`: call to
        `core::mem::transmute_copy::<srcTy, dstTy>(op)`, copying the referenced
        value to `dst` if `srcTy` and `dstTy` have equal byte size (or failing
        with `.failed` on size mismatch) and continuing at `target`.
      - `call1 dst callee arg target typeArgs`: static single-argument call to
        `callee` instantiated with `typeArgs`, storing the returned value in
        `dst` and continuing at `target`.

      > "Block has one successor; we continue execution there."
      >
      > "Switches based on the computed value.
      >
      > First, evaluates the `discr` operand. The type of the operand must be a
      > signed or unsigned integer, char, or bool, and must match the given
      > type. Then, if the list of switch targets contains the computed value,
      > continues execution at the associated basic block. Otherwise, continues
      > execution at the 'otherwise' basic block."
      >
      > "Returns from the function."
      >
      > "Indicates a terminator that can never be reached.
      >
      > Executing this terminator is UB."

      Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L798 -/
  @[candidate mir_ast]
  inductive Terminator where
    | return_
    | goto (target : BlockId)
    | unreachable
    | panic
    | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
    | callSizeOf (dst : LocalId) (ty : MirTy) (target : BlockId)
    | callTransmuteCopy (dst : LocalId) (srcTy dstTy : MirTy) (op : Operand)
        (target : BlockId)
    | call1 (dst : LocalId) (callee : MirBody) (arg : Operand) (target : BlockId)
        (typeArgs : List MirTy := [])

  /-- Basic block consisting of sequential statements and a single terminator.

      Corresponds to `rustc_middle::mir::BasicBlockData` in
      `Body::basic_blocks`.

      Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
  @[candidate mir_ast]
  structure BasicBlock where
    stmts : List Stmt
    terminator : Terminator

  /-- Lowered `Runtime(PostCleanup)` MIR body of a single function or
      compile-time constant.

      Corresponds to `rustc_middle::mir::Body`, recording the parameter types
      (`arg_count` arguments starting at local `1`), the return type (`_0`), the
      total number of locals, the control-flow graph of basic blocks, and the
      list of compile-time constant MIR bodies (`requiredConsts`) that must
      evaluate to normal completion during monomorphization:

      > "The lowered representation of a single function."
      >
      > "Starting at local 1, `arg_count` locals will be provided by the caller
      > and can be assumed to be initialized."
      >
      > "Constants that are required to evaluate successfully for this `Body` to
      > be well-formed. Wait until monomorphization to evaluate them."

      Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L204-L285 -/
  @[candidate mir_ast]
  structure MirBody where
    argTys : List MirTy
    retTy : MirTy
    localCount : Nat
    blocks : List BasicBlock
    requiredConsts : List MirBody := []
end

end Trusted
