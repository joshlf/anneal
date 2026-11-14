-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
prelude
import Init.NotationExtra

/-!
# Trusted MIR Abstract Syntax Tree (`Trusted/MirAst.lean`)

Defines the first-order representation of `rustc`'s
`MirPhase::Runtime(RuntimePhase::PostCleanup)` Mid-level Intermediate
Representation (MIR) for scalar, aggregate (ADT and tuple), and reference-taking
functions (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

This module fixes the syntax vocabulary of `MirBody`; operational meaning is
assigned in `Trusted/MirSemantics.lean`.
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...), corresponding
to `rustc_middle::mir::Local`
(`compiler/rustc_middle/src/mir/mod.rs#L235-L240`):
> "The first local is the return value pointer, followed by `arg_count` locals
> for the function arguments, followed by any user-declared variables and
> temporaries." -/
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) in `Body::basic_blocks`
(`compiler/rustc_middle/src/mir/mod.rs#L207-L209`):
> "A list of basic blocks. References to basic block use a newtyped index type
> [`BasicBlock`] that indexes into this vector." -/
structure BlockId where
  index : Nat

/-- MIR type grammar for scalar, aggregate, and reference types
(`src/types/numeric.md#L37-L38`, `src/types/boolean.md#L6-L7`,
`compiler/rustc_type_ir/src/ty_kind.rs#L106-L165`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."

Integer types in this subset are unsigned (`usize` and `uint bits`), matching
the unsigned scalar payload `MirVal.int (val : Nat)`. -/
inductive MirTy where
  | usize
  | uint (bits : Nat)
  | bool
  | unit
  | never
  | adt (id : Nat)
  | tuple (elems : List MirTy)
  | ref (inner : MirTy)
  | refMut (inner : MirTy)

/-- Single projection step along a `Place` path
(`rustc_middle::mir::ProjectionElem`,
`compiler/rustc_middle/src/mir/syntax.rs#L1192-L1283`):
- `.deref`: dereference a reference or pointer (`*p`).
- `.field idx`: project field `idx` (`p.idx`). -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)

/-- Memory location path rooted at a `LocalId` followed by a sequence of
projections (`rustc_middle::mir::Place`,
`compiler/rustc_middle/src/mir/syntax.rs#L1168-L1187`):
> "A `Place` represents a memory location: a local variable together with a
> list of projections (field accesses, dereferences, indexing, etc.)." -/
structure Place where
  loc : LocalId
  projection : List PlaceElem := []

/-- Runtime MIR value (`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are 'valid', and producing an invalid value is hence immediate UB."

- `.uninit`: an uninitialized sub-value before initialization or after a move;
  reading any value containing `.uninit` is undefined behavior
  (`MirVal.isFullyInit`).
- `.int val`: an initialized scalar integer value.
- `.bool val`: an initialized boolean value (`false` or `true`).
- `.unit`: the zero-sized unit value `()`.
- `.adt id inner`: an aggregate struct value of declaration `id` whose field
  spine is stored in `inner` as a right-nested `.fieldCons` chain terminated by
  `.unit`.
- `.fieldCons head tail`: right-nested field spine for structs and tuples.
- `.ref mutable gen loc fieldPath reborrowDepth`: a shared (`mutable = false`)
  or mutable (`mutable = true`) reference to sub-place `fieldPath` of local slot
  `loc` at reborrow nesting depth `reborrowDepth`, valid only while `loc`'s
  storage generation equals `gen` and no conflicting active borrow or child
  reborrow overlaps `fieldPath`. -/
inductive MirVal where
  | uninit
  | int (val : Nat)
  | bool (val : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | fieldCons (head : MirVal) (tail : MirVal)
  | ref (mutable : Bool) (gen : Nat) (loc : LocalId)
      (fieldPath : List Nat := []) (reborrowDepth : Nat := 0)

/-- MIR operand (`rustc_middle::mir::Operand`,
`compiler/rustc_middle/src/mir/syntax.rs#L1303-L1335`):
> "Creates a value by loading the given place."
> "This *may* additionally overwrite the place with `uninit` bytes..." -/
inductive Operand where
  | copy (src : Place)
  | move (src : Place)
  | constVal (val : MirVal)

/-- Binary operator on `Rvalue.binaryOp` (`rustc_middle::mir::BinOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709`). -/
inductive BinOp where
  | add
  | sub
  | mul
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | bitAnd
  | bitOr
  | bitXor

/-- Unary operator on `Rvalue.unaryOp` (`rustc_middle::mir::UnOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617`). -/
inductive UnOp where
  | not

/-- Right-hand side value computation (`rustc_middle::mir::Rvalue`,
`compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488`):
> "Yields the operand unchanged, except for a potential retag."
> "Creates a reference of the indicated kind to the place." -/
inductive Rvalue where
  | use (op : Operand)
  | ref (src : Place)
  | refMut (src : Place)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | unaryOp (op : UnOp) (src : Operand)
  | aggregateFields (ops : List Operand) (adtId : Option Nat := none)
  | copyForDeref (src : Place)

/-- Statement inside a MIR basic block (`rustc_middle::mir::StatementKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L397-L466`):
> "Assign statements roughly correspond to an assignment in Rust proper (`x =
> ...`) except without the possibility of dropping the previous value."
> "`StorageLive` and `StorageDead` statements mark the live range of a local."
-/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | placeMention (src : Place)
  | nop

/-- Single `(value, target)` branch arm in `SwitchTargets`
(`rustc_middle::mir::SwitchTargets`,
`compiler/rustc_middle/src/mir/terminator.rs#L30-L56`). -/
structure SwitchBranch where
  val : Nat
  target : BlockId

/-- Multi-way integer switch target table on `Terminator.switchInt`
(`rustc_middle::mir::SwitchTargets`,
`compiler/rustc_middle/src/mir/terminator.rs#L30-L56`):
> "Target blocks for a `SwitchInt` terminator. Each value in `values`
> corresponds to a target block in `targets`, and the final element of
> `targets` is the `otherwise` block." -/
structure SwitchTargets where
  branches : List SwitchBranch := []
  otherwise : BlockId

/-- Basic-block control-flow terminator (`rustc_middle::mir::TerminatorKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L684-L798`):
> "Terminators are the final statement in a basic block and represent control
> flow between basic blocks." -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | switchInt (discr : Operand) (targets : SwitchTargets)
  | unreachable

/-- Single basic block in a `MirBody` (`rustc_middle::mir::BasicBlockData`,
`compiler/rustc_middle/src/mir/mod.rs#L1215-L1234`). -/
structure BasicBlock where
  stmts : List Stmt := []
  terminator : Terminator

/-- Captured `Runtime(PostCleanup)` MIR function body
(`rustc_middle::mir::Body`,
`compiler/rustc_middle/src/mir/mod.rs#L202-L270`):
> "The lowered representation of a single function."
> "Declarations of locals. The first local is the return value pointer,
> followed by `arg_count` locals for the function arguments, followed by any
> user-declared variables and temporaries." -/
structure MirBody where
  argCount : Nat
  localCount : Nat
  ptrWidthBits : Nat := 64
  localTys : List MirTy := []
  blocks : List BasicBlock

end Trusted
