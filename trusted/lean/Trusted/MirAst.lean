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

Defines the first-order representation of a subset of `rustc`'s
`MirPhase::Runtime(RuntimePhase::PostCleanup)` Mid-level Intermediate
Representation (MIR) at
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, with Rust
semantics taken from
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`. The subset
covers functions over unsigned integers, `bool`, `()`, structs and tuples, and
shared and mutable references. At the pin, `rustc` builds struct and tuple
values with `Rvalue::Aggregate`, which this subset omits, so aggregate values
enter a body only through its arguments, aggregate constants, and copies (a
body can also fill an uninitialized aggregate local field by field). The
syntax types below list the MIR constructs this subset omits; a producer of
`MirBody` values must reject any body that uses one rather than approximate
it.

Citation convention: paths beginning with `compiler/` or `src/tools/` refer
to `rust-lang/rust` at the commit above, and all other `src/` paths refer to
`rust-lang/reference` at the commit above.

This module fixes the syntax vocabulary of `MirBody`; operational meaning is
assigned in `Trusted/MirSemantics.lean`.
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...), corresponding
to `rustc_middle::mir::Local`
(`compiler/rustc_middle/src/mir/mod.rs#L861-L869`).
The body's local declarations fix the order of the locals
(`compiler/rustc_middle/src/mir/mod.rs#L235-L239`):
> "The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries." -/
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) in `Body::basic_blocks`
(`compiler/rustc_middle/src/mir/mod.rs#L207-L209`):
> "A list of basic blocks. References to basic block use a newtyped index type
> [`BasicBlock`] that indexes into this vector." -/
structure BlockId where
  index : Nat

/-- Fuel-indexed syntax tree backing `MirTy` so structural equality and type
inspection elaborate via `@Nat.recCompiled` without requiring `noncomputable`
eliminators under `prelude`. `.nil` and `.cons` are not types: they build the
field lists of `.adt` and `.tuple`, and `Trusted/MirSemantics.lean`
(`MirTy.wellFormed`) rejects declared types that use them anywhere else. -/
inductive MirTyTree : Nat → Type where
  | usize : MirTyTree 0
  | uint (bits : Nat) : MirTyTree 0
  | bool : MirTyTree 0
  | unit : MirTyTree 0
  | never : MirTyTree 0
  | adt {f : Nat} (id : Nat) (fields : MirTyTree f) : MirTyTree (f + 1)
  | tuple {f : Nat} (elems : MirTyTree f) : MirTyTree (f + 1)
  | nil : MirTyTree 0
  | cons {fh ft : Nat} (head : MirTyTree fh) (tail : MirTyTree ft) :
      MirTyTree (fh + ft + 1)
  | ref {f : Nat} (inner : MirTyTree f) : MirTyTree (f + 1)
  | refMut {f : Nat} (inner : MirTyTree f) : MirTyTree (f + 1)

/-- MIR type grammar for scalar, aggregate, and reference types
(`src/types/numeric.md#L37-L38`, `src/types/boolean.md#L8-L9`,
`compiler/rustc_type_ir/src/ty_kind.rs#L136-L347`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."
> "The *boolean type* or *bool* is a primitive data type that can take on one
> of two values, called *true* and *false*."
> "Defines the kinds of types used by the type system."

Integer types in this subset are unsigned (`usize` and `uint bits`), matching
the unsigned scalar payload `MirVal.int (val : Nat)`. The subset has no signed
integer, `char`, float, `str`, array, slice, raw-pointer, function, closure,
enum, or union type; a producer must reject a body whose locals use one. -/
structure MirTy where
  fuel : Nat
  tree : MirTyTree fuel

namespace MirTy

/-- Platform pointer-sized unsigned integer type `usize`. -/
def usize : MirTy := ⟨0, .usize⟩

/-- Fixed-width unsigned integer type `u8`, `u16`, `u32`, `u64`, or `u128`.

`bits` must be `8`, `16`, `32`, `64`, or `128`. The constructor accepts any
`Nat` so that the syntax stays first-order, but `Trusted/MirSemantics.lean`
assigns no meaning to other widths: `MirTy.uintWidthsSupported` rejects any
`MirBody` that declares one before execution starts, and `tyBitWidth` and
`checkValMatchesTy` give such a type no bit-width and no inhabitants. -/
def uint (bits : Nat) : MirTy := ⟨0, .uint bits⟩

/-- Boolean type `bool`. -/
def bool : MirTy := ⟨0, .bool⟩

/-- Unit type `()`. -/
def unit : MirTy := ⟨0, .unit⟩

/-- Never type `!`. -/
def never : MirTy := ⟨0, .never⟩

/-- Pack a list of `MirTy` values into a right-nested `.cons`/`.nil` spine. -/
def packList (ts : List MirTy) : MirTy :=
  ts.foldr (fun h acc => ⟨h.fuel + acc.fuel + 1, .cons h.tree acc.tree⟩)
    ⟨0, .nil⟩

/-- Unpack a right-nested `.cons`/`.nil` spine into a `List MirTy`. -/
def unpackList (t : MirTy) : List MirTy :=
  @Nat.recCompiled (fun _ => MirTy → List MirTy)
    (fun _ => [])
    (fun _ ih cur =>
      match cur with
      | ⟨_, .cons h r⟩ => ⟨_, h⟩ :: ih ⟨_, r⟩
      | _ => [])
    t.fuel t

/-- Struct type `adt id fieldTys`: declaration `id` with one variant whose
fields have types `fieldTys` and occupy disjoint storage
(`src/type-layout.md#L178-L179`):
> "For [structs], it is further guaranteed that the fields do not overlap."

This AST has no union or enum type. `Trusted/MirSemantics.lean` treats
distinct fields of an `.adt` as disjoint places (`pathsOverlap`), which is
wrong for a union, whose fields share storage
(`src/items/unions.md#L24-L25`):
> "The key property of unions is that all fields of a union share common
> storage."

`.adt` represents structs only. A producer of `MirBody` values must reject a
program that uses a union or an enum rather than encode it as `.adt`. -/
def adt (id : Nat) (fieldTys : List MirTy) : MirTy :=
  let packed := packList fieldTys
  ⟨packed.fuel + 1, .adt id packed.tree⟩

/-- Tuple type `(T_0, ..., T_{n-1})`. -/
def tuple (elems : List MirTy) : MirTy :=
  let packed := packList elems
  ⟨packed.fuel + 1, .tuple packed.tree⟩

/-- Shared reference type `&inner`. -/
def ref (inner : MirTy) : MirTy := ⟨inner.fuel + 1, .ref inner.tree⟩

/-- Mutable reference type `&mut inner`. -/
def refMut (inner : MirTy) : MirTy := ⟨inner.fuel + 1, .refMut inner.tree⟩

end MirTy

/-- Single projection step along a `Place` path
(`rustc_middle::mir::ProjectionElem`,
`compiler/rustc_middle/src/mir/syntax.rs#L1169-L1258`):
- `.deref`: dereference a reference or pointer (`*p`).
- `.field idx`: project field `idx` (`p.idx`).

The subset omits the other pinned projections, `Index`, `ConstantIndex`,
`Subslice`, `Downcast`, `OpaqueCast`, and `UnwrapUnsafeBinder`
(`compiler/rustc_middle/src/mir/syntax.rs#L1195-L1257`); a producer must
reject a body whose places use one. -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)

/-- Memory location path rooted at a `LocalId` followed by a sequence of
projections (`rustc_middle::mir::Place`,
`compiler/rustc_middle/src/mir/syntax.rs#L1092`,
`compiler/rustc_middle/src/mir/syntax.rs#L1106-L1107`,
`compiler/rustc_middle/src/mir/syntax.rs#L1161-L1167`):
> "Places roughly correspond to a "location in memory.""
> "Each local naturally corresponds to the place `Place { local, projection:
> [] }`. This place has the address of the local's allocation and the type of
> the local."
> "/// projection out of a place (access a field, deref a pointer, etc)
> pub projection: &'tcx List<PlaceElem<'tcx>>," -/
structure Place where
  loc : LocalId
  projection : List PlaceElem := []

/-- Fuel-indexed syntax tree backing `MirVal` so structural folds over runtime
values elaborate via `@Nat.recCompiled` without requiring `noncomputable`
eliminators under `prelude`. -/
inductive MirValTree : Nat → Type where
  | uninit : MirValTree 0
  | int (val : Nat) : MirValTree 0
  | bool (val : Bool) : MirValTree 0
  | unit : MirValTree 0
  | adt {f : Nat} (id : Nat) (inner : MirValTree f) : MirValTree (f + 1)
  | fieldCons {fh ft : Nat} (head : MirValTree fh) (tail : MirValTree ft) :
      MirValTree (fh + ft + 1)
  | ref (mutable : Bool) (gen : Nat) (loc : LocalId)
      (fieldPath : List Nat := []) (reborrowDepth : Nat := 0) : MirValTree 0

/-- Runtime MIR value (`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are "valid", and producing an invalid value is hence immediate UB."

- `.uninit`: an uninitialized sub-value before initialization or after a move;
  reading any value containing `.uninit` is undefined behavior
  (`MirVal.isFullyInit`).
- `.int val`: an initialized scalar integer value.
- `.bool val`: an initialized boolean value (`false` or `true`).
- `.unit`: the zero-sized unit value `()`.
- `.adt id inner`: a struct value (see `MirTy.adt`) of declaration `id` whose
  field spine is stored in `inner` as a right-nested `.fieldCons` chain
  terminated by `.unit`.
- `.fieldCons head tail`: right-nested field spine for structs and tuples.
- `.ref mutable gen loc fieldPath reborrowDepth`: a shared (`mutable = false`)
  or mutable (`mutable = true`) reference to sub-place `fieldPath` of local slot
  `loc` whose tag has depth `reborrowDepth` in the reborrow tree of its
  referent (`Trusted/MirSemantics.lean`, `refDepthConflicts`). It is valid
  only while `loc`'s storage generation equals `gen` and no access has retired
  it. -/
structure MirVal where
  fuel : Nat
  tree : MirValTree fuel

namespace MirVal

/-- An uninitialized sub-value before initialization or after a move. -/
def uninit : MirVal := ⟨0, .uninit⟩

/-- An initialized scalar integer value. -/
def int (val : Nat) : MirVal := ⟨0, .int val⟩

/-- An initialized boolean value (`false` or `true`). -/
def bool (val : Bool) : MirVal := ⟨0, .bool val⟩

/-- The zero-sized unit value `()`. -/
def unit : MirVal := ⟨0, .unit⟩

/-- A struct value of declaration `id` whose field spine is `inner` (see
`MirTy.adt`). -/
def adt (id : Nat) (inner : MirVal) : MirVal :=
  ⟨inner.fuel + 1, .adt id inner.tree⟩

/-- Right-nested field spine node for structs and tuples. -/
def fieldCons (head tail : MirVal) : MirVal :=
  ⟨head.fuel + tail.fuel + 1, .fieldCons head.tree tail.tree⟩

/-- A shared (`mutable = false`) or mutable (`mutable = true`) reference to
sub-place `fieldPath` of local slot `loc` at reborrow nesting depth
`reborrowDepth`. -/
def ref (mutable : Bool) (gen : Nat) (loc : LocalId)
    (fieldPath : List Nat := []) (reborrowDepth : Nat := 0) : MirVal :=
  ⟨0, .ref mutable gen loc fieldPath reborrowDepth⟩

end MirVal

/-- MIR operand (`rustc_middle::mir::Operand`,
`compiler/rustc_middle/src/mir/syntax.rs#L1282-L1314`):
> "Creates a value by loading the given place."
> "This *may* additionally overwrite the place with `uninit` bytes, depending
> on how we decide in [UCG#188]."
> "Constants are already semantically values, and remain unchanged."

The subset omits the pinned `Operand::RuntimeChecks` variant
(`compiler/rustc_middle/src/mir/syntax.rs#L1313`), which the runtime cleanup
pass `LowerIntrinsics` introduces when it lowers the `ub_checks`,
`contract_checks`, and `overflow_checks` intrinsics
(`compiler/rustc_mir_transform/src/lib.rs#L673`,
`compiler/rustc_mir_transform/src/lower_intrinsics.rs#L29-L39`); a producer
must reject a body that uses it. -/
inductive Operand where
  | copy (src : Place)
  | move (src : Place)
  | constVal (val : MirVal)

/-- Binary operator on `Rvalue.binaryOp` (`rustc_middle::mir::BinOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1606-L1698`). The subset omits the
pinned operators `AddUnchecked`, `AddWithOverflow`, `SubUnchecked`,
`SubWithOverflow`, `MulUnchecked`, `MulWithOverflow`, `Div`, `Rem`, `Shl`,
`ShlUnchecked`, `Shr`, `ShrUnchecked`, `Cmp`, and `Offset`; a producer must
reject a body that uses one. -/
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
`compiler/rustc_middle/src/mir/syntax.rs#L1588-L1604`). The subset omits
`Neg` and `PtrMetadata`; a producer must reject a body that uses either. -/
inductive UnOp where
  | not

/-- Whether an `Rvalue.use` performs a retag (`rustc_middle::mir::WithRetag`,
`compiler/rustc_middle/src/mir/syntax.rs#L485-L491`):
> "Describes whether this operand use performs a retag."

MIR building emits `Yes` when it lowers an expression operand
(`compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs#L427`), while the
compiler-inserted dereference temporaries are lowered to `No`
(`compiler/rustc_mir_transform/src/erase_deref_temps.rs#L19-L24`). The flag
mirrors `Rvalue::Use(Operand, WithRetag)` exactly, and `Rvalue.use` defaults
to `yes`; `Trusted/MirSemantics.lean` (`bodyDerefTempsValid`) accepts `no` only
for dereference temporaries. `Trusted/MirSemantics.lean`
(`retagVal`) gives `yes` the meaning of a reborrow of every reference in the
copied value, and gives `no` the meaning of a plain copy that keeps each
reference's identity. -/
inductive WithRetag where
  | no
  | yes

/-- Right-hand side value computation in `Runtime(PostCleanup)` MIR
(`rustc_middle::mir::Rvalue`,
`compiler/rustc_middle/src/mir/syntax.rs#L1342-L1467`):
> "Yields the operand unchanged, except for a potential retag."
> "Creates a reference of the indicated kind to the place."

The subset represents `Use`, `Ref` (shared and mutable borrows only),
`BinaryOp`, and `UnaryOp`. It omits the other pinned `Rvalue` variants:
`Repeat`, `ThreadLocalRef`, `RawPtr`, `Cast`, `Discriminant`, `Aggregate`,
`CopyForDeref`, `WrapUnsafeBinder`, and `Reborrow`. `Aggregate` in particular
survives into runtime MIR at the pin: the validator checks tuple and struct
aggregates without restricting them to earlier phases
(`compiler/rustc_mir_transform/src/validate.rs#L1018-L1100`). A producer of
`MirBody` values must reject a body that uses any omitted variant, and must
not rewrite one into other statements (for example, an `Aggregate` into
field-wise assignments). `CopyForDeref` does not occur in runtime MIR
(`compiler/rustc_mir_transform/src/validate.rs#L1013-L1017`):
> "`CopyForDeref` should have been removed in runtime MIR"
because `EraseDerefTemps` lowers it to `Use(.., WithRetag::No)` (see
`WithRetag`). -/
inductive Rvalue where
  | use (op : Operand) (withRetag : WithRetag := .yes)
  | ref (src : Place)
  | refMut (src : Place)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | unaryOp (op : UnOp) (src : Operand)

/-- Statement inside a MIR basic block (`rustc_middle::mir::StatementKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L298-L456`):
> "Assign statements roughly correspond to an assignment in Rust proper (`x =
> ...`) except without the possibility of dropping the previous value (that
> must be done separately, if at all)."
> "`StorageLive` and `StorageDead` statements mark the live range of a local."

The subset represents `Assign`, `StorageLive`, `StorageDead`, `PlaceMention`,
and `Nop`. A producer must reject a body that contains any other pinned
`StatementKind` (`FakeRead`, `SetDiscriminant`, `AscribeUserType`, `Coverage`,
`Intrinsic`, `ConstEvalCounter`, or `BackwardIncompatibleDropHint`).

`PlaceMention` and `Nop` normally do not reach `Runtime(PostCleanup)` MIR: the
runtime cleanup passes run `RemovePlaceMention` before that phase
(`compiler/rustc_mir_transform/src/lib.rs#L671-L678`), and it deletes both
unless `-Zmir-preserve-ub` is set
(`compiler/rustc_mir_transform/src/remove_place_mention.rs#L12-L23`):
> "PassPolicy::optional_non_optimization(
> !sess.opts.unstable_opts.mir_preserve_ub)"
> "StatementKind::PlaceMention(..) | StatementKind::Nop => false,"
The subset keeps them so that bodies captured with that flag (as Miri uses)
are covered.
-/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | placeMention (src : Place)
  | nop

/-- Single `(value, target)` branch arm in `SwitchTargets`
(`rustc_middle::mir::SwitchTargets`,
`compiler/rustc_middle/src/mir/syntax.rs#L976-L1003`). -/
structure SwitchBranch where
  val : Nat
  target : BlockId

/-- Multi-way integer switch target table on `Terminator.switchInt`
(`rustc_middle::mir::SwitchTargets`,
`compiler/rustc_middle/src/mir/syntax.rs#L976-L1003`):
> "Possible values. For each value, the location to branch to is found in
> the corresponding element in the `targets` vector."
> "Possible branch targets. The last element of this vector is used for
> the "otherwise" branch, so `targets.len() == values.len() + 1` always
> holds."

`branches` pairs each value with its target, and `otherwise` is the last
element of `targets`. Like the MIR validator, `Trusted/MirSemantics.lean`
(`terminatorCfgValid`) requires the values to be distinct and to fit the
discriminant's type, and no target to be `bb0`. -/
structure SwitchTargets where
  branches : List SwitchBranch := []
  otherwise : BlockId

/-- Basic-block control-flow terminator (`rustc_middle::mir::TerminatorKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L655-L968`):
> "The various kinds of terminators, representing ways of exiting from a basic
> block."

The subset represents `Return`, `Goto`, `SwitchInt`, and `Unreachable`. A
producer must reject a body that contains any other pinned `TerminatorKind`
(`UnwindResume`, `UnwindTerminate`, `Drop`, `Call`, `TailCall`, `Assert`,
`Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, or `InlineAsm`). -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | switchInt (discr : Operand) (targets : SwitchTargets)
  | unreachable

/-- Single basic block in a `MirBody` (`rustc_middle::mir::BasicBlockData`,
`compiler/rustc_middle/src/mir/mod.rs#L1314-L1342`):
> "Data for a basic block, including a list of its statements." -/
structure BasicBlock where
  stmts : List Stmt := []
  terminator : Terminator

/-- Captured `Runtime(PostCleanup)` MIR function body
(`rustc_middle::mir::Body`,
`compiler/rustc_middle/src/mir/mod.rs#L204-L251`):
> "The lowered representation of a single function."
> "Declarations of locals.
>
> The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries."

`localTys` lists the declared type of each local `0 .. localCount - 1`;
`Trusted/MirSemantics.lean` (`bodyTysSupported`) rejects a body that leaves
a local without one. Entries at `localCount` and beyond give the types of
caller-owned slots in the entry state; every caller-owned slot that an entry
reference reaches must have one, and it is authoritative.

`ptrWidthBits` is the target's pointer width, which fixes the range of
`usize`. It has no default: a producer must state the width of the target it
captured the body for (`Trusted/MirSemantics.lean` rejects widths that Rust
does not support, `isRustPtrWidth`). -/
structure MirBody where
  argCount : Nat
  localCount : Nat
  ptrWidthBits : Nat
  localTys : List MirTy := []
  blocks : List BasicBlock

end Trusted
