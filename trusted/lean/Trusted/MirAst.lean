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
Representation (MIR) for scalar, aggregate (ADT), and polymorphic functions,
including `Body::required_consts` for Post-Monomorphization Error (PME)
constant-evaluation obligations and the first-order specification and crate
descriptors (`InvariantSpec`, `RequiresSpec`, `PostSpec`, `TCBItem`,
`BodyDecl`, `CapturedFn`, `Crate`)
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

This file fixes the complete first-order syntax vocabulary that
`anneal-rustc-capture` emits into `Mir.lean`. It assigns no semantic meaning;
`Trusted/MirSemantics.lean` does.
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

/-- Crate-local identifier of a captured `MirBody` in `Crate.bodies`.
Referencing callees and required constants by `BodyId` rather than embedding
`MirBody` inline keeps the AST non-mutually-inductive and lets `TCBItem` compare
body identities without traversing syntax trees. -/
structure BodyId where
  index : Nat

/-- Single projection step along a `Place` path
(`rustc_middle::mir::ProjectionElem`,
`compiler/rustc_middle/src/mir/syntax.rs#L1189-L1255`):
- `.deref`: dereference a reference (`*p`).
- `.field idx`: project field `idx` of a struct (`p.idx`).
- `.unsupported`: any projection outside the modeled fragment, which fails
  closed during place evaluation. -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  | unsupported

/-- Memory location path rooted at a `LocalId` followed by a sequence of
projections (`rustc_middle::mir::Place`,
`compiler/rustc_middle/src/mir/syntax.rs#L1168-L1187`):
> "A `Place` represents a memory location: a local variable together with a
> list of projections (field accesses, dereferences, indexing, etc.)." -/
structure Place where
  loc : LocalId
  projection : List PlaceElem := []

/-- Whether safe code outside the defining module may name a struct field in a
struct expression (`compiler/rustc_middle/src/ty/adt.rs#L114-L120`):
> "Visibility of the field (mostly matters for structs)."

The only question the semantics asks of a field is whether downstream safe
code can construct the struct from arbitrary field values
(`AdtDecl.allFieldsPubSafe`). A field that is not public, and a field declared
`unsafe` under the unstable `feature(unsafe_fields)`, both prevent that, so
the capture emits `.priv` for both. -/
inductive FieldAccess where
  | pubSafe
  | priv

/-- MIR type grammar for scalar, aggregate (ADT), polymorphic, and reference
types (`src/types/numeric.md#L37-L38`, `src/types/boolean.md#L6-L7`,
`compiler/rustc_type_ir/src/ty_kind.rs#L106-L165`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."

`.param idx` is the `idx`-th generic type parameter of the *root* function
being verified. Callee bodies are instantiated by substitution
(`MirBody.subst`), so a `.param` that the semantics reads always refers to the
root function's parameters. `.adt id` names the `AdtDecl` with that `id`; the
capture monomorphizes generic ADTs into distinct declarations, so `.adt` has
no type arguments. `.unsupported` represents any type outside the modeled
fragment and has no size or valid values. -/
inductive MirTy where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)
  | unsupported

/-- Single field declaration inside an ADT (`rustc_middle::ty::FieldDef`,
`compiler/rustc_middle/src/ty/adt.rs#L108-L121`). -/
structure FieldDecl where
  ty : MirTy
  access : FieldAccess

/-- First-order representation invariant of a single-`usize`-field struct
(`/// anneal:invariant <field> != <ne>`): the field is not equal to `ne`. -/
structure InvariantSpec where
  ne : Nat

/-- Captured ADT (struct) declaration (`rustc_middle::ty::AdtDefData`,
`compiler/rustc_middle/src/ty/adt.rs#L140-L176`).

Every list of fields is accepted here, but the semantics gives meaning only to
single-field structs (`AdtDecl.payloadTy`). A fieldless struct or a struct with
two or more fields has no modeled size or valid value, so every function whose
signature mentions it fails closed at entry, and other functions are
unaffected. -/
structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  invariant : Option InvariantSpec := none

/-- Whether safe downstream code can construct the struct directly with a
struct expression (`r[expr.struct.safety]`,
`src/expressions/struct-expr.md#L58-L65`):
> "A struct expression can only be used if all fields are visible in the current
> scope, and the struct is not marked `#[non_exhaustive]` in another crate."

`#[non_exhaustive]` is not recorded. Ignoring it can only make this function
return `true` where Rust would forbid construction, which makes
`AdmissibleAdtInv` demand more of the invariant, never less. -/
def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv => false)

/-- The type of the single value that a `MirVal.adt` of this struct carries.

`MirVal.adt id inner` stores one field value, so a single-field struct carries
its field's type (`some f.ty`), while a fieldless struct or a struct with two
or more fields has no payload type (`none`). Every consumer (size, validity,
transmutation) goes through this one function, so that restriction lives in one
place. -/
def AdtDecl.payloadTy (decl : AdtDecl) : Option MirTy :=
  match decl.fields with
  | [f] => some f.ty
  | _ => none

/-- Runtime value (`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are 'valid', and producing an invalid value is hence immediate UB."

- `.uninit`: an uninitialized sub-value written by a partial move out of a
  projected place (`Operand.move`); reading any value containing `.uninit` is
  undefined behavior (`MirVal.isFullyInit`).
- `.adt id inner`: a struct value with its single payload (see
  `AdtDecl.payloadTy`).
- `.bytes sz bits`: the opaque value of a generic parameter type, `sz` bytes
  wide. The semantics never reinterprets these bits as another type.
- `.ref frameId gen loc`: a shared reference to local `loc` of the activation
  with identifier `frameId`, valid only while that local's storage generation
  is still `gen` (see `resolveRef`). -/
inductive MirVal where
  | uninit
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (depth : Nat) (gen : Nat) (loc : LocalId)

/-- MIR operand (`rustc_middle::mir::Operand`,
`compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310`):
> "Creates a value by loading the given place."
> "This *may* additionally overwrite the place with `uninit` bytes..."

`constVal` accepts any `MirVal` syntactically, but evaluation admits only
reference-free scalars (see `evalOperand`). -/
inductive Operand where
  | copy (src : Place)
  | move (src : Place)
  | constVal (val : MirVal)
  | unsupported

/-- Binary comparison operator (`rustc_middle::mir::BinOp::Eq`,
`compiler/rustc_middle/src/mir/syntax.rs#L1686-L1716`):
> "The `==` operator (equality)" -/
inductive BinOp where
  | eq

/-- Right-hand side value computation (`rustc_middle::mir::Rvalue`,
`compiler/rustc_middle/src/mir/syntax.rs#L1340-L1435`):
> "Yields the operand unchanged, except for a potential retag."
> "Creates a pointer/reference to the given place." -/
inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | aggregate (adtId : Nat) (op : Operand)
  | ref (src : Place)
  | unsupported

/-- Sequential statement inside a MIR basic block
(`rustc_middle::mir::StatementKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L305-L385`):
> "`StorageLive` and `StorageDead` statements mark the live range of a local."
> "`PlaceMention` evaluates the `Place` without reading its value." -/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | placeMention (place : Place)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop
  | unsupported

/-- Control-flow transfer at the end of a MIR basic block
(`rustc_middle::mir::TerminatorKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L683-L798`):
> "Block has one successor; we continue execution there."
> "Returns from the function."
> "Indicates a terminator that can never be reached. Executing this terminator
> is UB."
> "Jumps to `target` if `cond` equals `expected`, otherwise panics."

In `call1`, `callee` is the `BodyId` of the callee's generic body in
`Crate.bodies` and `typeArgs` are its type arguments, written in the caller's
own parameter space. -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | callSizeOf (dst : Place) (ty : MirTy) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | unsupported

/-- Basic block (`rustc_middle::mir::BasicBlockData`,
`compiler/rustc_middle/src/mir/mod.rs#L207-L209`). -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- Lowered `Runtime(PostCleanup)` MIR body (`rustc_middle::mir::Body`,
`compiler/rustc_middle/src/mir/mod.rs#L204-L285`):
> "Constants that are required to evaluate successfully for this `Body` to be
> well-formed. Wait until monomorphization to evaluate them."

Each required constant names a zero-argument generic body in `Crate.bodies` by
its `BodyId`, paired with its type arguments in this body's parameter space. -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  requiredConsts : List (BodyId × List MirTy) := []

/-- Entry in `Crate.bodies` associating a `BodyId` with its `MirBody`. -/
structure BodyDecl where
  id : BodyId
  body : MirBody

/-- First-order `# Safety` precondition of a `pub unsafe fn`
(`/// anneal:requires <arg> != <ne>`): argument local `argLocal` (`usize`) is
not equal to `ne`. -/
structure RequiresSpec where
  argLocal : Nat
  ne : Nat

/-- First-order user specification (`/// anneal:spec ensures(ret == <arg>)`) on
a public function. -/
inductive PostSpec where
  | ensuresEqArg (argLocal : Nat)

/-- Identifier of an obligation in a crate's verification result. Each captured
function contributes exactly two obligations:

- `rustcLowering fnName bodyId`: `rustc` correctly compiles the body at
  `bodyId`. **Unchecked `rustc` lowering assumption:** this obligation is
  constructed via `Obligation.assumed`, so it can never be proved and can only
  be waived (`defaultTrustPolicy`), making trusting `rustc` an explicit,
  per-function entry in `Crate.tcb`.
- `fnVerified fnName bodyId`: the body at `bodyId` satisfies its specifications.
  This obligation can never be waived (`defaultTrustPolicy`), so it must be
  proved. -/
inductive TCBItem where
  | rustcLowering (fnName : String) (bodyId : BodyId)
  | fnVerified (fnName : String) (bodyId : BodyId)

/-- Captured public MIR function.

`requires` is the optional `# Safety` precondition of a `pub unsafe fn`, which
its callers must establish (`src/unsafety.md#L1-L35`). A safe function has no
such precondition (`requires := none`); omitting `requires` only strengthens
what must be proved. -/
structure CapturedFn where
  name : String
  bodyId : BodyId
  requires : Option RequiresSpec := none
  specs : List PostSpec := []

/-- Captured Rust crate. Every field is first-order syntax data;
`Trusted/MirSemantics.lean` denotes `adts`, `bodies`, `functions`, and `tcb` to
state `Trusted.CrateTheorem`. -/
structure Crate where
  adts : List AdtDecl := []
  bodies : List BodyDecl := []
  functions : List CapturedFn
  tcb : List TCBItem

end Trusted
