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
descriptors (`InvariantSpec`, `RequiresSpec`, `PostSpec`, `ObligationId`,
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
`MirBody` inline keeps the AST non-mutually-inductive and lets body lookups
operate over a flat table. -/
structure BodyId where
  index : Nat

/-- MIR type grammar for scalar, aggregate (ADT), polymorphic, reference, and
pointer types (`src/types/numeric.md#L37-L38`, `src/types/boolean.md#L6-L7`,
`compiler/rustc_type_ir/src/ty_kind.rs#L106-L165`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."

`.param idx` is the `idx`-th generic type parameter of the *root* function
being verified. Callee bodies are instantiated by substitution
(`MirBody.subst`), so a `.param` that the semantics reads always refers to the
root function's parameters. `.adt id` names the `AdtDecl` with that `id`; the
capture monomorphizes generic ADTs into distinct declarations, so `.adt` has
no type arguments. `.unmodeled` is the bounded leaf fallback for `rustc`
type-checker internal types (`Dynamic`, `Alias`, `Coroutine`, `Closure`, `Pat`,
`UnsafeBinder`, `Bound`, `Placeholder`, `Foreign`) and has no size or valid
values in `Trusted/MirSemantics.lean`. -/
inductive MirTy where
  | usize
  | isize
  | uint (bits : Nat)
  | int (bits : Nat)
  | float (bits : Nat)
  | bool
  | char
  | str
  | unit
  | never
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)
  | refMut (inner : MirTy)
  | rawPtr (inner : MirTy) (mutable : Bool)
  | array (elem : MirTy) (len : Nat)
  | slice (elem : MirTy)
  | tuple (elems : List MirTy)
  | fnDef (name : String)
  | fnPtr
  | unmodeled

/-- Single projection step along a `Place` path
(`rustc_middle::mir::ProjectionElem`,
`compiler/rustc_middle/src/mir/syntax.rs#L1192-L1283`):
- `.deref`: dereference a reference or pointer (`*p`).
- `.field idx`: project field `idx` (`p.idx`).
- `.index loc`: index into an array or slice by local `loc` (`p[loc]`).
- `.constantIndex`: endpoint-relative slice/array pattern index.
- `.subslice`: slice pattern subrange.
- `.downcast variantIdx`: narrow an enum or coroutine place to `variantIdx`.
- `.opaqueCast ty`: cast an opaque type in place.
- `.unwrapUnsafeBinder ty`: project out of an unsafe binder. -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  | index (loc : LocalId)
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool)
  | subslice (fromIdx : Nat) (toIdx : Nat) (fromEnd : Bool)
  | downcast (variantIdx : Nat)
  | opaqueCast (ty : MirTy)
  | unwrapUnsafeBinder (ty : MirTy)

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
- `.ref frameId gen loc fieldDepth`: a shared reference to `fieldDepth` nested
  `.field 0` projections of local `loc` of the activation with identifier
  `frameId`, valid only while that local's storage generation is still `gen`
  (see `resolveRef`). -/
inductive MirVal where
  | uninit
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (frameId : Nat) (gen : Nat) (loc : LocalId) (fieldDepth : Nat := 0)

/-- Session runtime-check flag queried by `Operand.runtimeChecks`
(`rustc_middle::mir::RuntimeChecks`,
`compiler/rustc_middle/src/mir/syntax.rs#L1579-L1589`). -/
inductive RuntimeChecks where
  | ubChecks
  | contractChecks
  | overflowChecks

/-- MIR operand (`rustc_middle::mir::Operand`,
`compiler/rustc_middle/src/mir/syntax.rs#L1303-L1335`):
> "Creates a value by loading the given place."
> "This *may* additionally overwrite the place with `uninit` bytes..."

`constVal` accepts any `MirVal` syntactically, but evaluation admits only
reference-free scalars (see `evalOperand`). -/
inductive Operand where
  | copy (src : Place)
  | move (src : Place)
  | constVal (val : MirVal)
  | runtimeChecks (chk : RuntimeChecks)

/-- Raw pointer mutability flavor on `Rvalue.rawPtr`
(`rustc_middle::mir::RawPtrKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L180-L192`). -/
inductive RawPtrKind where
  | mut_
  | const_
  | fakeForPtrMetadata

/-- Cast kind on `Rvalue.cast` (`rustc_middle::mir::CastKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532`). -/
inductive CastKind where
  | pointerExposeProvenance
  | pointerWithExposedProvenance
  | pointerCoercion
  | intToInt
  | floatToInt
  | floatToFloat
  | intToFloat
  | ptrToPtr
  | fnPtrToPtr
  | transmute
  | subtype

/-- Unary operator on `Rvalue.unaryOp` (`rustc_middle::mir::UnOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617`). -/
inductive UnOp where
  | not
  | neg
  | ptrMetadata

/-- Binary operator on `Rvalue.binaryOp` (`rustc_middle::mir::BinOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709`). -/
inductive BinOp where
  | add
  | addUnchecked
  | addWithOverflow
  | sub
  | subUnchecked
  | subWithOverflow
  | mul
  | mulUnchecked
  | mulWithOverflow
  | div
  | rem
  | bitXor
  | bitAnd
  | bitOr
  | shl
  | shlUnchecked
  | shr
  | shrUnchecked
  | eq
  | lt
  | le
  | ne
  | ge
  | gt
  | cmp
  | offset

/-- Right-hand side value computation (`rustc_middle::mir::Rvalue`,
`compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488`):
> "Yields the operand unchanged, except for a potential retag."
> "Creates a reference of the indicated kind to the place." -/
inductive Rvalue where
  | use (op : Operand)
  | repeat (op : Operand) (len : Nat)
  | ref (src : Place)
  | refMut (src : Place)
  | refFake (src : Place)
  | threadLocalRef (defId : Nat)
  | rawPtr (kind : RawPtrKind) (src : Place)
  | cast (kind : CastKind) (op : Operand) (ty : MirTy)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | unaryOp (op : UnOp) (opnd : Operand)
  | discriminant (src : Place)
  | aggregate (adtId : Nat) (op : Operand)
  | aggregateFields (ops : List Operand)
  | copyForDeref (src : Place)
  | wrapUnsafeBinder (op : Operand) (ty : MirTy)
  | reborrow (ty : MirTy) (mutable : Bool) (src : Place)

/-- Non-diverging intrinsic statement payload
(`rustc_middle::mir::NonDivergingIntrinsic`,
`compiler/rustc_middle/src/mir/syntax.rs#L469-L492`). -/
inductive NonDivergingIntrinsic where
  | assume (op : Operand)
  | copyNonOverlapping (src : Operand) (dst : Operand) (count : Operand)

/-- Sequential statement inside a MIR basic block
(`rustc_middle::mir::StatementKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L305-L456`):
> "`StorageLive` and `StorageDead` statements mark the live range of a local."
> "`PlaceMention` evaluates the `Place` without reading its value." -/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | fakeRead (place : Place)
  | setDiscriminant (place : Place) (variantIdx : Nat)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | placeMention (place : Place)
  | ascribeUserType (place : Place)
  | coverage
  | intrinsic (intr : NonDivergingIntrinsic)
  | constEvalCounter
  | nop
  | backwardIncompatibleDropHint (place : Place)

/-- Control-flow transfer at the end of a MIR basic block
(`rustc_middle::mir::TerminatorKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L692-L981`):
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
  | panic (hasCleanup : Bool := false)
  | unwindResume
  | unwindTerminate
  | drop (place : Place) (target : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
      (hasCleanup : Bool := false)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | switchIntGeneral (discr : Operand) (targets : List (Nat × BlockId))
      (otherwise : BlockId)
  | callSizeOf (dst : Place) (ty : MirTy) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | call (dst : Place) (args : List Operand) (target : Option BlockId)
  | tailCall (args : List Operand)
  | yield (val : Operand) (resume : BlockId) (resumeArg : Place)
  | coroutineDrop
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | falseUnwind (realTarget : BlockId)
  | inlineAsm

/-- Basic block (`rustc_middle::mir::BasicBlockData`,
`compiler/rustc_middle/src/mir/mod.rs#L207-L209`). -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- Lowered `Runtime(PostCleanup)` MIR body (`rustc_middle::mir::Body`,
`compiler/rustc_middle/src/mir/mod.rs#L204-L285`,
`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`):
> "Constants that are required to evaluate successfully for this `Body` to be
> well-formed. Wait until monomorphization to evaluate them."

Each required constant in `requiredConsts` names a zero-argument generic body in
`Crate.bodies` by its `BodyId`, paired with its type arguments in this body's
parameter space. Each entry in `requiredLayouts` records a local or signature
type whose layout (`evalTyByteSize` ≤ `isize::MAX`) must be admitted at
monomorphization time. -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  requiredConsts : List (BodyId × List MirTy) := []
  requiredLayouts : List MirTy := []

/-- Entry in `Crate.bodies` associating a `BodyId` with its `MirBody`. -/
structure BodyDecl where
  id : BodyId
  body : MirBody

/-- First-order precondition clause (`/// anneal:requires <arg> != <ne>`):
argument local `argLocal` (`usize`) is not equal to `ne`.

On an `unsafe fn` (`CapturedFn.isUnsafe = true`), `requires` states the
function's `# Safety` precondition, which callers must establish and which both
baseline safety (`SafetyPre`) and functional specifications (`ContractPost`) may
assume. On a safe function (`CapturedFn.isUnsafe = false`), `requires` narrows
only the domain of `/// anneal:spec` postconditions (`ContractPost`); baseline
safety (`SafetyPre`) does not assume `requires`, because safe callers are not
obligated to establish Anneal preconditions at call sites. -/
structure RequiresSpec where
  argLocal : Nat
  ne : Nat

/-- First-order user specification (`/// anneal:spec ensures(ret == <arg>)`) on
a captured function. -/
inductive PostSpec where
  | ensuresEqArg (argLocal : Nat)

/-- Identifier of a function-body behavioral verification obligation in
`CrateTheorem`.

An obligation `ObligationId.fnBody fnName` is waived only if it appears in
`Crate.tcbWaivedIds` (populated from `/// anneal:trusted` waivers and verified
by `cargo-anneal` to match `anneal-tcb.lock` in a 1-to-1 bijection). Unwaivable
structural and contract well-formedness obligations (`AdmissibleAdtInv` and
`FnContractWellFormed`) sit outside `VerificationResult` so they can never be
waived. -/
inductive ObligationId where
  | fnBody (fnName : String)

/-- Captured MIR function descriptor.

- `bodyId`: crate-local `BodyId` of the primary (`--release`) lowered MIR body.
- `debugBodyId`: optional `BodyId` of the `--debug` lowered MIR body when the
  debug compilation profile produces a distinct MIR body from `--release`.
- `isUnsafe`: whether the function is declared `unsafe fn`, determining whether
  `requires` enters `SafetyPre` or only qualifies `ContractPost`.
- `requires`: optional `/// anneal:requires` precondition clause.
- `specs`: list of `/// anneal:spec` postcondition clauses. -/
structure CapturedFn where
  name : String
  bodyId : BodyId
  debugBodyId : Option BodyId := none
  isUnsafe : Bool := false
  requires : Option RequiresSpec := none
  specs : List PostSpec := []

/-- Captured Rust crate. Every field is first-order syntax data;
`Trusted/MirSemantics.lean` denotes `adts`, `bodies`, `functions`, and
`tcbWaivedIds` to state `Trusted.CrateTheorem`. -/
structure Crate where
  adts : List AdtDecl := []
  bodies : List BodyDecl := []
  functions : List CapturedFn
  tcbWaivedIds : List ObligationId := []

end Trusted
