-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Trusted.Refinement
import Trusted.StepResult
import Trusted.MirAst

/-!
# Trusted MIR Semantics and Crate Theorem (`Trusted/MirSemantics.lean`)

Defines the small-step operational semantics `MirSem` for `Trusted/MirAst.lean`,
static body well-formedness (`LocalLayoutsAdmitted`, `StaticBodyWf`),
Post-Monomorphization Error (PME) admission (`RequiresConst`, `ConstSucceeds`,
`ConstUnwinds`, `ConstsTotal`, `MonoAdmitted`, `MonoConstsWf`,
`ContractWellFormed`), the library representation invariant and API boundary
contract (`AdtInv`, `denoteAdtInv`, `MirVal.valid`, `AdmissibleAdtInv`,
`SafetyPre`, `SafetyPost`, `ContractPost`, `EffectivePost`, `FnBodyVerified`),
and the top-level crate verification obligation `Trusted.CrateTheorem`
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`; citations marked
`rustc@f8a08b68` are to
`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, the commit of the
pinned `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`).

## Reading guide

The semantics has two notions of "well-typed", and only two:

- **Type well-formedness** (`evalTyByteSize`, `MirTy.wfInAdts`,
  `LocalLayoutsAdmitted`): the model can measure the type within target bounds
  (`≤ isizeMaxBytes`). Every unmodeled shape (`MirTy.unmodeled`, unmodeled
  primitive/pointer/composite types, an undeclared ADT, a struct with two or
  more fields, a cycle of struct declarations, or an overflowing array layout)
  is ill formed.
- **Value validity** (`MirVal.valid`): a value is valid at a type in a given
  state. It is the only validity relation; function entry, function return,
  and `AdmissibleAdtInv` all use it.

Every model limit fails closed. During execution a limit makes the step
`.failed` (undefined behavior, so the function cannot be verified). At the
static boundary, `StaticBodyWf` (`MirLang.wf`) and `ContractWellFormed`
reject ill-formed bodies, unmodeled or overflowing layouts, and dead-on-arrival
post-monomorphization errors before any behavioral obligation is discharged.

Generic code is verified once for all instantiations. A generic function's
type parameters stay abstract: values of parameter type are opaque bytes
(`MirVal.bytes`) that are never reinterpreted, so `transmute_copy` into or out
of a type parameter is undefined behavior in the model. A call to a generic
callee looks up its `BodyId` in `Crate.bodies` and substitutes its type
arguments into the callee body (`MirBody.subst`), so every `.param` the
semantics reads refers to the root function's parameters, whose sizes are
`MirState.tySizes`.
-/

namespace Trusted

/-- Saved caller activation frame pushed onto `MirState.stack` by a static
`Terminator.call1` and popped by the callee's `Terminator.return_`.

`tySizes` is not saved: instantiation by substitution keeps every frame in the
root function's parameter space, so `MirState.tySizes` never changes during an
execution. -/
structure StackFrame where
  callerBody : MirBody
  callerLocals : Nat → Option MirVal
  callerLocalGens : Nat → Nat
  retDst : Place
  retBlock : Nat
  callerFrameId : Nat

/-- Instantaneous execution state of a `MirBody`.

- `locals`/`localGens`: the active frame's locals and, for each local, a
  storage generation that `StorageLive`/`StorageDead` increment. A reference
  records the generation it was created at, so a reference that outlives its
  referent's storage no longer resolves (`resolveRef`).
- `tySizes`: the byte size of each type parameter of the root function.
- `curBody`/`stack`: the active callee body (`none` at the root) and the saved
  caller frames.
- `frameId`/`nextFrameId`: monotonic activation identifiers. Every
  `Terminator.call1` takes a fresh identifier, so a reference into a returned
  activation can never resolve against a later sibling activation. The root
  activation is frame `0`; a caller-owned referent of the root function is a
  frame-`0` local at an index at or above the root's `localCount`.

The defaults exist for writing concrete states; `initEntryState` pins every
field that has a default. -/
structure MirState where
  locals : Nat → Option MirVal
  localGens : Nat → Nat := fun _ => 0
  block : Nat
  stmtIdx : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option MirBody := none
  stack : List StackFrame := []
  frameId : Nat := 0
  nextFrameId : Nat := 1

/-- Result of a normal return from the root function: the returned value and
the terminal state at `Terminator.return_`.

The terminal state is part of the outcome so that postconditions about
returned references (`SafetyPost`) read the referents as they are when
the function returns, not as they were when it was called. -/
structure MirReturn where
  value : MirVal
  state : MirState

/-- Update local slot `target` in `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Increment the storage-liveness generation counter of local `target`. -/
def bumpGen (gens : Nat → Nat) (target : Nat) : Nat → Nat :=
  fun i => if i == target then gens i + 1 else gens i

/-- Look up element `idx` in `xs`. -/
def lookupAt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr
    (fun x ih n =>
      match n with
      | 0 => some x
      | i + 1 => ih i)
    (fun _ => none)
    idx

/-- Apply `f` to every element of `xs`, succeeding only if every application
succeeds. -/
def mapAll {α β : Type} (f : α → Option β) (xs : List α) : Option (List β) :=
  xs.foldr (fun x acc => (f x).bind fun y => acc.map (y :: ·)) (some [])

/-- Look up an `AdtDecl` by its crate-local identifier `id`. -/
def findAdtDecl (adts : List AdtDecl) (id : Nat) : Option AdtDecl :=
  adts.find? (fun d => d.id == id)

/-- Look up a `MirBody` by its crate-local `BodyId` in `bodies`. -/
def findBody (bodies : List BodyDecl) (id : BodyId) : Option MirBody :=
  (bodies.find? (fun d => d.id.index == id.index)).map BodyDecl.body

/-! ## Instantiating generic bodies -/

/-- Substitute type arguments for type parameters: `.param idx` becomes
`typeArgs[idx]`.

The type arguments are written in the caller's parameter space, so the result
is in the caller's parameter space too; nothing is left in the callee's. A
parameter with no corresponding argument or an unmodeled type constructor makes
substitution fail (`none`), and every user of `subst` treats failure as
undefined behavior, so an arity mismatch or unmodeled type can never leave a
callee parameter to be misread as a caller parameter. -/
def MirTy.subst (typeArgs : List MirTy) : MirTy → Option MirTy
  | .usize => some .usize
  | .bool => some .bool
  | .unit => some .unit
  | .adt id => some (.adt id)
  | .param idx => lookupAt typeArgs idx
  | .ref inner => (inner.subst typeArgs).map .ref
  | .array elem len => (elem.subst typeArgs).map fun elem' => .array elem' len
  | .isize | .uint _ | .int _ | .float _ | .char | .str | .never
  | .refMut _ | .rawPtr _ _ | .slice _ | .tuple _
  | .fnDef _ | .fnPtr | .unmodeled => none

/-- Substitute type arguments into every type in a `Terminator`, failing
(`none`) on unmodeled terminators.

The `callee` of a nested `call1` is a `BodyId` referencing a closed generic
body in `Crate.bodies`, whose own parameters are bound by that call's
`typeArgs`; only those `typeArgs` are substituted here. -/
def Terminator.subst (typeArgs : List MirTy) :
    Terminator → Option Terminator
  | .return_ => some .return_
  | .goto target => some (.goto target)
  | .unreachable => some .unreachable
  | .panic hasCleanup => some (.panic hasCleanup)
  | .assert cond expected target hasCleanup =>
    some (.assert cond expected target hasCleanup)
  | .switchInt discr f t => some (.switchInt discr f t)
  | .callSizeOf dst ty target =>
    (ty.subst typeArgs).map fun ty' => .callSizeOf dst ty' target
  | .callTransmuteCopy dst srcTy dstTy op target =>
    (srcTy.subst typeArgs).bind fun srcTy' =>
      (dstTy.subst typeArgs).map fun dstTy' =>
        .callTransmuteCopy dst srcTy' dstTy' op target
  | .call1 dst callee arg target calleeTypeArgs =>
    (mapAll (MirTy.subst typeArgs) calleeTypeArgs).map fun calleeTypeArgs' =>
      .call1 dst callee arg target calleeTypeArgs'
  | .unwindResume | .unwindTerminate | .drop _ _
  | .switchIntGeneral _ _ _ | .call _ _ _ | .tailCall _
  | .yield _ _ _ | .coroutineDrop | .falseEdge _ _
  | .falseUnwind _ | .inlineAsm => none

/-- Substitute type arguments into a `BasicBlock` (statements carry no
types). -/
def BasicBlock.subst (typeArgs : List MirTy)
    (bb : BasicBlock) : Option BasicBlock :=
  (bb.terminator.subst typeArgs).map fun term =>
    { stmts := bb.stmts, terminator := term }

/-- Instantiate a generic body with `typeArgs`, written in the caller's
parameter space. This is the only way the semantics instantiates generics.

As in `Terminator.subst`, required constants are referenced by `BodyId`; only
their type-argument lists and `requiredLayouts` are substituted. -/
def MirBody.subst (typeArgs : List MirTy)
    (b : MirBody) : Option MirBody :=
  (mapAll (MirTy.subst typeArgs) b.argTys).bind fun argTys =>
  (b.retTy.subst typeArgs).bind fun retTy =>
  (mapAll (BasicBlock.subst typeArgs) b.blocks).bind fun blocks =>
  (mapAll (fun (rc : BodyId × List MirTy) =>
      (mapAll (MirTy.subst typeArgs) rc.2).map fun rcArgs => (rc.1, rcArgs))
    b.requiredConsts).bind fun requiredConsts =>
  (mapAll (MirTy.subst typeArgs) b.requiredLayouts).map fun requiredLayouts =>
  { argTys := argTys
    retTy := retTy
    localCount := b.localCount
    blocks := blocks
    requiredConsts := requiredConsts
    requiredLayouts := requiredLayouts }

/-! ## Type well-formedness and size -/

/-- Maximum byte size of a Rust type on a 64-bit target (`isize::MAX`,
`2^63 - 1`, `compiler/rustc_abi/src/layout.rs#L50-L60`). -/
def isizeMaxBytes : Nat := 9223372036854775807

/-- Whether every type-parameter byte size in `tySizes` fits within the
target's maximum object size (`≤ isizeMaxBytes`). -/
def ValidTySizes (tySizes : Nat → Nat) : Prop :=
  ∀ idx, tySizes idx ≤ isizeMaxBytes

/-- Byte size of `ty`, allowing at most `fuel` nested struct unfoldings.

The recursion is structural on `ty` except at `.adt`, which replaces the
struct by its payload type (`AdtDecl.payloadTy`) and spends one unit of fuel.
A reference is pointer-sized, but only if its pointee type is itself
well formed, so `&&Undeclared` is rejected at every depth; references cost no
fuel because the pointee is a subterm of the reference type.

Sizes model `x86_64-unknown-linux-gnu`, the only target the pinned toolchain
is used for:

- `usize` and references to sized types are 8 bytes. The target specification
  fixes the pointer width (`rustc@f8a08b68`,
  `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs#L32`):
  > `pointer_width: 64,`
- `bool` is 1 byte and `()` is 0 bytes (`src/type-layout.md`, "Primitive
  Data Layout").
- A single-field struct has its field's size. `repr(Rust)` makes no layout
  guarantee (`src/type-layout.md`, "The `Rust` Representation"), so this is a
  statement about the pinned `rustc`: `univariant` places the first field at
  offset 0 and rounds the end offset up to the struct's alignment, which for
  one field is that field's alignment (`rustc@f8a08b68`,
  `compiler/rustc_abi/src/layout.rs#L1283-L1320`):
  > `offset = offset.align_to(field_align.abi);`
  > `align = align.max(field_align.abi);`
  > ...
  > `let min_size = offset;`
  > `let size = min_size.align_to(align);`

  A field's size is already a multiple of its alignment, so the struct's size
  equals the field's. This assumes no `repr(align)`/`repr(packed)` attribute;
  the capture rejects both. -/
def tySizeStep (adts : List AdtDecl) (tySizes : Nat → Nat)
    (unfold : MirTy → Option Nat) : MirTy → Option Nat
  | .usize => some 8
  | .bool => some 1
  | .unit => some 0
  | .adt id =>
    (findAdtDecl adts id).bind fun decl => decl.payloadTy.bind unfold
  | .param idx => some (tySizes idx)
  | .ref inner => (tySizeStep adts tySizes unfold inner).map fun _ => 8
  | .array elem len =>
    (tySizeStep adts tySizes unfold elem).bind fun elemSz =>
      let sz := elemSz * len
      if decide (sz ≤ isizeMaxBytes) then some sz else none
  | _ => none

def tySizeFuel (adts : List AdtDecl) (tySizes : Nat → Nat) :
    Nat → MirTy → Option Nat
  | 0, _ => none
  | fuel + 1, ty => tySizeStep adts tySizes (tySizeFuel adts tySizes fuel) ty

/-- Byte size of a `MirTy` under `adts` and `tySizes` (`core::mem::size_of`,
`src/type-layout.md#L16-L18`):
> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."

The fuel `adts.length + 1` suffices for every acyclic set of declarations: a
chain of nested unfoldings visits distinct declarations, and there are at most
`adts.length` of them. A struct that contains itself (possible in Rust only
behind a reference, such as `struct Node { next: &'static Node }`) exhausts
the fuel, so its size is `none` and it is ill formed. -/
def evalTyByteSize (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) : Option Nat :=
  tySizeFuel adts tySizes (adts.length + 1) ty

/-- Type well-formedness: the model can measure `ty` in `adts` under zero
parameter sizes. -/
def MirTy.wfInAdts (adts : List AdtDecl) (ty : MirTy) : Bool :=
  (evalTyByteSize adts (fun _ => 0) ty).isSome

/-- Whether every signature and local type (`argTys`, `retTy`, and
`requiredLayouts`) of `body` has a valid byte size under `adts` and `tySizes`
(`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`). -/
def LocalLayoutsAdmitted (adts : List AdtDecl) (body : MirBody)
    (tySizes : Nat → Nat) : Bool :=
  body.argTys.all (fun ty => (evalTyByteSize adts tySizes ty).isSome) &&
  (evalTyByteSize adts tySizes body.retTy).isSome &&
  body.requiredLayouts.all
    (fun ty => (evalTyByteSize adts tySizes ty).isSome)

/-- Static structural well-formedness of a `MirBody` (`MirLang.wf`):
the body declares a return local and all argument locals
(`1 + body.argTys.length ≤ body.localCount`), at least an entry basic block
(`0 < body.blocks.length`), and well-formed layouts at both zero and unit
type-parameter sizes (`LocalLayoutsAdmitted adts body (fun _ => 0) = true` and
`LocalLayoutsAdmitted adts body (fun _ => 1) = true`). -/
def StaticBodyWf (adts : List AdtDecl) (body : MirBody) : Prop :=
  1 + body.argTys.length ≤ body.localCount ∧
  0 < body.blocks.length ∧
  LocalLayoutsAdmitted adts body (fun _ => 0) = true ∧
  LocalLayoutsAdmitted adts body (fun _ => 1) = true

/-! ## Initialization and references -/

/-- Whether `v` and all struct payloads inside `v` are initialized (contain no
`.uninit` sub-value). -/
def MirVal.isFullyInit : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ | .ref _ _ _ _ => true
  | .adt _ inner => inner.isFullyInit

/-- Peel `d` single-field `.adt` wrappers off `v` (`d > 0` corresponds to `d`
`.field 0` projections from a borrowed local). -/
def peelFields : Nat → MirVal → Option MirVal
  | 0, v => some v
  | d + 1, .adt _ inner => peelFields d inner
  | _ + 1, _ => none

/-- Resolve a shared reference `.ref targetFrameId gen loc fieldDepth` in state
`s` using monotonic frame IDs (`s.frameId` and `frame.callerFrameId`),
generation counters, and nested `.field 0` projection depth
(`r[undefined.validity.reference]`,
`src/behavior-considered-undefined.md#L120-L125`):
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`." -/
def resolveRef (s : MirState) (targetFrameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat := 0) : Option MirVal :=
  let raw :=
    if targetFrameId == s.frameId then
      if s.localGens loc.index == gen then
        s.locals loc.index
      else
        none
    else
      match s.stack.find? (fun f => f.callerFrameId == targetFrameId) with
      | some frame =>
        if frame.callerLocalGens loc.index == gen then
          frame.callerLocals loc.index
        else
          none
      | none => none
  match fieldDepth with
  | 0 => raw
  | d + 1 => raw.bind (peelFields (d + 1))

/-- Whether every reference reachable from `v` (through struct payloads and up
to four reference hops) survives `Terminator.return_` from the active frame of
`s`, whose body has `localCount` locals.

A reference survives if it resolves in `s` and does not point into storage
that the return deallocates:

- When the root (frame `0`) returns, only caller-owned referents survive:
  frame-`0` locals at or above `localCount`.
- When a callee returns, references into its own frame, or into any frame
  newer than it, die; references into older (caller) frames survive.

An uninitialized value or a chain longer than four hops is rejected; this
limit fails closed. -/
def returnRefsStep (s : MirState) (localCount : Nat)
    (follow : MirVal → Bool) : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ => true
  | .adt _ inner => returnRefsStep s localCount follow inner
  | .ref frameId gen loc fieldDepth =>
    !(if s.frameId == 0 then
        decide (0 < frameId) || decide (loc.index < localCount)
      else
        decide (s.frameId ≤ frameId)) &&
    (resolveRef s frameId gen loc fieldDepth).any follow

def returnRefsFuel (s : MirState) (localCount : Nat) :
    Nat → MirVal → Bool
  | 0 => fun _ => false
  | fuel + 1 =>
    returnRefsStep s localCount (returnRefsFuel s localCount fuel)

def MirVal.returnRefsOk (s : MirState) (localCount : Nat)
    (v : MirVal) : Bool :=
  returnRefsFuel s localCount 5 v

/-! ## Value validity and first-order invariant denotation -/

/-- Library-level representation invariant on user-defined ADT values
(`src/unsafety.md#L1-L35`):
> "`unsafe` code may trust that *safe* code cannot violate library-level
> invariants when interacting only through the public safe API."

`adtInv id inner` constrains the payload `inner` of a struct value
`.adt id inner`. -/
abbrev AdtInv := Nat → MirVal → Prop

/-- Default ADT representation invariant (`fun _ _ => True`). -/
def defaultAdtInv : AdtInv :=
  fun _ _ => True

/-- Denote a first-order `InvariantSpec` as a predicate on a struct's single
field payload `MirVal`. -/
def denoteInvariant (inv : InvariantSpec) (v : MirVal) : Prop :=
  match v with
  | .usize n => n ≠ inv.ne
  | _ => False

/-- Derive the crate's `AdtInv` from the first-order `AdtDecl` table:
if no declared ADT carries an `invariant`, every payload is accepted
(`defaultAdtInv`); otherwise a payload `v` of struct `id` must satisfy the
`invariant` (if any) of the `AdtDecl` with `decl.id == id`. -/
def denoteAdtInv (adts : List AdtDecl) : AdtInv :=
  if adts.all (·.invariant.isNone) then
    defaultAdtInv
  else
    fun id v =>
      match findAdtDecl adts id with
      | some { invariant := some inv, .. } => denoteInvariant inv v
      | _ => True

/-- Value validity with at most `fuel` nested struct unfoldings; see
`MirVal.valid`, which fixes the fuel. `MirVal.usize` models non-negative
integers (`Nat`), while arithmetic overflow checks in `evalBinOp` guard
operation boundaries. -/
def validStep (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat)
    (unfold : MirTy → MirVal → Prop) : MirTy → MirVal → Prop
  | .usize, .usize _ => True
  | .usize, _ => False
  | .bool, .bool _ => True
  | .bool, _ => False
  | .unit, .unit => True
  | .unit, _ => False
  | .adt id, .adt vId inner =>
    vId = id ∧
    adtInv id inner ∧
    match (findAdtDecl adts id).bind AdtDecl.payloadTy with
    | some payload => unfold payload inner
    | none => False
  | .adt _, _ => False
  | .param idx, .bytes sz _ => sz = s.tySizes idx
  | .param _, _ => False
  | .ref inner, .ref frameId gen loc fieldDepth =>
    frameId = 0 ∧
    callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee =>
      validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  | .ref _, _ => False
  | _, _ => False

def MirVal.validFuel (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) : Nat → MirTy → MirVal → Prop
  | 0, _, _ => False
  | fuel + 1, ty, v =>
    validStep adts adtInv s callerBase
      (MirVal.validFuel adts adtInv s callerBase fuel) ty v

/-- Value validity: `v` is a valid value of type `ty` in state `s`, for the
root function whose caller-owned referents start at local `callerBase`
(`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are 'valid', and producing an invalid value is hence immediate UB."

This is the only value-validity relation. It is used at function entry (each
argument), at function return (the returned value, in the terminal state),
and by `AdmissibleAdtInv`. Its cases:

- `usize`, `bool`, `()`: the value has the matching scalar constructor.
- `.adt id`: the value is a struct value of the same `id`, its payload
  satisfies the library invariant `adtInv id`, and the payload is valid at the
  declared payload type. Structs that `AdtDecl.payloadTy` cannot represent
  have no valid value.
- `.param idx`: the value is opaque bytes of the parameter's size.
- `.ref inner`: the value is a reference to a caller-owned referent (a frame-0
  local at or above `callerBase`) that resolves in `s` to a valid `inner`.
  At function entry this rules out aliasing the callee's own locals; at return
  it matches what `MirVal.returnRefsOk` lets through.
- Any unmodeled `MirTy` and `MirVal.uninit`: never valid.

Fuel bounds struct unfoldings: a type the model cannot measure has no valid
value. -/
def MirVal.valid (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) (ty : MirTy) (v : MirVal) : Prop :=
  MirVal.validFuel adts adtInv s callerBase (adts.length + 1) ty v

/-! ## Function entry -/

/-- Entry condition on the locals: argument `k` (local `k`, for `k ≥ 1`) holds
a valid value of the `k`-th argument type, and every other local except `_0`
is uninitialized (`compiler/rustc_middle/src/mir/mod.rs#L245-L249`,
`compiler/rustc_middle/src/mir/syntax.rs#L366-L368`):
> "Starting at local 1, `arg_count` locals will be provided by the caller and
> can be assumed to be initialized."

Caller-owned referents live at local indices at or above `localCount`. -/
def argsMatchInv (adts : List AdtDecl) (adtInv : AdtInv)
    (localCount : Nat) (s : MirState) (argTys : List MirTy) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, s.locals k = some v ∧ v.valid adts adtInv s localCount ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → j < localCount → s.locals j = none)
    1

/-- Structural entry state of `body` (`src/items/functions.md#L114-L116`):
control at the first statement of the root frame, no saved frames, fresh
storage generations, an uninitialized return place, well-formed signature and
local layouts (`LocalLayoutsAdmitted`), and structurally valid arguments
(validity without any library invariant, `defaultAdtInv`). -/
def initEntryState (adts : List AdtDecl) (body : MirBody)
    (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.frameId = 0 ∧
  s.nextFrameId = 1 ∧
  s.localGens = (fun _ => 0) ∧
  s.locals 0 = none ∧
  1 + body.argTys.length ≤ body.localCount ∧
  body.argTys.all (MirTy.wfInAdts adts) = true ∧
  LocalLayoutsAdmitted adts body s.tySizes = true ∧
  argsMatchInv adts defaultAdtInv body.localCount s body.argTys

/-! ## Place lenses and small-step evaluation -/

/-- Whether `v` may appear as a MIR constant operand: only reference-free
scalars (`usize`, `bool`, `()`) are admitted.

A constant's value comes from compile-time evaluation, not from any stack
frame. `rustc` represents it as a `ConstValue` (`rustc@f8a08b68`,
`compiler/rustc_middle/src/mir/consts.rs#L33-L71`), whose pointer-carrying
forms point into global allocations named by an `AllocId`:
> "A value not representable by the other variants; needs to be stored
> in-memory."
> `Indirect { alloc_id: AllocId, offset: Size }`

The model's references (`MirVal.ref`) can only name locals of an activation,
so a constant reference would forge provenance to some frame's local.
Constant struct values are rejected too: they would bypass the single-field
check that `Rvalue.aggregate` performs. Opaque generic bytes cannot be MIR
literals. Rejecting a constant makes the step undefined behavior, which fails
closed. -/
def MirVal.isConstScalar : MirVal → Bool
  | .usize _ | .bool _ | .unit => true
  | .uninit | .adt _ _ | .bytes _ _ | .ref _ _ _ _ => false

/-- Follow a projection list from `v` in state `s`, requiring the resulting
value to be fully initialized (`MirVal.isFullyInit`). -/
def evalProj (s : MirState) :
    List PlaceElem → MirVal → Option MirVal
  | [], v => if v.isFullyInit then some v else none
  | .field 0 :: rest, .adt _ inner => evalProj s rest inner
  | .deref :: rest, .ref frameId gen loc fieldDepth =>
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee => evalProj s rest pointee
    | none => none
  | _, _ => none

/-- Read the value at `p` within a frame of `localCount` locals. -/
def evalPlace (localCount : Nat) (s : MirState)
    (p : Place) : Option MirVal :=
  if p.loc.index < localCount then
    match s.locals p.loc.index with
    | some v => evalProj s p.projection v
    | none => none
  else
    none

/-- Replace the sub-value at `proj` inside a local's value with `newVal`.
Writing through `.deref` is rejected because shared references (`&T`) are
immutable. -/
def updateProj (newVal : MirVal) :
    List PlaceElem → Option MirVal → Option MirVal
  | [], _ => some newVal
  | .field 0 :: rest, some (.adt id inner) =>
    (updateProj newVal rest (some inner)).map (.adt id)
  | _, _ => none

/-- Write `val` to `dst` within a frame of `localCount` locals. -/
def assignPlace (localCount : Nat) (locals : Nat → Option MirVal)
    (dst : Place) (val : MirVal) : Option (Nat → Option MirVal) :=
  if dst.loc.index < localCount then
    (updateProj val dst.projection (locals dst.loc.index)).map fun v' =>
      updateLocal locals dst.loc.index (some v')
  else
    none

/-- Deinitialize `p` after `Operand.move p`: clears the local slot to `none`
when `p` is a bare local, or writes `MirVal.uninit` at `p.projection` so any
subsequent read of the moved field or its enclosing struct fails closed. -/
def deinitPlace (localCount : Nat) (locals : Nat → Option MirVal)
    (p : Place) : Option (Nat → Option MirVal) :=
  if p.loc.index < localCount then
    match p.projection with
    | [] => some (updateLocal locals p.loc.index none)
    | proj =>
      (updateProj .uninit proj (locals p.loc.index)).map fun v' =>
        updateLocal locals p.loc.index (some v')
  else
    none

/-- Follow `.field 0` and `.deref` projections to evaluate a shared borrow `&p`
(`Rvalue.ref`), verifying that the final pointee is live and initialized. -/
def evalRefProj (s : MirState) (frameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat := 0) : List PlaceElem → MirVal → Option MirVal
  | [], v =>
    if v.isFullyInit then some (.ref frameId gen loc fieldDepth) else none
  | .field 0 :: rest, .adt _ inner =>
    evalRefProj s frameId gen loc (fieldDepth + 1) rest inner
  | .deref :: rest, .ref frameId' gen' loc' fieldDepth' =>
    match resolveRef s frameId' gen' loc' fieldDepth' with
    | some pointee =>
      evalRefProj s frameId' gen' loc' fieldDepth' rest pointee
    | none => none
  | _, _ => none

/-- Evaluate a shared borrow `&p` (`Rvalue.ref p`) within a frame of
`localCount` locals. -/
def evalRefPlace (localCount : Nat) (s : MirState) (p : Place) :
    Option MirVal :=
  if p.loc.index < localCount then
    match s.locals p.loc.index with
    | some v =>
      evalRefProj s s.frameId (s.localGens p.loc.index) p.loc 0 p.projection v
    | none => none
  else
    none

/-- Evaluate a MIR `Operand` within a frame of `localCount` locals. -/
def evalOperand (localCount : Nat) (s : MirState)
    (op : Operand) : Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    (evalPlace localCount s src).map fun v => (v, s.locals)
  | .move src =>
    (evalPlace localCount s src).bind fun v =>
      (deinitPlace localCount s.locals src).map fun locals' => (v, locals')
  | .constVal v =>
    if v.isConstScalar then some (v, s.locals) else none
  | .runtimeChecks _ => none

/-- Evaluate a binary comparison `BinOp` on two initialized `MirVal`
operands. -/
def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | _, _, _ => none

/-- Advance to the next statement in the current basic block with `locals'`. -/
def MirState.nextStmt :
    MirState → (Nat → Option MirVal) → StepResult MirState Empty MirReturn
  | ⟨_, localGens, block, stmtIdx, tySizes, curBody, stack, frameId,
     nextFrameId⟩, locals' =>
    .silent ⟨locals', localGens, block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId⟩

/-- Advance to the next statement updating both `locals'` and `localGens'`. -/
def MirState.nextStmtGen :
    MirState → (Nat → Option MirVal) → (Nat → Nat) →
      StepResult MirState Empty MirReturn
  | ⟨_, _, block, stmtIdx, tySizes, curBody, stack, frameId, nextFrameId⟩,
    locals', localGens' =>
    .silent ⟨locals', localGens', block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId⟩

/-- Jump to statement `0` of basic block `target` in the current frame. -/
def MirState.gotoBlock :
    MirState → (Nat → Option MirVal) → Nat →
      StepResult MirState Empty MirReturn
  | ⟨_, localGens, _, _, tySizes, curBody, stack, frameId, nextFrameId⟩,
    locals', target =>
    .silent ⟨locals', localGens, target, 0, tySizes, curBody, stack, frameId,
      nextFrameId⟩

/-- Single-step operational evaluation of a MIR statement inside `activeBody`
(`src/behavior-considered-undefined.md#L54-L55`,
`src/expressions.md#L199-L215`):
> "After moving out of a place expression that evaluates to a local variable,
> the location is deinitialized and cannot be read from again until it is
> reinitialized." -/
def evalMirStmt (activeBody : MirBody) (s : MirState)
    (stmt : Stmt) (adts : List AdtDecl) :
    StepResult MirState Empty MirReturn :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match assignPlace activeBody.localCount locals' dst v with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | none => .failed
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand activeBody.localCount s lhs with
    | some (v1, locals1) =>
      match evalOperand activeBody.localCount
          { s with locals := locals1 } rhs with
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some outVal =>
          match assignPlace activeBody.localCount locals2 dst outVal with
          | some locals3 => s.nextStmt locals3
          | none => .failed
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.aggregate adtId op) =>
    -- `MirVal.adt` carries exactly one field value, so only declared
    -- single-field ADTs may be constructed.
    if (findAdtDecl adts adtId).any (·.fields.length == 1) then
      match evalOperand activeBody.localCount s op with
      | some (v, locals') =>
        match assignPlace activeBody.localCount locals' dst (.adt adtId v) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign dst (.ref src) =>
    match evalRefPlace activeBody.localCount s src with
    | some refVal =>
      match assignPlace activeBody.localCount s.locals dst refVal with
      | some locals' => s.nextStmt locals'
      | none => .failed
    | none => .failed
  | .assign _ _ =>
    .failed
  | .placeMention p =>
    match p.projection with
    | [] =>
      if p.loc.index < activeBody.localCount then
        s.nextStmt s.locals
      else
        .failed
    | _ =>
      match evalPlace activeBody.localCount s p with
      | some _ => s.nextStmt s.locals
      | none => .failed
  | .storageLive loc | .storageDead loc =>
    if loc.index < activeBody.localCount then
      s.nextStmtGen (updateLocal s.locals loc.index none)
        (bumpGen s.localGens loc.index)
    else
      .failed
  | .nop | .constEvalCounter =>
    s.nextStmt s.locals
  | _ =>
    .failed

/-- Extract the byte size and bit pattern of a `transmute_copy` source value,
looking through struct payloads.

Opaque generic bytes (`MirVal.bytes`) and uninitialized values
(`MirVal.uninit`) are rejected: a value of parameter type may contain padding
or uninitialized bytes, and reading those bytes as an integer is undefined
behavior (`src/behavior-considered-undefined.md`, "invalid values"):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory."

References are rejected because the model gives them no bit pattern. -/
def extractTransmuteBits (adts : List AdtDecl) :
    MirVal → Option (Nat × Nat)
  | .usize bits => some (8, bits)
  | .bool b => some (1, if b then 1 else 0)
  | .unit => some (0, 0)
  | .adt adtId inner =>
    (findAdtDecl adts adtId).bind fun decl =>
      decl.payloadTy.bind fun _ => extractTransmuteBits adts inner
  | .uninit | .bytes _ _ | .ref _ _ _ _ => none

/-- Build the `transmute_copy` result of type `ty` from `dstSz` bytes holding
`bits`, with at most `fuel` nested struct unfoldings. Fails (`none`) unless
every bit pattern of that size is a valid value of `ty`:

- `usize` (8 bytes) and `()` (0 bytes) accept every bit pattern.
- A struct accepts the result only if safe code could build it from arbitrary
  field values (`AdtDecl.allFieldsPubSafe`); otherwise its library invariant
  might be violated.
- `bool` and references are rejected because not every bit pattern is valid
  (`src/behavior-considered-undefined.md`, "invalid values"):
  > "A value other than `false` (`0`) or `true` (`1`) in a `bool`."
- A type parameter is rejected. A generic function is verified once for every
  instantiation, and the parameter could be instantiated with `bool`, a
  reference, or a struct with an invariant, so no bit pattern is valid for
  every instantiation. A transmute into a parameter is therefore undefined
  behavior in the model; only call sites that instantiate the parameter with
  a concrete type (by `MirBody.subst`) can transmute successfully. -/
def constructTransmuteVal (adts : List AdtDecl)
    (dstSz bits : Nat) : Nat → MirTy → Option MirVal
  | 0, _ => none
  | _ + 1, .usize => if dstSz == 8 then some (.usize bits) else none
  | _ + 1, .bool => none
  | _ + 1, .unit => if dstSz == 0 then some .unit else none
  | fuel + 1, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if decl.allFieldsPubSafe then
        decl.payloadTy.bind fun payload =>
          (constructTransmuteVal adts dstSz bits fuel payload).map
            (MirVal.adt id)
      else
        none
  | _ + 1, _ => none

/-- Operational evaluation of `core::mem::transmute_copy::<srcTy, dstTy>(&src)`
(`rustc@f8a08b68`, `library/core/src/mem/mod.rs#L1028-L1039`):
> "Interprets `src` as having type `&Dst`, and then reads `src` without moving
> the contained value."
> "This function triggers undefined behavior if `Dst` is larger than `Src`."

The model accepts only equal sizes, and only when the source value has a
modeled bit pattern of that size and every bit pattern is valid at `dstTy`
(`constructTransmuteVal`). -/
def evalTransmuteCopy (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (argVal : MirVal) : Option MirVal :=
  match evalTyByteSize adts s.tySizes srcTy,
        evalTyByteSize adts s.tySizes dstTy, argVal with
  | some srcSz, some dstSz, .ref frameId gen target fieldDepth =>
    if decide (srcSz = dstSz) then
      match resolveRef s frameId gen target fieldDepth with
      | some pointee =>
        match extractTransmuteBits adts pointee with
        | some (vSz, bits) =>
          if decide (vSz = srcSz) then
            constructTransmuteVal adts dstSz bits (adts.length + 1) dstTy
          else
            none
        | none => none
      | none => none
    else
      none
  | _, _, _ => none

/-- Single-step operational evaluation of a MIR terminator
(`compiler/rustc_middle/src/mir/syntax.rs#L684-L798`):
> "Returning very likely at least assigns the value currently in the return
> place (`_0`) to the place specified in the associated `Call` terminator in the
> calling function, as if assigned via `dest = move _0`."

A root `return_` produces `.terminated (.normal ⟨value, s⟩)`, carrying the
terminal state. A `call1` looks up the callee's `BodyId` in `bodies`,
instantiates it with `MirBody.subst`, and runs it in a fresh activation; an
unknown `BodyId` or failed instantiation is undefined behavior. -/
def evalMirTerminator (adts : List AdtDecl)
    (bodies : List BodyDecl) (activeBody : MirBody) (s : MirState)
    (term : Terminator) : StepResult MirState Empty MirReturn :=
  match term with
  | .return_ =>
    if 0 < activeBody.localCount then
      match s.locals 0 with
      | none => .failed
      | some retVal =>
        if retVal.isFullyInit &&
           retVal.returnRefsOk s activeBody.localCount then
          match s.stack with
          | [] => .terminated (.normal ⟨retVal, s⟩)
          | frame :: restStack =>
            if frame.retBlock < frame.callerBody.blocks.length then
              match assignPlace frame.callerBody.localCount frame.callerLocals
                  frame.retDst retVal with
              | some callerLocals' =>
                .silent {
                  locals := callerLocals'
                  localGens := frame.callerLocalGens
                  block := frame.retBlock
                  stmtIdx := 0
                  tySizes := s.tySizes
                  curBody :=
                    if restStack.isEmpty then none else some frame.callerBody
                  stack := restStack
                  frameId := frame.callerFrameId
                  nextFrameId := s.nextFrameId
                }
              | none => .failed
            else
              .failed
        else
          .failed
    else
      .failed
  | .goto target =>
    if target.index < activeBody.blocks.length then
      s.gotoBlock s.locals target.index
    else
      .failed
  | .unreachable =>
    .failed
  | .panic hasCleanup =>
    if hasCleanup || !s.stack.isEmpty then
      .failed
    else
      .terminated .unwind
  | .assert cond expected target hasCleanup =>
    match evalOperand activeBody.localCount s cond with
    | some (.bool b, locals') =>
      if b == expected then
        if target.index < activeBody.blocks.length then
          s.gotoBlock locals' target.index
        else
          .failed
      else if hasCleanup || !s.stack.isEmpty then
        .failed
      else
        .terminated .unwind
    | _ => .failed
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand activeBody.localCount s discr with
    | some (.bool false, locals') =>
      if falseTarget.index < activeBody.blocks.length then
        s.gotoBlock locals' falseTarget.index
      else
        .failed
    | some (.bool true, locals') =>
      if trueTarget.index < activeBody.blocks.length then
        s.gotoBlock locals' trueTarget.index
      else
        .failed
    | _ => .failed
  | .callSizeOf dst ty target =>
    if target.index < activeBody.blocks.length then
      match evalTyByteSize adts s.tySizes ty with
      | some sz =>
        match assignPlace activeBody.localCount s.locals dst (.usize sz) with
        | some locals' => s.gotoBlock locals' target.index
        | none => .failed
      | none => .failed
    else
      .failed
  | .callTransmuteCopy dst srcTy dstTy op target =>
    if target.index < activeBody.blocks.length then
      match evalOperand activeBody.localCount s op with
      | some (argVal, locals') =>
        match evalTransmuteCopy adts { s with locals := locals' }
            srcTy dstTy argVal with
        | some outVal =>
          match assignPlace activeBody.localCount locals' dst outVal with
          | some locals'' => s.gotoBlock locals'' target.index
          | none => .failed
        | none => .failed
      | none => .failed
    else
      .failed
  | .call1 dst calleeId arg target typeArgs =>
    ((findBody bodies calleeId).bind (MirBody.subst typeArgs)).elim .failed
      fun instCallee =>
      if dst.loc.index < activeBody.localCount &&
         target.index < activeBody.blocks.length &&
         instCallee.argTys.length == 1 &&
         2 ≤ instCallee.localCount &&
         0 < instCallee.blocks.length then
        match evalOperand activeBody.localCount s arg with
        | some (argVal, callerLocals') =>
          let calleeLocals : Nat → Option MirVal :=
            updateLocal (fun _ => none) 1 (some argVal)
          let frame : StackFrame := {
            callerBody := activeBody
            callerLocals := callerLocals'
            callerLocalGens := s.localGens
            retDst := dst
            retBlock := target.index
            callerFrameId := s.frameId
          }
          .silent {
            locals := calleeLocals
            localGens := fun _ => 0
            block := 0
            stmtIdx := 0
            tySizes := s.tySizes
            curBody := some instCallee
            stack := frame :: s.stack
            frameId := s.nextFrameId
            nextFrameId := s.nextFrameId + 1
          }
        | none => .failed
      else
        .failed
  | _ =>
    .failed

/-- Single-step transition function of a `MirBody` under `adts` and `bodies`. -/
def evalMirStep (adts : List AdtDecl)
    (bodies : List BodyDecl := []) (rootBody : MirBody)
    (s : MirState) : StepResult MirState Empty MirReturn :=
  let active := s.curBody.getD rootBody
  match lookupAt active.blocks s.block with
  | none => .failed
  | some bb =>
    match lookupAt bb.stmts s.stmtIdx with
    | some stmt => evalMirStmt active s stmt adts
    | none =>
      if s.stmtIdx == bb.stmts.length then
        evalMirTerminator adts bodies active s bb.terminator
      else
        .failed

/-- Relational step transition of a `MirBody`. -/
abbrev MirStep (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState)
    (r : StepResult MirState Empty MirReturn) : Prop :=
  r = evalMirStep adts bodies body s

/-! ## Post-monomorphization constants -/

/-- `RequiresConst bodies (some body) c` holds when instantiating `body`
requires the constant instance `c` to evaluate successfully
(`Body::required_consts`, `compiler/rustc_middle/src/mir/mod.rs#L279-L285`,
`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`):
> "Constants that are required to evaluate successfully for this `Body` to be
> well-formed. Wait until monomorphization to evaluate them."

Requirements are transitive through the constants' own required constants and
through the bodies of called functions. Every instance is looked up in `bodies`
by `BodyId` and instantiated with `MirBody.subst`, so it is in the root
function's parameter space and is evaluated under the root's `tySizes`. An
undeclared `BodyId` or failed instantiation yields `none`, and `failedInstance`
makes `none` require the unsatisfiable constant `none`, so a failed lookup or
instantiation can never silently drop a requirement. -/
inductive RequiresConst (bodies : List BodyDecl) :
    Option MirBody → Option MirBody → Prop where
  | failedInstance : RequiresConst bodies none none
  | direct {body : MirBody} {cId : BodyId} {typeArgs : List MirTy} :
      (cId, typeArgs) ∈ body.requiredConsts →
      RequiresConst bodies (some body)
        ((findBody bodies cId).bind (MirBody.subst typeArgs))
  | viaConst {body : MirBody} {cId : BodyId} {typeArgs : List MirTy}
      {d : Option MirBody} :
      (cId, typeArgs) ∈ body.requiredConsts →
      RequiresConst bodies
        ((findBody bodies cId).bind (MirBody.subst typeArgs)) d →
      RequiresConst bodies (some body) d
  | viaCall {body : MirBody} {bb : BasicBlock} {dst : Place}
      {calleeId : BodyId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} {d : Option MirBody} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst calleeId arg target typeArgs →
      RequiresConst bodies
        ((findBody bodies calleeId).bind (MirBody.subst typeArgs)) d →
      RequiresConst bodies (some body) d

/-- Canonical initial state for evaluating a zero-argument compile-time constant
`MirBody` under `tySizes`. -/
def constEntryState (tySizes : Nat → Nat) : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0
  tySizes := tySizes

/-- Compile-Time Function Evaluation (CTFE) success predicate
(`src/const_eval.md#L1-L25`):
> "A constant expression is evaluated at compile time. If evaluation fails (for
> example, due to a panic or integer overflow), compilation fails." -/
def ConstSucceeds (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  c.argTys = [] ∧
  ∃ n v,
    ReachesPrefix (MirStep adts bodies) c n (constEntryState tySizes) []
      (.terminated (.normal v))

/-- A required constant cleanly panics (`Terminator.panic` or
`Terminator.assert`) under `tySizes`. In `rustc`, a `const` block that panics
during monomorphization causes CTFE to reject that monomorphization at compile
time (a Post-Monomorphization Error). By contrast, a constant that steps to
`.failed` or diverges reflects either undefined behavior or a model limit,
which must never silently exclude a `tySizes` assignment from verification. -/
def ConstUnwinds (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  c.argTys = [] ∧
  ∃ n,
    ReachesPrefix (MirStep adts bodies) c n (constEntryState tySizes) []
      (.terminated .unwind)

/-- Every reachable required constant of `body` is total across all valid
`tySizes` assignments (`ValidTySizes`): at every `tySizes`, lookup and
substitution succeed and the constant either returns normally (`ConstSucceeds`)
or panics cleanly (`ConstUnwinds`). If any required constant steps to `.failed`
or fails lookup/substitution on even a single valid `tySizes` branch,
`ConstsTotal` is false and `initMirState` becomes empty everywhere, causing
`NonVacuousOn` to fail closed. -/
def ConstsTotal (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) : Prop :=
  ∀ (tySizes : Nat → Nat) (c : Option MirBody),
    ValidTySizes tySizes →
    RequiresConst bodies (some body) c →
    ∃ cBody, c = some cBody ∧
      (ConstSucceeds adts bodies tySizes cBody ∨
       ConstUnwinds adts bodies tySizes cBody)

/-- Monomorphization admission: every constant instance that `body` requires
exists and evaluates successfully under `tySizes`. A constant the model cannot
evaluate makes this false, which empties the function's initial-state set and
fails closed (see `NonVacuousOn`). -/
def MonoAdmitted (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConst bodies (some body) c →
    ∃ cBody, c = some cBody ∧ ConstSucceeds adts bodies tySizes cBody

/-- Full initial state predicate of `MirMachine` for `body`. -/
def initMirState (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState) : Prop :=
  initEntryState adts body s ∧
  ConstsTotal adts bodies body ∧
  MonoAdmitted adts bodies s.tySizes body

/-- Small-step operational machine for `MirBody` under `adts` and `bodies`. -/
def MirMachine (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    SmallStepMachine MirBody MirState Empty MirReturn where
  wf := StaticBodyWf adts
  initState := initMirState adts bodies
  step := MirStep adts bodies

/-- Operational language of Rust MIR (`(MirMachine adts bodies).toLanguage`). -/
def MirLang (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    Language :=
  (MirMachine adts bodies).toLanguage

/-- Operational behavior of a `MirBody`. -/
abbrev MirSem (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) : (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).sem body

/-! ## Library contract and first-order spec denotation -/

/-- Admissibility of an ADT representation invariant `adtInv`
(`r[expr.struct.safety]`, `src/expressions/struct-expr.md#L58-L65`).

If safe code can build a struct directly (all fields public and safe), the
invariant must accept every structurally valid payload, in every state:
otherwise unsafe code could rely on a property that safe code can violate.
Quantifying over the state `s` makes reference-valued payloads count too (a
reference is valid only relative to a state); `callerBase := 0` accepts the
widest set of references, which only strengthens the requirement.

There is no requirement that every declared struct be inhabited. An
invariant that no value satisfies only makes functions that take the struct
unverifiable (their initial-state set is empty), and an unsupported struct
shape affects only the functions that mention it. -/
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (payload : MirTy) (inner : MirVal),
      decl.payloadTy = some payload →
      inner.valid adts defaultAdtInv s 0 payload →
      adtInv decl.id inner

/-- Postcondition asserting that a normal return value equals the initial value
of argument local `argLocal`. -/
def EnsuresEqArg (argLocal : Nat) (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) : (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).Spec (fun s out =>
    ∀ tr r, out = .terminated tr (.normal r) →
      s.locals argLocal = some r.value)

/-- Denote an optional first-order `RequiresSpec` (`/// anneal:requires`) as a
precondition on the entry `MirState`. -/
def denoteRequires : Option RequiresSpec → MirState → Prop
  | none, _ => True
  | some req, s =>
    ∀ n, s.locals req.argLocal = some (.usize n) → n ≠ req.ne

/-- Denote a first-order `PostSpec` (`/// anneal:spec`) as a behavioral
specification in `MirLang adts bodies`. -/
def denotePostSpec (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    PostSpec → (MirLang adts bodies).Behavior
  | .ensuresEqArg argLocal => EnsuresEqArg argLocal adts bodies

/-- Denoted `# Safety` precondition of `fn`. -/
abbrev CapturedFn.safetyPre (fn : CapturedFn) : MirState → Prop :=
  denoteRequires fn.requires

/-- Denoted library representation invariant of `c`. -/
abbrev Crate.adtInv (c : Crate) : AdtInv :=
  denoteAdtInv c.adts

/-! ## Contract well-formedness, obligations, and `CrateTheorem` -/

/-- Post-monomorphization contract completeness (`MonoConstsWf`) for `fn` and
`body`:
- When `fn` carries an explicit Anneal contract (`fn.requires.isSome` or
  `!fn.specs.isEmpty`), every valid type-size assignment whose local layouts are
  admitted must also satisfy `MonoAdmitted` (so an unguarded PME in a contracted
  function fails closed).
- When `fn` is an unannotated Level-1 function (`fn.requires.isNone` and
  `fn.specs.isEmpty`), at least one valid type-size assignment must satisfy both
  `LocalLayoutsAdmitted` and `MonoAdmitted` (so a dead-on-arrival function that
  panics at compile time for every monomorphization is rejected, while a
  generic Level-1 function is verified across the monomorphizations that `rustc`
  admits). -/
def MonoConstsWf (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (fn : CapturedFn) (body : MirBody) : Prop :=
  if fn.requires.isSome || !fn.specs.isEmpty then
    ∀ tySizes,
      ValidTySizes tySizes →
      LocalLayoutsAdmitted adts body tySizes = true →
      MonoAdmitted adts bodies tySizes body
  else
    ∃ tySizes,
      ValidTySizes tySizes ∧
      LocalLayoutsAdmitted adts body tySizes = true ∧
      MonoAdmitted adts bodies tySizes body

/-- Unwaivable static and post-monomorphization contract well-formedness of a
single `MirBody` for `fn`. -/
def ContractWellFormed (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (fn : CapturedFn) (body : MirBody) : Prop :=
  StaticBodyWf adts body ∧
  ConstsTotal adts bodies body ∧
  MonoConstsWf adts bodies fn body

/-- Canonical ill-formed fallback `MirBody` returned when a `BodyId` is missing
from `Crate.bodies`, ensuring `StaticBodyWf` (`0 < localCount`,
`0 < blocks.length`, `LocalLayoutsAdmitted`) fails closed. -/
def illFormedFallbackBody : MirBody where
  argTys := []
  retTy := .unmodeled
  localCount := 0
  blocks := []

/-- Look up `id` in `bodies`, falling back to `illFormedFallbackBody` if `id` is
missing. -/
def resolveBodyById (bodies : List BodyDecl) (id : BodyId) : MirBody :=
  (findBody bodies id).getD illFormedFallbackBody

/-- Look up `fn.bodyId` in `bodies`, falling back to `illFormedFallbackBody` so
any missing `BodyId` fails `StaticBodyWf`. -/
def CapturedFn.resolveBody (bodies : List BodyDecl) (fn : CapturedFn) :
    MirBody :=
  resolveBodyById bodies fn.bodyId

/-- Unwaivable contract well-formedness across both `fn.bodyId` (`--release`)
and optional `fn.debugBodyId` (`--debug`). -/
def FnContractWellFormed (adts : List AdtDecl) (bodies : List BodyDecl)
    (fn : CapturedFn) : Prop :=
  ContractWellFormed adts bodies fn (fn.resolveBody bodies) ∧
  match fn.debugBodyId with
  | none => True
  | some dbgId =>
    ContractWellFormed adts bodies fn (resolveBodyById bodies dbgId)

/-- Baseline safety precondition of `body` for `fn`:
an initialized entry state (`initMirState`), arguments valid under the crate's
library representation invariant `adtInv`, and—only when `fn.isUnsafe = true`—
the function's `# Safety` precondition `fn.safetyPre`. Safe functions
(`fn.isUnsafe = false`) cannot assume `fn.safetyPre` to avoid undefined behavior
or violate library representation invariants. -/
def SafetyPre (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (s : MirState) : Prop :=
  initMirState adts bodies body s ∧
  argsMatchInv adts adtInv body.localCount s body.argTys ∧
  (fn.isUnsafe = true → fn.safetyPre s)

/-- Mandatory return-validity postcondition: any normal return yields a value
that is valid (including `adtInv`) in the terminal state, with references
restricted to caller-owned referents. -/
def SafetyPost (adts : List AdtDecl) (adtInv : AdtInv)
    (body : MirBody) (_s : MirState)
    (out : EventualOut Empty MirReturn) : Prop :=
  ∀ tr r, out = .terminated tr (.normal r) →
    r.value.valid adts adtInv r.state body.localCount body.retTy

/-- Conjunction of all user-declared postconditions (`fn.specs`) evaluated at
initial state `s` and outcome `out`. -/
def ContractPost (adts : List AdtDecl) (bodies : List BodyDecl)
    (fn : CapturedFn) (s : MirState)
    (out : EventualOut Empty MirReturn) : Prop :=
  AllHold (fn.specs.map (fun p =>
    (denotePostSpec adts bodies p s).val True.intro out))

/-- Multi-guarantee postcondition combining unconditional return validity
(`SafetyPost`) with conditional functional correctness
(`fn.safetyPre s → ContractPost`). By `Anneal.verified_meet_iff`, verifying
`body` against `(SafetyPre, EffectivePost)` is equivalent to verifying
`(SafetyPre, SafetyPost)` and refining
`SpecOn (SafetyPre ∧ fn.safetyPre) ContractPost`. -/
def EffectivePost (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (s : MirState) (out : EventualOut Empty MirReturn) : Prop :=
  SafetyPost adts adtInv body s out ∧
  (fn.safetyPre s → ContractPost adts bodies fn s out)

/-- Behavioral verification of a single lowered `MirBody` (`bodyId` or
`debugBodyId`) for `fn`. -/
def FnBodyVerified (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody) : Prop :=
  (MirLang adts bodies).Verified
    (SafetyPre adts bodies adtInv fn body)
    (EffectivePost adts bodies adtInv fn body)
    body

/-- Behavioral verification of `fn` across both `fn.bodyId` (`--release`) and
optional `fn.debugBodyId` (`--debug`). -/
def FnVerified (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) : Prop :=
  FnBodyVerified adts bodies adtInv fn (fn.resolveBody bodies) ∧
  match fn.debugBodyId with
  | none => True
  | some dbgId =>
    FnBodyVerified adts bodies adtInv fn (resolveBodyById bodies dbgId)

/-- Named behavioral verification obligation for `fn`. -/
def CapturedFn.obligation (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) : Obligation ObligationId where
  id := .fnBody fn.name
  prop := FnVerified adts bodies adtInv fn

/-- Top-level theorem required of every verified Rust crate:
1. Non-empty function inventory (`c.functions ≠ []`),
2. Distinct body IDs and function names (`NoDupIds`),
3. Unwaivable ADT invariant admissibility (`AdmissibleAdtInv`),
4. Unwaivable static and post-monomorphization contract well-formedness
   (`FnContractWellFormed`) for every function in `c.functions`, and
5. Waiver-aware behavioral verification (`VerificationResult c.tcbWaivedIds`)
   across every function in `c.functions`. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (FnContractWellFormed c.adts c.bodies)) ∧
  VerificationResult c.tcbWaivedIds
    (c.functions.map (fun fn => fn.obligation c.adts c.bodies c.adtInv))

end Trusted
