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
in-order compile-time constant evaluation (`Stmt.evalConst`), target-aware and
forward-compatible type layout (`tyLayoutStep`, `evalTyByteSize`, `evalTyAlign`,
`evalLayoutQuery`), the library representation invariant and API boundary
contract (`AdtInv`, `denoteAdtInv`, `MirVal.valid`, `AdmissibleAdtInv`), and the
top-level crate verification obligation `Trusted.CrateTheorem`
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`; citations marked
`rustc@f8a08b68` are to
`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, the commit of the
pinned `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`).

## Reading guide

The semantics has two notions of "well-typed", and only two:

- **Type well-formedness** (`evalTyByteSize`, `MirTy.wfInAdts`): the model can
  measure the type. Every unmodeled shape (`MirTy.unmodeled`, unmodeled
  primitive/pointer/composite types, an undeclared ADT, an ADT with
  `AdtRepr.unmodeled`, or a cycle of struct declarations) is ill formed.
- **Value validity** (`MirVal.valid`): a value is valid at a type in a given
  state. It is the only validity relation; function entry, function return,
  and `AdmissibleAdtInv` all use it.

Every model limit fails closed. During execution a limit makes the step
`.failed` (undefined behavior, so the function cannot be verified). At function
entry a limit makes the function's initial-state set empty, and
`NonVacuousOn` (`Trusted/Refinement.lean`) rejects an empty initial-state set.

## Forward-compatible layout and compile-time guards

Rust's default `#[repr(Rust)]` representation makes no stability guarantee on
field ordering or padding (`src/type-layout.md#L47-L56`):
> "The default representation of nominal types is called the `Rust`
> representation... In other words, the data layout is undefined."

By contrast, `#[repr(C)]` (`src/type-layout.md#L127-L162`) and
`#[repr(transparent)]` (`src/type-layout.md#L211-L234`) have language-specified
layouts. Each execution state `MirState` therefore carries `adtPad : Nat → Nat`:
for `AdtRepr.c` and `AdtRepr.transparent`, layout is deterministic across all
`adtPad` worlds, whereas for `AdtRepr.rust`, `adtPad id` adds an arbitrary
non-negative byte count of compiler-chosen padding to struct `id`. A proof that
holds for all initial states therefore holds across all valid `#[repr(Rust)]`
padding choices unless the code either uses `#[repr(C)]`/`#[repr(transparent)]`,
executes an in-order `Stmt.evalConst` layout guard (which terminates with
`.compileTimeError` on rejected layout worlds and surfaces
`TCBItem.compileTimeGuard`), or carries an explicit
`TCBItem.pinnedCompilerCoupled` waiver.

Generic code is verified once for all instantiations. A generic function's
type parameters stay abstract: values of parameter type are opaque bytes
(`MirVal.bytes`) that are never reinterpreted as integers, so `transmute_copy`
into or out of a bare type parameter is undefined behavior in the model. A call
to a generic callee looks up its `BodyId` in `Crate.bodies` and substitutes its
type arguments into the callee body (`MirBody.subst`), so every `.param` the
semantics reads refers to the root function's parameters, whose sizes are
`MirState.tySizes`.
-/

namespace Trusted

/-- Saved caller activation frame pushed onto `MirState.stack` by a static
`Terminator.call1` and popped by the callee's `Terminator.return_`.

`tySizes` and `adtPad` are not saved: instantiation by substitution keeps every
frame in the root function's parameter and layout space, so `MirState.tySizes`
and `MirState.adtPad` never change during an execution. -/
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
- `adtPad`: non-negative compiler-chosen extra padding bytes for each
  `AdtRepr.rust` struct declaration `id`.
- `ubChecks`: nondeterministic boolean value yielded by
  `Operand.runtimeChecks .ubChecks` (`core::intrinsics::ub_checks()`).

The defaults exist for writing concrete states; `initEntryState` pins every
structural control field while leaving `tySizes`, `adtPad`, and `ubChecks`
universally quantified across initial states. -/
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
  adtPad : Nat → Nat := fun _ => 0
  ubChecks : Bool := true

/-- Result of a normal return from the root function: the returned value and
the terminal state at `Terminator.return_`.

The terminal state is part of the outcome so that postconditions about
returned references (`EnsuresRetLibInv`) read the referents as they are when
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
  | .isize => some .isize
  | .uint w => some (.uint w)
  | .int w => some (.int w)
  | .bool => some .bool
  | .char => some .char
  | .unit => some .unit
  | .adt id => some (.adt id)
  | .param idx => lookupAt typeArgs idx
  | .ref inner => (inner.subst typeArgs).map .ref
  | .rawPtr inner m => (inner.subst typeArgs).map (MirTy.rawPtr · m)
  | .array elem len => (elem.subst typeArgs).map (MirTy.array · len)
  | .arraySizeOf elem sizedTy =>
    (elem.subst typeArgs).bind fun elem' =>
      (sizedTy.subst typeArgs).map (MirTy.arraySizeOf elem')
  | .float _ | .str | .never | .refMut _ | .slice _ | .tuple _
  | .fnDef _ | .fnPtr | .unmodeled => none

/-- Substitute type arguments into a `LayoutQuery`. -/
def LayoutQuery.subst (typeArgs : List MirTy) :
    LayoutQuery → Option LayoutQuery
  | .sizeOf ty => (ty.subst typeArgs).map .sizeOf
  | .alignOf ty => (ty.subst typeArgs).map .alignOf
  | .offsetOf ty varIdx fieldIdx =>
    (ty.subst typeArgs).map (LayoutQuery.offsetOf · varIdx fieldIdx)

/-- Substitute type arguments into every type in an `Rvalue`, failing (`none`)
on unmodeled rvalues. -/
def Rvalue.subst (typeArgs : List MirTy) : Rvalue → Option Rvalue
  | .use op => some (.use op)
  | .repeat op len => some (.repeat op len)
  | .repeatSizeOf op sizedTy =>
    (sizedTy.subst typeArgs).map (.repeatSizeOf op)
  | .ref src => some (.ref src)
  | .rawPtr m src => some (.rawPtr m src)
  | .cast (.transmute srcTy) op dstTy =>
    (srcTy.subst typeArgs).bind fun srcTy' =>
      (dstTy.subst typeArgs).map fun dstTy' =>
        .cast (.transmute srcTy') op dstTy'
  | .cast kind op dstTy =>
    (dstTy.subst typeArgs).map (.cast kind op)
  | .binaryOp op lhs rhs => some (.binaryOp op lhs rhs)
  | .unaryOp op src => some (.unaryOp op src)
  | .aggregate adtId op => some (.aggregate adtId op)
  | .aggregateFields ops adtId => some (.aggregateFields ops adtId)
  | .refMut _ | .refFake _ | .threadLocalRef _ | .discriminant _
  | .copyForDeref _ | .wrapUnsafeBinder _ _ | .reborrow _ _ _ => none

/-- Substitute type arguments into a `Stmt`, failing (`none`) on unmodeled
statements. -/
def Stmt.subst (typeArgs : List MirTy) : Stmt → Option Stmt
  | .assign dst rv => (rv.subst typeArgs).map (.assign dst)
  | .evalConst dst constId calleeTypeArgs =>
    (mapAll (MirTy.subst typeArgs) calleeTypeArgs).map
      (fun tys => .evalConst dst constId tys)
  | .placeMention p => some (.placeMention p)
  | .storageLive loc => some (.storageLive loc)
  | .storageDead loc => some (.storageDead loc)
  | .nop => some .nop
  | .constEvalCounter => some .constEvalCounter
  | .setDiscriminant _ _ | .fakeRead _ | .ascribeUserType _
  | .intrinsic _ | .coverage | .backwardIncompatibleDropHint _ => none

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
  | .panic => some .panic
  | .assert cond expected target onFail =>
    some (.assert cond expected target onFail)
  | .switchInt discr f t => some (.switchInt discr f t)
  | .callLayout dst query target =>
    (query.subst typeArgs).map fun q' => .callLayout dst q' target
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

/-- Substitute type arguments into a `BasicBlock`. -/
def BasicBlock.subst (typeArgs : List MirTy)
    (bb : BasicBlock) : Option BasicBlock :=
  (mapAll (Stmt.subst typeArgs) bb.stmts).bind fun stmts =>
    (bb.terminator.subst typeArgs).map fun term =>
      { stmts := stmts, terminator := term }

/-- Instantiate a generic body with `typeArgs`, written in the caller's
parameter space. This is the only way the semantics instantiates generics. -/
def MirBody.subst (typeArgs : List MirTy)
    (b : MirBody) : Option MirBody :=
  (mapAll (MirTy.subst typeArgs) b.argTys).bind fun argTys =>
  (b.retTy.subst typeArgs).bind fun retTy =>
  (mapAll (BasicBlock.subst typeArgs) b.blocks).map fun blocks =>
  { argTys := argTys
    retTy := retTy
    localCount := b.localCount
    blocks := blocks }

/-! ## Type well-formedness, size, alignment, and field offsets -/

/-- Maximum byte size of a Rust type on a 64-bit target (`isize::MAX`,
`2^63 - 1`, `compiler/rustc_abi/src/layout.rs#L50-L60`). -/
def isizeMaxBytes : Nat := 9223372036854775807

/-- Whether every type-parameter byte size in `tySizes` fits within the
target's maximum object size (`≤ isizeMaxBytes`). -/
def ValidTySizes (tySizes : Nat → Nat) : Prop :=
  ∀ idx, tySizes idx ≤ isizeMaxBytes

/-- Round `offset` up to the next multiple of `align` (`align ≥ 1`,
`compiler/rustc_abi/src/layout.rs#L1283-L1320`). -/
def alignUp (offset align : Nat) : Nat :=
  let rem := offset % align
  if rem == 0 then offset else offset + (align - rem)

/-- Sequential `#[repr(C)]` field layout fold (`src/type-layout.md#L127-L162`):
> "The alignment of the struct is the alignment of the most-aligned field in
> it... For each field in declaration order in the struct, first determine the
> size and alignment of the field. If the current offset is not a multiple of
> the field's alignment, then add padding bytes to the current offset until it
> is a multiple of the field's alignment. The offset for the field is what the
> current offset is now. Then increase the current offset by the size of the
> field. Finally, the size of the struct is the current offset rounded up to the
> nearest multiple of the struct's alignment." -/
def foldReprCFields (unfold : MirTy → Option (Nat × Nat)) :
    List FieldDecl → Nat → Nat → Option (Nat × Nat)
  | [], offset, maxAlign =>
    some (alignUp offset maxAlign, maxAlign)
  | f :: rest, offset, maxAlign =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      foldReprCFields unfold rest (alignedOffset + fSz)
        (Nat.max maxAlign fAlign)

/-- Byte offset of field `targetIdx` inside a `#[repr(C)]` field list, failing
(`none`) if `targetIdx` is out of bounds or any field type is ill formed. -/
def reprCFieldOffset (unfold : MirTy → Option (Nat × Nat)) :
    List FieldDecl → Nat → Nat → Option Nat
  | [], _, _ => none
  | f :: rest, 0, offset =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      (foldReprCFields unfold rest (alignedOffset + fSz) fAlign).map
        fun _ => alignedOffset
  | f :: rest, idx + 1, offset =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      reprCFieldOffset unfold rest idx (alignedOffset + fSz)

/-- Boolean equality on `AdtRepr`. -/
def AdtRepr.beq : AdtRepr → AdtRepr → Bool
  | .rust, .rust => true
  | .transparent, .transparent => true
  | .c, .c => true
  | .unmodeled, .unmodeled => true
  | _, _ => false

instance : BEq AdtRepr := ⟨AdtRepr.beq⟩

/-- Byte width and alignment of an `n`-bit integer type (`u8`/`i8` through
`u128`/`i128`) under `target`. -/
def intBitWidthLayout (target : TargetLayout) (w : Nat) : Option (Nat × Nat) :=
  if w == 8 then some (1, 1)
  else if w == 16 then some (2, 2)
  else if w == 32 then some (4, 4)
  else if w == 64 then some (8, target.i64Align)
  else if w == 128 then some (16, target.i128Align)
  else none

/-- Byte size and alignment `(size, align)` of `ty`, allowing at most `fuel`
nested struct unfoldings:

- Primitive scalars follow `src/type-layout.md` ("Primitive Data Layout") and
  the captured `TargetLayout` (`ptrByteWidth`, `i64Align`, `i128Align`).
- Shared references and raw pointers to well-formed pointees have size and
  alignment `target.ptrByteWidth`.
- Fixed-length arrays `[T; N]` and `[T; size_of::<U>()]` have size
  `size(T) * N` and alignment `align(T)` (`src/type-layout.md`, "Array Layout").
- `AdtRepr.c` and `AdtRepr.transparent` structs have deterministic layout;
  `AdtRepr.rust` structs add `adtPad id` non-negative compiler-chosen padding
  bytes (`src/type-layout.md`, "The `Rust` Representation"). -/
def tyLayoutStep (adts : List AdtDecl) (tySizes : Nat → Nat)
    (adtPad : Nat → Nat) (target : TargetLayout)
    (unfold : MirTy → Option (Nat × Nat)) : MirTy → Option (Nat × Nat)
  | .usize | .isize => some (target.ptrByteWidth, target.ptrByteWidth)
  | .uint w | .int w => intBitWidthLayout target w
  | .bool => some (1, 1)
  | .char => some (4, 4)
  | .unit => some (0, 1)
  | .param idx => some (tySizes idx, 1)
  | .ref inner | .rawPtr inner _ =>
    (tyLayoutStep adts tySizes adtPad target unfold inner).map
      fun _ => (target.ptrByteWidth, target.ptrByteWidth)
  | .array elem len =>
    (tyLayoutStep adts tySizes adtPad target unfold elem).map
      fun (elemSz, elemAlign) => (elemSz * len, elemAlign)
  | .arraySizeOf elem sizedTy =>
    (tyLayoutStep adts tySizes adtPad target unfold elem).bind
      fun (elemSz, elemAlign) =>
        (tyLayoutStep adts tySizes adtPad target unfold sizedTy).map
          fun (n, _) => (elemSz * n, elemAlign)
  | .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      match decl.repr with
      | .unmodeled => none
      | .transparent =>
        match decl.fields with
        | [f] => unfold f.ty
        | fields => foldReprCFields unfold fields 0 1
      | .c =>
        match decl.fields with
        | [f] => unfold f.ty
        | fields => foldReprCFields unfold fields 0 1
      | .rust =>
        match decl.fields with
        | [f] =>
          (unfold f.ty).map fun (sz, al) => (adtPad id + sz, al)
        | fields =>
          (foldReprCFields unfold fields 0 1).map
            fun (sz, al) => (adtPad id + sz, al)
  | _ => none

def tyLayoutFuel (adts : List AdtDecl) (tySizes : Nat → Nat)
    (adtPad : Nat → Nat := fun _ => 0) (target : TargetLayout := {}) :
    Nat → MirTy → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, ty =>
    tyLayoutStep adts tySizes adtPad target
      (tyLayoutFuel adts tySizes adtPad target fuel) ty

/-- Byte size of a `MirTy` under `adts`, `tySizes`, `adtPad`, and `target`
(`core::mem::size_of`, `src/type-layout.md#L16-L18`):
> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."

The fuel `adts.length + 1` suffices for every acyclic set of declarations: a
chain of nested unfoldings visits distinct declarations, and there are at most
`adts.length` of them. A struct that contains itself (possible in Rust only
behind a reference, such as `struct Node { next: &'static Node }`) exhausts
the fuel, so its size is `none` and it is ill formed. -/
def evalTyByteSize (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := {}) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad target (adts.length + 1) ty).map Prod.fst

/-- Byte alignment of a `MirTy` under `adts`, `tySizes`, `adtPad`, and `target`
(`core::mem::align_of`, `src/type-layout.md#L20-L24`). -/
def evalTyAlign (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := {}) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad target (adts.length + 1) ty).map Prod.snd

/-- Evaluate a compile-time or runtime `LayoutQuery` (`size_of`, `align_of`,
or `offset_of!`). -/
def evalLayoutQuery (adts : List AdtDecl) (tySizes : Nat → Nat)
    (query : LayoutQuery) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := {}) : Option Nat :=
  match query with
  | .sizeOf ty => evalTyByteSize adts tySizes ty adtPad target
  | .alignOf ty => evalTyAlign adts tySizes ty adtPad target
  | .offsetOf (.adt id) variantIdx fieldIdx =>
    if variantIdx == 0 then
      (findAdtDecl adts id).bind fun decl =>
        let unfold := tyLayoutFuel adts tySizes adtPad target (adts.length + 1)
        match decl.repr with
        | .c => reprCFieldOffset unfold decl.fields fieldIdx 0
        | .transparent =>
          if fieldIdx == 0 && decl.fields.length == 1 then
            (evalTyByteSize adts tySizes (.adt id) adtPad target).map fun _ => 0
          else
            none
        | .rust =>
          if fieldIdx == 0 && decl.fields.length == 1 && adtPad id == 0 then
            (evalTyByteSize adts tySizes (.adt id) adtPad target).map fun _ => 0
          else
            none
        | .unmodeled => none
    else
      none
  | .offsetOf _ _ _ => none

/-- Type well-formedness: the model can measure `ty` in `adts`. Parameter sizes
and extra padding never affect whether a size exists, so `fun _ => 0` gives the
same answer as any `tySizes` and `adtPad`. -/
def MirTy.wfInAdts (adts : List AdtDecl) (ty : MirTy) : Bool :=
  (evalTyByteSize adts (fun _ => 0) ty).isSome

/-! ## Initialization and references -/

/-- Whether `v` and all struct or field payloads inside `v` are initialized
(contain no `.uninit` sub-value). -/
def MirVal.isFullyInit : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ | .ref _ _ _ => true
  | .adt _ inner => inner.isFullyInit
  | .fieldCons h t => h.isFullyInit && t.isFullyInit

/-- Resolve a shared reference `.ref targetFrameId gen loc` in state `s` using
monotonic frame IDs (`s.frameId` and `frame.callerFrameId`) and generation
counters (`r[undefined.validity.reference]`,
`src/behavior-considered-undefined.md#L120-L125`):
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`." -/
def resolveRef (s : MirState) (targetFrameId gen : Nat) (loc : LocalId) :
    Option MirVal :=
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
  | .fieldCons h t =>
    returnRefsStep s localCount follow h &&
    returnRefsStep s localCount follow t
  | .ref frameId gen loc =>
    !(if s.frameId == 0 then
        decide (0 < frameId) || decide (loc.index < localCount)
      else
        decide (s.frameId ≤ frameId)) &&
    (resolveRef s frameId gen loc).any follow

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

/-- Field-by-field validity of a struct payload `MirVal` against a list of
declared fields. Single-field structs `[f]` reduce directly to `unfold f.ty v`;
multi-field structs match `.fieldCons h t` against `f :: rest`. -/
def validFields (unfold : MirTy → MirVal → Prop) :
    List FieldDecl → MirVal → Prop
  | [], .unit => True
  | [], _ => False
  | [f], v => unfold f.ty v
  | f :: rest, .fieldCons h t => unfold f.ty h ∧ validFields unfold rest t
  | _ :: _, _ => False

/-- Validity of `inner` as the payload of `decl` under `unfold`. Structs with
`AdtRepr.unmodeled` have no valid value. -/
def validAdtDecl (unfold : MirTy → MirVal → Prop) (decl : AdtDecl)
    (inner : MirVal) : Prop :=
  match decl.repr with
  | .unmodeled => False
  | .rust | .transparent | .c => validFields unfold decl.fields inner

/-- Value validity with at most `fuel` nested struct unfoldings; see
`MirVal.valid`, which fixes the fuel. `MirVal.usize` models integer scalars
(`Nat`), while arithmetic checks in `evalBinOp` guard operation boundaries. -/
def validStep (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat)
    (unfold : MirTy → MirVal → Prop) : MirTy → MirVal → Prop
  | .usize, .usize _ => True
  | .usize, _ => False
  | .isize, .usize _ => True
  | .isize, _ => False
  | .uint _, .usize _ => True
  | .uint _, _ => False
  | .int _, .usize _ => True
  | .int _, _ => False
  | .char, .usize _ => True
  | .char, _ => False
  | .bool, .bool _ => True
  | .bool, _ => False
  | .unit, .unit => True
  | .unit, _ => False
  | .adt id, .adt vId inner =>
    vId = id ∧
    adtInv id inner ∧
    match findAdtDecl adts id with
    | some decl => validAdtDecl unfold decl inner
    | none => False
  | .adt _, _ => False
  | .param idx, .bytes sz _ => sz = s.tySizes idx
  | .param _, _ => False
  | .array elem len, .bytes sz _ =>
    match evalTyByteSize adts s.tySizes (.array elem len) s.adtPad with
    | some arrSz => sz = arrSz
    | none => False
  | .array _ _, _ => False
  | .arraySizeOf elem sizedTy, .bytes sz _ =>
    match evalTyByteSize adts s.tySizes (.arraySizeOf elem sizedTy) s.adtPad with
    | some arrSz => sz = arrSz
    | none => False
  | .arraySizeOf _ _, _ => False
  | .ref inner, .ref frameId gen loc =>
    frameId = 0 ∧
    callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc with
    | some pointee =>
      validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  | .ref _, _ => False
  | .rawPtr inner _, .ref frameId gen loc =>
    frameId = 0 ∧
    callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc with
    | some pointee =>
      validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  | .rawPtr _ _, _ => False
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
and by `AdmissibleAdtInv`. -/
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
storage generations, an uninitialized return place, well-formed signature
types, and structurally valid arguments (validity without any library
invariant, `defaultAdtInv`). -/
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
  body.retTy.wfInAdts adts = true ∧
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
Constant struct values are rejected too: they would bypass the constructor
checks that `Rvalue.aggregate` and `Rvalue.aggregateFields` perform. Opaque
generic bytes cannot be MIR literals. Rejecting a constant makes the step
undefined behavior, which fails closed. -/
def MirVal.isConstScalar : MirVal → Bool
  | .usize _ | .bool _ | .unit => true
  | .uninit | .adt _ _ | .fieldCons _ _ | .bytes _ _ | .ref _ _ _ => false

/-- Pack a list of field values into a `MirVal` payload. A single field `[v]`
is stored directly as `v` so single-field structs are `.adt id v`; two or more
fields are right-nested with `.fieldCons`. -/
def packFields : List MirVal → MirVal
  | [] => .unit
  | [v] => v
  | v :: rest => .fieldCons v (packFields rest)

/-- Extract field `idx` from a struct or tuple payload `MirVal`. -/
def getFieldVal : Nat → MirVal → Option MirVal
  | 0, .fieldCons h _ => some h
  | 0, v => some v
  | i + 1, .fieldCons _ t => getFieldVal i t
  | _ + 1, _ => none

/-- Replace field `idx` in a struct or tuple payload `MirVal` with
`newField`. -/
def setFieldVal (newField : MirVal) : Nat → MirVal → Option MirVal
  | 0, .fieldCons _ t => some (.fieldCons newField t)
  | 0, _ => some newField
  | i + 1, .fieldCons h t => (setFieldVal newField i t).map (.fieldCons h)
  | _ + 1, _ => none

/-- Follow a projection list from `v` in state `s`, requiring the resulting
value to be fully initialized (`MirVal.isFullyInit`). -/
def evalProj (s : MirState) :
    List PlaceElem → MirVal → Option MirVal
  | [], v => if v.isFullyInit then some v else none
  | .field idx :: rest, .adt _ inner =>
    (getFieldVal idx inner).bind (evalProj s rest)
  | .field idx :: rest, .fieldCons h t =>
    (getFieldVal idx (.fieldCons h t)).bind (evalProj s rest)
  | .deref :: rest, .ref frameId gen loc =>
    match resolveRef s frameId gen loc with
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
  | .field idx :: rest, some (.adt id inner) =>
    (getFieldVal idx inner).bind fun curField =>
      (updateProj newVal rest (some curField)).bind fun updatedField =>
        (setFieldVal updatedField idx inner).map (.adt id)
  | .field idx :: rest, some (.fieldCons h t) =>
    (getFieldVal idx (.fieldCons h t)).bind fun curField =>
      (updateProj newVal rest (some curField)).bind fun updatedField =>
        setFieldVal updatedField idx (.fieldCons h t)
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

/-- Follow `.deref` projections to evaluate a shared borrow `&*...*p`
(`Rvalue.ref`), verifying that the final pointee is live and initialized. -/
def evalRefProj (s : MirState) (frameId gen : Nat) (loc : LocalId) :
    List PlaceElem → MirVal → Option MirVal
  | [], v =>
    if v.isFullyInit then some (.ref frameId gen loc) else none
  | .deref :: rest, .ref frameId' gen' loc' =>
    match resolveRef s frameId' gen' loc' with
    | some pointee => evalRefProj s frameId' gen' loc' rest pointee
    | none => none
  | _, _ => none

/-- Evaluate a shared borrow `&p` (`Rvalue.ref p`) within a frame of
`localCount` locals. -/
def evalRefPlace (localCount : Nat) (s : MirState) (p : Place) :
    Option MirVal :=
  if p.loc.index < localCount then
    match s.locals p.loc.index with
    | some v =>
      evalRefProj s s.frameId (s.localGens p.loc.index) p.loc p.projection v
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
  | .runtimeChecks .ubChecks =>
    some (.bool s.ubChecks, s.locals)
  | .runtimeChecks _ => none

/-- Evaluate a list of operands left-to-right, threading `locals` updates
across moves. -/
def evalOperandList (localCount : Nat) (s : MirState) :
    List Operand → Option (List MirVal × (Nat → Option MirVal))
  | [] => some ([], s.locals)
  | op :: rest =>
    (evalOperand localCount s op).bind fun (v, locals1) =>
      (evalOperandList localCount { s with locals := locals1 } rest).map
        fun (vs, locals2) => (v :: vs, locals2)

/-- Evaluate a binary operation `BinOp` on two initialized `MirVal`
operands. -/
def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | .ne, .usize a, .usize b => some (.bool (decide (a ≠ b)))
  | .ne, .bool a, .bool b => some (.bool (decide (a ≠ b)))
  | .ne, .unit, .unit => some (.bool false)
  | .lt, .usize a, .usize b => some (.bool (decide (a < b)))
  | .le, .usize a, .usize b => some (.bool (decide (a ≤ b)))
  | .gt, .usize a, .usize b => some (.bool (decide (b < a)))
  | .ge, .usize a, .usize b => some (.bool (decide (b ≤ a)))
  | .add, .usize a, .usize b => some (.usize (a + b))
  | .sub, .usize a, .usize b =>
    if decide (b ≤ a) then some (.usize (a - b)) else none
  | .mul, .usize a, .usize b => some (.usize (a * b))
  | .bitAnd, .bool a, .bool b => some (.bool (a && b))
  | .bitOr, .bool a, .bool b => some (.bool (a || b))
  | .bitXor, .bool a, .bool b => some (.bool (bne a b))
  | _, _, _ => none

/-- Evaluate a unary operation `UnOp` on an initialized `MirVal` operand. -/
def evalUnOp (op : UnOp) (v : MirVal) : Option MirVal :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | _, _ => none

/-! ## Transmutation and transparent wrapper peeling -/

/-- Structural boolean equality on `MirTy`. -/
def MirTy.beq : MirTy → MirTy → Bool
  | .usize, .usize | .isize, .isize | .bool, .bool
  | .char, .char | .unit, .unit => true
  | .uint a, .uint b => a == b
  | .int a, .int b => a == b
  | .adt a, .adt b => a == b
  | .param a, .param b => a == b
  | .ref a, .ref b => MirTy.beq a b
  | .rawPtr a m1, .rawPtr b m2 => m1 == m2 && MirTy.beq a b
  | .array a n1, .array b n2 => n1 == n2 && MirTy.beq a b
  | .arraySizeOf a1 s1, .arraySizeOf a2 s2 =>
    MirTy.beq a1 a2 && MirTy.beq s1 s2
  | _, _ => false

/-- Peel single-field `#[repr(transparent)]` (or zero-padded `#[repr(Rust)]`)
struct wrappers off `(ty, v)` down to the underlying payload type and value. -/
def peelTransparent (adts : List AdtDecl) (adtPad : Nat → Nat) :
    Nat → MirTy → MirVal → Option (MirTy × MirVal)
  | 0, ty, v => some (ty, v)
  | fuel + 1, .adt id, .adt vId inner =>
    if vId == id then
      match findAdtDecl adts id with
      | some decl =>
        if decl.repr == .transparent ||
           (decl.repr == .rust && adtPad id == 0) then
          match decl.payloadTy with
          | some payload => peelTransparent adts adtPad fuel payload inner
          | none => some (.adt id, .adt vId inner)
        else
          some (.adt id, .adt vId inner)
      | none => none
    else
      none
  | _ + 1, ty, v => some (ty, v)

/-- Wrap `baseVal` of type `baseTy` into `dstTy` through `allFieldsPubSafe`
single-field `#[repr(transparent)]` (or zero-padded `#[repr(Rust)]`) struct
wrappers. -/
def wrapTransparent (adts : List AdtDecl) (adtPad : Nat → Nat) :
    Nat → MirTy → MirTy → MirVal → Option MirVal
  | 0, _, _, _ => none
  | fuel + 1, baseTy, dstTy, baseVal =>
    if MirTy.beq baseTy dstTy then
      some baseVal
    else
      match dstTy with
      | .adt id =>
        (findAdtDecl adts id).bind fun decl =>
          if decl.allFieldsPubSafe &&
             (decl.repr == .transparent ||
              (decl.repr == .rust && adtPad id == 0)) then
            decl.payloadTy.bind fun payload =>
              (wrapTransparent adts adtPad fuel baseTy payload baseVal).map
                (MirVal.adt id)
          else
            none
      | _ => none

/-- Byte width of a primitive scalar `MirTy` on `target`. -/
def primitiveByteSize (target : TargetLayout := {}) : MirTy → Option Nat
  | .usize | .isize => some target.ptrByteWidth
  | .uint w | .int w => (intBitWidthLayout target w).map Prod.fst
  | .bool => some 1
  | .char => some 4
  | .unit => some 0
  | _ => none

/-- Extract the total initialized byte count and little-endian bit pattern from
a struct's field values. -/
def extractFieldBits (extract : MirVal → MirTy → Option (Nat × Nat)) :
    List FieldDecl → MirVal → Option (Nat × Nat)
  | [], .unit => some (0, 0)
  | [f], v =>
    match v with
    | .fieldCons _ _ => none
    | _ => extract v f.ty
  | f :: rest, .fieldCons h t =>
    (extract h f.ty).bind fun (sz1, bits1) =>
      (extractFieldBits extract rest t).map fun (sz2, bits2) =>
        (sz1 + sz2, bits1 + bits2 * (2 ^ (8 * sz1)))
  | _, _ => none

/-- Extract the initialized byte size and bit pattern of a `transmute` source
value with at most `fuel` nested struct unfoldings.

Opaque generic type-parameter bytes (`.param _`) and uninitialized values
(`MirVal.uninit`) are rejected: a value of parameter type may contain padding
or uninitialized bytes, and reading those bytes as an integer is undefined
behavior (`src/behavior-considered-undefined.md`, "invalid values"):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory."

Byte arrays (`[u8; N]` and `[u8; size_of::<T>()]`) have every byte initialized
as a `u8`. References are rejected because the model gives them no integer bit
pattern. -/
def extractTransmuteBitsFuel (adts : List AdtDecl) :
    Nat → MirVal → MirTy → Option (Nat × Nat)
  | 0, _, _ => none
  | _ + 1, .usize bits, ty =>
    match primitiveByteSize {} ty with
    | some sz => some (sz, bits)
    | none => some (8, bits)
  | _ + 1, .bool b, _ => some (1, if b then 1 else 0)
  | _ + 1, .unit, _ => some (0, 0)
  | _ + 1, .bytes sz bits, .array (.uint w) _ =>
    if w == 8 then some (sz, bits) else none
  | _ + 1, .bytes sz bits, .arraySizeOf (.uint w) _ =>
    if w == 8 then some (sz, bits) else none
  | fuel + 1, .adt adtId inner, _ =>
    (findAdtDecl adts adtId).bind fun decl =>
      if decl.repr == .unmodeled then
        none
      else
        extractFieldBits (extractTransmuteBitsFuel adts fuel) decl.fields inner
  | _, _, _ => none

def extractTransmuteBits (adts : List AdtDecl) (v : MirVal)
    (srcTy : MirTy := .unmodeled) : Option (Nat × Nat) :=
  extractTransmuteBitsFuel adts (adts.length + 1) v srcTy

/-- Construct a list of field values from `bits`, returning the sum of field
byte sizes along with the constructed field values. -/
def constructFieldVals (construct : Nat → MirTy → Option MirVal)
    (bits : Nat) : List FieldDecl → Option (Nat × List MirVal)
  | [] => some (0, [])
  | f :: rest =>
    (primitiveByteSize {} f.ty).bind fun fSz =>
      (construct fSz f.ty).bind fun v =>
        (constructFieldVals construct (bits / (2 ^ (8 * fSz))) rest).map
          fun (restSz, vs) => (fSz + restSz, v :: vs)

/-- Build the `transmute` result of type `ty` from `dstSz` bytes holding
`bits`, with at most `fuel` nested struct unfoldings. Fails (`none`) unless
every bit pattern of that size is a valid value of `ty`:

- All-bit-pattern integers (`usize`, `isize`, `u*`, `i*`), `()` (0 bytes), and
  byte arrays (`[u8; N]`, `[u8; size_of::<T>()]`) accept every initialized bit
  pattern of matching byte length.
- A struct accepts the result only if safe code could build it from arbitrary
  field values (`AdtDecl.allFieldsPubSafe`) and its fields have no padding
  (`sumSz == dstSz`); otherwise its library invariant might be violated.
- `bool`, `char`, and references are rejected because not every bit pattern is
  valid (`src/behavior-considered-undefined.md`, "invalid values"):
  > "A value other than `false` (`0`) or `true` (`1`) in a `bool`."
- An unconstrained type parameter is rejected because it could be instantiated
  with `bool`, a reference, or a struct with an invariant. -/
def constructTransmuteVal (adts : List AdtDecl)
    (dstSz bits : Nat) : Nat → MirTy → Option MirVal
  | 0, _ => none
  | _ + 1, .usize | _ + 1, .isize =>
    if dstSz == 8 then some (.usize bits) else none
  | _ + 1, .uint w | _ + 1, .int w =>
    match intBitWidthLayout {} w with
    | some (sz, _) => if dstSz == sz then some (.usize bits) else none
    | none => none
  | _ + 1, .bool | _ + 1, .char => none
  | _ + 1, .unit => if dstSz == 0 then some .unit else none
  | _ + 1, .array (.uint w) len =>
    if w == 8 && dstSz == len then some (.bytes dstSz bits) else none
  | _ + 1, .arraySizeOf (.uint w) _ =>
    if w == 8 then some (.bytes dstSz bits) else none
  | fuel + 1, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if decl.allFieldsPubSafe && decl.repr != .unmodeled then
        match decl.fields with
        | [f] =>
          (constructTransmuteVal adts dstSz bits fuel f.ty).map
            (MirVal.adt id)
        | fields =>
          (constructFieldVals
            (fun fSz fTy => constructTransmuteVal adts fSz bits fuel fTy)
            bits fields).bind fun (sumSz, vs) =>
              if sumSz == dstSz then
                some (.adt id (packFields vs))
              else
                none
      else
        none
  | _ + 1, _ => none

/-- Evaluate a by-value transmutation of `srcVal` from `srcTy` to `dstTy`
(`CastKind.transmute` and the core of `transmute_copy`).

Accepts either:
1. Equal-size transparent wrapper peeling/wrapping (`peelTransparent` +
   `wrapTransparent`) when the peeled payload type equals the target payload
   type (for example, `Wrapper<T> <-> T` under `#[repr(transparent)]`), or
2. Equal-size bit-pattern transmutation when `srcVal` has `vSz = srcSz`
   initialized non-padding bytes (`extractTransmuteBits`) and every bit pattern
   of that size is valid at `dstTy` (`constructTransmuteVal`). -/
def evalTransmuteVal (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (srcVal : MirVal)
    (target : TargetLayout := {}) : Option MirVal :=
  if !srcVal.isFullyInit then
    none
  else
    match evalTyByteSize adts s.tySizes srcTy s.adtPad target,
          evalTyByteSize adts s.tySizes dstTy s.adtPad target with
    | some srcSz, some dstSz =>
      if decide (srcSz = dstSz) then
        let fuel := adts.length + 1
        match (peelTransparent adts s.adtPad fuel srcTy srcVal).bind
            (fun (baseTy, baseVal) =>
              wrapTransparent adts s.adtPad fuel baseTy dstTy baseVal) with
        | some wrapped => some wrapped
        | none =>
          match extractTransmuteBits adts srcVal srcTy with
          | some (vSz, bits) =>
            if decide (vSz = srcSz) then
              constructTransmuteVal adts dstSz bits fuel dstTy
            else
              none
          | none => none
      else
        none
    | _, _ => none

/-- Operational evaluation of `core::mem::transmute_copy::<srcTy, dstTy>(&src)`
(`rustc@f8a08b68`, `library/core/src/mem/mod.rs#L1028-L1039`):
> "Interprets `src` as having type `&Dst`, and then reads `src` without moving
> the contained value."
> "This function triggers undefined behavior if `Dst` is larger than `Src`." -/
def evalTransmuteCopy (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (argVal : MirVal)
    (target : TargetLayout := {}) : Option MirVal :=
  match argVal with
  | .ref depth gen loc =>
    match resolveRef s depth gen loc with
    | some pointee => evalTransmuteVal adts s srcTy dstTy pointee target
    | none => none
  | _ => none

/-! ## Small-step statement, terminator, and constant evaluation -/

/-- Advance to the next statement in the current basic block with `locals'`. -/
def MirState.nextStmt :
    MirState → (Nat → Option MirVal) → RawStep MirState MirReturn
  | ⟨_, localGens, block, stmtIdx, tySizes, curBody, stack, frameId,
     nextFrameId, adtPad, ubChecks⟩, locals' =>
    .silent ⟨locals', localGens, block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId, adtPad, ubChecks⟩

/-- Advance to the next statement updating both `locals'` and `localGens'`. -/
def MirState.nextStmtGen :
    MirState → (Nat → Option MirVal) → (Nat → Nat) →
      RawStep MirState MirReturn
  | ⟨_, _, block, stmtIdx, tySizes, curBody, stack, frameId, nextFrameId,
     adtPad, ubChecks⟩, locals', localGens' =>
    .silent ⟨locals', localGens', block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId, adtPad, ubChecks⟩

/-- Jump to statement `0` of basic block `target` in the current frame. -/
def MirState.gotoBlock :
    MirState → (Nat → Option MirVal) → Nat →
      RawStep MirState MirReturn
  | ⟨_, localGens, _, _, tySizes, curBody, stack, frameId, nextFrameId,
     adtPad, ubChecks⟩, locals', target =>
    .silent ⟨locals', localGens, target, 0, tySizes, curBody, stack, frameId,
      nextFrameId, adtPad, ubChecks⟩

/-- Canonical initial state for evaluating a zero-argument compile-time constant
`MirBody` under `tySizes` and `adtPad`. -/
def constEntryState (tySizes : Nat → Nat)
    (adtPad : Nat → Nat := fun _ => 0) : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0
  tySizes := tySizes
  adtPad := adtPad

/-- Single-step operational evaluation of a MIR statement inside `activeBody`
(`src/behavior-considered-undefined.md#L54-L55`,
`src/expressions.md#L199-L215`):
> "After moving out of a place expression that evaluates to a local variable,
> the location is deinitialized and cannot be read from again until it is
> reinitialized."

`Stmt.evalConst` evaluates a compile-time constant or `const { ... }` block in
the exact basic-block statement order where `rustc` places it: a constant that
panics (`Terminator.panic` or `Terminator.assert`) terminates the enclosing
execution with `.terminated .compileTimeError` (pruning that layout or
type-parameter world as a compile-time error), whereas a constant that hits
undefined behavior or a model limit steps to `.failed`. -/
def evalMirStmt (activeBody : MirBody) (s : MirState)
    (stmt : Stmt) (adts : List AdtDecl)
    (bodies : List BodyDecl := [])
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn :=
      fun _ _ => .failed)
    (target : TargetLayout := {}) :
    RawStep MirState MirReturn :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match assignPlace activeBody.localCount locals' dst v with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | none => .failed
  | .assign dst (.repeat op len) =>
    match evalOperand activeBody.localCount s op with
    | some (.usize bits, locals') =>
      match assignPlace activeBody.localCount locals' dst
          (.bytes len bits) with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | some (.bool b, locals') =>
      match assignPlace activeBody.localCount locals' dst
          (.bytes len (if b then 1 else 0)) with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | _ => .failed
  | .assign dst (.repeatSizeOf op sizedTy) =>
    match evalOperand activeBody.localCount s op,
          evalTyByteSize adts s.tySizes sizedTy s.adtPad target with
    | some (.usize bits, locals'), some sz =>
      match assignPlace activeBody.localCount locals' dst (.bytes sz bits) with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | some (.bool b, locals'), some sz =>
      match assignPlace activeBody.localCount locals' dst
          (.bytes sz (if b then 1 else 0)) with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | _, _ => .failed
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
  | .assign dst (.unaryOp op src) =>
    match evalOperand activeBody.localCount s src with
    | some (v, locals') =>
      match evalUnOp op v with
      | some outVal =>
        match assignPlace activeBody.localCount locals' dst outVal with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.aggregate adtId op) =>
    if (findAdtDecl adts adtId).any
        (fun d => d.fields.length == 1 && d.repr != .unmodeled) then
      match evalOperand activeBody.localCount s op with
      | some (v, locals') =>
        match assignPlace activeBody.localCount locals' dst (.adt adtId v) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign dst (.aggregateFields ops adtIdOpt) =>
    match evalOperandList activeBody.localCount s ops with
    | some (vs, locals') =>
      match adtIdOpt with
      | some adtId =>
        if (findAdtDecl adts adtId).any
            (fun d => d.fields.length == vs.length && d.repr != .unmodeled) then
          match assignPlace activeBody.localCount locals' dst
              (.adt adtId (packFields vs)) with
          | some locals'' => s.nextStmt locals''
          | none => .failed
        else
          .failed
      | none =>
        match assignPlace activeBody.localCount locals' dst (packFields vs) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
    | none => .failed
  | .assign dst (.ref src) | .assign dst (.rawPtr _ src) =>
    match evalRefPlace activeBody.localCount s src with
    | some refVal =>
      match assignPlace activeBody.localCount s.locals dst refVal with
      | some locals' => s.nextStmt locals'
      | none => .failed
    | none => .failed
  | .assign dst (.cast (.transmute srcTy) op dstTy) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match evalTransmuteVal adts { s with locals := locals' }
          srcTy dstTy v target with
      | some outVal =>
        match assignPlace activeBody.localCount locals' dst outVal with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.cast .intToInt op dstTy)
  | .assign dst (.cast .ptrToPtr op dstTy) =>
    if (evalTyByteSize adts s.tySizes dstTy s.adtPad target).isSome then
      match evalOperand activeBody.localCount s op with
      | some (v, locals') =>
        match assignPlace activeBody.localCount locals' dst v with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign _ _ =>
    .failed
  | .evalConst dst constId typeArgs =>
    match (findBody bodies constId).bind (MirBody.subst typeArgs) with
    | some cBody =>
      if cBody.argTys.isEmpty then
        match evalConstBody cBody (constEntryState s.tySizes s.adtPad) with
        | .terminated (.normal ret) =>
          if ret.value.isConstScalar then
            match assignPlace activeBody.localCount s.locals dst ret.value with
            | some locals' => s.nextStmt locals'
            | none => .failed
          else
            .failed
        | .terminated .unwind | .terminated .abort
        | .terminated .compileTimeError =>
          .terminated .compileTimeError
        | _ => .failed
      else
        .failed
    | none => .failed
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
    (term : Terminator) (targetLayout : TargetLayout := {}) :
    RawStep MirState MirReturn :=
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
                  adtPad := s.adtPad
                  ubChecks := s.ubChecks
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
  | .panic =>
    .terminated .unwind
  | .assert cond expected target onFail =>
    match evalOperand activeBody.localCount s cond with
    | some (.bool b, locals') =>
      if b == expected then
        if target.index < activeBody.blocks.length then
          s.gotoBlock locals' target.index
        else
          .failed
      else
        match onFail with
        | .unwind => .terminated .unwind
        | .abort => .terminated .abort
        | .ub => .failed
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
  | .callLayout dst query target =>
    if target.index < activeBody.blocks.length then
      match evalLayoutQuery adts s.tySizes query s.adtPad targetLayout with
      | some val =>
        match assignPlace activeBody.localCount s.locals dst (.usize val) with
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
            srcTy dstTy argVal targetLayout with
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
            adtPad := s.adtPad
            ubChecks := s.ubChecks
          }
        | none => .failed
      else
        .failed
  | _ =>
    .failed

/-- Single-step transition of `rootBody` parameterized by a constant-body
evaluator `evalConstBody`. -/
def evalMirStepWith (adts : List AdtDecl) (bodies : List BodyDecl)
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn)
    (target : TargetLayout) (rootBody : MirBody)
    (s : MirState) : RawStep MirState MirReturn :=
  let active := s.curBody.getD rootBody
  match lookupAt active.blocks s.block with
  | none => .failed
  | some bb =>
    match lookupAt bb.stmts s.stmtIdx with
    | some stmt =>
      evalMirStmt active s stmt adts bodies evalConstBody target
    | none =>
      if s.stmtIdx == bb.stmts.length then
        evalMirTerminator adts bodies active s bb.terminator target
      else
        .failed

/-- Run `stepFn` for at most `fuel` silent steps on `cBody` starting from `cs`
(`src/const_eval.md#L1-L25`):
> "A constant expression is evaluated at compile time. If evaluation fails (for
> example, due to a panic or integer overflow), compilation fails." -/
def runConstSteps (stepFn : MirBody → MirState → RawStep MirState MirReturn) :
    Nat → MirBody → MirState → RawStep MirState MirReturn
  | 0, _, _ => .failed
  | fuel + 1, cBody, cs =>
    match stepFn cBody cs with
    | .silent cs' => runConstSteps stepFn fuel cBody cs'
    | out => out

/-- Default step budget per compile-time constant evaluation. -/
def defaultConstFuel : Nat := 64

/-- Evaluate `evalMirStepWith` supporting up to `depth` nested constant
evaluations via structural recursion on `depth`. -/
def evalMirStepDepth (adts : List AdtDecl) (bodies : List BodyDecl)
    (target : TargetLayout) :
    Nat → MirBody → MirState → RawStep MirState MirReturn
  | 0, rootBody, s =>
    evalMirStepWith adts bodies (fun _ _ => .failed) target rootBody s
  | depth + 1, rootBody, s =>
    let stepFn := evalMirStepDepth adts bodies target depth
    evalMirStepWith adts bodies
      (runConstSteps stepFn defaultConstFuel) target rootBody s

/-- Single-step transition function of a `MirBody` under `adts`, `bodies`, and
`target`. -/
def evalMirStep (adts : List AdtDecl)
    (bodies : List BodyDecl := []) (rootBody : MirBody)
    (s : MirState) (target : TargetLayout := {}) :
    RawStep MirState MirReturn :=
  evalMirStepDepth adts bodies target 2 rootBody s

/-- Relational step transition of a `MirBody`. -/
abbrev MirStep (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState)
    (r : StepResult MirState Empty MirReturn) : Prop :=
  r = (evalMirStep adts bodies body s).toStepResult

/-- Full initial state predicate of `MirMachine` for `body`. -/
def initMirState (adts : List AdtDecl) (_bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState) : Prop :=
  initEntryState adts body s

/-- Small-step operational machine for `MirBody` under `adts` and `bodies`. -/
def MirMachine (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    SmallStepMachine MirBody MirState Empty MirReturn where
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
    ∀ (s : MirState) (inner : MirVal),
      validAdtDecl (MirVal.valid adts defaultAdtInv s 0) decl inner →
      adtInv decl.id inner

/-- Mandatory postcondition of every public function:
1. A normal return yields a value that is valid, including the library
   invariant, *in the terminal state*, with references restricted to
   caller-owned referents.
2. When `allowCompileTimeGuard` is `false` (no `TCBItem.compileTimeGuard` waiver
   in `Crate.tcb`), execution never terminates with `.compileTimeError` in any
   layout or type-parameter world. When `allowCompileTimeGuard` is `true`,
   `.compileTimeError` may prune incompatible layout or type-parameter worlds,
   provided a monomorphic function still never hits `.compileTimeError` in the
   pinned zero-extra-padding world (`s.adtPad = fun _ => 0`). -/
def EnsuresRetLibInv (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (adtInv : AdtInv) (body : MirBody) (pre : MirState → Prop)
    (allowCompileTimeGuard : Bool := false) :
    (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).SpecOn pre (fun s out =>
    (∀ tr r, out = .terminated tr (.normal r) →
      r.value.valid adts adtInv r.state body.localCount body.retTy) ∧
    (if allowCompileTimeGuard then
       s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
         ∀ tr, out ≠ .terminated tr .compileTimeError
     else
       ∀ tr, out ≠ .terminated tr .compileTimeError))

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

/-! ## Trust policy, crate obligations, and `CrateTheorem` -/

/-- Trust policy permitting `rustcLowering` and audited forward-compatibility
TCB disclosures (`compileTimeGuard`, `transparentDepBody`, `documentedIntent`,
`pinnedCompilerCoupled`) while forbidding `fnVerified` waivers. -/
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True
    | .compileTimeGuard _ _ => True
    | .transparentDepBody _ _ => True
    | .documentedIntent _ _ _ => True
    | .pinnedCompilerCoupled _ _ _ => True
    | .fnVerified _ _ => False

/-- Whether `tcb` carries a `TCBItem.compileTimeGuard` waiver for `fn`. -/
def hasCompileTimeGuardWaiver (fn : CapturedFn) : List TCBItem → Bool
  | [] => false
  | .compileTimeGuard name bodyId :: rest =>
    (name == fn.name && bodyId.index == fn.bodyId.index) ||
      hasCompileTimeGuardWaiver fn rest
  | _ :: rest => hasCompileTimeGuardWaiver fn rest

/-- Whether `tcb` carries a `TCBItem.pinnedCompilerCoupled` waiver for `fn`. -/
def hasPinnedCoupledWaiver (fn : CapturedFn) : List TCBItem → Bool
  | [] => false
  | .pinnedCompilerCoupled name bodyId _ :: rest =>
    (name == fn.name && bodyId.index == fn.bodyId.index) ||
      hasPinnedCoupledWaiver fn rest
  | _ :: rest => hasPinnedCoupledWaiver fn rest

/-- Cross-crate transparent dependency bodies called by `b`, each surfaced as an
`Obligation.assumed (TCBItem.transparentDepBody ...)` that must be waived in
`Crate.tcb`. -/
def calledTransparentDeps (bodies : List BodyDecl) (fnName : String)
    (b : MirBody) : List (Obligation TCBItem) :=
  (bodies.filter (fun d =>
    d.isTransparentDep &&
    b.blocks.any (fun bb =>
      match bb.terminator with
      | .call1 _ calleeId _ _ _ => calleeId.index == d.id.index
      | _ => false))).map (fun d =>
    Obligation.assumed (TCBItem.transparentDepBody fnName d.id))

/-- Look up `fn.bodyId` in `bodies`, falling back to an ill-formed body with an
empty entry domain (`localCount := 0`, `retTy := .unmodeled`) so any missing
`BodyId` fails `NonVacuousOn`. -/
def CapturedFn.resolveBody (bodies : List BodyDecl) (fn : CapturedFn) :
    MirBody :=
  (findBody bodies fn.bodyId).getD {
    argTys := []
    retTy := .unmodeled
    localCount := 0
    blocks := []
  }

/-- Entry precondition of a public function: a real initial state, arguments
valid under the library invariant (safe callers can only hold such values),
and the function's own safety precondition. When a
`TCBItem.pinnedCompilerCoupled` waiver is present in `tcb`, the precondition
additionally restricts `s.adtPad` to the pinned compiler's zero-extra-padding
world (`s.adtPad = fun _ => 0`). -/
def CapturedFn.effectivePre (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (s : MirState)
    (tcb : List TCBItem := []) : Prop :=
  let body := fn.resolveBody bodies
  initMirState adts bodies body s ∧
  argsMatchInv adts adtInv body.localCount s body.argTys ∧
  (if hasPinnedCoupledWaiver fn tcb then
     s.adtPad = (fun _ => 0) ∧ fn.safetyPre s
   else
     fn.safetyPre s)

/-- Specifications of a public function: the mandatory return-invariant
postcondition followed by the user's specifications. -/
def CapturedFn.effectiveSpecs (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) :
    List (MirLang adts bodies).Behavior :=
  let body := fn.resolveBody bodies
  EnsuresRetLibInv adts bodies adtInv body
    (fun s => fn.effectivePre adts bodies adtInv s tcb)
    (hasCompileTimeGuardWaiver fn tcb) ::
    fn.specs.map (denotePostSpec adts bodies)

/-- Per-function obligation inventory under `adts`, `bodies`, `adtInv`, and
`tcb`: the (waivable, never provable) `rustc` lowering assumption, the (never
waivable) verification of the function against its effective precondition and
specifications, and any called `transparentDepBody` assumptions. -/
def CapturedFn.obligations (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) :
    List (Obligation TCBItem) :=
  let body := fn.resolveBody bodies
  [
    Obligation.assumed (TCBItem.rustcLowering fn.name fn.bodyId),
    Obligation.wellFormedAndSpecsOn (TCBItem.fnVerified fn.name fn.bodyId)
      (MirLang adts bodies)
      (fun s => fn.effectivePre adts bodies adtInv s tcb)
      (fn.effectiveSpecs adts bodies adtInv tcb) body
  ] ++ calledTransparentDeps bodies fn.name body

/-- Top-level theorem required of every verified Rust crate. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.bodies c.adtInv c.tcb)))

end Trusted
