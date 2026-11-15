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
import Init.Core
import Init.Data.Nat.Bitwise.Basic
import Trusted.MirAst

/-!
# Trusted MIR Small-Step Operational Semantics (`Trusted/MirSemantics.lean`)

Defines the small-step operational semantics (`stepStmt`, `stepTerminator`,
`stepMirCore`, and `runMirSteps`) for `Trusted/MirAst.lean`
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

Citation convention: paths beginning with `compiler/` or `src/tools/` refer
to `rust-lang/rust` at the commit above, and all other `src/` paths refer to
`rust-lang/reference` at the commit above.

## Semantic invariants

- **Initialization discipline:** Reading any value containing `MirVal.uninit`
  is undefined behavior and transitions to `StepOutcome.fault`.
- **Reference liveness and mutability discipline:** Every reference
  `MirVal.ref mutable gen loc fieldPath reborrowDepth` records the storage
  generation `gen` of its referent local `loc` at borrow creation time and its
  reborrow nesting depth `reborrowDepth`. `Stmt.storageLive` and
  `Stmt.storageDead` (on a live slot) increment `loc`'s generation counter,
  immediately invalidating any outstanding reference to `loc`. Mutating or
  taking a mutable reborrow through a shared reference (`mutable = false`)
  transitions to `StepOutcome.fault`.
- **Aliasing discipline:** Borrows, retags, and accesses retire the references
  that Stacked Borrows would invalidate (`refDepthConflicts`), and any later
  use of a retired reference faults. Retiring a reference rewrites it in
  memory to name a slot that does not exist
  (`invalidateConflictingRefsInVal`), whereas Stacked Borrows leaves its bytes
  unchanged, so a terminal state does not record retired references as Rust's
  memory holds them (`MirReturn`).
- **Admission and entry validation:** `runMirSteps` runs only an admissible
  body (`bodyAdmissible`: the pointer width is valid and every local has a
  well-formed Rust type, the control-flow graph has no edge into `bb0` and only
  well-formed `SwitchInt` tables, every `WithRetag::No` copy is a dereference
  temporary used only as the base of a dereference and no write, move, mutable
  borrow, or unique-reference copy crosses a shared reference, and no `Use`
  assignment reads a place that statically conflicts with its destination) from
  a valid entry state (`entryStateValid`: the state has a slot and a generation
  counter for every local, every non-argument frame slot is dead or
  uninitialized as at function entry, and the arguments are valid, typed by
  their targets' declared types, and free of conflicting aliases). Otherwise it
  returns `MirRunOutcome.rejected`, which is distinct from a fault
  (`MirRunOutcome.fault`) and from running out of fuel
  (`MirRunOutcome.outOfFuel`).
- **Type discipline:** Every assignment must be well typed under the declared
  local types (`rvalueTysOk`), and every stored value must conform to its
  destination's type.
- **Fail-closed transitions:** Out-of-bounds local or basic-block indices,
  ill-typed operations, dangling dereferences, and `Terminator.unreachable`
  transition to `StepOutcome.fault`.
-/

namespace Trusted

/-! ## Total list indexing and power-of-two helpers -/

/-- Compute $2^{\text{bits}}$ via `Nat.recCompiled`. -/
def natPow2 (bits : Nat) : Nat :=
  @Nat.recCompiled (fun _ => Nat) 1 (fun _ ih => ih + ih) bits

/-- Look up element `idx` in `xs` using `Nat.recCompiled` so concrete indices
reduce in $O(\text{idx})$ head steps without traversing the remainder of `xs`.
-/
def lookupAt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  @Nat.recCompiled (fun _ => List α → Option α)
    (fun l =>
      match l with
      | [] => none
      | x :: _ => some x)
    (fun _ ih l =>
      match l with
      | [] => none
      | _ :: rest => ih rest)
    idx xs

/-- Replace element `idx` in `xs` with `val`, returning `none` if `idx` is out
of bounds. -/
def setAt {α : Type} (xs : List α) (idx : Nat) (val : α) : Option (List α) :=
  @Nat.recCompiled (fun _ => List α → Option (List α))
    (fun l =>
      match l with
      | [] => none
      | _ :: rest => some (val :: rest))
    (fun _ ih l =>
      match l with
      | [] => none
      | x :: rest =>
        match ih rest with
        | some rest' => some (x :: rest')
        | none => none)
    idx xs

/-! ## Execution state and step outcomes -/

/-- Instantaneous execution state of a `MirBody`
(`compiler/rustc_middle/src/mir/mod.rs#L204-L251`):

- `locals`: current local slots `0 .. localCount - 1` (`_0` return slot,
  `_1 .. _argCount` argument slots, and temporaries), followed by any
  caller-owned referent slots (`idx ≥ localCount`) passed via reference
  arguments.
- `localGens`: per-slot storage generation counters incremented by
  `Stmt.storageLive` and `Stmt.storageDead`.
- `block`: index of the active basic block in `MirBody.blocks`.
- `stmtIdx`: index of the next statement to execute in the active basic block
  (`stmtIdx == bb.stmts.length` selects `bb.terminator`). -/
structure MirState where
  locals : List (Option MirVal)
  localGens : List Nat
  block : Nat
  stmtIdx : Nat

/-- Normal return outcome of a `MirBody`: the returned value loaded from `_0`
(or, when `_0` is uninitialized and its type has a unique value, that value;
see `MirTy.unitValue`) together with the terminal `MirState` at
`Terminator.return_` so postconditions can inspect mutated caller-owned
referents.

`state` does not record retired references as Rust's memory holds them.
Stacked Borrows retires a reference by removing or disabling its item in the
borrow stack and leaves the reference's bytes unchanged. This model instead
rewrites the stored reference so that its target is `⟨localGens.length⟩`, a
slot that does not exist, and its generation is `0`, keeping its mutability,
field path, and reborrow depth (`invalidateConflictingRefsInVal`). A
reference in a caller slot that an access of the callee retired keeps this
form in `state` unless a later store overwrites it, including a reference in
a slot that no argument reaches (`stepTerminator`), so it no longer names the
place that the pointer in the caller's memory still points to. A
specification must therefore not depend on the target, generation, field
path, or reborrow depth of a retired reference in `state`.

The rest of each caller slot is faithful: values without references hold
what Rust's memory holds, and a reference that is valid in the terminal state
(`MirVal.isValidInState state.localGens`) names the place that the pointer in
Rust's memory points to. A retired reference is never valid, because the slot
it names has no generation counter, so requiring `MirVal.isValidInState` of
every value read from `state` excludes retired references. -/
structure MirReturn where
  value : MirVal
  state : MirState

/-- Single-step operational transition outcome (`StepOutcome`):
- `.stepped next`: execution advanced to `next`.
- `.returned ret`: execution terminated normally via `Terminator.return_`.
- `.fault`: execution encountered undefined behavior or an invalid state. -/
inductive StepOutcome where
  | stepped (next : MirState)
  | returned (ret : MirReturn)
  | fault

/-- Outcome of running a body for a bounded number of steps (`runMirSteps`,
`stepMirLoop`):
- `.rejected`: the body is not admissible (`bodyAdmissible`), or the state
  does not start at `bb0` or is not a valid entry state (`entryStateValid`);
  the body was not run. This is a precondition failure, not a
  property of the execution.
- `.fault`: execution reached undefined behavior or an operation this
  semantics does not support, and stopped.
- `.outOfFuel`: execution neither faulted nor returned within the step bound.
- `.returned ret`: execution returned normally with `ret`.

Keeping these apart lets a specification distinguish them. With a single
failure value, a statement of the form "if the run succeeds then …" holds
vacuously for a body that faults, and "the body never faults, for any step
bound" cannot be stated at all. -/
inductive MirRunOutcome where
  | rejected
  | fault
  | outOfFuel
  | returned (ret : MirReturn)

/-- True iff the run returned normally. -/
def MirRunOutcome.isReturned : MirRunOutcome → Bool
  | .returned _ => true
  | _ => false

/-! ## Value validity, type checking, and aggregate field spines -/

/-- Structural fold over `MirVal` computed via `@Nat.recCompiled` over `v.fuel`,
avoiding `noncomputable` eliminators under `prelude`. -/
def MirVal.fold {α : Type}
    (fUninit : α)
    (fInt : Nat → α)
    (fBool : Bool → α)
    (fUnit : α)
    (fAdt : Nat → MirVal → α → α)
    (fFieldCons : MirVal → MirVal → α → α → α)
    (fRef : Bool → Nat → LocalId → List Nat → Nat → α)
    (v : MirVal) : α :=
  @Nat.recCompiled (fun _ => MirVal → α)
    (fun w =>
      match w with
      | ⟨_, .uninit⟩ => fUninit
      | ⟨_, .int n⟩ => fInt n
      | ⟨_, .bool b⟩ => fBool b
      | ⟨_, .unit⟩ => fUnit
      | ⟨_, .ref isMut gen loc path depth⟩ => fRef isMut gen loc path depth
      | ⟨_, .adt _ _⟩ => fUninit
      | ⟨_, .fieldCons _ _⟩ => fUninit)
    (fun _ ih w =>
      match w with
      | ⟨_, .uninit⟩ => fUninit
      | ⟨_, .int n⟩ => fInt n
      | ⟨_, .bool b⟩ => fBool b
      | ⟨_, .unit⟩ => fUnit
      | ⟨_, .ref isMut gen loc path depth⟩ => fRef isMut gen loc path depth
      | ⟨_, .adt id inner⟩ =>
        let innerVal : MirVal := ⟨_, inner⟩
        fAdt id innerVal (ih innerVal)
      | ⟨_, .fieldCons h t⟩ =>
        let hVal : MirVal := ⟨_, h⟩
        let tVal : MirVal := ⟨_, t⟩
        fFieldCons hVal tVal (ih hVal) (ih tVal))
    v.fuel v

/-- Structural equality on `MirTy` values computed via `@Nat.recCompiled`,
identifying the two encodings of the unit type, `.unit` and `.tuple []`
(`src/types/tuple.md#L26`):
> "For convenience and historical reasons, the tuple type with no fields
> (`()`) is often called *unit* or *the unit type*." -/
def MirTy.beq (t1 t2 : MirTy) : Bool :=
  @Nat.recCompiled (fun _ => MirTy → MirTy → Bool)
    (fun a b =>
      match a, b with
      | ⟨_, .usize⟩, ⟨_, .usize⟩ => true
      | ⟨_, .uint b1⟩, ⟨_, .uint b2⟩ => b1 == b2
      | ⟨_, .bool⟩, ⟨_, .bool⟩ => true
      | ⟨_, .unit⟩, ⟨_, .unit⟩ => true
      | ⟨_, .never⟩, ⟨_, .never⟩ => true
      | ⟨_, .nil⟩, ⟨_, .nil⟩ => true
      | ⟨_, .unit⟩, ⟨_, .tuple .nil⟩ => true
      | _, _ => false)
    (fun _ ih a b =>
      match a, b with
      | ⟨_, .usize⟩, ⟨_, .usize⟩ => true
      | ⟨_, .uint b1⟩, ⟨_, .uint b2⟩ => b1 == b2
      | ⟨_, .bool⟩, ⟨_, .bool⟩ => true
      | ⟨_, .unit⟩, ⟨_, .unit⟩ => true
      | ⟨_, .never⟩, ⟨_, .never⟩ => true
      | ⟨_, .nil⟩, ⟨_, .nil⟩ => true
      | ⟨_, .unit⟩, ⟨_, .tuple .nil⟩ => true
      | ⟨_, .tuple .nil⟩, ⟨_, .unit⟩ => true
      | ⟨_, .adt id1 fs1⟩, ⟨_, .adt id2 fs2⟩ =>
        id1 == id2 && ih ⟨_, fs1⟩ ⟨_, fs2⟩
      | ⟨_, .tuple es1⟩, ⟨_, .tuple es2⟩ => ih ⟨_, es1⟩ ⟨_, es2⟩
      | ⟨_, .cons h1 r1⟩, ⟨_, .cons h2 r2⟩ =>
        ih ⟨_, h1⟩ ⟨_, h2⟩ && ih ⟨_, r1⟩ ⟨_, r2⟩
      | ⟨_, .ref i1⟩, ⟨_, .ref i2⟩ => ih ⟨_, i1⟩ ⟨_, i2⟩
      | ⟨_, .refMut i1⟩, ⟨_, .refMut i2⟩ => ih ⟨_, i1⟩ ⟨_, i2⟩
      | _, _ => false)
    t1.fuel t1 t2

/-- True iff `v` and all nested aggregate payloads inside `v` are initialized
(contain no `MirVal.uninit` sub-value)
(`src/behavior-considered-undefined.md#L114-L132`):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory." -/
def MirVal.isFullyInit (v : MirVal) : Bool :=
  MirVal.fold
    false
    (fun _ => true)
    (fun _ => true)
    true
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead && ihTail)
    (fun _ _ _ _ _ => true)
    v

/-- True iff `v` is fully initialized AND every reference `MirVal.ref _ refGen
loc _ _` inside `v` (including references nested inside aggregate structs or
tuples) points to a live slot whose current storage generation in `localGens`
equals `refGen` (`src/behavior-considered-undefined.md#L147`):
> "A reference or [`Box<T>`] must be aligned and non-null, it cannot be
> [dangling], and it must point to a valid value (in case of dynamically sized
> types, using the actual dynamic type of the pointee as determined by the
> [metadata])." -/
def MirVal.isValidInState (localGens : List Nat) (v : MirVal) : Bool :=
  MirVal.fold
    false
    (fun _ => true)
    (fun _ => true)
    true
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead && ihTail)
    (fun _ refGen loc _ _ =>
      match lookupAt localGens loc.index with
      | some curGen => curGen == refGen
      | none => false)
    v

/-- True iff `v` (or any nested `.adt`/`.fieldCons` sub-value) contains a
reference `.ref _ _ targetLoc _ _` pointing to an in-frame local slot
`targetLoc.index < localCount`. Because all in-frame locals `0 .. localCount -
1` are deallocated when the function frame returns, returning such a reference
or leaving it stored in a caller-owned referent slot would create a dangling
reference (`src/behavior-considered-undefined.md#L147`):
> "A reference or [`Box<T>`] must be aligned and non-null, it cannot be
> [dangling], and it must point to a valid value (in case of dynamically sized
> types, using the actual dynamic type of the pointee as determined by the
> [metadata])."

Caller-owned referent slots at indices `targetLoc.index ≥ localCount` outlive
the returning frame and remain valid. -/
def MirVal.refsFrameLocal (localCount : Nat) (v : MirVal) : Bool :=
  MirVal.fold
    false
    (fun _ => false)
    (fun _ => false)
    false
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead || ihTail)
    (fun _ _ loc _ _ => decide (loc.index < localCount))
    v

/-- Every reference `(mutable, gen, loc, fieldPath, reborrowDepth)` stored in
`v`, including references in fields of aggregates but not references behind
other references. -/
def MirVal.refsIn (v : MirVal) : List (Bool × Nat × LocalId × List Nat × Nat) :=
  MirVal.fold
    []
    (fun _ => [])
    (fun _ => [])
    []
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead ++ ihTail)
    (fun isMut gen loc path depth => [(isMut, gen, loc, path, depth)])
    v

/-- `v` with the `reborrowDepth` of every reference in `v` (as enumerated by
`MirVal.refsIn`) increased by one. -/
def MirVal.deepenRefs (v : MirVal) : MirVal :=
  MirVal.fold
    .uninit
    (fun n => .int n)
    (fun b => .bool b)
    .unit
    (fun id _ ihInner => .adt id ihInner)
    (fun _ _ ihHead ihTail => .fieldCons ihHead ihTail)
    (fun isMut gen loc path depth => .ref isMut gen loc path (depth + 1))
    v

/-- True iff `bits` is the width of one of Rust's fixed-width unsigned integer
types (`src/types/numeric.md#L8-L16`):
> "The unsigned integer types consist of:"

```text
Type   | Minimum | Maximum
-------|---------|-------------------
`u8`   | 0       | 2<sup>8</sup>-1
`u16`  | 0       | 2<sup>16</sup>-1
`u32`  | 0       | 2<sup>32</sup>-1
`u64`  | 0       | 2<sup>64</sup>-1
`u128` | 0       | 2<sup>128</sup>-1
```

`MirTy.uint bits` with any other `bits` is not a Rust type, so the semantics
gives it no bit-width (`tyBitWidth`) and no inhabitants (`checkValMatchesTy`),
and `bodyTysSupported` rejects bodies that mention it. -/
def isRustUintWidth (bits : Nat) : Bool :=
  bits == 8 || bits == 16 || bits == 32 || bits == 64 || bits == 128

/-- True iff `bits` is a pointer width that `rustc` supports, and hence a
possible width of `usize` (`src/types/numeric.md#L37-L38`,
`compiler/rustc_abi/src/lib.rs#L679-L687`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."

```rust
pub fn ptr_sized_integer(&self) -> Integer {
    use Integer::*;
    match self.pointer_offset().bits() {
        16 => I16,
        32 => I32,
        64 => I64,
        bits => panic!("ptr_sized_integer: unknown pointer bit size {bits}"),
    }
}
``` -/
def isRustPtrWidth (bits : Nat) : Bool :=
  bits == 16 || bits == 32 || bits == 64

/-- True iff every `.uint bits` node anywhere inside `t` (including field,
element, and pointee types) has a Rust integer width (`isRustUintWidth`). -/
def MirTy.uintWidthsSupported (t : MirTy) : Bool :=
  @Nat.recCompiled (fun _ => MirTy → Bool)
    (fun a =>
      match a with
      | ⟨_, .uint bits⟩ => isRustUintWidth bits
      | ⟨_, .usize⟩ | ⟨_, .bool⟩ | ⟨_, .unit⟩ | ⟨_, .never⟩ | ⟨_, .nil⟩ => true
      -- Unreachable: a node of fuel `0` has no children. Reject it anyway.
      | _ => false)
    (fun _ ih a =>
      match a with
      | ⟨_, .uint bits⟩ => isRustUintWidth bits
      | ⟨_, .adt _ fs⟩ => ih ⟨_, fs⟩
      | ⟨_, .tuple es⟩ => ih ⟨_, es⟩
      | ⟨_, .cons h r⟩ => ih ⟨_, h⟩ && ih ⟨_, r⟩
      | ⟨_, .ref i⟩ => ih ⟨_, i⟩
      | ⟨_, .refMut i⟩ => ih ⟨_, i⟩
      | ⟨_, .usize⟩ | ⟨_, .bool⟩ | ⟨_, .unit⟩ | ⟨_, .never⟩ | ⟨_, .nil⟩ => true)
    t.fuel t

/-- True iff `t` is a well-formed type of this AST: `.nil` and `.cons` occur
only as properly terminated field lists of `.adt` and `.tuple` (the spines that
`MirTy.packList` builds), and every field, element, and pointee is itself a
well-formed type. `MirTyTree` represents field lists with the same constructors
as types so that structural recursion stays first-order; this check keeps a
bare spine from being used as a type. -/
def MirTy.wellFormed (t : MirTy) : Bool :=
  @Nat.recCompiled (fun _ => MirTy → Bool → Bool)
    (fun a expectSpine =>
      match a, expectSpine with
      | ⟨_, .nil⟩, true => true
      | ⟨_, .usize⟩, false | ⟨_, .uint _⟩, false | ⟨_, .bool⟩, false
      | ⟨_, .unit⟩, false | ⟨_, .never⟩, false => true
      -- A node of fuel `0` has no children, so nothing else is well formed.
      | _, _ => false)
    (fun _ ih a expectSpine =>
      match a, expectSpine with
      | ⟨_, .nil⟩, true => true
      | ⟨_, .cons h r⟩, true => ih ⟨_, h⟩ false && ih ⟨_, r⟩ true
      | ⟨_, .adt _ fs⟩, false => ih ⟨_, fs⟩ true
      | ⟨_, .tuple es⟩, false => ih ⟨_, es⟩ true
      | ⟨_, .ref i⟩, false => ih ⟨_, i⟩ false
      | ⟨_, .refMut i⟩, false => ih ⟨_, i⟩ false
      | ⟨_, .usize⟩, false | ⟨_, .uint _⟩, false | ⟨_, .bool⟩, false
      | ⟨_, .unit⟩, false | ⟨_, .never⟩, false => true
      | _, _ => false)
    t.fuel t false

/-- True iff `body` declares a type for every local and every declared type is
a Rust type: `body.localCount ≤ body.localTys.length`, `body.ptrWidthBits` is a
supported pointer width (`isRustPtrWidth`), and every declared type is well
formed (`MirTy.wellFormed`) and uses only Rust integer widths
(`MirTy.uintWidthsSupported`).

A captured body declares a type for every local, the return place first
(`compiler/rustc_middle/src/mir/mod.rs#L235-L240`):
> "Declarations of locals.
>
> The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries."

Entries `0 .. localCount - 1` of `localTys` are those declarations, so every
place a body can name has a declared type and the semantics never runs a body
with an untyped local. Entries at `localCount` and beyond give the types of
the caller-owned slots of the entry state (`MirState.locals`), which are not
part of the captured body. Every caller-owned slot that an entry reference
reaches must have such an entry (`collectEntryRefsInVal`). -/
def bodyTysSupported (body : MirBody) : Bool :=
  decide (body.localCount ≤ body.localTys.length) &&
    isRustPtrWidth body.ptrWidthBits &&
    body.localTys.foldr
      (fun t acc => t.wellFormed && t.uintWidthsSupported && acc) true

/-- Bit-width of an unsigned integer `MirTy` (`ptrWidthBits` for `.usize`,
`bits` for `.uint bits`), or `none` when the width is not one Rust supports
(`isRustPtrWidth`, `isRustUintWidth`) (`src/types/numeric.md#L8-L16`,
`src/types/numeric.md#L37-L38`). -/
def tyBitWidth (ptrWidthBits : Nat) : MirTy → Option Nat
  | ⟨_, .usize⟩ =>
    if isRustPtrWidth ptrWidthBits then some ptrWidthBits else none
  | ⟨_, .uint bits⟩ => if isRustUintWidth bits then some bits else none
  | _ => none

/-- Project a `PlaceElem` path through a declared `MirTy` (`Deref` unwraps
`.ref` and `.refMut`; `Field idx` indexes into `.tuple elems` and
`.adt _ fieldTys`), following `PlaceTy::projection_ty`
(`compiler/rustc_middle/src/mir/statement.rs#L184`,
`compiler/rustc_middle/src/mir/statement.rs#L219-L223`,
`compiler/rustc_middle/src/mir/statement.rs#L245-L246`):
> "elems.iter().fold(self, |place_ty, &elem| place_ty.projection_ty(tcx,
> elem))"
> "ProjectionElem::Deref => {
> let ty = self.ty.builtin_deref(true).unwrap_or_else(|| {
> bug!("deref projection of non-dereferenceable ty {:?}", self)
> });
> PlaceTy::from_ty(ty)"
> "ProjectionElem::Field(f, fty) => {
> PlaceTy::from_ty(handle_field(self.ty, self.variant_index, f, fty))"

Correspondence: `builtin_deref` of `&T` or `&mut T` is `T`, and the field type
of field `idx` of a tuple or (non-generic, single-variant) struct is its
declared type. Where upstream would hit `bug!` (dereferencing a
non-reference) or index out of range, this function returns `none`, and
callers treat that as ill typed. The other projections are not in the subset
(`PlaceElem`). -/
def projectPlaceTy (projs : List PlaceElem) (ty : MirTy) : Option MirTy :=
  projs.foldr
    (fun proj ih curTy =>
      match proj, curTy with
      | .deref, ⟨_, .ref inner⟩ => ih ⟨_, inner⟩
      | .deref, ⟨_, .refMut inner⟩ => ih ⟨_, inner⟩
      | .field idx, ⟨_, .tuple elems⟩ =>
        match lookupAt (MirTy.unpackList ⟨_, elems⟩) idx with
        | some elemTy => ih elemTy
        | none => none
      | .field idx, ⟨_, .adt _ fieldTys⟩ =>
        match lookupAt (MirTy.unpackList ⟨_, fieldTys⟩) idx with
        | some elemTy => ih elemTy
        | none => none
      | _, _ => none)
    (fun curTy => some curTy)
    ty

/-- Project a resolved field-index path `fieldPath` through a declared `MirTy`
(indexing into `.tuple elems` and `.adt _ fieldTys` at each step). This is
`projectPlaceTy` restricted to `Field` projections, used for the field path
that remains after `resolvePlace` has followed a dereference; see
`projectPlaceTy` for the upstream correspondence. -/
def projectFieldPathTy (fieldPath : List Nat) (ty : MirTy) : Option MirTy :=
  fieldPath.foldr
    (fun idx ih curTy =>
      match curTy with
      | ⟨_, .tuple elems⟩ =>
        match lookupAt (MirTy.unpackList ⟨_, elems⟩) idx with
        | some elemTy => ih elemTy
        | none => none
      | ⟨_, .adt _ fieldTys⟩ =>
        match lookupAt (MirTy.unpackList ⟨_, fieldTys⟩) idx with
        | some elemTy => ih elemTy
        | none => none
      | _ => none)
    (fun curTy => some curTy)
    ty

/-- Extract element `idx` from a right-nested `.fieldCons` spine. -/
def getSpineAt (idx : Nat) (spine : MirVal) : Option MirVal :=
  @Nat.recCompiled (fun _ => MirVal → Option MirVal)
    (fun s =>
      match s with
      | ⟨_, .fieldCons h _⟩ => some ⟨_, h⟩
      | _ => none)
    (fun _ ih s =>
      match s with
      | ⟨_, .fieldCons _ t⟩ => ih ⟨_, t⟩
      | _ => none)
    idx spine

/-- Project field `idx` from an aggregate `MirVal` (`.adt` or tuple
`.fieldCons`). -/
def getMirField (idx : Nat) (v : MirVal) : Option MirVal :=
  match v with
  | ⟨_, .adt _ inner⟩ => getSpineAt idx ⟨_, inner⟩
  | ⟨_, .fieldCons _ _⟩ => getSpineAt idx v
  | _ => none

/-- Read nested field path `path` of arbitrary depth from `v`. -/
def readFieldPath (path : List Nat) (v : MirVal) : Option MirVal :=
  path.foldr
    (fun idx ih cur =>
      match getMirField idx cur with
      | some sub => ih sub
      | none => none)
    (fun cur => some cur)
    v

/-- Check whether runtime value `v` conforms to declared MIR type `ty` under
target pointer bit-width `ptrWidthBits`
(`src/types/numeric.md#L8-L16`, `src/types/numeric.md#L37-L38`,
`src/types/boolean.md#L8-L9`, `src/types/tuple.md#L11-L26`,
`src/behavior-considered-undefined.md#L147`):
> "The unsigned integer types consist of:"
> "`u8`   | 0       | 2<sup>8</sup>-1"
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."
> "A reference or [`Box<T>`] must be aligned and non-null, it cannot be
> [dangling], and it must point to a valid value (in case of dynamically sized
> types, using the actual dynamic type of the pointee as determined by the
> [metadata])."

When `allowUninit = true` (used to validate the root aggregate after a projected
sub-field write into a partially initialized struct or tuple), `MirVal.uninit`
sub-values are permitted for not-yet-initialized sibling fields while all
initialized fields must match their declared types. No integer value conforms
to `.uint bits` unless `isRustUintWidth bits`, or to `.usize` unless
`isRustPtrWidth ptrWidthBits`. For `.ref isMut _ loc path
_` against `.ref inner` or `.refMut inner`, when `localTys` declares a type for
`loc.index`, its projected field type at `path` must equal `inner`; otherwise
the pointee value at `(loc, path)` in `locals` must exist and conform to
`inner`. A reference whose target has neither a declared type nor a value in
`locals` never conforms, so passing empty lists rejects every reference. -/
def checkValMatchesTy (ptrWidthBits : Nat) (ty : MirTy)
    (v : MirVal) (allowUninit : Bool)
    (localTys : List MirTy)
    (locals : List (Option MirVal)) : Bool :=
  let stepNonRef
      (onRef : Bool → Nat → LocalId → List Nat → Nat → MirTy → Bool)
      (curTy0 : MirTy) (v0 : MirVal) (allowUninit0 : Bool) : Bool :=
    @MirVal.fold (MirTy → Bool)
      (fun _ => allowUninit0)
      (fun n curTy =>
        match curTy with
        | ⟨_, .usize⟩ =>
          isRustPtrWidth ptrWidthBits && decide (n < natPow2 ptrWidthBits)
        | ⟨_, .uint bits⟩ => isRustUintWidth bits && decide (n < natPow2 bits)
        | _ => false)
      (fun _ curTy =>
        match curTy with
        | ⟨_, .bool⟩ => true
        | _ => false)
      (fun curTy =>
        match curTy with
        | ⟨_, .unit⟩ => true
        | ⟨_, .tuple .nil⟩ => true
        | _ => false)
      (fun id _ ihInner curTy =>
        match curTy with
        | ⟨_, .adt id' fieldTys⟩ =>
          id == id' && ihInner ⟨_, .tuple fieldTys⟩
        | _ => false)
      (fun _ _ ihHead ihTail curTy =>
        match curTy with
        | ⟨_, .tuple (.cons elemTy restTys)⟩ =>
          ihHead ⟨_, elemTy⟩ && ihTail ⟨_, .tuple restTys⟩
        | _ => false)
      onRef
      v0 curTy0
  @Nat.recCompiled (fun _ => MirTy → MirVal → Bool → Bool)
    (stepNonRef (fun _ _ _ _ _ _ => false))
    (fun _ ihTy =>
      stepNonRef (fun isMut _ loc path _ curTy =>
        let expectedInnerOpt : Option MirTy :=
          match curTy with
          | ⟨_, .ref inner⟩ => if !isMut then some ⟨_, inner⟩ else none
          | ⟨_, .refMut inner⟩ => if isMut then some ⟨_, inner⟩ else none
          | _ => none
        match expectedInnerOpt with
        | none => false
        | some expectedInner =>
          match lookupAt localTys loc.index with
          | some rootTy =>
            match projectFieldPathTy path rootTy with
            | some pointeeTy => MirTy.beq pointeeTy expectedInner
            | none => false
          | none =>
            match lookupAt locals loc.index with
            | some (some rootVal) =>
              match readFieldPath path rootVal with
              | some pointeeVal => ihTy expectedInner pointeeVal false
              | none => false
            | _ => false))
    ty.fuel ty v allowUninit

/-- Check whether storing root value `v` into local slot `locIdx` satisfies
the slot's declared type in `localTys` (with pointer width `ptrWidthBits`). A
slot without a declared type accepts nothing. Every slot that the semantics
stores into or returns from has one: in-frame locals by admission
(`bodyTysSupported`), and caller slots that an entry reference reaches by
entry validation (`collectEntryRefsInVal`). -/
def checkLocalStoreTy (ptrWidthBits : Nat) (localTys : List MirTy)
    (locIdx : Nat) (v : MirVal) (allowUninit : Bool)
    (locals : List (Option MirVal)) : Bool :=
  match lookupAt localTys locIdx with
  | some ty =>
    checkValMatchesTy ptrWidthBits ty v allowUninit localTys locals
  | none => false

/-- True iff every reference `.ref _ refGen loc fieldPath _` inside `v`
resolves in `locals` at `(loc.index, fieldPath)` to an allocated, initialized
pointee value that is valid in `localGens`
(`src/behavior-considered-undefined.md#L147`). -/
def valRefsHaveLivePointees (localGens : List Nat)
    (locals : List (Option MirVal)) (v : MirVal) : Bool :=
  MirVal.fold
    false
    (fun _ => true)
    (fun _ => true)
    true
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead && ihTail)
    (fun _ refGen loc fieldPath _ =>
      match lookupAt localGens loc.index, lookupAt locals loc.index with
      | some curGen, some (some rootVal) =>
        curGen == refGen &&
        match readFieldPath fieldPath rootVal with
        | some pointeeVal => pointeeVal.isValidInState localGens
        | none => false
      | _, _ => false)
    v

/-- Pack a list of field values into a right-nested `.fieldCons` spine
terminated by `.unit`. -/
def packSpine (vals : List MirVal) : MirVal :=
  vals.foldr MirVal.fieldCons MirVal.unit

/-- Replace element `idx` in a right-nested `.fieldCons` spine with `newVal`.
-/
def setSpineAt (idx : Nat) (newVal : MirVal) (spine : MirVal) : Option MirVal :=
  @Nat.recCompiled (fun _ => MirVal → Option MirVal)
    (fun s =>
      match s with
      | ⟨_, .fieldCons _ t⟩ => some (.fieldCons newVal ⟨_, t⟩)
      | _ => none)
    (fun _ ih s =>
      match s with
      | ⟨_, .fieldCons h t⟩ =>
        match ih ⟨_, t⟩ with
        | some t' => some (.fieldCons ⟨_, h⟩ t')
        | none => none
      | _ => none)
    idx spine

/-- Update field `idx` of an aggregate `MirVal` (`.adt` or tuple `.fieldCons`)
to `newVal`. -/
def setMirField (idx : Nat) (newVal : MirVal) (v : MirVal) : Option MirVal :=
  match v with
  | ⟨_, .adt id inner⟩ =>
    match setSpineAt idx newVal ⟨_, inner⟩ with
    | some inner' => some (.adt id inner')
    | none => none
  | ⟨_, .fieldCons _ _⟩ => setSpineAt idx newVal v
  | _ => none

/-- Write `newVal` at nested field path `path` of arbitrary depth inside `v`. -/
def writeFieldPath (path : List Nat) (newVal : MirVal) (v : MirVal) :
    Option MirVal :=
  path.foldr
    (fun idx ih cur =>
      match getMirField idx cur with
      | some sub =>
        match ih sub with
        | some sub' => setMirField idx sub' cur
        | none => none
      | none => none)
    (fun _ => some newVal)
    v

/-- Materialize an uninitialized aggregate shell for `ty` when a projected field
write targets an `.uninit` aggregate slot (`_1.0 = v` after `StorageLive(_1)` or
after moving out of `_1`).

Correspondence: in the pinned interpreter a local is a block of bytes, which
`StorageLive` makes entirely uninitialized
(`compiler/rustc_const_eval/src/interpret/stack.rs#L562-L573`, quoted at
`entryFrameSlotsCanonical`), and a store to a field writes only that field's
bytes, because the fields of a struct or tuple do not overlap
(`src/type-layout.md#L178-L179`, quoted at `MirTy.adt`). This model represents
a local whose fields are not all written as a field spine whose untouched
fields are `.uninit`; this function builds that spine before the first field
store. -/
def mkUninitAggregateForTy : MirTy → Option MirVal
  | ⟨_, .tuple elems⟩ =>
    let elemTys := MirTy.unpackList ⟨_, elems⟩
    if elemTys.isEmpty then none
    else some (packSpine (elemTys.map (fun _ => MirVal.uninit)))
  | ⟨_, .adt id fields⟩ =>
    let fieldTys := MirTy.unpackList ⟨_, fields⟩
    if fieldTys.isEmpty then none
    else some (.adt id (packSpine (fieldTys.map (fun _ => MirVal.uninit))))
  | _ => none

/-- Length of a right-nested `.fieldCons` spine terminated by `.unit`, or
`none` if `v` is not a `.unit`-terminated `.fieldCons` spine. -/
def spineLength (v : MirVal) : Option Nat :=
  MirVal.fold
    none
    (fun _ => none)
    (fun _ => none)
    (some 0)
    (fun _ _ _ => none)
    (fun _ _ _ ihTail =>
      match ihTail with
      | some n => some (n + 1)
      | none => none)
    (fun _ _ _ _ _ => none)
    v

/-- Write `newVal` at nested field path `path` inside `v`, materializing
uninitialized aggregate shells along `path` from `rootTyOpt` whenever an
intermediate `.uninit` value has a declared `.tuple` or `.adt` type with
field types, and verifying that each existing aggregate container along `path`
matches the outer `.tuple` or `.adt` constructor and field-spine length of its
declared type without inspecting untouched sibling fields. Only the addressed
field changes, matching a store that writes only that field's bytes
(`mkUninitAggregateForTy`). -/
def writeFieldPathWithTy (path : List Nat) (newVal : MirVal)
    (rootTyOpt : Option MirTy) (v : MirVal) : Option MirVal :=
  path.foldr
    (fun idx ih cur curTyOpt =>
      let curAggOpt : Option MirVal :=
        match cur, curTyOpt with
        | ⟨_, .uninit⟩, some curTy => mkUninitAggregateForTy curTy
        | _, some ⟨_, .tuple elems⟩ =>
          let elemTys := MirTy.unpackList ⟨_, elems⟩
          if !elemTys.isEmpty && spineLength cur == some elemTys.length then
            some cur
          else
            none
        | ⟨_, .adt id inner⟩, some ⟨_, .adt id' fields⟩ =>
          let fieldTys := MirTy.unpackList ⟨_, fields⟩
          if id == id' && !fieldTys.isEmpty &&
              spineLength ⟨_, inner⟩ == some fieldTys.length then
            some cur
          else
            none
        | _, _ => none
      let subTyOpt : Option MirTy :=
        match curTyOpt with
        | some curTy => projectFieldPathTy [idx] curTy
        | none => none
      match curAggOpt with
      | some curAgg =>
        match getMirField idx curAgg with
        | some sub =>
          match ih sub subTyOpt with
          | some sub' => setMirField idx sub' curAgg
          | none => none
        | none => none
      | none => none)
    (fun _ _ => some newVal)
    v rootTyOpt

/-! ## Place resolution, loads, and stores -/

/-- Extract a sequence of `.field idx` projections from `elems`, returning
`none` if any `.deref` element appears in `elems`. -/
def extractFieldPath (elems : List PlaceElem) : Option (List Nat) :=
  elems.foldr
    (fun e acc =>
      match e, acc with
      | .field idx, some rest => some (idx :: rest)
      | _, _ => none)
    (some [])

/-- Resolved target local slot, nested field path, reference mutability mode,
originating reference local slot (if dereferenced), and reborrow nesting depth
of a `Place` in a given `MirState`.
`viaMutRef` is `none` for direct local access, `some true` when accessed through
a mutable reference (`&mut T`), and `some false` when accessed through a shared
reference (`&T`). -/
structure ResolvedPlace where
  targetLoc : LocalId
  fieldPath : List Nat
  viaMutRef : Option Bool
  sourceRefSlot : Option Nat
  reborrowDepth : Nat

/-- True iff field path `p1` and field path `p2` are equal. -/
def pathEq (p1 p2 : List Nat) : Bool :=
  p1.foldr
    (fun x ih ys =>
      match ys with
      | [] => false
      | y :: ys' => x == y && ih ys')
    (fun ys =>
      match ys with
      | [] => true
      | _ :: _ => false)
    p2

/-- True iff field path `p1` and field path `p2` overlap (one is a prefix of
the other).

Distinct field indices at the same position denote disjoint storage because
every aggregate in this AST is a tuple or a struct (`MirTy.adt`, which has no
union or enum form). The borrow checker relies on the same fact and makes
the one exception for unions
(`compiler/rustc_borrowck/src/places_conflict.rs#L309-L324`):
> "(ProjectionElem::Field(f1, _), ProjectionElem::Field(f2, _)) => {
> if f1 == f2 {
> // same field (e.g., `a.y` vs. `a.y`) - recur.
> ...
> } else {
> let ty = pi1.ty(body, tcx).ty;
> if ty.is_union() {
> // Different fields of a union, we are basically stuck.
> ...
> Overlap::Arbitrary
> } else {
> // Different fields of a struct (`a.x` vs. `a.y`). Disjoint!"

The Reference also guarantees that struct fields do not overlap
(`src/type-layout.md#L178-L179`):
> "For [structs], it is further guaranteed that the fields do not overlap."
-/
def pathsOverlap (p1 p2 : List Nat) : Bool :=
  p1.foldr
    (fun x ih ys =>
      match ys with
      | [] => true
      | y :: ys' => x == y && ih ys')
    (fun _ => true)
    p2

/-- True iff an access to `resolved` retires a live reference with mutability
`otherMut` and reborrow depth `otherDepth` that points into an overlapping
sub-place of the same local (`needMut = true` for writes, moves, mutable
borrows, and retags of mutable references; `needMut = false` for reads, shared
borrows, and retags of shared references).

## Upstream contract

The pinned Rust Reference states only the outline of the aliasing rules
(`src/behavior-considered-undefined.md#L24-L27`):
> "Breaking the pointer aliasing rules. The exact aliasing rules are not
> determined yet, but here is an outline of the general principles:"
> "`&T` must point to memory that is not mutated while they are live (except
> for data inside an [`UnsafeCell<U>`]), and `&mut T` must point to memory that
> is not read or written by any pointer not derived from the reference and that
> no other reference points to while they are live (with no exceptions)."

The rules below therefore follow Stacked Borrows, the executable aliasing model
that the pinned toolchain's Miri checks by default
(`src/tools/miri/src/eval.rs#L180`, `src/tools/miri/README.md#L20-L21`):
> "borrow_tracker: Some(BorrowTrackerMethod::StackedBorrows),"
> "**Experimental**: Violations of the [Stacked Borrows] rules governing
> aliasing for reference types"

In Stacked Borrows, each location has a stack of tagged items. Creating or
retagging a reference grants a new tag derived from its parent: `&mut T` gets a
`Unique` item through a write access and `&T` gets a `SharedReadOnly` item
through a read access
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L77-L82`,
`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L102-L106`). The
access goes through the parent's tag, and the new item is pushed on top
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L396-L400`):
> "// Simple case: We are just a regular memory access, and then push our thing
> on top,
> // like a regular stack."

An access through a tag removes or disables the conflicting items above the
item that grants it, and leaves the items below it alone
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L288-L290`,
`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L307`):
> "// Remove everything above the write-compatible items, like a proper stack.
> This makes sure read-only and unique
> // pointers become invalid on write accesses (ensures F2a, and ensures U2 for
> write accesses)."
> "// On a read, *disable* all `Unique` above the granting item.  This ensures
> U2 for read accesses."

This subset has no raw pointers or calls, and the model gives every `&mut T`
a `Unique` item and every `&T` a `SharedReadOnly` item. Miri grants the more
permissive `SharedReadWrite` item, with no access, in three cases: two-phase
mutable borrows, mutable references to `!Unpin` pointees, and shared
references to pointees that are not `Freeze` (that contain an `UnsafeCell`)
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L65-L90`,
`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L102-L112`):
> "We mostly just give up on 2phase-borrows, and treat these exactly like raw
> pointers."
> "`!Unpin` dereferences do not get `noalias` nor `dereferenceable`."
> "perm: Permission::SharedReadWrite,
> access: None,"
> "freeze_perm: Permission::SharedReadOnly, ... nonfreeze_perm:
> Permission::SharedReadWrite,
> // Inside UnsafeCell, this does *not* count as an access, as there
> // might actually be mutable references further up the stack that
> // we have to keep alive.
> nonfreeze_access: None,"
A struct `.adt` may contain an `UnsafeCell` or be `!Unpin`, so these cases can
arise. Treating such a reference as `Unique` or `SharedReadOnly` makes its
creation perform an access and makes accesses through it remove more items,
so it can only retire more references and add faults; it never lets an
execution succeed that Stacked Borrows rejects. A removed or disabled item
corresponds to a retired reference (`invalidateConflictingRefsInVal`).

## Correspondence

`reborrowDepth` is the depth of a reference's tag in the reborrow tree of its
referent. An owner access has depth `0`. A borrow through a place of depth `d`
(`evalBorrow`) and a retag of a reference of depth `d` (`retagVal`) both create
a tag of depth `d + 1`. A copy without a retag (`Rvalue.use _ .no`) keeps its
source's tag, and so its depth, because Miri skips the retag in that mode
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L865-L870`):
> "RetagMode::None => return interp_ok(None), // no retagging"

Argument references keep whatever depth the entry state gives them.
Overlapping entry references are one stored reference reached twice, all
shared, or shared references together with a `&mut` that the callee reaches
only through a shared reference (`entryArgsExclusive`,
`collectEntryRefsInVal`). In the third case the `&mut` is read-only for the
callee: `stmtDerefTempsOk` rejects writes, moves, mutable borrows, and
unique-reference copies through it, so it never yields a write or a mutable
child. Entry validation also requires each of those shared references to be
deeper than the `&mut` (`conflictsWithAnyEntryRef`), as a reborrow of the
`&mut` is; in a call that borrowck accepts, each of them is such a reborrow
(see `collectEntryRefsInVal`). A read through a reference retires only deeper
mutable references, so a read through the `&mut` keeps the shared
references, and a read through a shared reference keeps the shallower
`&mut`, as in Stacked Borrows. Without the depth check, a read through a
shared reference that is not deeper would retire the `&mut`, which Stacked
Borrows keeps. Retiring rewrites the `&mut` stored in the caller's slot
(`invalidateConflictingRefsInVal`), so the terminal state (`MirReturn`) would
then show a change that the caller's memory does not have.

Every operation that creates a tag of depth `d + 1` first performs the
corresponding access through its depth-`d` parent, and that access retires
every conflicting overlapping reference deeper than `d`. A mutable borrow or a
mutable retag never goes through a shared reference (`evalBorrow`, `retagVal`),
so every ancestor of a mutable reference is mutable. Together with entry
validation, these keep the following invariant: two live references to
overlapping sub-places with the same depth, at least one of them a mutable
reference that the callee can write through (not one reached only through a
shared reference, as above), are copies of a single tag. Under this
invariant, every live overlapping reference that an access through a tag must
retire descends from that tag. Likewise,
when the access is a write or the shallower reference is mutable, every live
overlapping reference at a smaller depth is an ancestor of the accessing tag
(or a copy of one). The rules therefore match Stacked Borrows:

- An owner access (`resolved.viaMutRef = none`) uses the owner's item, which
  lies below every reference to the local. A write retires every overlapping
  reference, and a read retires every overlapping mutable reference
  (`needMut || otherMut`).
- An access through a reference of depth `d` (`resolved.viaMutRef = some _`)
  keeps every shallower reference (its ancestors lie below it on the stack)
  and keeps copies of its own tag (depth `d`). The deeper references it
  conflicts with descend from it and lie above it: a write retires all of
  them, and a read retires the mutable ones
  (`d < otherDepth && (needMut || otherMut)`). A read keeps deeper shared
  references, as Stacked Borrows keeps `SharedReadOnly` items above the
  granting item on a read.
- A write through a reference of depth `d` also retires overlapping shared
  references of depth `d` (`needMut && !otherMut`). The writing reference is
  one the callee can write through, and the invariant rules out a live shared
  reference at the same depth as such a reference, so this case
  is unreachable from a valid entry state; the rule makes it fail closed, in
  line with the write rule that pops `SharedReadOnly` items (F2a).
- A mutable reference of depth `d` that survives a write through another
  reference of depth `d` is, by the invariant, a copy of the same tag, so
  Stacked Borrows also lets both be used. A compiler copy such as
  `_2 = copy ((*_1).0)` takes this path. -/
def refDepthConflicts (resolved : ResolvedPlace) (needMut : Bool)
    (otherMut : Bool) (otherDepth : Nat) : Bool :=
  match resolved.viaMutRef with
  | none => needMut || otherMut
  | some _ =>
    (decide (resolved.reborrowDepth < otherDepth) && (needMut || otherMut)) ||
    (needMut && !otherMut && decide (resolved.reborrowDepth == otherDepth))

/-- True iff `v` contains a live reference that an access to `resolved` must
retire (`needMut = true` for writes, moves, mutable borrows, and retags of
mutable references; `needMut = false` for reads, shared borrows, and retags of
shared references).

A reference in `v` is checked when all of the following hold:
- `curGen == otherGen`: its referent's storage generation is still current, so
  it is not already dangling.
- `otherLoc.index == resolved.targetLoc.index && pathsOverlap otherPath
  resolved.fieldPath`: it points into a sub-place of the same local that
  overlaps the accessed sub-place. Stacked Borrows keeps a separate stack per
  location, so references to disjoint sub-places never affect each other.
- `refDepthConflicts resolved needMut otherMut otherDepth`: the access would
  remove or disable the reference's item in Stacked Borrows.
  `refDepthConflicts` documents the upstream contract and how reborrow depths
  encode it. -/
def hasConflictingRefInVal (localGens : List Nat)
    (resolved : ResolvedPlace) (needMut : Bool) (v : MirVal) : Bool :=
  MirVal.fold
    false
    (fun _ => false)
    (fun _ => false)
    false
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead || ihTail)
    (fun otherMut otherGen otherLoc otherPath otherDepth =>
      match lookupAt localGens otherLoc.index with
      | some curGen =>
        curGen == otherGen &&
        otherLoc.index == resolved.targetLoc.index &&
        pathsOverlap otherPath resolved.fieldPath &&
        refDepthConflicts resolved needMut otherMut otherDepth
      | none => false)
    v

/-- True iff `st.locals` (outside `resolved.sourceRefSlot`) contains any live
reference that conflicts with accessing `resolved`. -/
def hasConflictingActiveBorrow (st : MirState)
    (resolved : ResolvedPlace) (needMut : Bool) : Bool :=
  let checkFn :=
    st.locals.foldr
      (fun slotOpt ih idx =>
        let notSameSlot :=
          match resolved.sourceRefSlot with
          | some rIdx => idx != rIdx
          | none => true
        let conflictHere :=
          if !notSameSlot then
            false
          else
            match slotOpt with
            | some v =>
              hasConflictingRefInVal st.localGens resolved needMut v
            | none => false
        conflictHere || ih (idx + 1))
      (fun _ => false)
  checkFn 0

/-- Retire (invalidate) any reference inside `v` that an access to `resolved`
must retire (`refDepthConflicts`; `needMut` as in `hasConflictingRefInVal`) by
redirecting its target `LocalId` to `⟨deadLocIdx⟩` (`deadLocIdx =
localGens.length`), where `lookupAt localGens deadLocIdx = none`. A retired
reference models a Stacked Borrows item that the access removed or disabled:
any later dereference, copy, move, or return of it fails
`MirVal.isValidInState` or `resolvePlace` and faults, while code that never
uses it again (as non-lexical lifetimes allow) still succeeds.

The rewrite changes the stored value, which Stacked Borrows does not do: it
removes or disables the reference's item in the borrow stack and leaves the
reference's bytes in memory unchanged. A retired reference in a caller slot
therefore does not name the place that the caller's pointer points to; see
`MirReturn` for what a terminal state records faithfully. -/
def invalidateConflictingRefsInVal (resolved : ResolvedPlace)
    (needMut : Bool) (deadLocIdx : Nat) (v : MirVal) : MirVal :=
  MirVal.fold
    .uninit
    (fun n => .int n)
    (fun b => .bool b)
    .unit
    (fun id _ ihInner => .adt id ihInner)
    (fun _ _ ihHead ihTail => .fieldCons ihHead ihTail)
    (fun otherMut otherGen otherLoc otherPath otherDepth =>
      if otherLoc.index == resolved.targetLoc.index &&
         pathsOverlap otherPath resolved.fieldPath &&
         refDepthConflicts resolved needMut otherMut otherDepth then
        .ref otherMut 0 ⟨deadLocIdx⟩ otherPath otherDepth
      else
        .ref otherMut otherGen otherLoc otherPath otherDepth)
    v

/-- Retire all references stored in `st.locals` (outside
`resolved.sourceRefSlot`) that an access to `resolved` must retire
(`invalidateConflictingRefsInVal`), returning `st.locals` unchanged when no
such reference is present so symbolic `MirState.locals` spines never
accumulate unforced map thunks. -/
def invalidateConflictingRefs (st : MirState)
    (resolved : ResolvedPlace) (needMut : Bool) : List (Option MirVal) :=
  if !hasConflictingActiveBorrow st resolved needMut then
    st.locals
  else
    let deadLocIdx := st.localGens.length
    let stepFn :=
      st.locals.foldr
        (fun slotOpt ih idx =>
          let notSameSlot :=
            match resolved.sourceRefSlot with
            | some rIdx => idx != rIdx
            | none => true
          let slotOpt' :=
            if !notSameSlot then
              slotOpt
            else
              match slotOpt with
              | some v =>
                some (invalidateConflictingRefsInVal resolved needMut
                  deadLocIdx v)
              | none => none
          slotOpt' :: ih (idx + 1))
        (fun _ => [])
    stepFn 0

/-- An entry reference collected by `collectEntryRefsInVal`:
`((holderSlot, holderPath), (isMut, behindShared), targetLoc, fieldPath,
reborrowDepth)`. The reference value is stored at sub-place `holderPath` of
slot `holderSlot` and points to sub-place `fieldPath` of slot `targetLoc`.
`isMut` is its mutability, `behindShared` records that it was reached through
a shared reference, and `reborrowDepth` is the reborrow depth stored in the
reference (`refDepthConflicts`). -/
abbrev EntryRef : Type :=
  (Nat × List Nat) × (Bool × Bool) × LocalId × List Nat × Nat

/-- Recursively collect all references (`EntryRef`) reachable from entry
argument `v` residing at `(holderSlot, holderPath)` (including references
nested inside `.adt` and `.fieldCons` aggregates or behind dereferenced
pointee values), returning `none` if `v` is `.uninit`, if any reference inside
`v` points to an in-frame local `targetLoc.index < localCount`, or if any
reference is dangling (its target slot is absent from `localGens`, has a
mismatched storage generation, or does not resolve at `fieldPath` in `locals`
to a valid, initialized pointee value conforming to its declared type)
(`src/behavior-considered-undefined.md#L147`):
> "A reference or [`Box<T>`] must be aligned and non-null, it cannot be
> [dangling], and it must point to a valid value (in case of dynamically sized
> types, using the actual dynamic type of the pointee as determined by the
> [metadata])."

Every caller-owned slot that an entry reference targets must have a declared
type in `localTys` (an entry at index `≥ localCount`), and that type is
authoritative. Each reference must have a declared reference type (`curTyOpt`,
from the argument's declared type or the enclosing pointee type) whose
mutability matches the reference and whose pointee type equals the slot's
type projected through `fieldPath`, and the pointee value must conform to that
type. Two references to the same sub-place, such as `&u8` and `&u16`
arguments that both point to one caller slot, therefore cannot both be
accepted.

Each collected reference records the physical memory place `(holderSlot,
holderPath)` that holds that `.ref` value so that reaching the same physical
reference in memory through multiple shared references (for example, `f(&r, &r)`
where `r: &mut T` resides in a single caller slot) is recognized as the same
reference rather than two aliasing references, whereas two distinct mutable
references in memory (such as `(&mut x, &mut x)` behind `&t`) have distinct
holder places and conflict.

A `&mut` reached through a shared reference is marked `behindShared`, and
`conflictsWithAnyEntryRef` lets it overlap a shared reference that is deeper
than it. For example, `let r = &mut x; f(&r, &*r)` passes `a: &&mut u8` and
`b: &u8`, which borrowck accepts and Stacked Borrows allows (`b`'s
`SharedReadOnly` item sits above `r`'s `Unique` item, and reads through `r`
keep it). Treating `**a` as a plain mutable reference would make it conflict
with `b` and reject this valid entry. This is sound because the callee cannot
write or mutably reborrow through a `&mut` that it reaches only through a
`&`. A place has at most one dereference, so every such access dereferences a
local of shared reference type or a dereference temporary copied from behind
one, which `frozenDerefTemps` marks frozen (`placeThroughShared`).
`stmtDerefTempsOk` rejects writes, moves, and mutable borrows through such
places, and copies out of them of any type with a unique reference
(`MirTy.hasUniqueRef`), so the `&mut` itself cannot be extracted either.

The shared reference must have a greater reborrow depth than the `&mut`, as
`b = &*r` does. Under the aliasing outline quoted at `refDepthConflicts`
(`src/behavior-considered-undefined.md#L24-L27`), a `&mut T` "must point to
memory that is not read or written by any pointer not derived from the
reference", and borrowck does not let a `&mut` be live together with another
borrow of an overlapping place, except a reborrow through that `&mut`. So in
a call that borrowck accepts, each shared reference that overlaps the `&mut`
was derived from it and is deeper. Stacked Borrows then keeps both references
on reads, because the shared reference's item lies above the `&mut`'s
`Unique` item, and so does `refDepthConflicts`, because a read through a
reference retires only deeper mutable references. A shared reference whose
depth is not greater therefore describes no valid call, and rejecting it
loses no valid entry. Accepting one with a smaller depth would let a read
through it retire the `&mut`, which Stacked Borrows keeps; retiring rewrites
the `&mut` stored in the caller's slot (`invalidateConflictingRefsInVal`), and
the terminal state would expose that change (`MirReturn`).

Two distinct mutable references to overlapping places still conflict even when
both are behind shared references, as in `(&mut x, &mut x)` above. Both can be
live only if one was reborrowed from the other, and then a read through the
parent disables the child's `Unique` item. Entry validation does not check
that the reborrow depths of two such references identify the parent, so
accepting both would let the callee read through each without the fault
Stacked Borrows requires. Borrowck already rejects such a call, because it
forbids using a `&mut` while a reborrow of it is live, so rejecting it loses
no valid entry. A mutable reference that is not behind a shared reference
conflicts with every overlapping entry reference. -/
def collectEntryRefsInVal (localCount ptrWidthBits : Nat)
    (localTys : List MirTy) (locals : List (Option MirVal))
    (localGens : List Nat) (argTyOpt : Option MirTy) (v : MirVal)
    (holderSlot : Nat := 0) (holderPath : List Nat := []) :
    Option (List EntryRef) :=
  @Nat.recCompiled
    (fun _ =>
      Option MirTy → Nat → List Nat → Nat → MirVal →
        Option (List EntryRef))
    (fun _ _ _ _ v0 =>
      MirVal.fold
        none
        (fun _ => some [])
        (fun _ => some [])
        (some [])
        (fun _ _ ihInner => ihInner)
        (fun _ _ ihHead ihTail =>
          match ihHead, ihTail with
          | some r1, some r2 => some (r1 ++ r2)
          | _, _ => none)
        (fun _ _ _ _ _ => none)
        v0)
    (fun _ ihFuel curTyOpt0 hSlot0 hPath0 fIdx0 v0 =>
      @MirVal.fold
        (Option MirTy → Nat → List Nat → Nat →
          Option (List EntryRef))
        (fun _ _ _ _ => none)
        (fun _ _ _ _ _ => some [])
        (fun _ _ _ _ _ => some [])
        (fun _ _ _ _ => some [])
        (fun _ _ ihInner curTyOpt hSlot hPath fIdx =>
          match curTyOpt with
          | some ⟨_, .adt _ fieldTys⟩ =>
            ihInner (some ⟨_, .tuple fieldTys⟩) hSlot hPath fIdx
          | _ => ihInner none hSlot hPath fIdx)
        (fun _ _ ihHead ihTail curTyOpt hSlot hPath fIdx =>
          let headTyOpt : Option MirTy :=
            match curTyOpt with
            | some ⟨_, .tuple (.cons elemTy _)⟩ => some ⟨_, elemTy⟩
            | _ => none
          let tailTyOpt : Option MirTy :=
            match curTyOpt with
            | some ⟨_, .tuple (.cons _ restTys)⟩ =>
              some ⟨_, .tuple restTys⟩
            | _ => none
          match ihHead headTyOpt hSlot (hPath ++ [fIdx]) 0,
                ihTail tailTyOpt hSlot hPath (fIdx + 1) with
          | some r1, some r2 => some (r1 ++ r2)
          | _, _ => none)
        (fun isMut refGen targetLoc fieldPath depth curTyOpt hSlot hPath fIdx =>
          if decide (targetLoc.index < localCount) then
            none
          else
            match lookupAt localGens targetLoc.index,
                  lookupAt locals targetLoc.index with
            | some curGen, some (some rootVal) =>
              if curGen != refGen then
                none
              else
                match readFieldPath fieldPath rootVal with
                | some pointeeVal =>
                  if !pointeeVal.isValidInState localGens then
                    none
                  else
                    -- The target slot's declared type is authoritative: the
                    -- reference's pointee type must equal it at `fieldPath`.
                    let expectedPointeeTyOpt : Option MirTy :=
                      match lookupAt localTys targetLoc.index with
                      | some rootTy =>
                        match projectFieldPathTy fieldPath rootTy, curTyOpt with
                        | some slotTy, some ⟨_, .ref innerTy⟩ =>
                          if !isMut && MirTy.beq ⟨_, innerTy⟩ slotTy then
                            some slotTy
                          else
                            none
                        | some slotTy, some ⟨_, .refMut innerTy⟩ =>
                          if isMut && MirTy.beq ⟨_, innerTy⟩ slotTy then
                            some slotTy
                          else
                            none
                        | _, _ => none
                      | none => none
                    let tyOk : Bool :=
                      match expectedPointeeTyOpt with
                      | some pTy =>
                        checkValMatchesTy ptrWidthBits pTy pointeeVal false
                          localTys locals
                      | none => false
                    let curHolderPath :=
                      if fIdx == 0 then hPath else hPath ++ [fIdx]
                    match ihFuel expectedPointeeTyOpt targetLoc.index fieldPath
                        0 pointeeVal with
                    | some nestedRefs =>
                      -- A reference reached through a shared reference is
                      -- recorded as shared (see the docstring).
                      let nestedRefs' :=
                        if isMut then nestedRefs
                        else
                          nestedRefs.map (fun r =>
                            match r with
                            | (holder, (m, _), loc, path, d) =>
                              (holder, (m, true), loc, path, d))
                      match tyOk with
                      | true =>
                        some
                          (((hSlot, curHolderPath), (isMut, false), targetLoc,
                            fieldPath, depth) :: nestedRefs')
                      | false => none
                    | none => none
                | none => none
            | _, _ => none)
        v0 curTyOpt0 hSlot0 hPath0 fIdx0)
    -- Each hop through a reference strips one `.ref`/`.refMut` layer from the
    -- expected type, so the type's fuel bounds the number of hops even when a
    -- chain revisits one slot at different field paths.
    ((match argTyOpt with
      | some argTy => argTy.fuel
      | none => 0) + locals.length + 1)
    argTyOpt
    holderSlot
    holderPath
    0
    v

/-- True iff `((holderSlot, holderPath), (isMut, behindShared), targetLoc,
fieldPath, depth)` conflicts with any entry reference at a distinct holder
place in `seen`: the two references point to overlapping sub-places of the
same referent slot, and either both are mutable, one of them is a mutable
reference that is not behind a shared reference, or one of them is a mutable
reference and the other is a shared reference whose reborrow depth is not
greater than the mutable one's (`collectEntryRefsInVal`). -/
def conflictsWithAnyEntryRef (holderSlot : Nat) (holderPath : List Nat)
    (isMut behindShared : Bool) (targetLoc : LocalId) (fieldPath : List Nat)
    (depth : Nat) (seen : List EntryRef) : Bool :=
  seen.foldr
    (fun item ih =>
      match item with
      | ((otherHSlot, otherHPath), (otherMut, otherBehindShared), otherLoc,
          otherPath, otherDepth) =>
        let sameHolder :=
          otherHSlot == holderSlot && pathEq otherHPath holderPath
        let mutConflict :=
          (isMut && otherMut) || (isMut && !behindShared) ||
            (otherMut && !otherBehindShared)
        -- A shared reference may overlap a `&mut` only if it is deeper, as a
        -- reborrow of the `&mut` is (see `collectEntryRefsInVal`).
        let depthConflict :=
          (isMut && !otherMut && decide (otherDepth ≤ depth)) ||
            (otherMut && !isMut && decide (depth ≤ otherDepth))
        if !sameHolder &&
           otherLoc.index == targetLoc.index &&
           pathsOverlap otherPath fieldPath &&
           (mutConflict || depthConflict) then
          true
        else
          ih)
    false

/-- True iff no two references in `refs` at distinct holder places conflict
(`conflictsWithAnyEntryRef`): two references to overlapping sub-places of the
same referent slot conflict unless both are shared, or one is a `&mut` behind
a shared reference and the other is a deeper shared reference. -/
def entryRefListExclusive
    (refs : List EntryRef) : Bool :=
  match
    refs.foldr
      (fun item
          (acc : Bool × List EntryRef) =>
        match item, acc with
        | ((hSlot, hPath), (isMut, behind), loc, path, depth), (ok, seen) =>
          (ok &&
             !conflictsWithAnyEntryRef hSlot hPath isMut behind loc path depth
               seen,
           ((hSlot, hPath), (isMut, behind), loc, path, depth) :: seen))
      (true, [])
  with
  | (ok, _) => ok

/-- True iff every argument local in `1 .. body.argCount` is allocated (`some
(some v)`), initialized and valid in `st.localGens`, conforms to its declared
type in `body.localTys`, and every reference reachable from `v` (including
references nested inside `.adt` or tuple `.fieldCons` arguments or behind
dereferenced pointees) resolves to a live, initialized, well-typed referent in
`st.locals` without conflicting with another distinct entry reference
(`entryRefListExclusive`: aliasing with a mutable side is allowed only for a
`&mut` behind a shared reference and a deeper shared reference)
(`src/behavior-considered-undefined.md#L24-L27`,
`src/behavior-considered-undefined.md#L114-L132`). Slots other than the
arguments are validated separately (`entryFrameSlotsCanonical`). -/
def entryArgsExclusive (body : MirBody) (st : MirState) : Bool :=
  let collectedOpt :
      Option (List EntryRef) :=
    @Nat.recCompiled
      (fun _ => Option (List EntryRef))
      (some [])
      (fun k ih =>
        match ih with
        | none => none
        | some prevRefs =>
          let slotIdx := k + 1
          match lookupAt st.locals slotIdx with
          | some (some v) =>
            match v.isValidInState st.localGens &&
                  checkLocalStoreTy body.ptrWidthBits body.localTys slotIdx
                    v false st.locals with
            | false => none
            | true =>
              let argTyOpt := lookupAt body.localTys slotIdx
              match collectEntryRefsInVal body.localCount body.ptrWidthBits
                  body.localTys st.locals st.localGens argTyOpt v slotIdx []
              with
              | some slotRefs => some (prevRefs ++ slotRefs)
              | none => none
          | _ => none)
      body.argCount
  match collectedOpt with
  | some allRefs => entryRefListExclusive allRefs
  | none => false

/-- Every statement of `body`, in block order. -/
def bodyStmts (body : MirBody) : List Stmt :=
  body.blocks.foldr (fun bb acc => bb.stmts ++ acc) []

/-- True iff some statement of `body` is `StorageLive` or `StorageDead` of local
`k`. -/
def hasStorageStmt (body : MirBody) (k : Nat) : Bool :=
  (bodyStmts body).foldr
    (fun stmt acc =>
      match stmt with
      | .storageLive loc | .storageDead loc => loc.index == k || acc
      | _ => acc)
    false

/-- True iff every in-frame slot of `st` other than the arguments holds its
canonical function-entry state: `body.argCount < body.localCount`, the return
place `_0` is allocated and uninitialized (`some (some .uninit)`), and every
user variable or temporary `_k` with `body.argCount < k < body.localCount` is
dead (`some none`) if the body has a `StorageLive` or `StorageDead` statement
for it (`hasStorageStmt`) and allocated and uninitialized (`some (some
.uninit)`) otherwise. The pinned reference interpreter starts every frame local
dead and then makes the return place and every local without `StorageLive` or
`StorageDead` statements live and uninitialized
(`compiler/rustc_const_eval/src/interpret/stack.rs#L386-L387`,
`compiler/rustc_const_eval/src/interpret/stack.rs#L477-L487`,
`compiler/rustc_const_eval/src/interpret/stack.rs#L582-L586`,
`compiler/rustc_const_eval/src/interpret/stack.rs#L562-L573`):
> "let dead_local = LocalState { value: LocalValue::Dead, layout:
> Cell::new(None) };
> let locals = IndexVec::from_elem(dead_local, &body.local_decls);"
> "// Mark all locals as live that are not arguments and don't have `Storage*`
> annotations
> // (this includes the return place, but not the arguments).
> self.storage_live(mir::RETURN_PLACE)?;"
> "/// Mark a storage as live, killing the previous content."
> "// Just make this an efficient immediate. ...
> Operand::Immediate(Immediate::Uninit)"

The set of locals without `Storage*` statements is computed as in
`always_storage_live_locals`
(`compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs#L12-L27`):
> "/// The set of locals in a MIR body that do not have
> `StorageLive`/`StorageDead` annotations."

Neither state holds a value, so no non-argument local can carry a reference
that aliases an argument. -/
def entryFrameSlotsCanonical (body : MirBody) (st : MirState) : Bool :=
  decide (body.argCount < body.localCount) &&
    @Nat.recCompiled (fun _ => Bool)
      true
      (fun k ih =>
        let slotOk : Bool :=
          if k == 0 then
            match lookupAt st.locals 0 with
            | some (some ⟨_, .uninit⟩) => true
            | _ => false
          else if decide (k ≤ body.argCount) then
            true
          else if hasStorageStmt body k then
            match lookupAt st.locals k with
            | some none => true
            | _ => false
          else
            match lookupAt st.locals k with
            | some (some ⟨_, .uninit⟩) => true
            | _ => false
        ih && slotOk)
      body.localCount

/-- Declared type of place `p` in `body`: the declared type of local `p.loc`
projected through `p.projection` (`projectPlaceTy`), or `none` if `p.loc` is
not an in-frame local (`< body.localCount`), has no declared type, or the
projection does not apply to its type. This follows `Place::ty_from`
(`compiler/rustc_middle/src/mir/statement.rs#L461`):
> "PlaceTy::from_ty(local_decls.local_decls()[local].ty)
> .multi_projection_ty(tcx, projection)"
Entries of `localTys` at `localCount` and beyond type caller-owned slots,
which no place may name. -/
def placeDeclTy (body : MirBody) (p : Place) : Option MirTy :=
  if !decide (p.loc.index < body.localCount) then none else
  match lookupAt body.localTys p.loc.index with
  | some baseTy => projectPlaceTy p.projection baseTy
  | none => none

/-- Declared type of a `Copy` or `Move` operand (`placeDeclTy`). A constant
operand has no type in this AST, so its type is `none`; `rvalueTysOk` instead
checks the constant's value against the type its use requires. -/
def operandDeclTy (body : MirBody) : Operand → Option MirTy
  | .copy p | .move p => placeDeclTy body p
  | .constVal _ => none

/-- True iff `x` occurs in `xs`. -/
def natListMem (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => y == x || acc) false

/-- True iff the elements of `xs` are pairwise distinct. -/
def natListDistinct (xs : List Nat) : Bool :=
  match
    xs.foldr
      (fun x (acc : Bool × List Nat) =>
        match acc with
        | (ok, seen) => (ok && !natListMem x seen, x :: seen))
      (true, [])
  with
  | (ok, _) => ok

/-- Bit width that a `SwitchInt` value must fit for discriminant `discr`: `1`
for a `bool` place, the integer width (`tyBitWidth`) for an unsigned integer
place, and `none` otherwise. A constant discriminant has no declared type in
this AST, so it is unsupported. -/
def switchDiscrBits (body : MirBody) (discr : Operand) : Option Nat :=
  match operandDeclTy body discr with
  | some ⟨_, .bool⟩ => some 1
  | some discrTy => tyBitWidth body.ptrWidthBits discrTy
  | none => none

/-- True iff terminator `term` satisfies the control-flow invariants that the
pinned MIR validator enforces: every edge targets an existing block other
than the start block `bb0`, the values of a `SwitchInt` are pairwise
distinct, and each value fits the discriminant's type
(`compiler/rustc_mir_transform/src/validate.rs#L140-L144`,
`compiler/rustc_mir_transform/src/validate.rs#L164-L166`,
`compiler/rustc_mir_transform/src/validate.rs#L346-L363`,
`compiler/rustc_mir_transform/src/validate.rs#L1586-L1606`):
> "fn check_edge(&mut self, location: Location, bb: BasicBlock, edge_kind:
> EdgeKind) {
> if bb == START_BLOCK {
> self.fail(location, "start block must not have predecessors")
> }
> if let Some(bb) = self.body.basic_blocks.get(bb) {"
> "} else {
> self.fail(location, format!("encountered jump to invalid basic block
> {bb:?}"))"
> "let has_duplicates = targets.iter().len() != self.value_cache.len();
> if has_duplicates {"
> "let size = Size::from_bits(match switch_ty.kind() {
> ty::Uint(uint) => uint.normalize(target_width).bit_width().unwrap(),
> ...
> ty::Bool => 1,"
> "if ScalarInt::try_from_uint(value, size).is_none() {
> self.fail(
> location,
> format!("the value {value:#x} is not a proper {switch_ty}"),"

The discriminant must be a place whose declared type is an unsigned integer
or `bool` (`switchDiscrBits`). Distinct values make `findSwitchTarget`'s
first-match lookup the unique match. -/
def terminatorCfgValid (body : MirBody) (term : Terminator) : Bool :=
  let edgeOk : BlockId → Bool := fun target =>
    target.index != 0 && decide (target.index < body.blocks.length)
  match term with
  | .return_ | .unreachable => true
  | .goto target => edgeOk target
  | .switchInt discr targets =>
    match switchDiscrBits body discr with
    | none => false
    | some bits =>
      edgeOk targets.otherwise &&
        targets.branches.foldr
          (fun br acc =>
            edgeOk br.target && decide (br.val < natPow2 bits) && acc)
          true &&
        natListDistinct (targets.branches.map (fun br => br.val))

/-- True iff `body` has a start block and every terminator of `body`
satisfies `terminatorCfgValid`. Since no edge targets `bb0`, a state at
`(block, stmtIdx) = (0, 0)` can arise only at function entry.

Admission checks only this structure, the declared types, and the static
statement disciplines (`bodyAdmissible`). Whether a statement is well typed
(`rvalueTysOk`) is checked when it executes, so a body whose only ill-typed
statement lies in a block that is never reached is admitted, although the
validator would reject it. The semantics still never executes an ill-typed
statement: executing one faults. -/
def bodyCfgValid (body : MirBody) : Bool :=
  !body.blocks.isEmpty &&
    body.blocks.foldr
      (fun bb acc => terminatorCfgValid body bb.terminator && acc) true

/-- True iff `t` contains a mutable reference type that is not behind a shared
reference type (`&mut T`, or a struct or tuple with such a field). A value of
such a type is not `Copy`, and copying it would duplicate a unique reference
(`src/types/pointer.md#L34`, `src/special-types-and-traits.md#L89`):
> "A mutable reference (that hasn't been borrowed) is the only way to access
> the value it points to, so is not `Copy`."
> "`Copy` can only be implemented for types which do not implement `Drop`, and
> whose fields are all `Copy`."
A `&mut` behind a shared reference does not count: copying the shared
reference copies only the pointer (`src/types/pointer.md#L25`):
> "Copying a reference is a "shallow" operation: it involves only copying
> the pointer itself, that is, pointers are `Copy`." -/
def MirTy.hasUniqueRef (t : MirTy) : Bool :=
  @Nat.recCompiled (fun _ => MirTy → Bool)
    (fun _ => false)
    (fun _ ih a =>
      match a with
      | ⟨_, .refMut _⟩ => true
      | ⟨_, .adt _ fs⟩ => ih ⟨_, fs⟩
      | ⟨_, .tuple es⟩ => ih ⟨_, es⟩
      | ⟨_, .cons h r⟩ => ih ⟨_, h⟩ || ih ⟨_, r⟩
      | _ => false)
    t.fuel t

/-- The locals that `body` assigns with a non-retagging copy (`Rvalue.use _
.no`); `bodyDerefTempsValid` requires each to be a dereference temporary. -/
def derefTemps (body : MirBody) : List Nat :=
  (bodyStmts body).foldr
    (fun stmt acc =>
      match stmt with
      | .assign dst (.use _ .no) => dst.loc.index :: acc
      | _ => acc)
    []

/-- True iff `p` mentions no local in `temps` except as the base of a leading
dereference (`(*t)...`). -/
def placeUsesTempsAsDerefBase (temps : List Nat) (p : Place) : Bool :=
  !natListMem p.loc.index temps ||
    match p.projection with
    | .deref :: _ => true
    | _ => false

/-- True iff operand `op` mentions locals in `temps` only as dereference
bases. -/
def operandUsesTempsAsDerefBase (temps : List Nat) (op : Operand) : Bool :=
  match op with
  | .copy p | .move p => placeUsesTempsAsDerefBase temps p
  | .constVal _ => true

/-- True iff `p` is reached through a shared reference: it dereferences a
local whose declared type is `&T`, or a dereference temporary in `frozen`
whose value was copied out from behind a shared reference. -/
def placeThroughShared (body : MirBody) (frozen : List Nat) (p : Place) :
    Bool :=
  match p.projection with
  | .deref :: _ =>
    natListMem p.loc.index frozen ||
      match lookupAt body.localTys p.loc.index with
      | some ⟨_, .ref _⟩ => true
      | _ => false
  | _ => false

/-- The dereference temporaries of `body` whose value is copied from a place
reached through a shared reference (`placeThroughShared`), computed as a
fixpoint because a temporary can copy out of another temporary. The bytes
behind such a reference stay immutable even when the copied reference is
`&mut`. -/
def frozenDerefTemps (body : MirBody) : List Nat :=
  @Nat.recCompiled (fun _ => List Nat)
    []
    (fun _ frozen =>
      (bodyStmts body).foldr
        (fun stmt acc =>
          match stmt with
          | .assign dst (.use (.copy src) .no) =>
            if placeThroughShared body frozen src &&
                !natListMem dst.loc.index acc then
              dst.loc.index :: acc
            else
              acc
          | _ => acc)
        frozen)
    (body.localCount + 1)

/-- True iff statement `stmt` respects the dereference-temporary discipline of
`body` (`temps = derefTemps body`, `frozen = frozenDerefTemps body`). -/
def stmtDerefTempsOk (body : MirBody) (temps frozen : List Nat)
    (stmt : Stmt) : Bool :=
  match stmt with
  | .assign dst rv =>
    match rv with
    | .use op .no =>
      -- A definition `t = copy p` of a dereference temporary `t`.
      match op with
      | .copy src =>
        (match dst.projection with
         | [] => true
         | _ :: _ => false) &&
        decide (body.argCount < dst.loc.index) &&
        decide (dst.loc.index < body.localCount) &&
        (match lookupAt body.localTys dst.loc.index with
         | some ⟨_, .ref _⟩ | some ⟨_, .refMut _⟩ => true
         | _ => false) &&
        placeUsesTempsAsDerefBase temps src
      | _ => false
    | _ =>
      let dstOk :=
        placeUsesTempsAsDerefBase temps dst &&
          !placeThroughShared body frozen dst
      let rvOk :=
        match rv with
        | .use op _ =>
          operandUsesTempsAsDerefBase temps op &&
            match op with
            | .copy src =>
              !(placeThroughShared body frozen src &&
                match placeDeclTy body src with
                | some srcTy => srcTy.hasUniqueRef
                | none => true)
            | .move src => !placeThroughShared body frozen src
            | .constVal _ => true
        | .ref src => placeUsesTempsAsDerefBase temps src
        | .refMut src =>
          placeUsesTempsAsDerefBase temps src &&
            !placeThroughShared body frozen src
        | .binaryOp _ lhs rhs =>
          operandUsesTempsAsDerefBase temps lhs &&
            operandUsesTempsAsDerefBase temps rhs
        | .unaryOp _ src => operandUsesTempsAsDerefBase temps src
      dstOk && rvOk
  | .placeMention src => placeUsesTempsAsDerefBase temps src
  | .storageLive _ | .storageDead _ | .nop => true

/-- True iff every non-retagging copy (`Rvalue.use _ .no`) in `body` defines a
dereference temporary and every such temporary is used only as the base of a
dereference, and no unique reference escapes from behind a shared reference.

In runtime MIR, `WithRetag::No` copies come from the dereference temporaries
that `Derefer` inserts as `CopyForDeref` and that `EraseDerefTemps` lowers
during runtime lowering
(`compiler/rustc_mir_transform/src/erase_deref_temps.rs#L19-L24`,
`compiler/rustc_mir_transform/src/lib.rs#L662`):
> "if let &mut Rvalue::CopyForDeref(place) = rvalue {
> // We do *NOT* want a retag here! This assignment might copy a mutable
> reference we
> // can't actually copy, we just need it temporarily to create another
> pointer.
> *rvalue = Rvalue::Use(Operand::Copy(place), WithRetag::No)"

Before that lowering, such a temporary has a dereferenceable type and "may
only be written to by a `CopyForDeref` and otherwise only accessed through a
deref" (`compiler/rustc_middle/src/mir/mod.rs#L1096-L1099`,
`compiler/rustc_mir_transform/src/validate.rs#L1660-L1664`), and the validator
checks that discipline on `DerefTemp` locals
(`compiler/rustc_mir_transform/src/validate.rs#L967-L979`):
> "/// It may only be written to by a `CopyForDeref` and otherwise only
> accessed through a deref."
> "format!("`DerefTemp` locals must only be dereferenced or directly assigned
> to"),"

`EraseDerefTemps` then marks the temporaries as ordinary locals
(`compiler/rustc_mir_transform/src/erase_deref_temps.rs#L27-L31`), so the
validator no longer checks them in `Runtime(PostCleanup)` MIR; the discipline
holds there because `Derefer` constructs it and the copies are never
retagged. This check restores it as an explicit precondition.

Correspondence (`stmtDerefTempsOk`):
- A definition `t = use (copy p) .no` must assign a bare temporary `t`
  (`argCount < t < localCount`) of reference type.
- Every other mention of a temporary must be the base of a leading
  dereference, in statements and in `SwitchInt` discriminants.
- The bytes behind a shared reference are immutable, transitively through
  other references (`src/behavior-considered-undefined.md#L39-L41`):
  > "Moreover, the bytes [pointed to] by a shared reference, including
  > transitively through other references (both shared and mutable) and
  > `Box`es, are immutable"

  A temporary copied from behind a shared reference (`frozenDerefTemps`) may
  only be read through: writing through it, moving out of it, or taking a
  mutable borrow through it is rejected, as is copying a value of a type with
  a unique reference (`MirTy.hasUniqueRef`) out from behind any shared
  reference (for example, returning the `&mut u8` inside a `&&mut u8`). -/
def bodyDerefTempsValid (body : MirBody) : Bool :=
  let temps := derefTemps body
  let frozen := frozenDerefTemps body
  (bodyStmts body).foldr
    (fun stmt acc => stmtDerefTempsOk body temps frozen stmt && acc) true &&
  body.blocks.foldr
    (fun bb acc =>
      (match bb.terminator with
       | .switchInt discr _ => operandUsesTempsAsDerefBase temps discr
       | _ => true) && acc)
    true

/-- True iff `st` has one storage generation counter per slot
(`st.locals.length = st.localGens.length`) and a slot for every in-frame local
(`body.localCount ≤ st.locals.length`). `Stmt.storageLive` and
`Stmt.storageDead` update a local's counter, and reference validity compares
against it, so a slot without a counter would have no generation to check. -/
def entryStateShapeValid (body : MirBody) (st : MirState) : Bool :=
  st.locals.length == st.localGens.length &&
    decide (body.localCount ≤ st.locals.length)

/-- True iff projection elements `a` and `b` are equal. -/
def placeElemEq (a b : PlaceElem) : Bool :=
  match a, b with
  | .deref, .deref => true
  | .field i, .field j => i == j
  | _, _ => false

/-- True iff places `a` and `b` are syntactically equal. -/
def placeEq (a b : Place) : Bool :=
  a.loc.index == b.loc.index &&
    (a.projection.foldr
      (fun x ih bs =>
        match bs with
        | y :: ys => placeElemEq x y && ih ys
        | [] => false)
      (fun bs => bs.isEmpty)) b.projection

/-- True iff `p` dereferences a pointer (`Place::is_indirect`). -/
def placeIsIndirect (p : Place) : Bool :=
  p.projection.foldr
    (fun e acc =>
      (match e with
       | .deref => true
       | .field _ => false) || acc)
    false

/-- True iff reading `src` while assigning to `dst` violates MIR's
non-overlap requirement, exactly as the pinned MIR lint decides it
(`compiler/rustc_mir_transform/src/lint.rs#L71-L72`):
> "fn places_conflict_for_assignment<'tcx>(dest: Place<'tcx>, src:
> Place<'tcx>) -> bool {
> dest == src || (dest.local == src.local && !dest.is_indirect() &&
> !src.is_indirect())" -/
def placesConflictForAssignment (dst src : Place) : Bool :=
  placeEq dst src ||
    (dst.loc.index == src.loc.index && !placeIsIndirect dst &&
      !placeIsIndirect src)

/-- True iff no `Use` assignment of `body` reads a place that conflicts with
its destination (`placesConflictForAssignment`). The pinned MIR lint applies
this check to `Use` rvalues (and to rvalues this subset omits), not to
`BinaryOp`, `UnaryOp`, or `Ref` (`compiler/rustc_mir_transform/src/lint.rs#L88`,
`compiler/rustc_mir_transform/src/lint.rs#L103`):
> "let forbid_aliasing = match rvalue {"
> "// The sides of an assignment must not alias." -/
def bodyUseAssignsDisjoint (body : MirBody) : Bool :=
  (bodyStmts body).foldr
    (fun stmt acc =>
      (match stmt with
       | .assign dst (.use (.copy src) _) | .assign dst (.use (.move src) _) =>
         !placesConflictForAssignment dst src
       | _ => true) && acc)
    true

/-- True iff `body` is admissible as `Runtime(PostCleanup)` MIR of this
subset, independently of any state: every declared type is a Rust type
(`bodyTysSupported`), the control-flow graph satisfies the validator's edge and
`SwitchInt` invariants (`bodyCfgValid`), and non-retagging copies follow the
dereference-temporary discipline (`bodyDerefTempsValid`), and no `Use`
assignment reads a place that statically conflicts with its destination
(`bodyUseAssignsDisjoint`). -/
def bodyAdmissible (body : MirBody) : Bool :=
  bodyTysSupported body && bodyCfgValid body && bodyDerefTempsValid body &&
    bodyUseAssignsDisjoint body

/-- True iff `st` is a valid function-entry state for the admissible body
`body` (the caller's side of the call): the state has a slot and a generation
counter for every local (`entryStateShapeValid`), every non-argument frame
slot holds its canonical entry state (`entryFrameSlotsCanonical`), and the
arguments are valid and free of conflicting aliases (`entryArgsExclusive`).
-/
def entryStateValid (body : MirBody) (st : MirState) : Bool :=
  entryStateShapeValid body st && entryFrameSlotsCanonical body st &&
    entryArgsExclusive body st

/-- Resolve `place` in state `st` for a function body with `localCount`
in-frame locals (`compiler/rustc_middle/src/mir/syntax.rs#L1092-L1167`,
`compiler/rustc_middle/src/mir/syntax.rs#L114-L115`,
`src/behavior-considered-undefined.md#L147`):
> "Furthermore, `Deref` projections must be the first projection within any
> place (if they appear at all)"
> "A reference or [`Box<T>`] must be aligned and non-null, it cannot be
> [dangling], and it must point to a valid value (in case of dynamically sized
> types, using the actual dynamic type of the pointee as determined by the
> [metadata])."

Every syntactic `Place` in a function body must name an in-frame local
`place.loc.index < localCount`; dereferencing an in-frame reference local may
resolve `targetLoc` to a caller-owned referent slot at index $\ge$ `localCount`.
-/
def resolvePlace (localCount : Nat) (st : MirState) (place : Place) :
    Option ResolvedPlace :=
  if !decide (place.loc.index < localCount) then
    none
  else
    match st with
    | ⟨locals, localGens, _, _⟩ =>
      match place.projection with
      | .deref :: rest =>
        match extractFieldPath rest with
        | some subPath =>
          match lookupAt locals place.loc.index with
          | some (some ⟨_, .ref mutable refGen targetLoc basePath depth⟩) =>
            match lookupAt localGens targetLoc.index with
            | some curGen =>
              if curGen == refGen then
                some ⟨targetLoc, basePath ++ subPath, some mutable,
                      some place.loc.index, depth⟩
              else
                none
            | none => none
          | _ => none
        | none => none
      | _ =>
        match extractFieldPath place.projection with
        | some fieldPath =>
          some ⟨place.loc, fieldPath, none, none, 0⟩
        | none => none

/-- True iff some statement of `body` borrows local `k` directly (`&_k` or
`&mut _k`, possibly through field projections, but not through a leading
dereference). References to an in-frame local can only be created by such a
borrow: entry references never point into the frame (`collectEntryRefsInVal`),
and retags only copy existing references. -/
def bodyBorrowsLocal (body : MirBody) (k : Nat) : Bool :=
  (bodyStmts body).foldr
    (fun stmt acc =>
      let direct : Place → Bool := fun src =>
        src.loc.index == k &&
          match src.projection with
          | .deref :: _ => false
          | _ => true
      match stmt with
      | .assign _ (.ref src) | .assign _ (.refMut src) => direct src || acc
      | _ => acc)
    false

/-- Perform the read of the reference local that a dereferencing place
`(*p)...` loads its pointer from, retiring the mutable references to `p` that
an owner read of `p` retires (`invalidateConflictingRefs` with an owner
access, `needMut = false`). Places without a leading dereference, places whose
base is not an in-frame local (which `resolvePlace` rejects), and bases that
`body` never borrows (`bodyBorrowsLocal`, so no reference to them can exist)
leave `st` unchanged.

The pinned interpreter evaluates a dereference by reading the pointer value
out of the base place
(`compiler/rustc_const_eval/src/interpret/place.rs#L468-L477`):
> "pub fn deref_pointer(
> ...
> let val = self.read_immediate(src)?;"
and in Miri a read of memory is a Stacked Borrows read access of the bytes
read (`src/tools/miri/src/machine.rs#L1705-L1707`):
> "if let Some(borrow_tracker) = &alloc_extra.borrow_tracker {
> borrow_tracker.before_memory_read(alloc_id, prov_extra, range, machine)?;
> }"
So after `_2 = &mut _1`, evaluating `*_1` reads `_1` and disables `_2`'s
`Unique` item, and a later use of `_2` is undefined behavior. -/
def readDerefBase (body : MirBody) (st : MirState) (place : Place) :
    MirState :=
  match place.projection with
  | .deref :: _ =>
    if decide (place.loc.index < body.localCount) &&
        bodyBorrowsLocal body place.loc.index then
      ⟨invalidateConflictingRefs st ⟨place.loc, [], none, none, 0⟩ false,
       st.localGens, st.block, st.stmtIdx⟩
    else
      st
  | _ => st

/-- Read a valid, initialized `MirVal` from `place` in state `st`, retiring any
conflicting deeper mutable borrows in the returned `MirState`. Fails (`none`) if
`place` does not resolve, if the read sub-value is uninitialized, or if the read
sub-value contains a dangling or retired reference. -/
def readPlace (body : MirBody) (st : MirState) (place : Place) :
    Option (MirVal × MirState) :=
  let st := readDerefBase body st place
  match st with
  | ⟨_, localGens, block, stmtIdx⟩ =>
    match resolvePlace body.localCount st place with
    | some resolved =>
      let locals' := invalidateConflictingRefs st resolved false
      match lookupAt locals' resolved.targetLoc.index with
      | some (some rootVal) =>
        match readFieldPath resolved.fieldPath rootVal with
        | some val =>
          if val.isValidInState localGens then
            some (val, ⟨locals', localGens, block, stmtIdx⟩)
          else
            none
        | none => none
      | _ => none
    | none => none

/-- Overwrite a moved-from `place` with `MirVal.uninit` in `st`, retiring the
borrows that a write to `place` retires (`invalidateConflictingRefs`)
(`compiler/rustc_middle/src/mir/syntax.rs#L1289-L1293`):
> "Creates a value by performing loading the place, just like the `Copy`
> operand.
>
> This *may* additionally overwrite the place with `uninit` bytes, depending
> on how we decide in [UCG#188]. You should not emit MIR that may attempt a
> subsequent second load of this place without first re-initializing it."

Fails (`none`) if `place` refers to a dead local slot or resolves through any
reference. Moving out of a place behind a reference is unsupported: the
upstream effect of `Move` is undecided, and choosing the `uninit` overwrite
for memory that the caller owns would leave a sub-place the caller lent
uninitialized when the call returns. Moves of in-frame places are
supported. -/
def deinitPlace (body : MirBody) (st : MirState)
    (place : Place) : Option MirState :=
  match st with
  | ⟨_, localGens, block, stmtIdx⟩ =>
    match resolvePlace body.localCount st place with
    | some resolved =>
      match resolved.viaMutRef with
      | some _ => none
      | none =>
        let locals1 := invalidateConflictingRefs st resolved true
        match lookupAt locals1 resolved.targetLoc.index with
        | some (some rootVal) =>
          match resolved.fieldPath with
          | [] =>
            match setAt locals1 resolved.targetLoc.index (some .uninit) with
            | some locals' =>
              some ⟨locals', localGens, block, stmtIdx⟩
            | none => none
          | _ =>
            match writeFieldPath resolved.fieldPath .uninit rootVal with
            | some rootVal' =>
              match setAt locals1 resolved.targetLoc.index
                  (some rootVal') with
              | some locals' =>
                some ⟨locals', localGens, block, stmtIdx⟩
              | none => none
            | none => none
        | _ => none
    | none => none

/-- Store a valid, initialized `newVal` into `place` in state `st`, retiring
any conflicting active borrows of `place` and returning the updated local slot
list (`StatementKind::Assign`,
`compiler/rustc_middle/src/mir/syntax.rs#L306-L307`,
`src/behavior-considered-undefined.md#L18-L19`,
`src/behavior-considered-undefined.md#L38-L41`,
`src/behavior-considered-undefined.md#L147`):
> "Assign statements roughly correspond to an assignment in Rust proper (`x =
> ...`) except without the possibility of dropping the previous value"
> "Accessing (loading from or storing to) a place that is [dangling] or [based
> on a misaligned pointer]."
> "Mutating immutable bytes." ... "Moreover, the bytes [pointed to] by a shared
> reference, including transitively through other references (both shared and
> mutable) and `Box`es, are immutable"

Correspondence:
- `newVal.isValidInState localGens`: the stored value must be initialized and
  must not contain dangling or retired references.
- `resolvePlace body.localCount st place` and `viaMutRef != some false`: `place`
  must resolve to an in-bounds slot without writing through a shared reference
  (`&T`).
- `resolved.targetLoc.index ≥ body.localCount` implies
  `!newVal.refsFrameLocal body.localCount`: a store into a caller-owned slot
  must not hold a reference into this frame. Such a reference would outlive
  the frame, which return deallocates, so no borrow-checked program performs
  the store: the slot's type names a caller lifetime that the frame-local
  borrow cannot satisfy. Rejecting the store keeps caller memory free of
  references into the frame, which return does not inspect (`stepTerminator`)
  and which would otherwise still look live after return, because return does
  not change any generation counter. This rule only adds faults.
- `!hasConflictingRefInVal localGens resolved true newVal`: the write to
  `place` must not retire a reference inside `newVal` itself. The pinned
  interpreter writes the value first and then retags the references it
  stored, so such a reference's retag would use a removed tag, which Stacked
  Borrows reports as undefined behavior (see `retagVal`).
- `invalidateConflictingRefs st resolved true`: writing to `place` retires any
  active shared or mutable borrows overlapping `resolved.fieldPath` (and any
  deeper child reborrows when writing through a parent reference).
- `lookupAt locals1 resolved.targetLoc.index = some (some rootVal)`: the target
  local slot must be live (allocated via `StorageLive`, not dead/`none`).
- Whole-place writes (`resolved.fieldPath = []`) check `newVal` with
  `checkValMatchesTy` (`allowUninit = false`) against the place's declared
  type `placeTyOpt` (the declared type of `place.loc` projected through
  `place.projection`, so a write `*r = v` is checked against `r`'s pointee
  type), falling back to the target slot's declared type when `place.loc` has
  none. Projected field writes (`resolved.fieldPath ≠ []`) materialize an
  uninitialized aggregate shell when `rootVal = .uninit`, verify that each
  aggregate container along `resolved.fieldPath` matches its declared `.tuple`
  or `.adt` constructor and field-spine length (`writeFieldPathWithTy`), and
  verify that `newVal` conforms to the leaf type (`projectFieldPathTy
  resolved.fieldPath rootTy`, which must agree with `placeTyOpt` when present)
  without inspecting untouched sibling fields.
- Every store is typed. If neither the place nor the target slot has a
  declared type, the store fails. `runMirSteps` never reaches that case,
  because admission and entry validation give every in-frame local and every
  caller slot an entry reference reaches a declared type (`bodyTysSupported`,
  `collectEntryRefsInVal`), but `stepStmt` and `stepMirCore` are also callable
  on unvalidated bodies and must not store untyped values there. -/
def assignPlace (body : MirBody) (st : MirState) (place : Place)
    (newVal : MirVal) : Option (List (Option MirVal)) :=
  let st := readDerefBase body st place
  match st with
  | ⟨_, localGens, _, _⟩ =>
    if !newVal.isValidInState localGens then
      none
    else
      match resolvePlace body.localCount st place with
      | some resolved =>
        match resolved.viaMutRef with
        | some false => none
        | _ =>
          if decide (body.localCount ≤ resolved.targetLoc.index) &&
              newVal.refsFrameLocal body.localCount then
            none
          else if hasConflictingRefInVal localGens resolved true newVal then
            none
          else
          let locals1 := invalidateConflictingRefs st resolved true
          match lookupAt locals1 resolved.targetLoc.index with
          | some (some rootVal) =>
            let placeTyOpt : Option MirTy :=
              match lookupAt body.localTys place.loc.index with
              | some baseTy => projectPlaceTy place.projection baseTy
              | none => none
            let placeProjectionInvalid : Bool :=
              match lookupAt body.localTys place.loc.index, placeTyOpt with
              | some _, none => true
              | _, _ => false
            if placeProjectionInvalid then
              none
            else
              match resolved.fieldPath with
              | [] =>
                let targetTyOpt : Option MirTy :=
                  match placeTyOpt with
                  | some pTy => some pTy
                  | none => lookupAt body.localTys resolved.targetLoc.index
                let rootStoreOk : Bool :=
                  match targetTyOpt with
                  | some ty =>
                    checkValMatchesTy body.ptrWidthBits ty newVal false
                      body.localTys locals1
                  | none => false
                if rootStoreOk then
                  setAt locals1 resolved.targetLoc.index (some newVal)
                else
                  none
              | _ =>
                let rootTyOpt := lookupAt body.localTys resolved.targetLoc.index
                let rootLeafTyOpt : Option MirTy :=
                  match rootTyOpt with
                  | some rootTy =>
                    projectFieldPathTy resolved.fieldPath rootTy
                  | none => none
                let leafTyOpt : Option MirTy :=
                  match rootLeafTyOpt, placeTyOpt with
                  | some rTy, some pTy =>
                    if MirTy.beq pTy rTy then some rTy else none
                  | some rTy, none => some rTy
                  | none, _ => none
                let leafTyOk : Bool :=
                  match leafTyOpt with
                  | some leafTy =>
                    checkValMatchesTy body.ptrWidthBits leafTy newVal false
                      body.localTys locals1
                  | none => false
                if !leafTyOk then
                  none
                else
                  match writeFieldPathWithTy resolved.fieldPath newVal rootTyOpt
                      rootVal with
                  | some rootVal' =>
                    setAt locals1 resolved.targetLoc.index (some rootVal')
                  | none => none
          | _ => none
      | none => none

/-! ## Operand, borrow, and rvalue evaluation -/

/-- Evaluate a MIR `Operand` in state `st`, returning the loaded value and the
state after the load (`compiler/rustc_middle/src/mir/syntax.rs#L1272-L1276`,
`compiler/rustc_middle/src/mir/syntax.rs#L1283-L1293`,
`compiler/rustc_middle/src/mir/syntax.rs#L1308-L1309`):
> "The most common way to create values is via loading a place. Loading a
> place is an operation which reads the memory of the place and converts it to
> a value. This is a fundamentally *typed* operation. The nature of the value
> produced depends on the type of the conversion. Furthermore, there may be
> other effects: if the type has a validity constraint loading the place might
> be UB if the validity constraint is not met."
> "/// Creates a value by loading the given place."
> "/// Creates a value by performing loading the place, just like the `Copy`
> operand.
> ///
> /// This *may* additionally overwrite the place with `uninit` bytes,
> depending on how we decide in [UCG#188]. You should not emit MIR that may
> attempt a subsequent second load of this place without first
> re-initializing it."
> "/// Constants are already semantically values, and remain unchanged.
> Constant(Box<ConstOperand<'tcx>>),"

The pinned reference interpreter evaluates `Copy` and `Move` the same way
(`compiler/rustc_const_eval/src/interpret/operand.rs#L847-L848`):
> "// FIXME: do some more logic on `move` to invalidate the old location
> &Copy(place) | &Move(place) => self.eval_place_to_op(place, layout)?,"

Correspondence:
- `.copy src` loads `src` (`readPlace`). The load is a read access through
  the place's tag, so it first retires the references that Stacked Borrows
  disables on a read (`invalidateConflictingRefs` with `needMut = false`;
  `refDepthConflicts`). It then fails if `src` does not resolve to a live
  local (`resolvePlace`) or if the loaded value is not valid: an `.uninit`
  part, or a dangling or retired reference, violates the validity constraint
  above.
- `.move src` performs the same load and then takes the option the upstream
  documentation allows: it overwrites `src` with `.uninit` (`deinitPlace`),
  which is a write access and retires the references a write retires. A later
  load of `src` therefore faults, which matches the rule that MIR must not
  load a moved-from place before re-initializing it. The overwrite fails when
  `src` lies behind a reference (see `deinitPlace`).
- `.constVal val` returns `val` and leaves `st` unchanged. It fails unless
  `val` is initialized and contains no reference (`MirVal.refsIn`). A Rust
  constant of reference type points to memory that the constant owns (for
  example, a promoted or static allocation), never to a local of the running
  frame. This semantics has no such memory, so a constant reference could only
  forge provenance for a local; constants that contain references are
  unsupported. Whether `val` fits the type of its use is checked against the
  destination or the other operand (`rvalueTysOk`). -/
def evalOperand (body : MirBody) (st : MirState)
    (op : Operand) : Option (MirVal × MirState) :=
  match op with
  | .copy src => readPlace body st src
  | .move src =>
    match readPlace body st src with
    | some (v, st1) =>
      match deinitPlace body st1 src with
      | some st2 => some (v, st2)
      | none => none
    | none => none
  | .constVal val =>
    match val.refsIn with
    | [] => if val.isFullyInit then some (val, st) else none
    | _ :: _ => none

/-- Create a shared (`mutable = false`) or mutable (`mutable = true`) reference
to `src` in state `st`, retiring any conflicting deeper borrows in the returned
`MirState` (`compiler/rustc_middle/src/mir/syntax.rs#L1351`,
`compiler/rustc_const_eval/src/interpret/step.rs#L219-L225`):
> "Creates a reference of the indicated kind to the place."
> "let mut val = ImmTy::from_immediate(place.to_ref(self), dest.layout);
> // A fresh reference was created, make sure it gets retagged with the right
> mode.
> let mode = if borrow_kind.is_two_phase_borrow() {
> RetagMode::TwoPhase
> } else {
> RetagMode::Default"

The new reference is a reborrow one level deeper than `src`
(`refDepthConflicts`). Stacked Borrows gives a two-phase mutable borrow a
`SharedReadWrite` item without an access
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L66-L73`); this
semantics does not distinguish two-phase borrows and treats every mutable
borrow as a `Unique` reborrow with a write access, which can only add faults.

Fails (`none`) if `src` does not currently hold a valid, initialized value or if
a mutable borrow is requested through a shared reference. -/
def evalBorrow (body : MirBody) (st : MirState) (mutable : Bool)
    (src : Place) : Option (MirVal × MirState) :=
  match resolvePlace body.localCount st src, readPlace body st src with
  | some resolved, some (_, st1) =>
    if mutable && resolved.viaMutRef == some false then
      none
    else
      let locals' := invalidateConflictingRefs st1 resolved mutable
      match lookupAt st1.localGens resolved.targetLoc.index with
      | some curGen =>
        let refVal :=
          MirVal.ref mutable curGen resolved.targetLoc resolved.fieldPath
            (resolved.reborrowDepth + 1)
        some (refVal, ⟨locals', st1.localGens, st1.block, st1.stmtIdx⟩)
      | none => none
  | _, _ => none

/-- True iff retagging the references `refs` of one copied value in order
retires none of them. Retagging a reference performs an access through its
tag (`retagVal`), and that access must not retire a later reference of the
same value (whose own retag would then use a removed tag, which Stacked
Borrows reports as undefined behavior), nor the new tag that an earlier
retag created (depth one greater than the earlier reference). For example, a
value holding a `&mut` and a shared reborrow of it faults: the mutable
retag's write access retires the shared reborrow. The second condition can
reject a value whose retired copy would never be used; that only adds
faults. -/
def retagRefsConsistent
    (refs : List (Bool × Nat × LocalId × List Nat × Nat)) : Bool :=
  (refs.foldr
    (fun r (acc : Bool × List (Bool × Nat × LocalId × List Nat × Nat)) =>
      match r with
      | (m, _, loc, path, d) =>
        let okHere :=
          acc.2.foldr
            (fun r2 ok2 =>
              match r2 with
              | (m2, _, loc2, path2, d2) =>
                !(loc2.index == loc.index && pathsOverlap path2 path &&
                  (refDepthConflicts ⟨loc, path, some m, none, d⟩ m m2 d2 ||
                   refDepthConflicts ⟨loc2, path2, some m2, none, d2⟩ m2 m
                     (d + 1))) && ok2)
            true
        (acc.1 && okHere, r :: acc.2))
    (true, [])).1

/-- Retag every reference in the copied value `v` for `Rvalue.use _ .yes`,
returning the retagged value and the state after the retags' accesses.

The pinned reference interpreter performs `Rvalue::Use` as a typed copy inside
a retag mode chosen by the `WithRetag` flag
(`compiler/rustc_const_eval/src/interpret/step.rs#L179-L184`):
> "let op = self.eval_operand(operand, Some(dest.layout))?;
> let mode = if with_retag.yes() { RetagMode::Default } else { RetagMode::None
> };
> M::with_retag_mode(self, mode, |ecx| ecx.copy_op(&op, &dest))?;"

The typed copy validates the destination, and validation walks the fields of
aggregates and retags every reference it reaches
(`compiler/rustc_const_eval/src/interpret/place.rs#L935-L939`,
`compiler/rustc_const_eval/src/interpret/validity.rs#L1539-L1542`,
`compiler/rustc_const_eval/src/interpret/validity.rs#L924-L926`,
`compiler/rustc_const_eval/src/interpret/validity.rs#L602-L625`):
> "self.validate_place(
> &dest,
> M::enforce_validity_recursively(self, dest.layout()),
> /*reset_provenance_and_padding*/ true,
> )?;"
> "_ => {
> // default handler
> try_validation!(
> self.walk_value(val),"
> "ty::Ref(_, _ty, mutbl) => {
> self.check_safe_pointer(value, ty, PtrKind::Ref(*mutbl))?;"
> "// If we're not allow to dangle, make sure this is dereferenceable and retag
> it for
> // the aliasing model."
> "M::retag_ptr_value(self.ecx, &ptr, ty)"

Under Stacked Borrows, a retag of `&mut T` grants a new `Unique` tag through a
write access by the old tag, and a retag of `&T` grants a new
`SharedReadOnly` tag through a read access
(`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L77-L82`,
`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs#L102-L106`). Each
reference `r` of depth `d` in `v` is therefore treated as a reborrow of `*r`:
the state first performs `r`'s access (retiring the references that
`refDepthConflicts` selects for an access through depth `d` with `needMut`
equal to `r`'s mutability), and the copied reference gets depth `d + 1`. The
retag never changes a reference's mutability, target, generation, or path. A
value without references is returned with `st` unchanged.

Order: the interpreter writes the copied value first and retags the
destination's references afterward, during validation of the destination
(quoted above). This function runs before `assignPlace` stores the value, so
two checks restore the effects of Miri's order. First, the retags of one
value must not retire each other (`retagRefsConsistent`); otherwise this
returns `none`. Second, `assignPlace` faults if the write to the destination
would retire a reference inside the stored value: in Miri that write removes
the reference's item, and the later retag of the stored reference fails. -/
def retagVal (st : MirState) (v : MirVal) : Option (MirVal × MirState) :=
  match v.refsIn with
  | [] => some (v, st)
  | refs =>
    if !retagRefsConsistent refs then
      none
    else
      let locals' :=
        refs.foldl
          (fun locals r =>
            match r with
            | (isMut, _, loc, path, depth) =>
              invalidateConflictingRefs
                ⟨locals, st.localGens, st.block, st.stmtIdx⟩
                ⟨loc, path, some isMut, none, depth⟩ isMut)
          st.locals
      some (v.deepenRefs, ⟨locals', st.localGens, st.block, st.stmtIdx⟩)

/-- Evaluate a binary operation `BinOp` on two initialized `MirVal`s, using
logarithmic bitwise operations (`Nat.land`, `Nat.lor`, `Nat.xor`) from
`Init.Data.Nat.Bitwise.Basic`
(`compiler/rustc_middle/src/mir/syntax.rs#L1608-L1698`,
`src/expressions/operator-expr.md#L381-L395`):
> "pub enum BinOp { Add, ... Sub, ... Mul, ... BitXor, BitAnd, BitOr, ... Eq,
> Lt, Le, Ne, Ge, Gt, ... }"
> "This table summarizes the behavior of arithmetic and logical binary
> operators on primitive types and which traits are used to overload these
> operators for other types."

```text
| Symbol | Integer                 | `bool`        | ...
| `+`    | Addition                |               | ...
| `-`    | Subtraction             |               | ...
| `*`    | Multiplication          |               | ...
| `&`    | Bitwise AND             | [Logical AND] | ...
| `\|` | Bitwise OR | [Logical OR]  | ...
| `^`    | Bitwise XOR             | [Logical XOR] | ...
```

The MIR operators `Add`, `Sub`, and `Mul` wrap on overflow; overflow UB
belongs only to the separate `*Unchecked` operators, and the `*WithOverflow`
operators return the same wrapped result paired with an overflow flag
(`compiler/rustc_middle/src/mir/syntax.rs#L1609-L1629`):
> "/// The `+` operator (addition)
> Add,
> /// Like `Add`, but with UB on overflow.  (Integers only.)
> AddUnchecked,
> /// Like `Add`, but returns `(T, bool)` of both the wrapped result
> /// and a bool indicating whether it overflowed.
> AddWithOverflow,"
(and likewise for `Sub`/`SubUnchecked`/`SubWithOverflow` and
`Mul`/`MulUnchecked`/`MulWithOverflow`). When overflow checks are enabled,
MIR building lowers a source-level `+`, `-`, or `*` to the `*WithOverflow`
operator followed by an `Assert` on the overflow flag
(`compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs#L456-L476`):
> "BinOp::Add | BinOp::Sub | BinOp::Mul if self.check_overflow &&
> ty.is_integral() => { ... let op_with_overflow =
> op.wrapping_to_overflowing().unwrap(); ... let err =
> AssertKind::Overflow(op, lhs, rhs); block = self.assert(block,
> Operand::Move(of), false, err, span);"
Otherwise it emits the plain operator. Either way, a plain `Add` in
`Runtime(PostCleanup)` MIR is unconditionally wrapping. The doc comment of
`Rvalue::BinaryOp` fixes the operand and result types
(`compiler/rustc_middle/src/mir/syntax.rs#L1397-L1402`):
> "The `Bit*` operations accept signed integers, unsigned integers, or bools
> with matching types and return a value of that type. ... The remaining
> operations accept signed integers, unsigned integers, or floats with
> matching types and return a value of that type."

Correspondence:
- When `intWidthOpt = some bits` (the width of the operands' declared type;
  see `binOpOperandTy`), `.add`, `.sub`, and `.mul` model this wrapping
  unsigned arithmetic modulo $2^{\text{bits}}$ (`(a + b) % 2^bits`,
  `(a + 2^bits - (b % 2^bits)) % 2^bits`, and `(a * b) % 2^bits`). Without a
  width (`intWidthOpt = none`) they fault, so arithmetic never runs on
  unbounded integers. This AST has only unsigned integer types (`MirTyTree`),
  so two's-complement signed wrapping does not arise.
- `.eq`, `.ne`, `.lt`, `.le`, `.gt`, and `.ge` model the comparisons
  documented in `rustc_middle` and the Reference; see `evalBinOp`'s comparison
  rules below.
- `.bitAnd`, `.bitOr`, and `.bitXor` model bitwise AND, OR, and XOR on
  `MirVal.int` and logical AND, OR, and XOR on `MirVal.bool`, as in the
  Reference table above. Bitwise operations on two values below $2^{bits}$
  stay below $2^{bits}$, so they need no width.

Comparison rules. MIR comparisons accept matching operand types and return
`bool` (`compiler/rustc_middle/src/mir/syntax.rs#L1391-L1393`):
> "The comparison operations accept `bool`s, `char`s, signed or unsigned
> integers, floats, raw pointers, or function pointers and return a `bool`.
> The types of the operands must be matching, up to the usual caveat of the
> lifetimes in function pointers."
On unsigned integers the operators have their mathematical meaning, which is
`decide` on `Nat` (`src/expressions/operator-expr.md#L456-L465`):

```text
| Symbol | Meaning                  | Overloading method         |
|--------|--------------------------|----------------------------|
| `==`   | Equal                    | `std::cmp::PartialEq::eq`  |
| `!=`   | Not equal                | `std::cmp::PartialEq::ne`  |
| `>`    | Greater than             | `std::cmp::PartialOrd::gt` |
| `<`    | Less than                | `std::cmp::PartialOrd::lt` |
| `>=`   | Greater than or equal to | `std::cmp::PartialOrd::ge` |
| `<=`   | Less than or equal to    | `std::cmp::PartialOrd::le` |
```

On `bool` the Reference fixes the ordering `false < true`
(`src/types/boolean.md#L84-L113`):

```text
| `a` | `b` | [`a == b`][op-compare] |
|- | - | - |
| `true` | `true` | `true` |
| `true` | `false` | `false` |
| `false` | `true` | `false` |
| `false` | `false` | `true` |

| `a` | `b` | [`a > b`][op-compare] |
|- | - | - |
| `true` | `true` | `false` |
| `true` | `false` | `true` |
| `false` | `true` | `false` |
| `false` | `false` | `false` |

* `a != b` is the same as `!(a == b)`
* `a >= b` is the same as `a == b | a > b`
* `a < b` is the same as `!(a >= b)`
* `a <= b` is the same as `a == b | a < b`
```

so `a > b` is `a && !b`, `a < b` is `!a && b`, `a >= b` is `a || !b`, and
`a <= b` is `!a || b`, exactly the `bool` cases below. Every other operand
combination, including comparisons of `()` values (which `rvalueTysOk` never
admits), faults. -/
def evalBinOp (op : BinOp) (lhs rhs : MirVal)
    (intWidthOpt : Option Nat := none) : Option MirVal :=
  match op, lhs, rhs with
  | .add, ⟨_, .int a⟩, ⟨_, .int b⟩ =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none else some (.int (Nat.mod (a + b) modulus))
    | none => none
  | .sub, ⟨_, .int a⟩, ⟨_, .int b⟩ =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none
      else some (.int (Nat.mod (a + modulus - Nat.mod b modulus) modulus))
    | none => none
  | .mul, ⟨_, .int a⟩, ⟨_, .int b⟩ =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none else some (.int (Nat.mod (a * b) modulus))
    | none => none
  | .eq, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (a = b)))
  | .eq, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (decide (a = b)))
  | .ne, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (a ≠ b)))
  | .ne, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (decide (a ≠ b)))
  | .lt, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (a < b)))
  | .lt, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (!a && b))
  | .le, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (a ≤ b)))
  | .le, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (!a || b))
  | .gt, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (b < a)))
  | .gt, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (a && !b))
  | .ge, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (decide (b ≤ a)))
  | .ge, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (a || !b))
  | .bitAnd, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.int (Nat.land a b))
  | .bitOr, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.int (Nat.lor a b))
  | .bitXor, ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.int (Nat.xor a b))
  | .bitAnd, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (a && b))
  | .bitOr, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (a || b))
  | .bitXor, ⟨_, .bool a⟩, ⟨_, .bool b⟩ => some (.bool (bne a b))
  | _, _, _ => none

/-- Evaluate a unary operation `UnOp` on an initialized `MirVal`
(`compiler/rustc_middle/src/mir/syntax.rs#L1590-L1604`,
`src/expressions/operator-expr.md#L341-L349`):
> "pub enum UnOp {
>     /// The `!` operator for logical inversion
>     Not,
>     /// The `-` operator for negation
>     Neg,
>     ...
>     PtrMetadata,
> }"

```text
| Symbol | Integer     | `bool`        | Floating Point | Overloading Trait  |
| `!`    | Bitwise NOT | [Logical NOT] |                | `std::ops::Not`    |
```

Correspondence:
- On `.bool b`, `.not` evaluates the truth-value inversion `!b`.
- On `.int a`, `.not` evaluates the width-masked bitwise complement
  `(2^bits - 1) - a` when `intWidthOpt = some bits` (the width of the operand
  type) and `a < 2^bits`, and faults otherwise. -/
def evalUnOp (op : UnOp) (intWidthOpt : Option Nat) (v : MirVal) :
    Option MirVal :=
  match op, v with
  | .not, ⟨_, .bool b⟩ => some (.bool (!b))
  | .not, ⟨_, .int a⟩ =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if decide (a < modulus) then
        some (.int ((modulus - 1) - a))
      else
        none
    | none => none
  | _, _ => none

/-- True iff `op` is a comparison (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`). -/
def BinOp.isComparison : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- True iff `op` is an arithmetic operator (`Add`, `Sub`, `Mul`). -/
def BinOp.isArithmetic : BinOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- True iff `t` is an unsigned integer type (`usize` or `uint bits`). -/
def MirTy.isUint (t : MirTy) : Bool :=
  match t with
  | ⟨_, .usize⟩ | ⟨_, .uint _⟩ => true
  | _ => false

/-- True iff `t` is `bool`. -/
def MirTy.isBool (t : MirTy) : Bool :=
  match t with
  | ⟨_, .bool⟩ => true
  | _ => false

/-- The common operand type of `Rvalue.binaryOp op lhs rhs` assigned to `dst`:
the declared type of the place operands, which must agree when both are
places. When both operands are constants:
- two `bool` constants have operand type `bool`, because `MirVal.bool` values
  have no other type in this subset (so `Eq(const true, const false)` is
  accepted);
- otherwise the type of an arithmetic or bitwise operation is the
  destination's type, because such operations return their operand type
  (`compiler/rustc_middle/src/mir/syntax.rs#L1397-L1402`);
- otherwise (a comparison of two integer constants, such as `Eq(const 1_u8,
  const 2_u8)`) the operand type is unknown, because `Operand.constVal`
  carries no type, and this yields `none`. Stepping such an assignment faults
  (`rvalueTysOk`); MIR building can emit them, so this is a documented
  unsupported form that a producer must reject rather than retype. -/
def binOpOperandTy (body : MirBody) (dst : Place) (op : BinOp)
    (lhs rhs : Operand) : Option MirTy :=
  match operandDeclTy body lhs, operandDeclTy body rhs with
  | some lt, some rt => if MirTy.beq lt rt then some lt else none
  | some lt, none => some lt
  | none, some rt => some rt
  | none, none =>
    match lhs, rhs with
    | .constVal ⟨_, .bool _⟩, .constVal ⟨_, .bool _⟩ => some MirTy.bool
    | _, _ => if op.isComparison then none else placeDeclTy body dst

/-- True iff `op` is not a constant, or is a constant whose value conforms to
`ty` (`checkValMatchesTy`). The check passes no local types or values, so a
constant that contains a reference never fits: this AST has no constant that
can denote a reference (`evalOperand` also rejects them). -/
def constOperandFits (ptrWidthBits : Nat) (ty : MirTy) : Operand → Bool
  | .constVal v => checkValMatchesTy ptrWidthBits ty v false [] []
  | .copy _ | .move _ => true

/-- True iff every place operand of `rv` has a declared type (`placeDeclTy`).
Only constants lack a declared type; a place operand without one (a field
index past the end of its type, or a dereference of a non-reference) is ill
typed, so `rvalueTysOk` rejects it rather than typing it from the other
operand or the destination. -/
def rvalueOperandsTyped (body : MirBody) (rv : Rvalue) : Bool :=
  let operandTyped : Operand → Bool := fun op =>
    match op with
    | .copy p | .move p => (placeDeclTy body p).isSome
    | .constVal _ => true
  match rv with
  | .use op _ => operandTyped op
  | .ref _ | .refMut _ => true
  | .binaryOp _ lhs rhs => operandTyped lhs && operandTyped rhs
  | .unaryOp _ src => operandTyped src

/-- True iff the assignment `dst = rv` is well typed under `body.localTys`.
The pinned MIR validator requires the two sides of an assignment to have the
same type (`compiler/rustc_mir_transform/src/validate.rs#L1469-L1474`):
> "StatementKind::Assign((dest, rvalue)) => {
> // LHS and RHS of the assignment must have the same type.
> let left_ty = dest.ty(&self.body.local_decls, self.tcx).ty;
> let right_ty = rvalue.ty(&self.body.local_decls, self.tcx);
>
> if !self.mir_assign_valid_types(right_ty, left_ty) {"

After borrow checking, `mir_assign_valid_types` compares types invariantly
(`compiler/rustc_mir_transform/src/validate.rs#L590-L596`), and this AST has
no lifetimes or subtyping, so the check here is `MirTy.beq`. The type of each
rvalue follows `Rvalue::ty`, `BinOp::ty`, and `UnOp::ty`
(`compiler/rustc_middle/src/mir/statement.rs#L814`,
`compiler/rustc_middle/src/mir/statement.rs#L819-L822`,
`compiler/rustc_middle/src/mir/statement.rs#L829-L837`,
`compiler/rustc_middle/src/mir/statement.rs#L893-L920`,
`compiler/rustc_middle/src/mir/statement.rs#L933-L935`):
> "Rvalue::Use(ref operand, _) => operand.ty(local_decls, tcx),"
> "Rvalue::Ref(reg, bk, ref place) => {
> let place_ty = place.ty(local_decls, tcx).ty;
> Ty::new_ref(tcx, reg, place_ty, bk.to_mutbl_lossy())"
> "UnOp::Not | UnOp::Neg => arg_ty,"
> "// these should be integers or floats of the same size.
> assert_eq!(lhs_ty, rhs_ty);
> lhs_ty"
> "&BinOp::Eq | &BinOp::Lt | &BinOp::Le | &BinOp::Ne | &BinOp::Ge | &BinOp::Gt
> => {
> tcx.types.bool"

The validator also requires both operands of these binary operators to have
the same type and restricts the operand kinds
(`compiler/rustc_mir_transform/src/validate.rs#L1155-L1170`,
`compiler/rustc_mir_transform/src/validate.rs#L1179-L1192`,
`compiler/rustc_mir_transform/src/validate.rs#L1213-L1231`,
`compiler/rustc_mir_transform/src/validate.rs#L1239-L1245`):
> "} else if a != b {
> self.fail(
> location,
> format!("Cannot perform binary op {op:?} on unequal types {a} and {b}"),"
> "Cannot {op:?} compare type {:?}", ty::Bool | ty::Char | ty::Int(..) |
> ty::Uint(..) | ty::Float(..) | ty::RawPtr(..) | ty::FnPtr(..)"
> "Cannot perform bitwise op {op:?} on type {:?}", ty::Uint(..) | ty::Int(..)
> | ty::Bool"
> "Cannot perform arithmetic {op:?} on type {:?}", ty::Uint(..) | ty::Int(..)
> | ty::Float(..)"
> "Cannot binary not type {:?}", ty::Int(..) | ty::Uint(..) | ty::Bool"

Correspondence (every case requires `dst` and every place operand to have a
declared type, `rvalueOperandsTyped`):
- `.use op _`: a place operand's declared type must equal `dst`'s; a constant
  must conform to `dst`'s type, since its type is the type of its use.
- `.ref src` and `.refMut src`: `dst` must have type `&T` or `&mut T`, where
  `T` is `src`'s declared type.
- `.binaryOp op lhs rhs`: the operand type (`binOpOperandTy`) must exist; it
  must be an unsigned integer type for arithmetic and an unsigned integer type
  or `bool` for comparisons and bitwise operators; `dst` must be `bool` for a
  comparison and the operand type otherwise; and constant operands must
  conform to the operand type.
- `.unaryOp .not src`: the operand type is `src`'s declared type, or `dst`'s
  type for a constant; it must be an unsigned integer type or `bool`, must
  equal `dst`'s type, and must fit a constant operand. -/
def rvalueTysOk (body : MirBody) (dst : Place) (rv : Rvalue) : Bool :=
  match placeDeclTy body dst with
  | none => false
  | some dstTy =>
    rvalueOperandsTyped body rv &&
    match rv with
    | .use op _ =>
      match operandDeclTy body op with
      | some opTy => MirTy.beq opTy dstTy
      | none => constOperandFits body.ptrWidthBits dstTy op
    | .ref src =>
      match placeDeclTy body src with
      | some srcTy => MirTy.beq (MirTy.ref srcTy) dstTy
      | none => false
    | .refMut src =>
      match placeDeclTy body src with
      | some srcTy => MirTy.beq (MirTy.refMut srcTy) dstTy
      | none => false
    | .binaryOp op lhs rhs =>
      match binOpOperandTy body dst op lhs rhs with
      | none => false
      | some opTy =>
        let kindOk : Bool :=
          if op.isArithmetic then opTy.isUint else opTy.isUint || opTy.isBool
        let resultOk : Bool :=
          if op.isComparison then dstTy.isBool else MirTy.beq opTy dstTy
        kindOk && resultOk &&
          constOperandFits body.ptrWidthBits opTy lhs &&
          constOperandFits body.ptrWidthBits opTy rhs
    | .unaryOp _ src =>
      let opTy : MirTy :=
        match operandDeclTy body src with
        | some t => t
        | none => dstTy
      (opTy.isUint || opTy.isBool) && MirTy.beq opTy dstTy &&
        constOperandFits body.ptrWidthBits opTy src

/-- Evaluate a MIR `Rvalue` in state `st` for assignment into `dst`, returning
both the computed `MirVal` and the post-rvalue `MirState`
(`compiler/rustc_middle/src/mir/syntax.rs#L1342-L1467`). It fails unless the
assignment is well typed (`rvalueTysOk`); the integer width of an arithmetic,
bitwise, or `Not` operation is the width of the operand type.

`Rvalue.use op withRetag` evaluates `op`. With `WithRetag.yes`, it then
retags every reference in the copied value (`retagVal`), which gives each copy
a new tag one level deeper than its source and performs that tag's access.
With `WithRetag.no`, the copy keeps its source's tag and depth, as the pinned
reference interpreter does when it copies under `RetagMode::None`
(`compiler/rustc_const_eval/src/interpret/step.rs#L179-L184`):
> "let op = self.eval_operand(operand, Some(dest.layout))?;
> let mode = if with_retag.yes() { RetagMode::Default } else { RetagMode::None
> };
> M::with_retag_mode(self, mode, |ecx| ecx.copy_op(&op, &dest))?;"

The dereference temporaries that `Derefer` inserts are lowered to
`WithRetag.no` copies, and each is used only to dereference the copied
reference (`compiler/rustc_middle/src/mir/syntax.rs#L1434-L1444`,
`compiler/rustc_mir_transform/src/erase_deref_temps.rs#L19-L24`); entry
validation accepts `WithRetag.no` only for such temporaries
(`bodyDerefTempsValid`). -/
def evalRvalue (body : MirBody) (dst : Place) (st : MirState)
    (rv : Rvalue) : Option (MirVal × MirState) :=
  if !rvalueTysOk body dst rv then none else
  match rv with
  | .use op .no => evalOperand body st op
  | .use op .yes =>
    match evalOperand body st op with
    | some (v, st1) => retagVal st1 v
    | none => none
  | .ref src => evalBorrow body st false src
  | .refMut src => evalBorrow body st true src
  | .binaryOp op lhs rhs =>
    let widthOpt : Option Nat :=
      match binOpOperandTy body dst op lhs rhs with
      | some opTy => tyBitWidth body.ptrWidthBits opTy
      | none => none
    match evalOperand body st lhs with
    | some (v1, st1) =>
      match evalOperand body st1 rhs with
      | some (v2, st2) =>
        match evalBinOp op v1 v2 widthOpt with
        | some res => some (res, st2)
        | none => none
      | none => none
    | none => none
  | .unaryOp op src =>
    let widthOpt : Option Nat :=
      match operandDeclTy body src, placeDeclTy body dst with
      | some opTy, _ => tyBitWidth body.ptrWidthBits opTy
      | none, some dstTy => tyBitWidth body.ptrWidthBits dstTy
      | none, none => none
    match evalOperand body st src with
    | some (v, st1) =>
      match evalUnOp op widthOpt v with
      | some res => some (res, st1)
      | none => none
    | none => none

/-! ## Small-step statement, terminator, and body execution -/

/-- True iff `rv` is a `Use` of a place that, in state `st`, resolves to a
place overlapping the place `dst` resolves to. This catches overlaps that the
static check (`bodyUseAssignsDisjoint`) cannot see because they go through
references, such as `(*_2) = copy (*_3)` with `_3 = &*_2`.

The pinned `Assign` contract allows the two sides of an assignment to overlap
only for types with a scalar or scalar-pair layout
(`compiler/rustc_middle/src/mir/syntax.rs#L328-L333`):
> "We currently require that the LHS place not overlap with any place
> read as part of computation of the RHS for some rvalues. This requirement is
> under discussion in [#68364]. Specifically, overlap is permitted only for
> assignments of a type with `BackendRepr::Scalar | BackendRepr::ScalarPair`
> where all the scalar fields are [`Scalar::Initialized`]..."
and the pinned interpreter copies other values with a nonoverlapping memory
copy (`compiler/rustc_const_eval/src/interpret/place.rs#L1039-L1046`):
> "self.mem_copy(src.ptr(), dest.ptr(), dest_size, /*nonoverlapping*/
> true)?;"
This semantics does not model layouts, so it faults on every overlapping
`Use`, including the scalar cases that upstream allows; that only adds
faults. -/
def useAssignOverlaps (body : MirBody) (st : MirState) (dst : Place)
    (rv : Rvalue) : Bool :=
  let overlap : Place → Bool := fun src =>
    match resolvePlace body.localCount st dst,
          resolvePlace body.localCount st src with
    | some d, some r =>
      d.targetLoc.index == r.targetLoc.index &&
        pathsOverlap d.fieldPath r.fieldPath
    | _, _ => false
  match rv with
  | .use (.copy src) _ | .use (.move src) _ => overlap src
  | _ => false

/-- Execute a single MIR `Stmt` in `body` from state `st`
(`compiler/rustc_middle/src/mir/syntax.rs#L298-L456`):
- `.assign dst rv`: faults if `rv` is a `Use` of a place that overlaps `dst`
  in the current state (`useAssignOverlaps`), and otherwise evaluates `rv`
  and stores the result into `dst`.
- `.storageLive loc` and `.storageDead loc` follow the pinned storage
  contract (`compiler/rustc_middle/src/mir/syntax.rs#L364-L381`):
  > "At any point during the execution of a function, each local is either
  > allocated or unallocated. Except as noted below, all locals except
  > function parameters are initially unallocated. `StorageLive` statements
  > cause memory to be allocated for the local while `StorageDead` statements
  > cause the memory to be freed. ... Using a local in any way (not only
  > reading/writing from it) while it is unallocated is UB.
  >
  > Some locals have no `StorageLive` or `StorageDead` statements within the
  > entire MIR body. These locals are implicitly allocated for the full
  > duration of the function. ...
  >
  > If the local is already allocated, calling `StorageLive` again will
  > implicitly free the local and then allocate fresh uninitialized memory.
  > If a local is already deallocated, calling `StorageDead` again is a NOP."

  Correspondence: slot `some none` is "unallocated" and `some (some v)` is
  "allocated". The generation counter stands for the allocation's identity:
  every free bumps it, so a reference created under an earlier allocation
  (`MirVal.ref _ gen ..` with an older `gen`) no longer names a live
  allocation and every later use of it faults.
  - `.storageLive loc` sets the slot to `some .uninit` ("fresh uninitialized
    memory") and bumps the generation. Starting from an allocated slot this is
    the "implicitly free ... and then allocate" case; starting from an
    unallocated slot the bump is harmless because no live reference can name
    an unallocated local.
  - `.storageDead loc` on an allocated slot sets it to `none` and bumps the
    generation ("freed"); on an unallocated slot it is the documented NOP.
  - Any other access to an unallocated local (load, store, borrow, or
    `PlaceMention`) faults, matching "Using a local in any way ... while it
    is unallocated is UB".
  - "Initially unallocated" versus "implicitly allocated" is enforced at entry
    by `entryFrameSlotsCanonical`: the return place starts allocated and
    uninitialized, a user variable or temporary that appears in some
    `StorageLive`/`StorageDead` statement starts unallocated, and every other
    user variable or temporary starts allocated and uninitialized.
  - Indices at or beyond `body.localCount` are not locals of this frame and
    fault.
- `.placeMention src` (`StatementKind::PlaceMention`,
  `compiler/rustc_middle/src/mir/syntax.rs#L387-L392`):
  > "This statement exists to preserve a trace of a scrutinee matched against
  > a wildcard binding. This is especially useful for `let _ = PLACE;`
  > bindings that desugar to a single `PlaceMention(PLACE)`.
  >
  > When executed at runtime, this computes the given place, but then
  > discards it without doing a load. `let _ = *ptr;` is fine even if the
  > pointer is dangling."
  Computes `src` without loading it: `src` must resolve (`resolvePlace`) to an
  allocated slot, and its projection must apply to its declared type
  (`placeDeclTy`). The runtime value is not read, so `let _ = x.a.0` succeeds
  after `x.a` has been moved out of. Computing a dereferencing place still
  reads the pointer out of its base local (`readDerefBase`), and resolving it
  requires a live reference, which is stricter than the upstream text above
  (it allows a dangling pointer) and can only add faults.
- `.nop`: advances `stmtIdx` without modifying locals or generations.

`PlaceMention` and `Nop` survive into `Runtime(PostCleanup)` MIR only when
`RemovePlaceMention` is disabled by `-Zmir-preserve-ub` (see `Stmt`). -/
def stepStmt (body : MirBody) (st : MirState)
    (stmt : Stmt) : StepOutcome :=
  match st with
  | ⟨locals, localGens, block, stmtIdx⟩ =>
    match stmt with
    | .assign dst rv =>
      if useAssignOverlaps body st dst rv then .fault else
      match evalRvalue body dst st rv with
      | some (val, stAfterRv) =>
        match assignPlace body stAfterRv dst val with
        | some locals' =>
          .stepped ⟨locals', stAfterRv.localGens, block, stmtIdx + 1⟩
        | none => .fault
      | none => .fault
    | .storageLive loc =>
      if decide (loc.index < body.localCount) then
        match lookupAt localGens loc.index with
        | some g =>
          match setAt locals loc.index (some .uninit),
                setAt localGens loc.index (g + 1) with
          | some locals', some gens' =>
            .stepped ⟨locals', gens', block, stmtIdx + 1⟩
          | _, _ => .fault
        | none => .fault
      else
        .fault
    | .storageDead loc =>
      if decide (loc.index < body.localCount) then
        match lookupAt locals loc.index, lookupAt localGens loc.index with
        | some none, some _ =>
          .stepped ⟨locals, localGens, block, stmtIdx + 1⟩
        | some (some _), some g =>
          match setAt locals loc.index none,
                setAt localGens loc.index (g + 1) with
          | some locals', some gens' =>
            .stepped ⟨locals', gens', block, stmtIdx + 1⟩
          | _, _ => .fault
        | _, _ => .fault
      else
        .fault
    | .placeMention src =>
      let stBase := readDerefBase body st src
      match resolvePlace body.localCount stBase src with
      | some resolved =>
        match lookupAt stBase.locals resolved.targetLoc.index,
              placeDeclTy body src with
        | some (some _), some _ =>
          .stepped ⟨stBase.locals, localGens, block, stmtIdx + 1⟩
        | _, _ => .fault
      | none => .fault
    | .nop => .stepped ⟨locals, localGens, block, stmtIdx + 1⟩

/-- Select the target `BlockId` in `targets` matching integer value `discrVal`
(`compiler/rustc_middle/src/mir/syntax.rs#L689-L692`):
> "Then, if the list of switch targets contains the computed value, continues
> execution at the associated basic block. Otherwise, continues execution at
> the "otherwise" basic block." -/
def findSwitchTarget (targets : SwitchTargets) (discrVal : Nat) : BlockId :=
  targets.branches.foldr
    (fun br acc => if br.val == discrVal then br.target else acc)
    targets.otherwise

/-- Convert an integer or boolean discriminant `MirVal` into its `SwitchInt`
scalar value (`false ↦ 0`, `true ↦ 1`, `.int n ↦ n`)
(`compiler/rustc_middle/src/mir/syntax.rs#L689-L690`):
> "First, evaluates the `discr` operand. The type of the operand must be a
> signed or unsigned integer, char, or bool, and must match the given type." -/
def evalSwitchDiscr (v : MirVal) : Option Nat :=
  match v with
  | ⟨_, .int n⟩ => some n
  | ⟨_, .bool false⟩ => some 0
  | ⟨_, .bool true⟩ => some 1
  | _ => none

/-- The unique value of `t` if `t` has no scalar or reference component: `()`
and tuples and structs whose fields all have such types (`some .unit`, a
`.fieldCons` spine of their field values, or `.adt id` of it); `none` for every
other type, including `!`, which has no values.

Such a value carries no data, so storage of the type is valid whatever its
bytes. The validity rules require initialization only of scalar components
(`src/behavior-considered-undefined.md#L132`), and the pinned interpreter keeps
fields of zero-sized layout as `Immediate::Uninit`
(`compiler/rustc_const_eval/src/interpret/operand.rs#L404-L406`):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory."
> "// the field contains no information, can be left uninit
> // (Scalar/ScalarPair can contain even aligned ZST, not just 1-ZST)
> _ if layout.is_zst() => Immediate::Uninit," -/
def MirTy.unitValue (t : MirTy) : Option MirVal :=
  @Nat.recCompiled (fun _ => MirTy → Option MirVal)
    (fun a =>
      match a with
      | ⟨_, .unit⟩ | ⟨_, .nil⟩ => some .unit
      | _ => none)
    (fun _ ih a =>
      match a with
      | ⟨_, .unit⟩ | ⟨_, .nil⟩ => some .unit
      | ⟨_, .tuple es⟩ => ih ⟨_, es⟩
      | ⟨_, .adt id fs⟩ =>
        match ih ⟨_, fs⟩ with
        | some spine => some (.adt id spine)
        | none => none
      | ⟨_, .cons h r⟩ =>
        match ih ⟨_, h⟩, ih ⟨_, r⟩ with
        | some hv, some rv => some (.fieldCons hv rv)
        | _, _ => none
      | _ => none)
    t.fuel t

/-- Execute a single MIR `Terminator` in `body` from state `st`
(`compiler/rustc_middle/src/mir/syntax.rs#L655-L968`):
- `.return_` (`TerminatorKind::Return`,
  `compiler/rustc_middle/src/mir/syntax.rs#L715-L721`):
  > "Returns from the function.
  >
  > Like function calls, the exact semantics of returns in Rust are unclear.
  > Returning very likely at least assigns the value currently in the return
  > place (`_0`) to the place specified in the associated `Call` terminator in
  > the calling function, as if assigned via `dest = move _0`. It might
  > additionally do other things, like have side-effects in the aliasing
  > model."
  Loads local `_0` (taking the unique value of `_0`'s type, `MirTy.unitValue`,
  when `_0` is uninitialized and its type has one), verifies that
  `retVal.isValidInState localGens` and
  `valRefsHaveLivePointees localGens locals retVal` hold (fully initialized and
  every reference inside `retVal` resolves to an initialized pointee), that
  `retVal` does not reference an in-frame local, and that `retVal` conforms
  to `_0`'s declared return type, and terminates with `.returned ⟨retVal,
  st⟩`.

  Return checks nothing about caller-owned slots. The upstream text above
  gives return no effect on them, and holding a dead or retired reference in
  memory is not undefined behavior; only a later use is, and every use here
  faults (`MirVal.isValidInState`, `resolvePlace`). Entry validation inspects
  only the caller sub-places that the arguments reach, so a slot no argument
  reaches may hold anything a valid caller could leave there (a reference to
  a partly moved-out value, or one that is stale or retired), and checking it
  at return would reject valid calls. The callee cannot make a caller slot
  invalid in any way that matters to its caller: every store into one is
  validated, typed, and free of references into this frame (`assignPlace`),
  moving out from behind a reference faults (`deinitPlace`), and
  `StorageLive`/`StorageDead` apply only to in-frame locals (`stepStmt`).
  What remains are references that a callee access retired. Stacked Borrows
  retires a reference by removing or disabling its item in the borrow stack
  and leaves the reference's bytes in memory unchanged, but this model
  rewrites the stored reference to name the dead slot index
  `localGens.length` (`invalidateConflictingRefsInVal`). Such a reference
  comes back in that form in the terminal state, where it no longer names the
  place that the caller's pointer points to (`MirReturn`).
- `.goto target` (`TerminatorKind::Goto`,
  `compiler/rustc_middle/src/mir/syntax.rs#L684-L685`):
  > "Block has one successor; we continue execution there."
  Checks `target.index < body.blocks.length` and transitions to statement `0` of
  `target`.
- `.switchInt discr targets` (`TerminatorKind::SwitchInt`,
  `compiler/rustc_middle/src/mir/syntax.rs#L687-L692`):
  > "Switches based on the computed value.
  >
  > First, evaluates the `discr` operand. The type of the operand must be a
  > signed or unsigned integer, char, or bool, and must match the given type.
  > Then, if the list of switch targets contains the computed value, continues
  > execution at the associated basic block. Otherwise, continues execution at
  > the "otherwise" basic block."
  Evaluates `discr`, maps booleans (`false ↦ 0`, `true ↦ 1`) and integers to
  their scalar value via `evalSwitchDiscr`, selects the matching successor in
  `targets` via `findSwitchTarget`, and transitions to statement `0` of that
  block if in bounds.
- `.unreachable` (`TerminatorKind::Unreachable`,
  `compiler/rustc_middle/src/mir/syntax.rs#L728-L730`):
  > "Indicates a terminator that can never be reached.
  >
  > Executing this terminator is UB."
  Transitions immediately to `StepOutcome.fault`. -/
def stepTerminator (body : MirBody) (st : MirState)
    (term : Terminator) : StepOutcome :=
  match st with
  | ⟨locals, localGens, block, stmtIdx⟩ =>
    match term with
    | .return_ =>
      -- A return place whose type has a unique value (`MirTy.unitValue`) holds
      -- that value even if the body never assigned it (`fn f() {}`).
      let retValOpt : Option MirVal :=
        match lookupAt locals 0 with
        | some (some ⟨_, .uninit⟩) =>
          match lookupAt body.localTys 0 with
          | some retTy =>
            match retTy.unitValue with
            | some u => some u
            | none => some .uninit
          | none => some .uninit
        | some (some v) => some v
        | _ => none
      match retValOpt with
      | some retVal =>
        if retVal.isValidInState localGens &&
           valRefsHaveLivePointees localGens locals retVal &&
           !retVal.refsFrameLocal body.localCount &&
           checkLocalStoreTy body.ptrWidthBits body.localTys 0 retVal false
             locals then
          .returned ⟨retVal, ⟨locals, localGens, block, stmtIdx⟩⟩
        else
          .fault
      | _ => .fault
    | .goto target =>
      if decide (target.index < body.blocks.length) then
        .stepped ⟨locals, localGens, target.index, 0⟩
      else
        .fault
    | .switchInt discr targets =>
      match evalOperand body st discr with
      | some (v, stAfterDiscr) =>
        match evalSwitchDiscr v with
        | some discrVal =>
          let target := findSwitchTarget targets discrVal
          if decide (target.index < body.blocks.length) then
            .stepped
              ⟨stAfterDiscr.locals, stAfterDiscr.localGens, target.index, 0⟩
          else
            .fault
        | none => .fault
      | none => .fault
    | .unreachable => .fault

/-- Perform one small-step operational transition of `body` from `st`: if
`st.stmtIdx` indexes a statement in the current basic block, executes that
statement; if `st.stmtIdx` equals the statement count of the current basic
block, executes its terminator.

This is the only single-step transition, and it does not depend on where `st`
is in the body. Admission and entry validation happen once, in
`runMirSteps`, before the first step; `bodyCfgValid` (part of admission,
`bodyAdmissible`) rules out edges into `bb0`, so a later step never reaches
`(block, stmtIdx) = (0, 0)` again. -/
def stepMirCore (body : MirBody) (st : MirState) : StepOutcome :=
  match st with
  | ⟨locals, localGens, block, stmtIdx⟩ =>
    match lookupAt body.blocks block with
    | some bb =>
      match lookupAt bb.stmts stmtIdx with
      | some stmt =>
        stepStmt body ⟨locals, localGens, block, stmtIdx⟩ stmt
      | none =>
        if stmtIdx == bb.stmts.length then
          stepTerminator body ⟨locals, localGens, block, stmtIdx⟩ bb.terminator
        else
          .fault
    | none => .fault

/-- Execute up to `fuel` small steps of `body` from state `st` using
`stepMirCore`: `.returned ret` if a `Terminator.return_` produces `ret` within
`fuel` steps, `.fault` if a step faults first, and `.outOfFuel` if neither
happens within `fuel` steps. It never returns `.rejected`; it does not check
admission or entry validity (see `runMirSteps`). -/
def stepMirLoop (body : MirBody) (fuel : Nat) (st : MirState) :
    MirRunOutcome :=
  @Nat.recCompiled (fun _ => MirState → MirRunOutcome)
    (fun _ => .outOfFuel)
    (fun _ ih cur =>
      match stepMirCore body cur with
      | .stepped next => ih next
      | .returned ret => .returned ret
      | .fault => .fault)
    fuel st

/-- Run `body` from the entry state `st` for up to `fuel` small steps. Returns
`.rejected` unless `st` is at the entry point (`st.block == 0 && st.stmtIdx ==
0`), `body` is admissible (`bodyAdmissible`), and `st` is a valid entry state
(`entryStateValid`); otherwise runs `stepMirLoop body fuel st`. This function
is the boundary that establishes admission and entry validity; later steps
use `stepMirCore` directly. -/
def runMirSteps (body : MirBody) (fuel : Nat) (st : MirState) :
    MirRunOutcome :=
  if st.block != 0 || st.stmtIdx != 0 then
    .rejected
  else if !bodyAdmissible body then
    .rejected
  else if !entryStateValid body st then
    .rejected
  else
    stepMirLoop body fuel st

end Trusted
