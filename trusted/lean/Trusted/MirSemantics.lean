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
`stepMir`, and `runMirSteps`) for `Trusted/MirAst.lean`
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

## Semantic invariants

- **Initialization discipline:** Reading any value containing `MirVal.uninit`
  is undefined behavior and transitions to `StepOutcome.fault`.
- **Reference liveness and mutability discipline:** Every reference
  `MirVal.ref mutable gen loc fieldPath` records the storage generation `gen` of
  its referent local `loc` at borrow creation time. `Stmt.storageLive` and
  `Stmt.storageDead` increment `loc`'s generation counter, immediately
  invalidating any outstanding reference to `loc`. Mutating or taking a mutable
  reborrow through a shared reference (`mutable = false`) transitions to
  `StepOutcome.fault`.
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
(`compiler/rustc_middle/src/mir/mod.rs#L202-L270`):

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
together with the terminal `MirState` at `Terminator.return_` so postconditions
can inspect mutated caller-owned referents. -/
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

/-! ## Value validity, type checking, and aggregate field spines -/

/-- True iff `v` and all nested aggregate payloads inside `v` are initialized
(contain no `MirVal.uninit` sub-value)
(`src/behavior-considered-undefined.md#L114-L132`):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory." -/
noncomputable def MirVal.isFullyInit (v : MirVal) : Bool :=
  @MirVal.rec (fun _ => Bool)
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
equals `refGen` (`src/behavior-considered-undefined.md#L120-L125`):
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`." -/
noncomputable def MirVal.isValidInState (localGens : List Nat) (v : MirVal) :
    Bool :=
  @MirVal.rec (fun _ => Bool)
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
would create a dangling reference
(`src/behavior-considered-undefined.md#L120-L125`):
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`."

Caller-owned referent slots at indices `targetLoc.index ≥ localCount` outlive
the returning frame and remain valid. -/
noncomputable def MirVal.refsFrameLocal (localCount : Nat) (v : MirVal) :
    Bool :=
  @MirVal.rec (fun _ => Bool)
    false
    (fun _ => false)
    (fun _ => false)
    false
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail => ihHead || ihTail)
    (fun _ _ loc _ _ => decide (loc.index < localCount))
    v

/-- Check whether runtime value `v` conforms to declared MIR type `ty` under
target pointer bit-width `ptrWidthBits`
(`src/types/numeric.md#L37-L56`, `src/types/boolean.md#L6-L7`,
`src/types/tuple.md#L6-L15`):
> "The unsigned integer types consist of:"
> "Type | Minimum | Maximum"
> "`u8` | 0 | $2^8 - 1$"
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type." -/
noncomputable def checkValMatchesTy (ptrWidthBits : Nat := 64) (ty : MirTy)
    (v : MirVal) : Bool :=
  @MirVal.rec (fun _ => MirTy → Bool)
    (fun _ => false)
    (fun n curTy =>
      match curTy with
      | .usize => decide (n < natPow2 ptrWidthBits)
      | .uint bits => decide (n < natPow2 bits)
      | _ => false)
    (fun _ curTy =>
      match curTy with
      | .bool => true
      | _ => false)
    (fun curTy =>
      match curTy with
      | .unit => true
      | .tuple [] => true
      | _ => false)
    (fun id _ _ curTy =>
      match curTy with
      | .adt id' => id == id'
      | _ => false)
    (fun _ _ ihHead ihTail curTy =>
      match curTy with
      | .tuple (elemTy :: restTys) =>
        ihHead elemTy && ihTail (.tuple restTys)
      | _ => false)
    (fun isMut _ _ _ _ curTy =>
      match curTy with
      | .ref _ => !isMut
      | .refMut _ => isMut
      | _ => false)
    v ty

/-- Check whether storing root value `v` into local slot `locIdx` satisfies
`localTys` (with pointer width `ptrWidthBits`) when `localTys` declares a type
for `locIdx`. -/
noncomputable def checkLocalStoreTy (ptrWidthBits : Nat) (localTys : List MirTy)
    (locIdx : Nat) (v : MirVal) : Bool :=
  match lookupAt localTys locIdx with
  | some ty => checkValMatchesTy ptrWidthBits ty v
  | none => true

/-- Pack a list of field values into a right-nested `.fieldCons` spine
terminated by `.unit`. -/
def packSpine (vals : List MirVal) : MirVal :=
  vals.foldr MirVal.fieldCons MirVal.unit

/-- Extract element `idx` from a right-nested `.fieldCons` spine. -/
def getSpineAt (idx : Nat) (spine : MirVal) : Option MirVal :=
  @Nat.recCompiled (fun _ => MirVal → Option MirVal)
    (fun s =>
      match s with
      | .fieldCons h _ => some h
      | _ => none)
    (fun _ ih s =>
      match s with
      | .fieldCons _ t => ih t
      | _ => none)
    idx spine

/-- Replace element `idx` in a right-nested `.fieldCons` spine with `newVal`.
-/
def setSpineAt (idx : Nat) (newVal : MirVal) (spine : MirVal) : Option MirVal :=
  @Nat.recCompiled (fun _ => MirVal → Option MirVal)
    (fun s =>
      match s with
      | .fieldCons _ t => some (.fieldCons newVal t)
      | _ => none)
    (fun _ ih s =>
      match s with
      | .fieldCons h t =>
        match ih t with
        | some t' => some (.fieldCons h t')
        | none => none
      | _ => none)
    idx spine

/-- Project field `idx` from an aggregate `MirVal` (`.adt` or tuple
`.fieldCons`). -/
def getMirField (idx : Nat) (v : MirVal) : Option MirVal :=
  match v with
  | .adt _ inner => getSpineAt idx inner
  | .fieldCons _ _ => getSpineAt idx v
  | _ => none

/-- Update field `idx` of an aggregate `MirVal` (`.adt` or tuple `.fieldCons`)
to `newVal`. -/
def setMirField (idx : Nat) (newVal : MirVal) (v : MirVal) : Option MirVal :=
  match v with
  | .adt id inner =>
    match setSpineAt idx newVal inner with
    | some inner' => some (.adt id inner')
    | none => none
  | .fieldCons _ _ => setSpineAt idx newVal v
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

/-- True iff field path `p1` and field path `p2` overlap (one is a prefix of
the other). -/
def pathsOverlap (p1 p2 : List Nat) : Bool :=
  p1.foldr
    (fun x ih ys =>
      match ys with
      | [] => true
      | y :: ys' => x == y && ih ys')
    (fun _ => true)
    p2

/-- True iff `v` contains a live reference that conflicts with accessing
`resolved` (`needMut = true` for writes, moves, and mutable borrows;
`needMut = false` for reads and shared borrows)
(`src/behavior-considered-undefined.md#L61-L65`,
`src/behavior-considered-undefined.md#L120-L125`):
> "Breaking the pointer aliasing rules. `Box<T>`, `&mut T` and `&T` follow
> LLVM's scoped `noalias` model, except if the `&T` contains an `UnsafeCell<U>`.
> This means references and boxes must never be 'aliased XOR mutable' at the
> same time."
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`."

Correspondence:
- `curGen == otherGen`: only references whose referent allocation generation is
  still live are checked.
- `otherLoc.index == resolved.targetLoc.index && pathsOverlap otherPath
  resolved.fieldPath`: the candidate reference points to a sub-place of the same
  root local that overlaps `resolved.fieldPath`.
- `decide (resolved.reborrowDepth ≤ otherDepth)`: in a reborrow stack (`p -> r1
  -> r2`), accessing a shallower borrow or the owner (`resolved.reborrowDepth ≤
  otherDepth`) conflicts with and retires deeper child reborrows, whereas
  accessing a child reborrow (`resolved.reborrowDepth > otherDepth`) keeps its
  parent borrow alive.
- `needMut || otherMut`: enforces "aliased XOR mutable" (shared reads conflict
  only with mutable borrows `otherMut = true`, whereas writes/mutable borrows
  `needMut = true` conflict with both shared and mutable borrows). -/
noncomputable def hasConflictingRefInVal (localGens : List Nat)
    (resolved : ResolvedPlace) (needMut : Bool) (v : MirVal) : Bool :=
  @MirVal.rec (fun _ => Bool)
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
        decide (resolved.reborrowDepth ≤ otherDepth) &&
        (needMut || otherMut)
      | none => false)
    v

/-- True iff `st.locals` (outside `resolved.sourceRefSlot`) contains any live
reference that conflicts with accessing `resolved`. -/
noncomputable def hasConflictingActiveBorrow (st : MirState)
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

/-- Retire (invalidate) any reference inside `v` that conflicts with an access
to `resolved` (`needMut = true` for writes, moves, and mutable borrows;
`needMut = false` for reads and shared borrows) by redirecting its target
`LocalId` to `⟨deadLocIdx⟩` (`deadLocIdx = localGens.length`), where
`lookupAt localGens deadLocIdx = none`. Any subsequent dereference, copy, move,
or return of that retired reference therefore fails `MirVal.isValidInState` /
`resolvePlace` and faults, while non-lexical lifetimes (NLL) that never use the
retired reference again succeed (`src/behavior-considered-undefined.md#L61-L65`,
`src/behavior-considered-undefined.md#L120-L125`):
> "Breaking the pointer aliasing rules. `Box<T>`, `&mut T` and `&T` follow
> LLVM's scoped `noalias` model... references and boxes must never be 'aliased
> XOR mutable' at the same time."
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`." -/
noncomputable def invalidateConflictingRefsInVal (resolved : ResolvedPlace)
    (needMut : Bool) (deadLocIdx : Nat) (v : MirVal) : MirVal :=
  @MirVal.rec (fun _ => MirVal)
    .uninit
    (fun n => .int n)
    (fun b => .bool b)
    .unit
    (fun id _ ihInner => .adt id ihInner)
    (fun _ _ ihHead ihTail => .fieldCons ihHead ihTail)
    (fun otherMut otherGen otherLoc otherPath otherDepth =>
      if otherLoc.index == resolved.targetLoc.index &&
         pathsOverlap otherPath resolved.fieldPath &&
         decide (resolved.reborrowDepth ≤ otherDepth) &&
         (needMut || otherMut) then
        .ref otherMut 0 ⟨deadLocIdx⟩ otherPath otherDepth
      else
        .ref otherMut otherGen otherLoc otherPath otherDepth)
    v

/-- Retire all references stored in `st.locals` (outside
`resolved.sourceRefSlot`) that conflict with accessing `resolved` (`needMut =
true` for writes, moves, and mutable borrows; `needMut = false` for reads and
shared borrows), returning `st.locals` unchanged when no conflicting reference
is present so symbolic `MirState.locals` spines never accumulate unforced map
thunks (`src/behavior-considered-undefined.md#L61-L65`,
`src/behavior-considered-undefined.md#L120-L125`). -/
noncomputable def invalidateConflictingRefs (st : MirState)
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

/-- Recursively collect all caller-supplied entry references (`reborrowDepth ==
0`) inside `v` (including references nested inside `.adt` and `.fieldCons`
aggregates), returning `none` if any caller-supplied reference inside `v` is
dangling (its target slot is absent from `localGens` or has a mismatched storage
generation) (`src/behavior-considered-undefined.md#L120-L125`). -/
noncomputable def collectEntryRefsInVal (localGens : List Nat) (v : MirVal) :
    Option (List (Bool × LocalId × List Nat)) :=
  @MirVal.rec (fun _ => Option (List (Bool × LocalId × List Nat)))
    (some [])
    (fun _ => some [])
    (fun _ => some [])
    (some [])
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihHead ihTail =>
      match ihHead, ihTail with
      | some r1, some r2 => some (r1 ++ r2)
      | _, _ => none)
    (fun isMut refGen targetLoc fieldPath depth =>
      if depth == 0 then
        match lookupAt localGens targetLoc.index with
        | some curGen =>
          if curGen == refGen then
            some [(isMut, targetLoc, fieldPath)]
          else
            none
        | none => none
      else
        some [])
    v

/-- True iff `(isMut, targetLoc, fieldPath)` conflicts with any entry reference
in `seen` (overlapping sub-places of the same referent slot with at least one
reference mutable). -/
def conflictsWithAnyEntryRef (isMut : Bool) (targetLoc : LocalId)
    (fieldPath : List Nat) (seen : List (Bool × LocalId × List Nat)) : Bool :=
  seen.foldr
    (fun item ih =>
      match item with
      | (otherMut, otherLoc, otherPath) =>
        if otherLoc.index == targetLoc.index &&
           pathsOverlap otherPath fieldPath &&
           (isMut || otherMut) then
          true
        else
          ih)
    false

/-- True iff no two references in `refs` conflict (`&mut` + `&mut` or `&mut` +
`&` to overlapping sub-places of the same referent slot). -/
def entryRefListExclusive (refs : List (Bool × LocalId × List Nat)) : Bool :=
  match
    refs.foldr
      (fun item (acc : Bool × List (Bool × LocalId × List Nat)) =>
        match item, acc with
        | (isMut, loc, path), (ok, seen) =>
          (ok && !conflictsWithAnyEntryRef isMut loc path seen,
           (isMut, loc, path) :: seen))
      (true, [])
  with
  | (ok, _) => ok

/-- True iff at function entry (`st.block == 0 && st.stmtIdx == 0`) every
caller-supplied reference (`reborrowDepth == 0`, including references nested
inside `.adt` or tuple `.fieldCons` arguments) in `1 .. body.argCount` points
to a live slot with matching generation in `st.localGens`, and no two distinct
caller-supplied reference occurrences alias with at least one side mutable
(`src/behavior-considered-undefined.md#L61-L65`,
`src/behavior-considered-undefined.md#L120-L125`). Intra-function reborrows
assigned into argument locals have `reborrowDepth ≥ 1` and are governed by
`invalidateConflictingRefs`. -/
noncomputable def entryArgsExclusive (body : MirBody) (st : MirState) : Bool :=
  if !(st.block == 0 && st.stmtIdx == 0) then
    true
  else
    let collectedOpt : Option (List (Bool × LocalId × List Nat)) :=
      @Nat.recCompiled
        (fun _ => Option (List (Bool × LocalId × List Nat)))
        (some [])
        (fun k ih =>
          match ih with
          | none => none
          | some prevRefs =>
            let slotIdx := k + 1
            match lookupAt st.locals slotIdx with
            | some (some v) =>
              match collectEntryRefsInVal st.localGens v with
              | some slotRefs => some (prevRefs ++ slotRefs)
              | none => none
            | _ => some prevRefs)
        body.argCount
    match collectedOpt with
    | some allRefs => entryRefListExclusive allRefs
    | none => false

/-- Resolve `place` in state `st` for a function body with `localCount`
in-frame locals (`compiler/rustc_middle/src/mir/syntax.rs#L1168-L1187`,
`compiler/rustc_middle/src/mir/mod.rs#L235-L240`,
`src/behavior-considered-undefined.md#L120-L125`):
> "After borrowck, `Deref` only occurs as the first projection."
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`."

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
          | some (some (.ref mutable refGen targetLoc basePath depth)) =>
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

/-- Read a valid, initialized `MirVal` from `place` in state `st`, retiring any
conflicting deeper mutable borrows in the returned `MirState`. Fails (`none`) if
`place` does not resolve, if the read sub-value is uninitialized, or if the read
sub-value contains a dangling or retired reference. -/
noncomputable def readPlace (localCount : Nat) (st : MirState) (place : Place) :
    Option (MirVal × MirState) :=
  match st with
  | ⟨_, localGens, block, stmtIdx⟩ =>
    match resolvePlace localCount st place with
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

/-- Overwrite a moved-from `place` with `MirVal.uninit` in `st`
(`compiler/rustc_middle/src/mir/syntax.rs#L1318-L1326`):
> "Move: Creates a value by loading the given place. ... This *may* additionally
> overwrite the place with `uninit` bytes"

Retires any conflicting active borrows of `place` and fails (`none`) if `place`
resolves through a shared reference or refers to a dead local slot. -/
noncomputable def deinitPlace (localCount : Nat) (st : MirState)
    (place : Place) : Option MirState :=
  match st with
  | ⟨_, localGens, block, stmtIdx⟩ =>
    match resolvePlace localCount st place with
    | some resolved =>
      match resolved.viaMutRef with
      | some false => none
      | _ =>
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
list. Fails (`none`) if `newVal` is not valid in `st.localGens`, if `place`
resolves through a shared reference (`viaMutRef = some false`), if the target
local slot is dead (`none`), if the updated root value violates `body.localTys`,
or if the target slot or field path does not exist. -/
noncomputable def assignPlace (body : MirBody) (st : MirState) (place : Place)
    (newVal : MirVal) : Option (List (Option MirVal)) :=
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
          let locals1 := invalidateConflictingRefs st resolved true
          match lookupAt locals1 resolved.targetLoc.index with
          | some (some rootVal) =>
            match resolved.fieldPath with
            | [] =>
              if checkLocalStoreTy body.ptrWidthBits body.localTys
                  resolved.targetLoc.index newVal then
                setAt locals1 resolved.targetLoc.index (some newVal)
              else
                none
            | _ =>
              match writeFieldPath resolved.fieldPath newVal rootVal with
              | some rootVal' =>
                if checkLocalStoreTy body.ptrWidthBits body.localTys
                    resolved.targetLoc.index rootVal' then
                  setAt locals1 resolved.targetLoc.index (some rootVal')
                else
                  none
              | none => none
          | _ => none
      | none => none

/-! ## Operand, borrow, and rvalue evaluation -/

/-- Evaluate a MIR `Operand` in state `st`, returning both the loaded `MirVal`
and the updated `MirState` (with `.move src` overwriting `src` with `.uninit`)
(`compiler/rustc_middle/src/mir/syntax.rs#L1303-L1335`). -/
noncomputable def evalOperand (localCount : Nat) (st : MirState)
    (op : Operand) : Option (MirVal × MirState) :=
  match op with
  | .copy src => readPlace localCount st src
  | .move src =>
    match readPlace localCount st src with
    | some (v, st1) =>
      match deinitPlace localCount st1 src with
      | some st2 => some (v, st2)
      | none => none
    | none => none
  | .constVal val =>
    if val.isValidInState st.localGens then some (val, st) else none

/-- Evaluate a list of operands in left-to-right order, threading state updates
from `Operand.move` and succeeding iff every operand evaluates to a valid,
initialized `MirVal`. -/
noncomputable def evalOperandList (localCount : Nat) (st : MirState)
    (ops : List Operand) : Option (List MirVal × MirState) :=
  ops.foldr
    (fun op ih curSt =>
      match evalOperand localCount curSt op with
      | some (v, nextSt) =>
        match ih nextSt with
        | some (vs, finalSt) => some (v :: vs, finalSt)
        | none => none
      | none => none)
    (fun curSt => some ([], curSt))
    st

/-- Create a shared (`mutable = false`) or mutable (`mutable = true`) reference
to `src` in state `st`, retiring any conflicting deeper borrows in the returned
`MirState` (`compiler/rustc_middle/src/mir/syntax.rs#L1408-L1416`):
> "`Ref` creates a reference of the indicated kind to the place."

Fails (`none`) if `src` does not currently hold a valid, initialized value or if
a mutable borrow is requested through a shared reference. -/
noncomputable def evalBorrow (localCount : Nat) (st : MirState) (mutable : Bool)
    (src : Place) : Option (MirVal × MirState) :=
  match resolvePlace localCount st src, readPlace localCount st src with
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

/-- Evaluate a binary operation `BinOp` on two initialized `MirVal`s, using
logarithmic bitwise operations (`Nat.land`, `Nat.lor`, `Nat.xor`) from
`Init.Data.Nat.Bitwise.Basic`
(`compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709`,
`src/expressions/operator-expr.md#L106-L157`):
> "pub enum BinOp { Add, ... Sub, ... Mul, ... BitXor, BitAnd, BitOr, ... Eq,
> Lt, Le, Ne, Ge, Gt, ... }"
> "Arithmetic and Logical Binary Operators: `+` Addition, `-` Subtraction,
> `*` Multiplication, `&` Bitwise AND, `|` Bitwise OR, `^` Bitwise XOR."

Correspondence:
- When `intWidthOpt = some bits` (inferred from `body.localTys`), `.add`,
  `.sub`, and `.mul` model `Runtime(PostCleanup)` wrapping unsigned arithmetic
  modulo $2^{\text{bits}}$ (`(a + b) % 2^bits`, `(a + 2^bits - (b % 2^bits)) %
  2^bits`, and `(a * b) % 2^bits`). When `intWidthOpt = none` (untyped symbolic
  `MirBody`s with `localTys = []`), `.add`, `.sub`, and `.mul` operate on
  unbounded `Nat` (with `b ≤ a` on `.sub`).
- `.eq`, `.ne`, `.lt`, `.le`, `.gt`, and `.ge` model equality and relational
  comparisons on `MirVal.int`, `MirVal.bool`, and `MirVal.unit`.
- `.bitAnd`, `.bitOr`, and `.bitXor` model bitwise AND, OR, and XOR on
  `MirVal.int` and `MirVal.bool`. -/
def evalBinOp (op : BinOp) (lhs rhs : MirVal)
    (intWidthOpt : Option Nat := none) : Option MirVal :=
  match op, lhs, rhs with
  | .add, .int a, .int b =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none else some (.int (Nat.mod (a + b) modulus))
    | none => some (.int (a + b))
  | .sub, .int a, .int b =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none
      else some (.int (Nat.mod (a + modulus - Nat.mod b modulus) modulus))
    | none =>
      if decide (b ≤ a) then some (.int (a - b)) else none
  | .mul, .int a, .int b =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if modulus == 0 then none else some (.int (Nat.mod (a * b) modulus))
    | none => some (.int (a * b))
  | .eq, .int a, .int b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | .ne, .int a, .int b => some (.bool (decide (a ≠ b)))
  | .ne, .bool a, .bool b => some (.bool (decide (a ≠ b)))
  | .ne, .unit, .unit => some (.bool false)
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .lt, .bool a, .bool b => some (.bool (!a && b))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .le, .bool a, .bool b => some (.bool (!a || b))
  | .gt, .int a, .int b => some (.bool (decide (b < a)))
  | .gt, .bool a, .bool b => some (.bool (a && !b))
  | .ge, .int a, .int b => some (.bool (decide (b ≤ a)))
  | .ge, .bool a, .bool b => some (.bool (a || !b))
  | .bitAnd, .int a, .int b => some (.int (Nat.land a b))
  | .bitOr, .int a, .int b => some (.int (Nat.lor a b))
  | .bitXor, .int a, .int b => some (.int (Nat.xor a b))
  | .bitAnd, .bool a, .bool b => some (.bool (a && b))
  | .bitOr, .bool a, .bool b => some (.bool (a || b))
  | .bitXor, .bool a, .bool b => some (.bool (bne a b))
  | _, _, _ => none

/-- Bit-width of an unsigned integer `MirTy` (`ptrWidthBits` for `.usize`,
`bits` for `.uint bits`)
(`src/types/numeric.md#L37-L56`). -/
def tyBitWidth (ptrWidthBits : Nat := 64) : MirTy → Option Nat
  | .usize => some ptrWidthBits
  | .uint bits => some bits
  | _ => none

/-- Project a `PlaceElem` path through a declared `MirTy` (`Deref` unwraps
`.ref` and `.refMut`; `Field idx` indexes into `.tuple elems`). -/
def projectPlaceTy (projs : List PlaceElem) (ty : MirTy) : Option MirTy :=
  projs.foldr
    (fun proj ih curTy =>
      match proj, curTy with
      | .deref, .ref inner => ih inner
      | .deref, .refMut inner => ih inner
      | .field idx, .tuple elems =>
        match lookupAt elems idx with
        | some elemTy => ih elemTy
        | none => none
      | _, _ => none)
    (fun curTy => some curTy)
    ty

/-- Project a resolved field-index path `fieldPath` through a declared `MirTy`
(indexing into `.tuple elems` at each step). -/
def projectFieldPathTy (fieldPath : List Nat) (ty : MirTy) : Option MirTy :=
  fieldPath.foldr
    (fun idx ih curTy =>
      match curTy with
      | .tuple elems =>
        match lookupAt elems idx with
        | some elemTy => ih elemTy
        | none => none
      | _ => none)
    (fun curTy => some curTy)
    ty

/-- Resolve the declared integer bit-width of `p : Place` from `body.localTys`
and `body.ptrWidthBits` (projecting `p.projection` through the syntactic local's
declared type first, and falling back to projecting `res.fieldPath` through the
resolved target local's declared type). -/
def inferPlaceIntWidth (body : MirBody) (st : MirState)
    (p : Place) : Option Nat :=
  let syntacticWidthOpt : Option Nat :=
    match lookupAt body.localTys p.loc.index with
    | some baseTy =>
      match projectPlaceTy p.projection baseTy with
      | some leafTy => tyBitWidth body.ptrWidthBits leafTy
      | none => none
    | none => none
  match syntacticWidthOpt with
  | some w => some w
  | none =>
    match resolvePlace body.localCount st p with
    | some res =>
      match lookupAt body.localTys res.targetLoc.index with
      | some rootTy =>
        match projectFieldPathTy res.fieldPath rootTy with
        | some leafTy => tyBitWidth body.ptrWidthBits leafTy
        | none => none
      | none => none
    | none => none

/-- Infer the declared integer bit-width of an `Operand` from `body.localTys`
and `body.ptrWidthBits`. -/
def inferOperandIntWidth (body : MirBody) (st : MirState)
    (src : Operand) : Option Nat :=
  match src with
  | .copy p | .move p => inferPlaceIntWidth body st p
  | .constVal _ => none

/-- Infer the declared integer bit-width of destination `dst` from
`body.localTys` and `body.ptrWidthBits`. -/
def inferDestIntWidth (body : MirBody) (st : MirState)
    (dst : Place) : Option Nat :=
  inferPlaceIntWidth body st dst

/-- Infer the declared integer bit-width for `Rvalue.unaryOp op src` assigned to
`dst` from `body.localTys` (checking the operand place first and falling back
to `dst`). -/
def inferUnOpIntWidth (body : MirBody) (st : MirState) (dst : Place)
    (src : Operand) : Option Nat :=
  match inferOperandIntWidth body st src with
  | some w => some w
  | none => inferDestIntWidth body st dst

/-- Infer the declared integer bit-width for `Rvalue.binaryOp op lhs rhs`
assigned to `dst` from `body.localTys` (checking `lhs`, then `rhs`, then
`dst`). -/
def inferBinOpIntWidth (body : MirBody) (st : MirState) (dst : Place)
    (lhs rhs : Operand) : Option Nat :=
  match inferOperandIntWidth body st lhs with
  | some w => some w
  | none =>
    match inferOperandIntWidth body st rhs with
    | some w => some w
    | none => inferDestIntWidth body st dst

/-- Evaluate a unary operation `UnOp` on an initialized `MirVal`
(`compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617`,
`src/expressions/operator-expr.md#L166-L180`):
> "pub enum UnOp {
>     /// The `!` operator for logical inversion
>     Not,
>     /// The `-` operator for negation
>     Neg,
>     /// Knows the offset of a slice's metadata (length).
>     PtrMetadata,
> }"
> "The negation operator `!` inverts the individual bits of an integer operand
> or the truth value of a boolean operand."

Correspondence:
- On `.bool b`, `.not` evaluates the truth-value inversion `!b`.
- On `.int a`, `.not` evaluates the width-masked bitwise complement
  `(2^bits - 1) - a` when the operand or destination place declares an unsigned
  integer bit-width `bits` (`usize` or `uint bits`) and `a < 2^bits`. -/
def evalUnOp (op : UnOp) (intWidthOpt : Option Nat) (v : MirVal) :
    Option MirVal :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | .not, .int a =>
    match intWidthOpt with
    | some bits =>
      let modulus := natPow2 bits
      if decide (a < modulus) then
        some (.int ((modulus - 1) - a))
      else
        none
    | none => none
  | _, _ => none

/-- Evaluate a MIR `Rvalue` in state `st` for assignment into `dst`, returning
both the computed `MirVal` and the post-rvalue `MirState`
(`compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488`). -/
noncomputable def evalRvalue (body : MirBody) (dst : Place) (st : MirState)
    (rv : Rvalue) : Option (MirVal × MirState) :=
  match rv with
  | .use op => evalOperand body.localCount st op
  | .ref src => evalBorrow body.localCount st false src
  | .refMut src => evalBorrow body.localCount st true src
  | .binaryOp op lhs rhs =>
    let widthOpt := inferBinOpIntWidth body st dst lhs rhs
    match evalOperand body.localCount st lhs with
    | some (v1, st1) =>
      match evalOperand body.localCount st1 rhs with
      | some (v2, st2) =>
        match evalBinOp op v1 v2 widthOpt with
        | some res => some (res, st2)
        | none => none
      | none => none
    | none => none
  | .unaryOp op src =>
    let widthOpt := inferUnOpIntWidth body st dst src
    match evalOperand body.localCount st src with
    | some (v, st1) =>
      match evalUnOp op widthOpt v with
      | some res => some (res, st1)
      | none => none
    | none => none
  | .aggregateFields ops adtIdOpt =>
    match evalOperandList body.localCount st ops with
    | some (vs, st1) =>
      let spine := packSpine vs
      match adtIdOpt with
      | some id => some (.adt id spine, st1)
      | none => some (spine, st1)
    | none => none
  | .copyForDeref src => readPlace body.localCount st src

/-! ## Small-step statement, terminator, and body execution -/

/-- Execute a single MIR `Stmt` in `body` from state `st`
(`compiler/rustc_middle/src/mir/syntax.rs#L397-L466`):
- `.assign dst rv`: evaluates `rv` and stores the result into `dst`.
- `.storageLive loc` / `.storageDead loc`: marks `loc` live (initialized to
  `.uninit`) or dead (`none`) and increments `loc`'s storage generation counter.
- `.placeMention src` (`StatementKind::PlaceMention`,
  `compiler/rustc_middle/src/mir/syntax.rs#L439-L448`):
  > "`PlaceMention` executes a place-expression without loading from the
  > resulting place. This is used for `let _ = place;`."
  Validates that `src` resolves to a live storage slot without requiring the
  pointee value to be initialized.
- `.nop`: advances `stmtIdx` without modifying locals or generations. -/
noncomputable def stepStmt (body : MirBody) (st : MirState)
    (stmt : Stmt) : StepOutcome :=
  match st with
  | ⟨locals, localGens, block, stmtIdx⟩ =>
    match stmt with
    | .assign dst rv =>
      match evalRvalue body dst ⟨locals, localGens, block, stmtIdx⟩ rv with
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
        match lookupAt localGens loc.index with
        | some g =>
          match setAt locals loc.index none,
                setAt localGens loc.index (g + 1) with
          | some locals', some gens' =>
            .stepped ⟨locals', gens', block, stmtIdx + 1⟩
          | _, _ => .fault
        | none => .fault
      else
        .fault
    | .placeMention src =>
      match resolvePlace body.localCount ⟨locals, localGens, block, stmtIdx⟩
          src with
      | some resolved =>
        match lookupAt locals resolved.targetLoc.index with
        | some (some _) => .stepped ⟨locals, localGens, block, stmtIdx + 1⟩
        | _ => .fault
      | none => .fault
    | .nop => .stepped ⟨locals, localGens, block, stmtIdx + 1⟩

/-- Select the target `BlockId` in `targets` matching integer value `discrVal`
(`compiler/rustc_middle/src/mir/terminator.rs#L30-L56`). -/
def findSwitchTarget (targets : SwitchTargets) (discrVal : Nat) : BlockId :=
  targets.branches.foldr
    (fun br acc => if br.val == discrVal then br.target else acc)
    targets.otherwise

/-- Convert an integer or boolean discriminant `MirVal` into its `SwitchInt`
scalar value (`false ↦ 0`, `true ↦ 1`, `.int n ↦ n`)
(`compiler/rustc_middle/src/mir/syntax.rs#L708-L725`). -/
def evalSwitchDiscr (v : MirVal) : Option Nat :=
  match v with
  | .int n => some n
  | .bool false => some 0
  | .bool true => some 1
  | _ => none

/-- Execute a single MIR `Terminator` in `body` from state `st`
(`compiler/rustc_middle/src/mir/syntax.rs#L684-L798`):
- `.return_` (`TerminatorKind::Return`,
  `compiler/rustc_middle/src/mir/syntax.rs#L727-L731`):
  > "Normal return from the function. The return value is read from the return
  > place `_0`."
  Loads local `_0`, verifies that `retVal.isValidInState localGens` holds (fully
  initialized and containing no dangling references), and terminates with
  `.returned ⟨retVal, st⟩`.
- `.goto target` (`TerminatorKind::Goto`,
  `compiler/rustc_middle/src/mir/syntax.rs#L687-L690`):
  > "Block should have one successor in the graph; we jump there."
  Checks `target.index < body.blocks.length` and transitions to statement `0` of
  `target`.
- `.switchInt discr targets` (`TerminatorKind::SwitchInt`,
  `compiler/rustc_middle/src/mir/syntax.rs#L708-L725`):
  > "Evaluates `discr` and jumps to the target block corresponding to the
  > resulting integer/boolean value, or `otherwise` if no value matches."
  Evaluates `discr`, maps booleans (`false ↦ 0`, `true ↦ 1`) and integers to
  their scalar value via `evalSwitchDiscr`, selects the matching successor in
  `targets` via `findSwitchTarget`, and transitions to statement `0` of that
  block if in bounds.
- `.unreachable` (`TerminatorKind::Unreachable`,
  `compiler/rustc_middle/src/mir/syntax.rs#L733-L736`):
  > "Indicates a block that can never be reached; reaching it is UB."
  Transitions immediately to `StepOutcome.fault`. -/
noncomputable def stepTerminator (body : MirBody) (st : MirState)
    (term : Terminator) : StepOutcome :=
  match st with
  | ⟨locals, localGens, block, stmtIdx⟩ =>
    match term with
    | .return_ =>
      match lookupAt locals 0 with
      | some (some retVal) =>
        if retVal.isValidInState localGens &&
           !retVal.refsFrameLocal body.localCount then
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
      match evalOperand body.localCount ⟨locals, localGens, block, stmtIdx⟩
          discr with
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

/-- Perform one small-step operational transition of `body` from `st`:
verifies `entryArgsExclusive body st` and then, if `st.stmtIdx` indexes a
statement in the current basic block, executes that statement; if `st.stmtIdx`
equals the statement count of the current basic block, executes its terminator.
-/
noncomputable def stepMir (body : MirBody) (st : MirState) : StepOutcome :=
  if !entryArgsExclusive body st then
    .fault
  else
    match st with
    | ⟨locals, localGens, block, stmtIdx⟩ =>
      match lookupAt body.blocks block with
      | some bb =>
        match lookupAt bb.stmts stmtIdx with
        | some stmt =>
          stepStmt body ⟨locals, localGens, block, stmtIdx⟩ stmt
        | none =>
          if stmtIdx == bb.stmts.length then
            stepTerminator body ⟨locals, localGens, block, stmtIdx⟩
              bb.terminator
          else
            .fault
      | none => .fault

/-- Execute up to `fuel` small steps of `body` starting from `st`, returning
`some ret` if `body` reaches `Terminator.return_` within `fuel` steps without
faulting. -/
noncomputable def runMirSteps (body : MirBody) (fuel : Nat) (st : MirState) :
    Option MirReturn :=
  @Nat.recCompiled (fun _ => MirState → Option MirReturn)
    (fun _ => none)
    (fun _ ih cur =>
      match stepMir body cur with
      | .stepped next => ih next
      | .returned ret => some ret
      | .fault => none)
    fuel st

end Trusted
