import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Tree Borrows tag lookup and invalidation, global allocation byte reads, place
projection traversal (`readProjectedValue`, `writeProjectedValue`), operand
evaluation (`evalOperand`, `evalOperands`), place writes (`writePlaceValue`),
and right-hand-side `Rvalue` evaluation (`evalRvalue`) for
`Runtime(PostCleanup)` MIR at `rustc 1.98.0-nightly (14210df0e 2026-05-31)`
(`#88`, `#100`, `#102`).

Reference (The Rust Reference, "Place expressions and value expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions.html#place-expressions-and-value-expressions>

> "A place expression is an expression that represents a memory location.
> These expressions are paths which refer to local variables, static
> variables, dereferences (*expr), array indexing expressions (expr[expr]),
> field references (expr.f) and parenthesized place expressions."
-/

/--
Definitional simplification equation for `tyIsSigned`.
-/
@[simp]
theorem tyIsSigned_eq (ty : Ty) :
    tyIsSigned ty =
      (match ty.kind with
      | .int _ => true
      | _ => false) := rfl

/--
Definitional simplification equation for `resolveProjectedTy` on the empty
projection list.
-/
@[simp]
theorem resolveProjectedTy_nil (layouts : LayoutTable) (baseTy : Ty) :
    resolveProjectedTy layouts baseTy .nil = .some baseTy := rfl

/--
Definitional simplification equation for `resolveProjectedTy` on a `.field`
projection.
-/
@[simp]
theorem resolveProjectedTy_field
    (layouts : LayoutTable)
    (baseTy : Ty)
    (idx : FieldIdx)
    (fieldTy : Ty)
    (rest : List ProjectionElem) :
    resolveProjectedTy layouts baseTy (.field idx fieldTy :: rest) =
      resolveProjectedTy layouts fieldTy rest := rfl

/--
Definitional simplification equation for `resolveProjectedTy` on a `.deref`
projection.
-/
@[simp]
theorem resolveProjectedTy_deref
    (layouts : LayoutTable)
    (baseTy : Ty)
    (rest : List ProjectionElem) :
    resolveProjectedTy layouts baseTy (.deref :: rest) =
      (match pointeeTyOf baseTy with
      | .some innerTy => resolveProjectedTy layouts innerTy rest
      | .none => .none) := rfl

/--
Definitional simplification equation for `resolveProjectedTy` on an `.index`
projection.
-/
@[simp]
theorem resolveProjectedTy_index
    (layouts : LayoutTable)
    (baseTy : Ty)
    (idxLocal : Local)
    (rest : List ProjectionElem) :
    resolveProjectedTy layouts baseTy (.index idxLocal :: rest) =
      (match elemTyOf baseTy with
      | .some elemTy => resolveProjectedTy layouts elemTy rest
      | .none => .none) := rfl

/--
Definitional simplification equation for `resolveProjectedTy` on a
`.constantIndex` projection.
-/
@[simp]
theorem resolveProjectedTy_constantIndex
    (layouts : LayoutTable)
    (baseTy : Ty)
    (offset minLen : Nat)
    (fromEnd : Bool)
    (rest : List ProjectionElem) :
    resolveProjectedTy layouts baseTy
      (.constantIndex offset minLen fromEnd :: rest) =
      (match elemTyOf baseTy with
      | .some elemTy => resolveProjectedTy layouts elemTy rest
      | .none => .none) := rfl

/--
Definitional simplification equation for `placeTy`.
-/
@[simp]
theorem placeTy_eq
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place) :
    placeTy localDecls layouts p =
      (match get? localDecls p.local_ with
      | .some decl => resolveProjectedTy layouts decl.ty p.projection
      | .none => .none) := rfl

/--
Definitional simplification equation for `operandTy`.
-/
@[simp]
theorem operandTy_eq
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    operandTy localDecls layouts op =
      (match op with
      | .copy p => placeTy localDecls layouts p
      | .move p => placeTy localDecls layouts p
      | .constant c => .some c.ty) := rfl

/--
Definitional simplification equation for `placeIsSigned`.
-/
@[simp]
theorem placeIsSigned_eq
    (localDecls : List LocalDecl)
    (p : Place)
    (layouts : LayoutTable) :
    placeIsSigned localDecls p layouts =
      (match placeTy localDecls layouts p with
      | .some ty => tyIsSigned ty
      | .none => false) := rfl

/--
Definitional simplification equation for `operandIsSigned`.
-/
@[simp]
theorem operandIsSigned_eq
    (localDecls : List LocalDecl)
    (op : Operand)
    (layouts : LayoutTable) :
    operandIsSigned localDecls op layouts =
      (match operandTy localDecls layouts op with
      | .some ty => tyIsSigned ty
      | .none => false) := rfl

/--
Definitional simplification equation for `appendProjections` on the empty
projection list.
-/
@[simp]
theorem appendProjections_nil_left (ys : List ProjectionElem) :
    appendProjections .nil ys = ys := rfl

/--
Definitional simplification equation for `appendProjections` on a non-empty
projection list.
-/
@[simp]
theorem appendProjections_cons
    (x : ProjectionElem)
    (xs ys : List ProjectionElem) :
    appendProjections (x :: xs) ys = x :: appendProjections xs ys := rfl

/--
Look up the `BorrowEntry` with provenance tag `tag` in `borrows`.
-/
def lookupBorrow : List BorrowEntry → Nat → Option BorrowEntry
  | .nil, _ => .none
  | entry :: rest, tag =>
    match Nat.beq entry.tag tag with
    | true => .some entry
    | false => lookupBorrow rest tag

/--
Strip transparent metadata projections (`.opaqueCast` and
`.unwrapUnsafeBinder`) from a `ProjectionElem` path before comparing sub-place
aliasing overlap.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1268-L1278>

> "/// Like an explicit cast from an opaque type to a concrete type, but without
> /// requiring an intermediate variable.
> OpaqueCast(T),
>
> /// Unwrap an unsafe binder, i.e. `unsafe<'a> T -> T`.
> UnwrapUnsafeBinder(T),"
-/
def stripTransparentProjections : List ProjectionElem → List ProjectionElem
  | .nil => .nil
  | .opaqueCast _ :: rest => stripTransparentProjections rest
  | .unwrapUnsafeBinder _ :: rest => stripTransparentProjections rest
  | elem :: rest => elem :: stripTransparentProjections rest

/--
Test whether two transparent-stripped projection paths within the same root
local overlap.

- If either list is `.nil`, one projection is a prefix of the other, so they
  overlap (`true`).
- Distinct `.field` indices (`idxA != idxB`), distinct `.constantIndex` offsets
  with matching `fromEnd` polarity, and distinct `.downcast` enum variants are
  disjoint (`false`).
- Otherwise returns `true` (conservative overlap).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1267>

> "pub enum ProjectionElem<V, T> {
>     Deref,
>
>     /// A field (e.g., `f` in `_1.f`) is one variant of [`ProjectionElem`]. Conceptually,
>     /// rustc can identify that a field projection refers to either two different regions of memory
>     /// or the same one between base and projectedmir type.
>     /// Reading from or writing to the projected place reads or writes the subset of bytes of the
>     /// base place described by the layout of the base place's type (adjusted by active
>     /// `Downcast` projection if any).
>     Field(FieldIdx, T),"
-/
def projectionsOverlapAux : List ProjectionElem → List ProjectionElem → Bool
  | .nil, _ => true
  | _, .nil => true
  | .field idxA _ :: restA, .field idxB _ :: restB =>
    match Nat.beq idxA idxB with
    | true => projectionsOverlapAux restA restB
    | false => false
  | .constantIndex offA _ fromEndA :: restA,
    .constantIndex offB _ fromEndB :: restB =>
    let sameFromEnd :=
      match fromEndA, fromEndB with
      | true, true => true
      | false, false => true
      | _, _ => false
    match sameFromEnd with
    | true =>
      match Nat.beq offA offB with
      | true => projectionsOverlapAux restA restB
      | false => false
    | false => projectionsOverlapAux restA restB
  | .downcast _ varA :: restA, .downcast _ varB :: restB =>
    match Nat.beq varA varB with
    | true => projectionsOverlapAux restA restB
    | false => false
  | _ :: _, _ :: _ => true

/--
Test whether two projection paths within the same root local overlap after
stripping transparent `.opaqueCast` and `.unwrapUnsafeBinder` projections.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1278>

> "/// A field (e.g., `f` in `_1.f`) is one variant of [`ProjectionElem`]. Conceptually,
> /// rustc can identify that a field projection refers to either two different regions of memory
> /// or the same one between base and projectedmir type."
-/
def projectionsOverlap (projA projB : List ProjectionElem) : Bool :=
  projectionsOverlapAux
    (stripTransparentProjections projA)
    (stripTransparentProjections projB)

/--
Test whether two half-open byte ranges `[offA, offA + lenA)` and
`[offB, offB + lenB)` within the same allocation overlap (`lenA > 0`, `lenB > 0`,
`offA < offB + lenB`, and `offB < offA + lenA`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def byteRangesOverlapBool (offA lenA offB lenB : Nat) : Bool :=
  Bool.and
    (Bool.not (Nat.beq lenA 0))
    (Bool.and
      (Bool.not (Nat.beq lenB 0))
      (Bool.and
        (Nat.ble (.succ offA) (Nat.add offB lenB))
        (Nat.ble (.succ offB) (Nat.add offA lenA))))

/--
Test whether a `BorrowEntry` overlaps a write at projection `writeProj` and
optional byte range `[writeRangeOff, writeRangeOff + writeRangeLen)`.

When both `entry.rangeLen > 0` and `writeRangeLen > 0`, overlap is determined by
`byteRangesOverlapBool entry.rangeOffset entry.rangeLen writeRangeOff
writeRangeLen`; otherwise it is determined by
`projectionsOverlap entry.targetProjection writeProj`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def borrowEntryOverlapsWrite
    (entry : BorrowEntry)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) :
    Bool :=
  match
    Bool.and
      (Bool.not (Nat.beq writeRangeLen 0))
      (Bool.not (Nat.beq entry.rangeLen 0))
  with
  | true =>
    byteRangesOverlapBool
      entry.rangeOffset
      entry.rangeLen
      writeRangeOff
      writeRangeLen
  | false =>
    projectionsOverlap entry.targetProjection writeProj

/--
Check whether natural number `x` occurs in `xs` using `Init.Core` `Nat.beq`.
-/
def natListContainsBool : List Nat → Nat → Bool
  | .nil, _ => false
  | y :: ys, x =>
    match Nat.beq y x with
    | true => true
    | false => natListContainsBool ys x

/--
Test whether `entry` carries a function-entry lifetime protector identifier
(`RetagKind.fnEntry`) that is currently active in `activeProtectors`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L287>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,
>     /// Retagging for a two-phase borrow.
>     TwoPhase,
>     /// Retagging raw pointers.
>     Raw,
>     /// Normal retagging of references.
>     Default,
> }"
-/
def isBorrowProtected
    (activeProtectors : List Nat)
    (entry : BorrowEntry) :
    Bool :=
  match entry.protector with
  | .some protId => natListContainsBool activeProtectors protId
  | .none => false

/--
Test whether a write with `writerTag` would disable `entry`'s Tree Borrows
permission if their regions overlap.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def borrowEntryWriteConflicts
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    Bool :=
  match writerTag with
  | .none =>
    match entry.perm with
    | .active => true
    | .frozen => true
    | .reserved => false
    | .disabled => false
  | .some tag =>
    match Nat.beq entry.tag tag with
    | true => false
    | false =>
      match entry.perm with
      | .disabled => false
      | _ => true

/--
Test whether any `BorrowEntry` in `borrows` targeting `targetLocal` at an
overlapping sub-place or byte range is currently protected by `activeProtectors`
and would be disabled by a write with `writerTag`.

Under Tree Borrows, disabling a borrow whose function-entry protector is still
active is immediate undefined behavior.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def hasProtectedWriteConflict
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem := .nil)
    (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) :
    Bool :=
  match borrows with
  | .nil => false
  | entry :: rest =>
    let thisConflict :=
      Bool.and
        (Nat.beq entry.targetLocal targetLocal)
        (Bool.and
          (borrowEntryOverlapsWrite
            entry
            writeProj
            writeRangeOff
            writeRangeLen)
          (Bool.and
            (isBorrowProtected activeProtectors entry)
            (borrowEntryWriteConflicts entry writerTag)))
    match thisConflict with
    | true => true
    | false =>
      hasProtectedWriteConflict
        rest
        activeProtectors
        targetLocal
        writerTag
        writeProj
        writeRangeOff
        writeRangeLen

/--
Attach function-entry lifetime protector `protId` to the `BorrowEntry` with
provenance tag `tag` in `borrows`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L279>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,"
-/
def attachBorrowProtector :
    List BorrowEntry → Nat → Nat → List BorrowEntry
  | .nil, _, _ => .nil
  | entry :: rest, tag, protId =>
    match Nat.beq entry.tag tag with
    | true =>
      { entry with protector := .some protId } ::
        attachBorrowProtector rest tag protId
    | false =>
      entry :: attachBorrowProtector rest tag protId

/--
Update the Tree Borrows permission of a single `BorrowEntry` when `targetLocal`
is mutated either directly (`writerTag = .none`) or through a pointer with
provenance tag `writerTag = .some tag`.

- When `writerTag = .none` (direct write to `targetLocal` not through a
  pointer): every entry targeting `targetLocal` with permission `.active` or
  `.frozen` transitions to `.disabled`, whereas `.reserved` borrows tolerate
  parent writes until activated.
- When `writerTag = .some tag` (write through pointer with tag `tag`): the entry
  with `entry.tag == tag` transitions `.reserved -> .active` (or stays
  `.active`), and any other entry (`entry.tag != tag`) targeting `targetLocal`
  transitions to `.disabled`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def updateBorrowPerm
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat) :
    BorrowEntry :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => entry
  | true =>
    match writerTag with
    | .none =>
      match entry.perm with
      | .active => { entry with perm := .disabled }
      | .frozen => { entry with perm := .disabled }
      | .reserved => entry
      | .disabled => entry
    | .some tag =>
      match Nat.beq entry.tag tag with
      | true =>
        match entry.perm with
        | .reserved => { entry with perm := .active }
        | _ => entry
      | false => { entry with perm := .disabled }

/--
Definitional simplification equation for `updateBorrowPerm`.
-/
@[simp]
theorem updateBorrowPerm_eq
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat) :
    updateBorrowPerm entry targetLocal writerTag =
      (match Nat.beq entry.targetLocal targetLocal with
      | false => entry
      | true =>
        match writerTag with
        | .none =>
          match entry.perm with
          | .active => { entry with perm := .disabled }
          | .frozen => { entry with perm := .disabled }
          | .reserved => entry
          | .disabled => entry
        | .some tag =>
          match Nat.beq entry.tag tag with
          | true =>
            match entry.perm with
            | .reserved => { entry with perm := .active }
            | _ => entry
          | false => { entry with perm := .disabled }) := rfl

/--
Transition all `BorrowEntry` records in `borrows` affected by a write to
`targetLocal` (either directly when `writerTag = .none`, or through pointer tag
`tag` when `writerTag = .some tag`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def invalidateConflictingBorrows :
    List BorrowEntry → Local → Option Nat → List BorrowEntry
  | .nil, _, _ => .nil
  | entry :: rest, targetLocal, writerTag =>
    updateBorrowPerm entry targetLocal writerTag ::
      invalidateConflictingBorrows rest targetLocal writerTag

/--
Definitional simplification equation for `invalidateConflictingBorrows` on the
empty borrow list.
-/
@[simp]
theorem invalidateConflictingBorrows_nil
    (targetLocal : Local)
    (writerTag : Option Nat) :
    invalidateConflictingBorrows .nil targetLocal writerTag = .nil := rfl

/--
Definitional simplification equation for `invalidateConflictingBorrows` on a
non-empty borrow list.
-/
@[simp]
theorem invalidateConflictingBorrows_cons
    (entry : BorrowEntry)
    (rest : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat) :
    invalidateConflictingBorrows (entry :: rest) targetLocal writerTag =
      updateBorrowPerm entry targetLocal writerTag ::
        invalidateConflictingBorrows rest targetLocal writerTag := rfl

/--
Projection- and byte-range-sensitive Tree Borrows permission transition for a
single `BorrowEntry` when `targetLocal` is mutated at projection `writeProj`
(and optional byte range `[writeRangeOff, writeRangeOff + writeRangeLen)`).

Borrows targeting disjoint struct/tuple fields, array elements, or byte ranges
within the same root local `targetLocal` (`borrowEntryOverlapsWrite = false`)
are preserved without invalidation.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def updateBorrowPermAtProj
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) :
    BorrowEntry :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => entry
  | true =>
    match writerTag with
    | .none =>
      match
        borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen
      with
      | false => entry
      | true =>
        match entry.perm with
        | .active => { entry with perm := .disabled }
        | .frozen => { entry with perm := .disabled }
        | .reserved => entry
        | .disabled => entry
    | .some tag =>
      match Nat.beq entry.tag tag with
      | true =>
        match entry.perm with
        | .reserved => { entry with perm := .active }
        | _ => entry
      | false =>
        match
          borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen
        with
        | false => entry
        | true => { entry with perm := .disabled }

/--
When `writeProj = .nil` and `entry.targetProjection = .nil` (with default
unranged write `writeRangeLen = 0`), `updateBorrowPermAtProj` reduces
definitionally to `updateBorrowPerm`.
-/
@[simp]
theorem updateBorrowPermAtProj_nil_eq_updateBorrowPerm
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (h_proj : entry.targetProjection = .nil) :
    updateBorrowPermAtProj entry targetLocal writerTag .nil =
      updateBorrowPerm entry targetLocal writerTag := by
  unfold updateBorrowPermAtProj updateBorrowPerm borrowEntryOverlapsWrite
  rw [h_proj]
  rfl

/--
Transition all `BorrowEntry` records in `borrows` affected by a write to
`targetLocal` at projection `writeProj` (and optional byte range
`[writeRangeOff, writeRangeOff + writeRangeLen)`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def invalidateConflictingBorrowsAtProj
    (borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    updateBorrowPermAtProj
      entry
      targetLocal
      writerTag
      writeProj
      writeRangeOff
      writeRangeLen ::
      invalidateConflictingBorrowsAtProj
        rest
        targetLocal
        writerTag
        writeProj
        writeRangeOff
        writeRangeLen

/--
Definitional simplification equation for `invalidateConflictingBorrowsAtProj` on
the empty borrow list.
-/
@[simp]
theorem invalidateConflictingBorrowsAtProj_nil
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat)
    (writeRangeLen : Nat) :
    invalidateConflictingBorrowsAtProj
      .nil
      targetLocal
      writerTag
      writeProj
      writeRangeOff
      writeRangeLen = .nil := rfl

/--
Definitional simplification equation for `invalidateConflictingBorrowsAtProj` on
a non-empty borrow list.
-/
@[simp]
theorem invalidateConflictingBorrowsAtProj_cons
    (entry : BorrowEntry)
    (rest : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat)
    (writeRangeLen : Nat) :
    invalidateConflictingBorrowsAtProj
      (entry :: rest)
      targetLocal
      writerTag
      writeProj
      writeRangeOff
      writeRangeLen =
      updateBorrowPermAtProj
        entry
        targetLocal
        writerTag
        writeProj
        writeRangeOff
        writeRangeLen ::
        invalidateConflictingBorrowsAtProj
          rest
          targetLocal
          writerTag
          writeProj
          writeRangeOff
          writeRangeLen := rfl

/--
Look up the `CapturedAllocation` with identifier `allocId` in `globals`.

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"
-/
def lookupGlobalAlloc :
    List CapturedAllocation → AllocId → Option CapturedAllocation
  | .nil, _ => .none
  | alloc :: rest, allocId =>
    match Nat.beq alloc.allocId allocId with
    | true => .some alloc
    | false => lookupGlobalAlloc rest allocId

/--
Read `remBytes` little-endian initialized bytes from `bytes` (`List (Option
UInt8)`) starting at byte offset `offset`.

Returns `.none` if any byte in `[offset .. offset + remBytes)` is out of bounds
or `.none` (uninitialized).

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"
-/
def readLittleEndianBytes
    (bytes : List (Option UInt8)) :
    Nat → Nat → Option Nat
  | _, .zero => .some 0
  | offset, .succ remBytes =>
    match get? bytes offset with
    | .some (.some byteVal) =>
      match readLittleEndianBytes bytes (Nat.add offset 1) remBytes with
      | .some highBits =>
        .some
          (Nat.add byteVal.toBitVec.toNat (Nat.mul 256 highBits))
      | .none => .none
    | _ => .none

/--
Read a `ScalarInt` of width `sizeBytes` in little-endian byte order from global
allocation `alloc` at `offset`.

Returns `.none` if `sizeBytes == 0` or if any byte in
`[offset .. offset + sizeBytes)` is out of bounds or `.none` (uninitialized) in
`alloc.bytes`.
-/
def readGlobalScalar
    (alloc : CapturedAllocation)
    (offset sizeBytes : Nat) :
    Option ScalarInt :=
  match Nat.beq sizeBytes 0 with
  | true => .none
  | false =>
    match readLittleEndianBytes alloc.bytes offset sizeBytes with
    | .some bits => .some ⟨bits, sizeBytes⟩
    | .none => .none

/--
Byte width of a scalar `Ty` (`bool`, `char`, `uint`, or `int`) on a 64-bit
target.
-/
def tyScalarBytes (ty : Ty) : Option Nat :=
  match ty.kind with
  | .bool => .some 1
  | .char => .some 4
  | k => intCastTargetBytes k

/--
Evaluate a `ConstValue` to a runtime `Value` when supported without global
allocation context.
-/
def evalConstValue : ConstValue → Option Value
  | .zeroSized => .some .unit
  | .scalar (.int s) => .some (.scalar s)
  | .scalar (.ptr p sz) => .some (.ptr p sz)
  | .slice _ _ => .none
  | .indirect _ _ => .none
  | .unevaluated _ => .none

/--
Drop the first `n` elements of a `List Value`.
-/
def dropValues : Nat → List Value → List Value
  | .zero, xs => xs
  | _, .nil => .nil
  | .succ k, _ :: xs => dropValues k xs

/--
Take the first `n` elements of a `List Value`.
-/
def takeValues : Nat → List Value → List Value
  | .zero, _ => .nil
  | _, .nil => .nil
  | .succ k, x :: xs => x :: takeValues k xs

/--
Extract the subslice of `elems` specified by `ProjectionElem.subslice fromIdx
toIdx fromEnd`.

When `fromEnd = true`, the subslice spans `elems[fromIdx .. elems.length -
toIdx]`; when `fromEnd = false`, it spans `elems[fromIdx .. toIdx]`. Returns
`.none` if the indices are out of bounds or inverted.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1239-L1254>

> "/// These indices are generated by slice patterns. Easiest to explain
> /// by example:
> ///
> /// ```ignore (illustrative)
> /// [X, _, .._, _, _] => { offset: 0, min_length: 4, from_end: false },
> /// [_, X, .._, _, _] => { offset: 1, min_length: 4, from_end: false },
> /// [_, _, .._, X, _] => { offset: 2, min_length: 4, from_end: true },
> /// [_, _, .._, _, X] => { offset: 1, min_length: 4, from_end: true },
> /// ```
> Subslice {
>     from: u64,
>     to: u64,
>     from_end: bool,
> },"
-/
def extractSubslice
    (elems : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool) :
    Option (List Value) :=
  let len := length elems
  match Nat.ble toIdx len with
  | false => .none
  | true =>
    let endIdx :=
      match fromEnd with
      | true => Nat.sub len toIdx
      | false => toIdx
    match Nat.ble fromIdx endIdx with
    | false => .none
    | true =>
      let count := Nat.sub endIdx fromIdx
      .some (takeValues count (dropValues fromIdx elems))

/--
Traverse a sequence of `.field`, `.downcast`, `.index`, `.constantIndex`,
`.subslice`, and `.opaqueCast` projections on an initialized `Value`.

Reference (The Rust Reference, "Field access expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/field-expr.html>

> "A field expression is a place expression that evaluates to the location of
> a field of a struct or union."

Reference (The Rust Reference, "Array and slice indexing expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/array-expr.html#array-and-slice-indexing-expressions>

> "Array and slice-typed expressions can be indexed with a usize index to access
> elements of the array or slice."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Downcast`](ProjectionElem::Downcast): This projection sets the place's
>   variant index to the given one, and makes no other changes. A `Downcast`
>   projection must always be followed immediately by a `Field` projection.
> - [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type. ...
> - [`ConstantIndex`](ProjectionElem::ConstantIndex): Computes an offset in
>   units of `T` into the place as described in the documentation for the
>   `ProjectionElem`. ...
> - [`Index`](ProjectionElem::Index): Like `ConstantIndex`, only legal on
>   `[T; N]` or `[T]`. However, `Index` additionally takes a local from which
>   the value of the index is computed at runtime."
-/
def readProjectedValue
    (locals : List LocalSlot) :
    Value → List ProjectionElem → ProjReadResult
  | val, .nil => .ok val
  | .aggregate _ fields, .field idx _ :: rest =>
    match get? fields idx with
    | .some fieldVal => readProjectedValue locals fieldVal rest
    | .none => .ub
  | .scalar sc, .field .zero _ :: rest =>
    readProjectedValue locals (.scalar sc) rest
  | .ptr p sz, .field .zero _ :: rest =>
    readProjectedValue locals (.ptr p sz) rest
  | .unit, .field .zero _ :: rest =>
    readProjectedValue locals .unit rest
  | _, .field _ _ :: _ => .ub
  | .aggregate actualVariant fields, .downcast _ variantIdx :: rest =>
    match Nat.beq actualVariant variantIdx with
    | true =>
      readProjectedValue locals (.aggregate actualVariant fields) rest
    | false => .ub
  | _, .downcast _ _ :: _ => .ub
  | .aggregate 0 fields, .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match get? fields sc.bits with
      | .some elemVal => readProjectedValue locals elemVal rest
      | .none => .ub
    | _ => .ub
  | _, .index _ :: _ => .ub
  | .aggregate 0 fields, .constantIndex offset minLen fromEnd :: rest =>
    let len := length fields
    match Nat.ble minLen len with
    | true =>
      let idx :=
        match fromEnd with
        | true => Nat.sub len offset
        | false => offset
      match get? fields idx with
      | .some elemVal => readProjectedValue locals elemVal rest
      | .none => .ub
    | false => .ub
  | _, .constantIndex _ _ _ :: _ => .ub
  | .aggregate 0 fields, .subslice fromIdx toIdx fromEnd :: rest =>
    match extractSubslice fields fromIdx toIdx fromEnd with
    | .some subElems =>
      readProjectedValue locals (.aggregate 0 subElems) rest
    | .none => .ub
  | _, .subslice _ _ _ :: _ => .ub
  | val, .opaqueCast _ :: rest =>
    readProjectedValue locals val rest
  | _, _ :: _ => .unsupported

/--
Update the value at a sequence of `.field`, `.downcast`, `.index`,
`.constantIndex`, and `.opaqueCast` projections inside an initialized `Value`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Downcast`](ProjectionElem::Downcast): This projection sets the place's
>   variant index to the given one, and makes no other changes. ...
> - [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
def writeProjectedValue
    (locals : List LocalSlot) :
    Value → List ProjectionElem → Value → ProjWriteResult
  | _, .nil, newVal => .ok newVal
  | .aggregate variantIdx fields, .field idx _ :: rest, newVal =>
    match get? fields idx with
    | .some oldFieldVal =>
      match writeProjectedValue locals oldFieldVal rest newVal with
      | .ok updatedFieldVal =>
        match set? fields idx updatedFieldVal with
        | .some fields' => .ok (.aggregate variantIdx fields')
        | .none => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .none => .ub
  | .scalar sc, .field .zero _ :: rest, newVal =>
    writeProjectedValue locals (.scalar sc) rest newVal
  | .ptr p sz, .field .zero _ :: rest, newVal =>
    writeProjectedValue locals (.ptr p sz) rest newVal
  | .unit, .field .zero _ :: rest, newVal =>
    writeProjectedValue locals .unit rest newVal
  | _, .field _ _ :: _, _ => .ub
  | .aggregate actualVariant fields,
    .downcast _ variantIdx :: rest,
    newVal =>
    match Nat.beq actualVariant variantIdx with
    | true =>
      writeProjectedValue
        locals
        (.aggregate actualVariant fields)
        rest
        newVal
    | false => .ub
  | _, .downcast _ _ :: _, _ => .ub
  | .aggregate 0 fields, .index idxLocal :: rest, newVal =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match get? fields sc.bits with
      | .some oldElemVal =>
        match writeProjectedValue locals oldElemVal rest newVal with
        | .ok updatedElemVal =>
          match set? fields sc.bits updatedElemVal with
          | .some fields' => .ok (.aggregate 0 fields')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | _ => .ub
  | _, .index _ :: _, _ => .ub
  | .aggregate 0 fields,
    .constantIndex offset minLen fromEnd :: rest,
    newVal =>
    let len := length fields
    match Nat.ble minLen len with
    | true =>
      let idx :=
        match fromEnd with
        | true => Nat.sub len offset
        | false => offset
      match get? fields idx with
      | .some oldElemVal =>
        match writeProjectedValue locals oldElemVal rest newVal with
        | .ok updatedElemVal =>
          match set? fields idx updatedElemVal with
          | .some fields' => .ok (.aggregate 0 fields')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | false => .ub
  | _, .constantIndex _ _ _ :: _, _ => .ub
  | val, .opaqueCast _ :: rest, newVal =>
    writeProjectedValue locals val rest newVal
  | _, _ :: _, _ => .unsupported

/--
Extract the element `RigidTy` of a slice or string constant type for
`ConstValue.slice` decoding.
-/
@[reducible]
def sliceConstElemKind (ty : Ty) : RigidTy :=
  match ty.kind with
  | .ref _ (.slice elemKind) => elemKind
  | .rawPtr _ (.slice elemKind) => elemKind
  | .slice elemKind => elemKind
  | .array elemKind _ => elemKind
  | _ => .uint .u8

/--
Evaluate an `Operand` in `locals` with active borrow table `borrows`, global
allocations `globals`, and layout table `layouts`, supporting root locals
(`projection = []`), dereferences (`ProjectionElem.deref` resolved through
`borrows` or `globals`), indirect and slice global constants
(`ConstValue.indirect` and `ConstValue.slice`), and nested `.field`, `.downcast`,
`.index`, `.constantIndex`, `.subslice`, and `.opaqueCast` projections.

In `Runtime(PostCleanup)` MIR, reading a root local via `Operand.move`
transitions its slot to `.uninit`, whereas a projected or dereferenced read
extracts the sub-value while keeping the parent aggregate slot initialized.

Reference (The Rust Reference, "Place expressions and value expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions.html#place-expressions-and-value-expressions>

> "A place expression is an expression that represents a memory location.
> These expressions are paths which refer to local variables, static
> variables, dereferences (*expr), array indexing expressions (expr[expr]),
> field references (expr.f) and parenthesized place expressions."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1177-L1179>

> "- On a `Deref` projection, we do an actual load of the inner place, with all
>   the usual consequences (the inner place must be based on an aligned pointer,
>   it must point to allocated memory, the aliasig model must allow reads, this
>   must not be a data race)."
-/
def evalOperand
    (locals : List LocalSlot)
    (op : Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil) :
    PlaceReadResult :=
  match op with
  | .constant c =>
    match c.val with
    | .indirect allocId offset =>
      match lookupGlobalAlloc globals allocId with
      | .some alloc =>
        match tyScalarBytes c.ty with
        | .some n =>
          match readGlobalScalar alloc offset n with
          | .some sc => .ok (.scalar sc) locals
          | .none => .ub
        | .none =>
          let sz :=
            match rigidTyByteSize layouts c.ty with
            | .some n => n
            | .none => Nat.sub (length alloc.bytes) offset
          match globalAllocSliceToAbstractBytes alloc offset sz with
          | .some absBytes =>
            match
              decodeValueFromBytes defaultCodecFuel layouts c.ty absBytes
            with
            | .some v => .ok v locals
            | .none =>
              match readGlobalScalar alloc offset sz with
              | .some sc => .ok (.scalar sc) locals
              | .none => .ub
          | .none => .ub
      | .none => .unsupported
    | .slice (.ptr p sz) lenMeta =>
      match lookupGlobalAlloc globals p.allocId with
      | .some alloc =>
        let elemKind := sliceConstElemKind c.ty
        let elemSz :=
          match rigidTyKindByteSize elemKind with
          | .some n => n
          | .none => 1
        let totalBytes := Nat.mul lenMeta elemSz
        match globalAllocSliceToAbstractBytes alloc p.offsetBytes totalBytes with
        | .some absBytes =>
          match
            decodeArrayChunksWith
              (fun chunk =>
                decodeValueFromBytes defaultCodecFuel layouts
                  { kind := elemKind, layoutIdx := 0 } chunk)
              elemSz
              lenMeta
              absBytes
          with
          | .some elems => .ok (.aggregate 0 elems) locals
          | .none => .ub
        | .none => .ub
      | .none =>
        .ok
          (.aggregate 0
            (.ptr p sz ::
              .scalar ⟨lenMeta, 8⟩ ::
              .nil))
          locals
    | .slice (.int s) lenMeta =>
      .ok
        (.aggregate 0
          (.scalar s ::
            .scalar ⟨lenMeta, 8⟩ ::
            .nil))
        locals
    | cv =>
      match evalConstValue cv with
      | .some v => .ok v locals
      | .none => .unsupported
  | .copy p =>
    match p.projection with
    | .deref :: restProj =>
      match get? locals p.local_ with
      | .some (.init (.ptr ptrVal sz)) =>
        match lookupBorrow borrows ptrVal.tag with
        | .some entry =>
          match entry.perm with
          | .disabled => .ub
          | _ =>
            match get? locals entry.targetLocal with
            | .some (.init targetRootVal) =>
              let fullProj :=
                match entry.targetProjection with
                | .nil => restProj
                | ph :: pt => ph :: appendProjections pt restProj
              match readProjectedValue locals targetRootVal fullProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .some _ => .ub
            | .none =>
              match get? callerLocals entry.targetLocal with
              | .some (.init targetRootVal) =>
                let fullProj :=
                  match entry.targetProjection with
                  | .nil => restProj
                  | ph :: pt => ph :: appendProjections pt restProj
                match readProjectedValue locals targetRootVal fullProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
              | _ => .ub
        | .none =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            match readGlobalScalar alloc ptrVal.offsetBytes sz with
            | .some sc =>
              match readProjectedValue locals (.scalar sc) restProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .none => .ub
          | .none => .ub
      | _ => .ub
    | _ =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal p.projection with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
  | .move p =>
    match p.projection with
    | .nil =>
      match get? locals p.local_ with
      | .some (.init v) =>
        match set? locals p.local_ .uninit with
        | .some locals' => .ok v locals'
        | .none => .ub
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | .deref :: restProj =>
      match get? locals p.local_ with
      | .some (.init (.ptr ptrVal sz)) =>
        match lookupBorrow borrows ptrVal.tag with
        | .some entry =>
          match entry.perm with
          | .disabled => .ub
          | _ =>
            match get? locals entry.targetLocal with
            | .some (.init targetRootVal) =>
              let fullProj :=
                match entry.targetProjection with
                | .nil => restProj
                | ph :: pt => ph :: appendProjections pt restProj
              match readProjectedValue locals targetRootVal fullProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .some _ => .ub
            | .none =>
              match get? callerLocals entry.targetLocal with
              | .some (.init targetRootVal) =>
                let fullProj :=
                  match entry.targetProjection with
                  | .nil => restProj
                  | ph :: pt => ph :: appendProjections pt restProj
                match readProjectedValue locals targetRootVal fullProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
              | _ => .ub
        | .none =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            match readGlobalScalar alloc ptrVal.offsetBytes sz with
            | .some sc =>
              match readProjectedValue locals (.scalar sc) restProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .none => .ub
          | .none => .ub
      | _ => .ub
    | proj :: rest =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal (proj :: rest) with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub

/--
Evaluate a list of `Operand`s left-to-right, threading `locals` state updates.

Reference (The Rust Reference, "Tuple and tuple indexing expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/tuple-expr.html>

> "For other tuple expressions, the first written tuple initializer operand
> initializes the field 0 and subsequent operands initializes the next highest
> field."
-/
def evalOperands
    (locals : List LocalSlot)
    (ops : List Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil) :
    OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperand locals op borrows globals layouts callerLocals with
    | .ok v locals₁ =>
      match evalOperands locals₁ rest borrows globals layouts callerLocals with
      | .ok vs locals₂ => .ok (v :: vs) locals₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

/--
Write `val` to `dst` in `locals` using active borrow table `borrows`, supporting
root locals (`projection = []`), dereference projections (`ProjectionElem.deref`
checked against `TreeBorrowPerm`), and nested `.field`, `.downcast`, `.index`,
`.constantIndex`, and `.opaqueCast` projections.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L305-L310>

> "/// Assign statements roughly correspond to an assignment in Rust proper
> /// (`x = ...`) except without the possibility of dropping the previous value
> /// (that must be done separately, if at all).
> Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),"
-/
def writePlaceValue
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value) :
    PlaceWriteResult :=
  match dst.projection with
  | .nil =>
    match get? locals dst.local_ with
    | .some .dead => .ub
    | .some _ =>
      match set? locals dst.local_ (.init val) with
      | .some locals' => .ok locals'
      | .none => .ub
    | .none => .ub
  | .deref :: restProj =>
    match get? locals dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .frozen => .ub
        | .disabled => .ub
        | _ =>
          let fullProj :=
            match entry.targetProjection with
            | .nil => restProj
            | ph :: pt => ph :: appendProjections pt restProj
          match fullProj with
          | .nil =>
            match get? locals entry.targetLocal with
            | .some .dead => .ub
            | .some _ =>
              match set? locals entry.targetLocal (.init val) with
              | .some locals' => .ok locals'
              | .none => .ub
            | .none => .ub
          | pHead :: pTail =>
            match get? locals entry.targetLocal with
            | .some (.init targetRootVal) =>
              match
                writeProjectedValue locals targetRootVal (pHead :: pTail) val
              with
              | .ok targetRootVal' =>
                match set? locals entry.targetLocal (.init targetRootVal') with
                | .some locals' => .ok locals'
                | .none => .ub
              | .ub => .ub
              | .unsupported => .unsupported
            | _ => .ub
      | .none => .ub
    | _ => .ub
  | proj :: rest =>
    match get? locals dst.local_ with
    | .some (.init rootVal) =>
      match writeProjectedValue locals rootVal (proj :: rest) val with
      | .ok rootVal' =>
        match set? locals dst.local_ (.init rootVal') with
        | .some locals' => .ok locals'
        | .none => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .some .uninit => .ub
    | .some .dead => .ub
    | .none => .ub

/--
Write `val` to `dst` in `locals` while checking active function-entry lifetime
protectors `activeProtectors` (`hasProtectedWriteConflict`).

Returns `.ub` if the write would disable a borrow protected by an active
protector in `activeProtectors`, and otherwise delegates to `writePlaceValue`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def evalPlaceWrite
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value)
    (activeProtectors : List Nat := .nil) :
    PlaceWriteResult :=
  match activeProtectors with
  | .nil => writePlaceValue locals borrows dst val
  | _ :: _ =>
    let conflict :=
      match dst.projection with
      | .nil =>
        hasProtectedWriteConflict
          borrows
          activeProtectors
          dst.local_
          .none
          .nil
      | .deref :: restProj =>
        match get? locals dst.local_ with
        | .some (.init (.ptr ptrVal _)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            let fullProj :=
              match entry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            hasProtectedWriteConflict
              borrows
              activeProtectors
              entry.targetLocal
              (.some ptrVal.tag)
              fullProj
              entry.rangeOffset
              entry.rangeLen
          | .none => false
        | _ => false
      | proj :: rest =>
        hasProtectedWriteConflict
          borrows
          activeProtectors
          dst.local_
          .none
          (proj :: rest)
    match conflict with
    | true => .ub
    | false => writePlaceValue locals borrows dst val

/--
When `activeProtectors` is `.nil`, `evalPlaceWrite` reduces definitionally to
`writePlaceValue`.
-/
@[simp]
theorem evalPlaceWrite_nil_protectors
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value) :
    evalPlaceWrite locals borrows dst val .nil =
      writePlaceValue locals borrows dst val := rfl

/--
Write `val` through a dereferenced pointer place `dst` (`.deref :: restProj` in
`frameLocals`) into a caller-owned referent slot in `callerLocals` when
`entry.targetLocal` lies outside the active stack frame
(`get? frameLocals entry.targetLocal = .none`).

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Mutable references point to memory which is owned by some other value."
-/
def writeCallerPlaceValue
    (frameLocals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value) :
    PlaceWriteResult :=
  match dst.projection with
  | .deref :: restProj =>
    match get? frameLocals dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .frozen => .ub
        | .disabled => .ub
        | _ =>
          match get? frameLocals entry.targetLocal with
          | .some _ => .ub
          | .none =>
            let fullProj :=
              match entry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            match fullProj with
            | .nil =>
              match get? callerLocals entry.targetLocal with
              | .some .dead => .ub
              | .some _ =>
                match set? callerLocals entry.targetLocal (.init val) with
                | .some callerLocals' => .ok callerLocals'
                | .none => .ub
              | .none => .ub
            | pHead :: pTail =>
              match get? callerLocals entry.targetLocal with
              | .some (.init targetRootVal) =>
                match
                  writeProjectedValue
                    frameLocals
                    targetRootVal
                    (pHead :: pTail)
                    val
                with
                | .ok targetRootVal' =>
                  match
                    set? callerLocals entry.targetLocal (.init targetRootVal')
                  with
                  | .some callerLocals' => .ok callerLocals'
                  | .none => .ub
                | .ub => .ub
                | .unsupported => .unsupported
              | _ => .ub
      | .none => .ub
    | _ => .ub
  | _ => .ub

/--
Write `val` through a dereferenced pointer place `dst` into `callerLocals` while
checking active function-entry lifetime protectors `activeProtectors`
(`hasProtectedWriteConflict`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def evalCallerPlaceWrite
    (frameLocals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value)
    (activeProtectors : List Nat := .nil) :
    PlaceWriteResult :=
  match activeProtectors with
  | .nil => writeCallerPlaceValue frameLocals callerLocals borrows dst val
  | _ :: _ =>
    let conflict :=
      match dst.projection with
      | .deref :: restProj =>
        match get? frameLocals dst.local_ with
        | .some (.init (.ptr ptrVal _)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            let fullProj :=
              match entry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            hasProtectedWriteConflict
              borrows
              activeProtectors
              entry.targetLocal
              (.some ptrVal.tag)
              fullProj
              entry.rangeOffset
              entry.rangeLen
          | .none => false
        | _ => false
      | _ => false
    match conflict with
    | true => .ub
    | false => writeCallerPlaceValue frameLocals callerLocals borrows dst val

/--
Update Tree Borrows permissions in `borrows` after a successful dereferenced
write to `dst` with post-deref projection suffix `restProj`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def invalidateDerefWriteBorrows
    (locals₁ : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (restProj : List ProjectionElem) :
    List BorrowEntry :=
  match get? locals₁ dst.local_ with
  | .some (.init (.ptr ptrVal _)) =>
    match lookupBorrow borrows ptrVal.tag with
    | .some entry =>
      let fullProj := appendProjections entry.targetProjection restProj
      match fullProj with
      | .nil =>
        match Nat.beq entry.rangeLen 0 with
        | true =>
          invalidateConflictingBorrows
            borrows
            entry.targetLocal
            (.some ptrVal.tag)
        | false =>
          invalidateConflictingBorrowsAtProj
            borrows
            entry.targetLocal
            (.some ptrVal.tag)
            .nil
            entry.rangeOffset
            entry.rangeLen
      | pHead :: pTail =>
        invalidateConflictingBorrowsAtProj
          borrows
          entry.targetLocal
          (.some ptrVal.tag)
          (pHead :: pTail)
          entry.rangeOffset
          entry.rangeLen
    | .none => borrows
  | _ => borrows

/--
Evaluate a byte-level representation cast (`CastKind.transmute` or
`CastKind.subtype`) from operand `op` to `targetTy` by encoding the source
`Value` into `List AbstractByte` and decoding at `targetTy`.

Returns `.ub` if the encoded bytes violate the bit-validity invariant of
`targetTy` (`decodeValueFromBytes` returns `.none`), and `.unsupported` if the
source and destination layout sizes do not match.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1711-L1747>

> "pub enum CastKind {
>     PointerExposeProvenance,
>     PointerWithExposedProvenance,
>     PointerCoercion(PointerCoercion, CoercionSource),
>     IntToInt,
>     FloatToInt,
>     FloatToFloat,
>     IntToFloat,
>     PtrToPtr,
>     FnPtrToPtr,
>     Transmute,
>     Subtype,
> }"
-/
def evalByteCast
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok v locals' =>
    match rigidTyByteSize layouts targetTy with
    | .none => .unsupported
    | .some dstSize =>
      match operandTy localDecls layouts op with
      | .some srcTy =>
        match rigidTyByteSize layouts srcTy with
        | .none => .unsupported
        | .some srcSize =>
          match Nat.beq srcSize dstSize with
          | false => .unsupported
          | true =>
            let encodedOpt : Option (List AbstractByte) :=
              match encodeValueToBytes defaultCodecFuel layouts srcTy v with
              | .some bs => .some bs
              | .none => encodeUntypedValueToBytes defaultCodecFuel v
            match encodedOpt with
            | .none => .ub
            | .some bs =>
              match Nat.beq (length bs) dstSize with
              | false => .ub
              | true =>
                match
                  decodeValueFromBytes defaultCodecFuel layouts targetTy bs
                with
                | .some v' => .ok v' locals' mem
                | .none => .ub
      | .none =>
        match encodeUntypedValueToBytes defaultCodecFuel v with
        | .none => .unsupported
        | .some bs =>
          match Nat.beq (length bs) dstSize with
          | false => .unsupported
          | true =>
            match decodeValueFromBytes defaultCodecFuel layouts targetTy bs with
            | .some v' => .ok v' locals' mem
            | .none => .ub

/--
Evaluate an `Rvalue` in `locals` and `mem`, using `localDecls` and `layouts` to
resolve operand types, signedness, and byte layouts for `Rvalue.binaryOp`,
`Rvalue.unaryOp`, `Rvalue.cast`, and `Rvalue.aggregate`.

Reference (The Rust Reference, "Negation operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#negation-operators>

> "Negation of these most negative values leaves the value unchanged due to
> two’s complement overflow conventions."

Reference (The Rust Reference, "Borrow operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#borrow-operators>

> "The & (shared borrow) and &mut (mutable borrow) operators are unary prefix
> operators. When applied to a place expression, this expressions produces a
> reference (pointer) to the location that the value refers to."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488>

> "pub enum Rvalue<'tcx> {
>     Use(Operand<'tcx>),
>     Repeat(Operand<'tcx>, ty::Const<'tcx>),
>     Ref(Region<'tcx>, BorrowKind, Place<'tcx>),
>     ThreadLocalRef(DefId),
>     RawPtr(RawPtrKind, Place<'tcx>),
>     Len(Place<'tcx>),
>     Cast(CastKind, Operand<'tcx>, Ty<'tcx>),
>     BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>),
>     NullaryOp(RuntimeChecks, Ty<'tcx>),
>     UnaryOp(UnOp, Operand<'tcx>),
>     Discriminant(Place<'tcx>),
>     Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>),
>     ShallowInitBox(Operand<'tcx>, Ty<'tcx>),
>     CopyForDeref(Place<'tcx>),
>     WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>),
> }"
-/
def evalRvalue
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory := emptyMemory)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  match rv with
  | .use op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .copyForDeref place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .repeat op count =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' => .ok (.aggregate 0 (replicateValue count v)) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .ref borrowKind place =>
    let perm :=
      match borrowKind with
      | .shared => TreeBorrowPerm.frozen
      | .mut false => TreeBorrowPerm.active
      | .mut true => TreeBorrowPerm.reserved
    match place.projection with
    | .deref :: restProj =>
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr _)) =>
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, borrowKind with
          | .disabled, _ => .ub
          | .frozen, .mut _ => .ub
          | _, _ =>
            let tag := mem.nextTag
            let fullProj :=
              match parentEntry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            let entry : BorrowEntry := {
              tag := tag
              targetLocal := parentEntry.targetLocal
              targetProjection := fullProj
              perm := perm
            }
            let mem' := {
              mem with
              borrows := entry :: mem.borrows
              nextTag := Nat.add tag 1
            }
            .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | .none => .ub
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        let tag := mem.nextTag
        let entry : BorrowEntry := {
          tag := tag
          targetLocal := place.local_
          targetProjection := place.projection
          perm := perm
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
  | .rawPtr mutability place =>
    let perm :=
      match mutability with
      | .not => TreeBorrowPerm.frozen
      | .mut => TreeBorrowPerm.active
    match place.projection with
    | .deref :: restProj =>
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr _)) =>
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, mutability with
          | .disabled, _ => .ub
          | .frozen, .mut => .ub
          | _, _ =>
            let tag := mem.nextTag
            let fullProj :=
              match parentEntry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            let entry : BorrowEntry := {
              tag := tag
              targetLocal := parentEntry.targetLocal
              targetProjection := fullProj
              perm := perm
            }
            let mem' := {
              mem with
              borrows := entry :: mem.borrows
              nextTag := Nat.add tag 1
            }
            .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | .none => .ub
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        let tag := mem.nextTag
        let entry : BorrowEntry := {
          tag := tag
          targetLocal := place.local_
          targetProjection := place.projection
          perm := perm
        }
        let mem' := {
          mem with
          borrows := entry :: mem.borrows
          nextTag := Nat.add tag 1
        }
        .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
  | .len place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.aggregate 0 elems) locals' =>
      .ok (.scalar ⟨length elems, 8⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .intToInt op targetTy =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.scalar sc) locals' =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        match intCastTargetBytes targetTy.kind with
        | .some targetBytes =>
          let modulus := scalarModulus targetBytes
          let castedBits :=
            match operandIsSigned localDecls op layouts with
            | false => wrapScalarBits sc.bits modulus
            | true =>
              match Nat.ble targetBytes sc.sizeBytes with
              | true => wrapScalarBits sc.bits modulus
              | false => signExtendBits sc.bits sc.sizeBytes targetBytes
          .ok (.scalar ⟨castedBits, targetBytes⟩) locals' mem
        | .none => .unsupported
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .ptrToPtr op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal sz) locals' => .ok (.ptr ptrVal sz) locals' mem
    | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
      .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast (.pointerCoercion _) op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal sz) locals' => .ok (.ptr ptrVal sz) locals' mem
    | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
      .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .pointerExposeProvenance op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal _) locals' =>
      let addr := Nat.add (Nat.mul ptrVal.allocId 65536) ptrVal.offsetBytes
      .ok (.scalar ⟨addr, 8⟩) locals' mem
    | .ok (.scalar sc) locals' => .ok (.scalar ⟨sc.bits, 8⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .pointerWithExposedProvenance op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.scalar sc) locals' =>
      let p : ProvenancePtr := {
        allocId := Nat.div sc.bits 65536
        offsetBytes := Nat.mod sc.bits 65536
      }
      .ok (.ptr p 8) locals' mem
    | .ok (.ptr ptrVal sz) locals' => .ok (.ptr ptrVal sz) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .transmute op targetTy =>
    evalByteCast locals op targetTy mem localDecls layouts
  | .cast .subtype op targetTy =>
    evalByteCast locals op targetTy mem localDecls layouts
  | .binaryOp op lhsOp rhsOp =>
    match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals with
    | .ok lhsVal locals₁ =>
      match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals with
      | .ok rhsVal locals₂ =>
        match lhsVal, rhsVal with
        | .scalar lhs, .scalar rhs =>
          let isSigned := operandIsSigned localDecls lhsOp layouts
          evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            .ok
              (.ptr
                { ptrVal with
                  offsetBytes := Nat.add ptrVal.offsetBytes offsetSc.bits }
                sz)
              locals₂
              mem
          | _ => .unsupported
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .not op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.scalar sc) locals' =>
      evalUnaryNot sc (operandTy localDecls layouts op) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .neg op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.scalar sc) locals' =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let modulus := scalarModulus sc.sizeBytes
        let canonical := wrapScalarBits sc.bits modulus
        let negBits := wrapScalarBits (Nat.sub modulus canonical) modulus
        .ok (.scalar ⟨negBits, sc.sizeBytes⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .ptrMetadata op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.aggregate 0 (.ptr _ _ :: .scalar metaSc :: .nil)) locals' =>
      .ok (.scalar ⟨metaSc.bits, 8⟩) locals' mem
    | .ok (.aggregate 0 elems) locals' =>
      .ok (.scalar ⟨length elems, 8⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .discriminant place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.aggregate variantIdx _) locals' =>
      .ok (.scalar ⟨variantIdx, 8⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate .tuple ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.array _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.adt _ variantIdx _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok vals locals' => .ok (.aggregate variantIdx vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.rawPtr _ _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal _ :: .unit :: .nil) locals' =>
      .ok (.ptr ptrVal 8) locals' mem
    | .ok (.ptr ptrVal _ :: .aggregate 0 .nil :: .nil) locals' =>
      .ok (.ptr ptrVal 8) locals' mem
    | .ok (.scalar addrSc :: .unit :: .nil) locals' =>
      let p : ProvenancePtr := {
        allocId := Nat.div addrSc.bits 65536
        offsetBytes := Nat.mod addrSc.bits 65536
      }
      .ok (.ptr p 8) locals' mem
    | .ok (.scalar addrSc :: .aggregate 0 .nil :: .nil) locals' =>
      let p : ProvenancePtr := {
        allocId := Nat.div addrSc.bits 65536
        offsetBytes := Nat.mod addrSc.bits 65536
      }
      .ok (.ptr p 8) locals' mem
    | .ok (.ptr ptrVal _ :: .scalar metaSc :: .nil) locals' =>
      .ok (.aggregate 0 (.ptr ptrVal 8 :: .scalar ⟨metaSc.bits, 8⟩ :: .nil))
        locals' mem
    | .ok (.scalar addrSc :: .scalar metaSc :: .nil) locals' =>
      let p : ProvenancePtr := {
        allocId := Nat.div addrSc.bits 65536
        offsetBytes := Nat.mod addrSc.bits 65536
      }
      .ok (.aggregate 0 (.ptr p 8 :: .scalar ⟨metaSc.bits, 8⟩ :: .nil))
        locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | _ => .unsupported

/--
Alias for `evalRvalue` with explicit `Memory` threading.
-/
abbrev evalRvalueWithMemory := evalRvalue

end Trusted.Rustc.V2026_06_01.MirSemantics
