import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_08_01.MirSemantics.Bytes

namespace Trusted.Rustc.V2026_08_01.MirSemantics

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst

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
Fuel-bounded traversal of `BorrowEntry.parentTag` links testing whether
`candidateTag` is equal to `ancestorTag` or is a transitive reborrow child of
`ancestorTag` in `borrows`.

Modeling choice vs. stable Rust Reference: The stable Rust Reference requires
that pointer accesses obey Rust's aliasing rules (`behavior-considered-undefined.md`).
Anneal models the reborrow hierarchy operationally via Tree Borrows (Villani et
al., PLDI 2025), matching Miri's `tree.rs` and MiniRust's
`spec/mem/tree_borrows/tree.md` classification into `NodeRelation::Local`
(`candidateTag` in `ancestorTag`'s subtree) vs. `NodeRelation::Foreign`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (The Rust Reference, "Mutable references (`&mut T`)"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html#mutable-references-mut>

> "Mutable references point to memory which is owned by some other value."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L47-L55>

> "When a node is accessed, each node in the tree can be divided into two
> disjoint sets: *local nodes* and *foreign nodes*, based on its relative
> position to the accessed node. The *local* set includes the node itself and
> all its descendants, while the *foreign* set contains all other nodes."

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def isBorrowDescendantOrSelfAux :
    Nat → List BorrowEntry → Nat → Nat → Bool
  | .zero, _, candidateTag, ancestorTag =>
    Nat.beq candidateTag ancestorTag
  | .succ fuel, borrows, candidateTag, ancestorTag =>
    match Nat.beq candidateTag ancestorTag with
    | true => true
    | false =>
      match lookupBorrow borrows candidateTag with
      | .some entry =>
        match entry.parentTag with
        | .some pTag =>
          isBorrowDescendantOrSelfAux fuel borrows pTag ancestorTag
        | .none => false
      | .none => false

/--
Test whether `candidateTag` is in the Tree Borrows subtree rooted at
`ancestorTag` (`candidateTag == ancestorTag` or `ancestorTag` is reachable via
`BorrowEntry.parentTag` links in `borrows`).

In Tree Borrows terminology, an access through `candidateTag` is a child/self
(`NodeRelation::Local`) access relative to `entry` iff
`isBorrowDescendantOrSelf borrows candidateTag entry.tag == true`, and a foreign
(`NodeRelation::Foreign`) access otherwise.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L101-L106>

> "// If `self` is an ancestor of the accessed node, the accessed node is local to `self`.
> // Otherwise, the accessed node is a `foreign` of `self`.
> let node_relation = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def isBorrowDescendantOrSelf
    (borrows : List BorrowEntry)
    (candidateTag ancestorTag : Nat) :
    Bool :=
  isBorrowDescendantOrSelfAux (length borrows) borrows candidateTag ancestorTag

/--
Resolve the effective writer provenance tag relative to `entry` in `borrows`
under the Tree Borrows parent/child hierarchy.

When `writerTag = .some wTag` and `wTag` is in the subtree rooted at `entry.tag`
(`isBorrowDescendantOrSelf borrows wTag entry.tag == true`), the write is a
child/self (`NodeRelation::Local`) write relative to `entry`, so
`resolveTreeBorrowWriterTag` normalizes the writer tag to `.some entry.tag`
(activating `entry` from `.reserved` to `.active` or preserving `.active`).
Otherwise (`NodeRelation::Foreign` write), `writerTag` is returned unchanged so
conflicting non-ancestor entries are disabled.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L37-L62>

> "fn local_write(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Frozen => throw_ub!(\"Tree Borrows: local write of Frozen reference\"),
>         PermissionUnprot::Disabled => throw_ub!(\"Tree Borrows: local write of Disabled reference\"),
>         PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
>         _ => ret(PermissionUnprot::Unique),
>     }
> }
> ...
> fn foreign_write(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
>         PermissionUnprot::ReservedIm => ret(PermissionUnprot::ReservedIm),
>         // All other states become Disabled.
>         _ => ret(PermissionUnprot::Disabled),
>     }
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def resolveTreeBorrowWriterTag
    (borrows : List BorrowEntry)
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    Option Nat :=
  match writerTag with
  | .none => .none
  | .some wTag =>
    match isBorrowDescendantOrSelf borrows wTag entry.tag with
    | true => .some entry.tag
    | false => .some wTag

/--
Tree-Borrows-aware write permission transition for `entry` within borrow table
`allBorrows` when `targetLocal` is mutated at `writeProj` and optional byte
range `[writeRangeOff, writeRangeOff + writeRangeLen)`.

Writes through a descendant tag (`isBorrowDescendantOrSelf allBorrows wTag
entry.tag == true`) act as `NodeRelation::Local` writes on `entry` (activating
`.reserved -> .active` and preserving `.active` on ancestors), whereas writes
through a non-descendant tag (`NodeRelation::Foreign` writes, including writes
through an ancestor tag relative to its children) disable overlapping
active/reserved/frozen entries.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L64-L75>

> "fn transition(
>     self,
>     access_kind: AccessKind,
>     node_relation: NodeRelation,
> ) -> Result<PermissionUnprot> {
>     match (node_relation, access_kind) {
>         (NodeRelation::Local, AccessKind::Read) => self.local_read(),
>         (NodeRelation::Local, AccessKind::Write) => self.local_write(),
>         (NodeRelation::Foreign, AccessKind::Read) => self.foreign_read(),
>         (NodeRelation::Foreign, AccessKind::Write) => self.foreign_write(),
>     }
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def updateBorrowPermTreeAtProj
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff : Nat := 0)
    (writeRangeLen : Nat := 0) :
    BorrowEntry :=
  updateBorrowPermAtProj
    entry
    targetLocal
    (resolveTreeBorrowWriterTag allBorrows entry writerTag)
    writeProj
    writeRangeOff
    writeRangeLen

/--
Transition all `BorrowEntry` records in `borrows` affected by a Tree Borrows
write in full borrow hierarchy `allBorrows` at `targetLocal` and `writeProj`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L89-L125>

> "/// Recusively do state transition on `self` node and all its descendants.
> /// `path` is the path from `self` to the accessed node.
> /// `path` is None when the accessed node is not a descendant of `self`."

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def invalidateTreeBorrowsAtProj
    (allBorrows : List BorrowEntry)
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
    updateBorrowPermTreeAtProj
      allBorrows
      entry
      targetLocal
      writerTag
      writeProj
      writeRangeOff
      writeRangeLen ::
      invalidateTreeBorrowsAtProj
        allBorrows
        rest
        targetLocal
        writerTag
        writeProj
        writeRangeOff
        writeRangeLen

/--
Tree-Borrows-aware read permission transition for `entry` within borrow table
`allBorrows` when `targetLocal` is read at `readProj` and optional byte range
`[readRangeOff, readRangeOff + readRangeLen)` through `readerTag`.

Under Tree Borrows, a child/self (`NodeRelation::Local`) read
(`isBorrowDescendantOrSelf allBorrows rTag entry.tag == true`) preserves
`entry.perm`, whereas a `NodeRelation::Foreign` read (such as reading through a
parent pointer after a child mutable borrow has been activated) transitions an
overlapping `.active` (`PermissionUnprot::Unique`) entry to `.frozen` while
leaving `.reserved`, `.frozen`, and `.disabled` entries unchanged.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L27-L53>

> "fn local_read(self) -> Result<PermissionUnprot> {
>     ret(
>         match self {
>             PermissionUnprot::Disabled => throw_ub!(\"Tree Borrows: local read of Disabled reference\"),
>             // All other states are kept unchanged.
>             perm => perm,
>         }
>     )
> }
> ...
> fn foreign_read(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Reserved => ret(PermissionUnprot::Reserved),
>         PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),
>         // All other states are kept unchanged.
>         perm => ret(perm),
>     }
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def updateBorrowPermOnReadAtProj
    (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) :
    BorrowEntry :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => entry
  | true =>
    match
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen
    with
    | false => entry
    | true =>
      let isLocalRead :=
        match readerTag with
        | .none => false
        | .some rTag => isBorrowDescendantOrSelf allBorrows rTag entry.tag
      match isLocalRead with
      | true => entry
      | false =>
        match entry.perm with
        | .active => { entry with perm := .frozen }
        | _ => entry

/--
Apply `updateBorrowPermOnReadAtProj` across `borrows` for a read at
`targetLocal` and `readProj` in full borrow hierarchy `allBorrows`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L89-L125>

> "/// Recusively do state transition on `self` node and all its descendants.
> /// `path` is the path from `self` to the accessed node.
> /// `path` is None when the accessed node is not a descendant of `self`."

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def freezeTreeBorrowsOnReadAtProj
    (allBorrows : List BorrowEntry)
    (borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    updateBorrowPermOnReadAtProj
      allBorrows
      entry
      targetLocal
      readerTag
      readProj
      readRangeOff
      readRangeLen ::
      freezeTreeBorrowsOnReadAtProj
        allBorrows
        rest
        targetLocal
        readerTag
        readProj
        readRangeOff
        readRangeLen

/--
Update Tree Borrows permissions in `borrows` after a dereference read from
pointer local `ptrLoc` with post-deref projection suffix `restProj`, freezing
any foreign `.active` borrows whose target region overlaps the read.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L46-L53>

> "fn foreign_read(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Reserved => ret(PermissionUnprot::Reserved),
>         PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),
>         // All other states are kept unchanged.
>         perm => ret(perm),
>     }
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def freezeDerefReadBorrowsAt
    (locals : List LocalSlot)
    (ptrLoc : Local)
    (restProj : List ProjectionElem)
    (borrows : List BorrowEntry) :
    List BorrowEntry :=
  match get? locals ptrLoc with
  | .some (.init (.ptr ptrVal _)) =>
    match lookupBorrow borrows ptrVal.tag with
    | .some readerEntry =>
      freezeTreeBorrowsOnReadAtProj
        borrows
        borrows
        readerEntry.targetLocal
        (.some ptrVal.tag)
        (appendProjections readerEntry.targetProjection restProj)
        readerEntry.rangeOffset
        readerEntry.rangeLen
    | .none => borrows
  | _ => borrows

/--
Test whether any `BorrowEntry` in `borrows` targeting `targetLocal` at an
overlapping sub-place or byte range is currently protected by `activeProtectors`
and would be disabled by a write with `writerTag` in full borrow hierarchy
`allBorrows`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L7-L8>

> "When a reborrow occurs at function entry (i.e. the original reference is
> passed as an argument), we add a *protector* to the reborrow. When a node is
> protected, it is UB for this node to become `Disabled`."

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
@[reducible]
def hasProtectedTreeWriteConflict
    (allBorrows : List BorrowEntry)
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
    let resolvedWriter :=
      resolveTreeBorrowWriterTag allBorrows entry writerTag
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
            (borrowEntryWriteConflicts entry resolvedWriter)))
    match thisConflict with
    | true => true
    | false =>
      hasProtectedTreeWriteConflict
        allBorrows
        rest
        activeProtectors
        targetLocal
        writerTag
        writeProj
        writeRangeOff
        writeRangeLen

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
Set the element at 0-based index `idx` in `fields` to `v`, extending `fields`
with `.unit` placeholders when `idx` exceeds the current list length (for
example, when writing a union variant field at index `idx > 0` into a union
aggregate initially constructed from a single variant field).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
def setOrExtendFields : List Value → Nat → Value → List Value
  | .nil, .zero, v => v :: .nil
  | .nil, .succ k, v => .unit :: setOrExtendFields .nil k v
  | _ :: xs, .zero, v => v :: xs
  | x :: xs, .succ k, v => x :: setOrExtendFields xs k v

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
    | .none =>
      match rest with
      | .nil => .ok (.aggregate variantIdx (setOrExtendFields fields idx newVal))
      | _ :: _ => .ub
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
            match borrows with
            | b₁ :: b₂ :: restBorrows =>
              let allBorrows := b₁ :: b₂ :: restBorrows
              hasProtectedTreeWriteConflict
                allBorrows
                allBorrows
                activeProtectors
                entry.targetLocal
                (.some ptrVal.tag)
                fullProj
                entry.rangeOffset
                entry.rangeLen
            | _ =>
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
            match borrows with
            | b₁ :: b₂ :: restBorrows =>
              let allBorrows := b₁ :: b₂ :: restBorrows
              hasProtectedTreeWriteConflict
                allBorrows
                allBorrows
                activeProtectors
                entry.targetLocal
                (.some ptrVal.tag)
                fullProj
                entry.rangeOffset
                entry.rangeLen
            | _ =>
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
  match borrows with
  | .nil => .nil
  | single :: .nil =>
    let b := single :: .nil
    match get? locals₁ dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow b ptrVal.tag with
      | .some entry =>
        let fullProj := appendProjections entry.targetProjection restProj
        match fullProj with
        | .nil =>
          match Nat.beq entry.rangeLen 0 with
          | true =>
            invalidateConflictingBorrows
              b
              entry.targetLocal
              (.some ptrVal.tag)
          | false =>
            invalidateConflictingBorrowsAtProj
              b
              entry.targetLocal
              (.some ptrVal.tag)
              .nil
              entry.rangeOffset
              entry.rangeLen
        | pHead :: pTail =>
          invalidateConflictingBorrowsAtProj
            b
            entry.targetLocal
            (.some ptrVal.tag)
            (pHead :: pTail)
            entry.rangeOffset
            entry.rangeLen
      | .none => b
    | _ => b
  | b₁ :: b₂ :: restBorrows =>
    let allBorrows := b₁ :: b₂ :: restBorrows
    match get? locals₁ dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow allBorrows ptrVal.tag with
      | .some entry =>
        let fullProj := appendProjections entry.targetProjection restProj
        invalidateTreeBorrowsAtProj
          allBorrows
          allBorrows
          entry.targetLocal
          (.some ptrVal.tag)
          fullProj
          entry.rangeOffset
          entry.rangeLen
      | .none => allBorrows
    | _ => allBorrows

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
Test whether a `CastKind.pointerCoercion` tag string denotes function-item or
non-capturing closure reification to a function pointer
(`PointerCoercion::ReifyFnPointer` or `PointerCoercion::ClosureFnPointer`).

Reference (`compiler/rustc_middle/src/ty/adjustment.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/adjustment.rs#L18-L41>

> "pub enum PointerCoercion {
>     /// Go from a fn-item type to a fn-pointer type.
>     ReifyFnPointer(Safety),
>
>     /// Go from a safe fn pointer to an unsafe fn pointer.
>     UnsafeFnPointer,
>
>     /// Go from a non-capturing closure to a fn pointer or an unsafe fn pointer.
>     /// It cannot convert a closure that requires unsafe.
>     ClosureFnPointer(Safety),"
-/
def isReifyFnPointerCoercion (coercionKind : String) : Bool :=
  Bool.or
    (stringEq coercionKind "ReifyFnPointer")
    (Bool.or
      (stringEq coercionKind "ReifyFnPointer(Safe)")
      (Bool.or
        (stringEq coercionKind "ReifyFnPointer(Unsafe)")
        (Bool.or
          (stringEq coercionKind "ClosureFnPointer")
          (Bool.or
            (stringEq coercionKind "ClosureFnPointer(Safe)")
            (Bool.or
              (stringEq coercionKind "ClosureFnPointer(Unsafe)")
              (stringEq coercionKind "UnsafeFnPointer"))))))

/--
Extract the target `(defPath, typeArgs)` from the `Ty` of a function-item
operand (`RigidTy.fnDef defPath typeArgs`).

Reference (The Rust Reference, "Function item types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-item.html>

> "When referred to, a function item, or the constructor of a tuple-like struct
> or enum variant, yields a zero-sized value of its function item type. That
> type uniquely identifies the function"
-/
def extractFnItemTarget? : Option Ty → Option (DefPath × List RigidTy)
  | .some { kind := .fnDef defPath typeArgs, .. } => .some (defPath, typeArgs)
  | _ => .none

/--
Test whether `coercionKind` is one of the `PointerCoercion::ClosureFnPointer`
coercion tags (`"ClosureFnPointer"`, `"ClosureFnPointer(Safe)"`, or
`"ClosureFnPointer(Unsafe)"`).
-/
@[reducible]
def isClosureFnPointerCoercion (coercionKind : String) : Bool :=
  Bool.or
    (stringEq coercionKind "ClosureFnPointer")
    (Bool.or
      (stringEq coercionKind "ClosureFnPointer(Safe)")
      (stringEq coercionKind "ClosureFnPointer(Unsafe)"))

/--
Extract the target `(defPath, typeArgs)` from the `Ty` of an operand being
reified into a function pointer via `coercionKind`:
- For `"ClosureFnPointer"` / `"ClosureFnPointer(Safe)"` /
  `"ClosureFnPointer(Unsafe)"`, requires a non-capturing closure type
  `RigidTy.closure defPath .nil`.
- For `"ReifyFnPointer"` / `"ReifyFnPointer(Safe)"` /
  `"ReifyFnPointer(Unsafe)"`, requires a function-item type
  `RigidTy.fnDef defPath typeArgs`.

Reference (`compiler/rustc_middle/src/ty/adjustment.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/adjustment.rs#L18-L41>

> "pub enum PointerCoercion {
>     /// Go from a fn-item type to a fn-pointer type.
>     ReifyFnPointer(Safety),
>
>     /// Go from a safe fn pointer to an unsafe fn pointer.
>     UnsafeFnPointer,
>
>     /// Go from a non-capturing closure to a fn pointer or an unsafe fn pointer.
>     /// It cannot convert a closure that requires unsafe.
>     ClosureFnPointer(Safety),"
-/
@[reducible]
def extractReifyCoercionTarget?
    (coercionKind : String)
    (tyOpt : Option Ty) :
    Option (DefPath × List RigidTy) :=
  match isClosureFnPointerCoercion coercionKind with
  | true =>
    match tyOpt with
    | .some { kind := .closure defPath .nil, .. } => .some (defPath, .nil)
    | _ => .none
  | false => extractFnItemTarget? tyOpt

/--
Test whether `ty` is a thin raw pointer type (`RigidTy.rawPtr _ pointee` where
`pointee` is not a dynamically-sized `.slice _`, `.str`, or `.dynamic _`).

Reference (The Rust Reference, "Type cast expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#type-cast-expressions>

> "* Function pointer types can be cast to any thin pointer type"
-/
def isThinRawPtrTy (ty : Ty) : Bool :=
  match ty.kind with
  | .rawPtr _ (.slice _) => false
  | .rawPtr _ .str => false
  | .rawPtr _ (.dynamic _) => false
  | .rawPtr _ _ => true
  | _ => false

/--
Test whether `ty` is a wide raw pointer type (`RigidTy.rawPtr _ pointee` where
`pointee` is a dynamically-sized `.slice _`, `.str`, or `.dynamic _`).

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
def isWideRawPtrTy (ty : Ty) : Bool :=
  match ty.kind with
  | .rawPtr _ (.slice _) => true
  | .rawPtr _ .str => true
  | .rawPtr _ (.dynamic _) => true
  | _ => false

/--
Test whether `v` is valid second-word metadata for a wide pointer (`Value.scalar`
for slice/`str` length or vtable address, or `Value.ptr` for vtable provenance).

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
@[reducible]
def isWidePtrMetadata : Value → Bool
  | .scalar _ => true
  | .ptr _ _ => true
  | _ => false

/--
Test whether `kind` is a slice or `str` reference or raw pointer (`&[T]`,
`&mut [T]`, `*const [T]`, `*mut [T]`, `&str`, `&mut str`, `*const str`, or
`*mut str`), which is always represented at runtime as a wide pointer
aggregate `[ptr, len]`.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
@[reducible]
def isSlicePtrOrRefKind : RigidTy → Bool
  | .ref _ (.slice _) => true
  | .rawPtr _ (.slice _) => true
  | .ref _ .str => true
  | .rawPtr _ .str => true
  | _ => false

/--
Test whether `kind` is a trait-object reference or raw pointer (`&dyn Trait`,
`&mut dyn Trait`, `*const dyn Trait`, or `*mut dyn Trait`), which requires
wide-pointer vtable metadata.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
@[reducible]
def isDynPtrOrRefKind : RigidTy → Bool
  | .ref _ (.dynamic _) => true
  | .rawPtr _ (.dynamic _) => true
  | _ => false

/--
Test whether `kind` is a reference or raw pointer whose pointee is statically
known to be thin (not a slice, `str`, `dyn Trait`, generic parameter, alias,
ADT with a potentially unsized tail, or non-empty tuple).

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
@[reducible]
def isStrictlyThinPtrOrRefKind : RigidTy → Bool
  | .ref _ (.slice _) => false
  | .ref _ .str => false
  | .ref _ (.dynamic _) => false
  | .ref _ (.param _ _) => false
  | .ref _ (.alias _ _) => false
  | .ref _ (.adt _ _) => false
  | .ref _ (.tuple (_ :: _)) => false
  | .ref _ _ => true
  | .rawPtr _ (.slice _) => false
  | .rawPtr _ .str => false
  | .rawPtr _ (.dynamic _) => false
  | .rawPtr _ (.param _ _) => false
  | .rawPtr _ (.alias _ _) => false
  | .rawPtr _ (.adt _ _) => false
  | .rawPtr _ (.tuple (_ :: _)) => false
  | .rawPtr _ _ => true
  | _ => false

/--
Check that an unsizing coercion preserves pointer mutability rules (`&mut` / `*mut`
can coerce to shared or mutable, whereas shared `&` / `*const` can only coerce to
shared/const).

Reference (The Rust Reference, "Unsized Coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#unsized-coercions>

> "The following coercions are called `unsized coercions`...
> * `&T` to `&U`
> * `&mut T` to `&mut U`
> * `&mut T` to `&U`
> * `*const T` to `*const U`
> * `*mut T` to `*mut U`
> * `*mut T` to `*const U`"
-/
@[reducible]
def unsizeMutabilityCompatible (srcMut dstMut : Mutability) : Bool :=
  Bool.or (mutabilityEq srcMut .mut) (mutabilityEq dstMut .not)

/--
Check that a pointer coercion from `opTy` to `targetKind` obeys Rust pointer
mutability and reference/raw-pointer direction rules (no coercion upgrades
shared/const `.not` to `.mut`, and a raw pointer is never coerced to a
reference).

Reference (The Rust Reference, "Type coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#coercion-types>

> "* `&mut T` to `&T`
> * `*mut T` to `*const T`
> * `&T` to `*const T`
> * `&mut T` to `*mut T`"
-/
@[reducible]
def pointerCoercionTypesCompatible
    (opTy : Option Ty)
    (targetKind : RigidTy) :
    Bool :=
  match opTy with
  | .none => true
  | .some { kind := .ref srcMut _, .. } =>
    match targetKind with
    | .ref dstMut _ => unsizeMutabilityCompatible srcMut dstMut
    | .rawPtr dstMut _ => unsizeMutabilityCompatible srcMut dstMut
    | _ => true
  | .some { kind := .rawPtr srcMut _, .. } =>
    match targetKind with
    | .ref _ _ => false
    | .rawPtr dstMut _ => unsizeMutabilityCompatible srcMut dstMut
    | _ => true
  | .some _ => true

/--
Check that a pointer with provenance tag `tag` in `borrows` is not `.disabled`
(and is not `.frozen` when coerced to a mutable reference or mutable raw pointer).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def unsizeBorrowPermCompatible
    (borrows : List BorrowEntry)
    (tag : Nat)
    (targetKind : RigidTy) :
    Bool :=
  match lookupBorrow borrows tag with
  | .none => true
  | .some entry =>
    match entry.perm, targetKind with
    | .disabled, _ => false
    | .frozen, .ref .mut _ => false
    | .frozen, .rawPtr .mut _ => false
    | _, _ => true

/--
When coercing a fixed-size array reference or raw pointer (`&[T; n]` or
`*const [T; n]`) to a slice reference or raw pointer (`&[T]` or `*const [T]`)
via `PointerCoercion::Unsize`, validate source/target mutability, element type
equality, 64-bit `usize` length range (`n < scalarModulus 8`), and Tree Borrows
tag permission, and extract the static array length `n` for the resulting wide
pointer's metadata.

Reference (The Rust Reference, "Unsized Coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#unsized-coercions>

> "* `[T; n]` to `[T]`."
-/
@[reducible]
def unsizeArrayLen?
    (coercionKind : String)
    (opTy : Option Ty)
    (targetKind : RigidTy)
    (borrows : List BorrowEntry := .nil)
    (tag : Nat := 0) :
    Option Nat :=
  match
    Bool.and
      (stringEq coercionKind "Unsize")
      (unsizeBorrowPermCompatible borrows tag targetKind)
  with
  | false => .none
  | true =>
    match targetKind, opTy with
    | .ref dstMut (.slice dstElem), .some { kind := .ref srcMut (.array srcElem n), .. } =>
      match
        Bool.and
          (Nat.blt n (scalarModulus 8))
          (Bool.and
            (unsizeMutabilityCompatible srcMut dstMut)
            (rigidTyEq srcElem dstElem))
      with
      | true => .some n
      | false => .none
    | .rawPtr dstMut (.slice dstElem), .some { kind := .rawPtr srcMut (.array srcElem n), .. } =>
      match
        Bool.and
          (Nat.blt n (scalarModulus 8))
          (Bool.and
            (unsizeMutabilityCompatible srcMut dstMut)
            (rigidTyEq srcElem dstElem))
      with
      | true => .some n
      | false => .none
    | .rawPtr dstMut (.slice dstElem), .some { kind := .ref srcMut (.array srcElem n), .. } =>
      match
        Bool.and
          (Nat.blt n (scalarModulus 8))
          (Bool.and
            (unsizeMutabilityCompatible srcMut dstMut)
            (rigidTyEq srcElem dstElem))
      with
      | true => .some n
      | false => .none
    | _, _ => .none

/--
Test whether a monomorphized caller `RigidTy` matches a (possibly polymorphic)
callee declaration `RigidTy` once every generic parameter `.param idx _` in the
declaration is resolved to `typeArgs[idx]`, the monomorphized type arguments of
the call target (`ResolvedCallTarget.typeArgs`, recorded for reified function
pointers in `FnPtrEntry.typeArgs`). A parameter without a type argument fails
closed, so a polymorphic body is only accepted at the instantiation it was
reified for.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L225-L246>

> "/// The first local is the return value pointer, followed by `arg_count`
> /// locals for the function arguments, followed by any user-declared
> /// variables and temporaries."
-/
def rigidTyMatchesCalleeDecl (typeArgs : List RigidTy) : Nat → RigidTy → RigidTy → Bool
  | .zero, callerTy, declTy => rigidTyEq callerTy declTy
  | .succ _, callerTy, .param idx _ =>
    match get? typeArgs idx with
    | .some argTy => rigidTyEq callerTy argTy
    | .none => false
  | .succ fuel, .ref m1 t1, .ref m2 t2 =>
    Bool.and (mutabilityEq m1 m2) (rigidTyMatchesCalleeDecl typeArgs fuel t1 t2)
  | .succ fuel, .rawPtr m1 t1, .rawPtr m2 t2 =>
    Bool.and (mutabilityEq m1 m2) (rigidTyMatchesCalleeDecl typeArgs fuel t1 t2)
  | .succ fuel, .slice t1, .slice t2 =>
    rigidTyMatchesCalleeDecl typeArgs fuel t1 t2
  | .succ fuel, .array t1 n1, .array t2 n2 =>
    Bool.and (Nat.beq n1 n2) (rigidTyMatchesCalleeDecl typeArgs fuel t1 t2)
  | .succ fuel, .tuple (t1 :: ts1), .tuple (t2 :: ts2) =>
    Bool.and
      (rigidTyMatchesCalleeDecl typeArgs fuel t1 t2)
      (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple ts1) (.tuple ts2))
  | .succ fuel, .adt p1 (a1 :: as1), .adt p2 (a2 :: as2) =>
    Bool.and
      (stringEq p1 p2)
      (Bool.and
        (rigidTyMatchesCalleeDecl typeArgs fuel a1 a2)
        (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple as1) (.tuple as2)))
  | .succ fuel, .fnDef p1 (a1 :: as1), .fnDef p2 (a2 :: as2) =>
    Bool.and
      (stringEq p1 p2)
      (Bool.and
        (rigidTyMatchesCalleeDecl typeArgs fuel a1 a2)
        (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple as1) (.tuple as2)))
  | .succ fuel, .closure p1 (a1 :: as1), .closure p2 (a2 :: as2) =>
    Bool.and
      (stringEq p1 p2)
      (Bool.and
        (rigidTyMatchesCalleeDecl typeArgs fuel a1 a2)
        (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple as1) (.tuple as2)))
  | .succ fuel, .alias p1 (a1 :: as1), .alias p2 (a2 :: as2) =>
    Bool.and
      (stringEq p1 p2)
      (Bool.and
        (rigidTyMatchesCalleeDecl typeArgs fuel a1 a2)
        (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple as1) (.tuple as2)))
  | .succ fuel, .fnPtr in1 out1 s1 abi1, .fnPtr in2 out2 s2 abi2 =>
    Bool.and
      (safetyEq s1 s2)
      (Bool.and
        (callConvEq abi1 abi2)
        (Bool.and
          (rigidTyMatchesCalleeDecl typeArgs fuel out1 out2)
          (rigidTyMatchesCalleeDecl typeArgs fuel (.tuple in1) (.tuple in2))))
  | .succ _, callerTy, declTy => rigidTyEq callerTy declTy

/--
Check that `fnInputs` pointwise match the `RigidTy` kinds of the leading
parameter declarations in `paramDecls`, resolving generic `RigidTy.param` slots
of polymorphic `CapturedMir` bodies through `typeArgs`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L225-L246>

> "/// The first local is the return value pointer, followed by `arg_count`
> /// locals for the function arguments, followed by any user-declared
> /// variables and temporaries."
-/
def calleeParamTysMatch (typeArgs : List RigidTy) : List RigidTy → List LocalDecl → Bool
  | .nil, _ => true
  | _ :: _, .nil => false
  | inputTy :: restInputs, decl :: restDecls =>
    Bool.and
      (rigidTyMatchesCalleeDecl typeArgs 8 inputTy decl.ty.kind)
      (calleeParamTysMatch typeArgs restInputs restDecls)

/--
Validate that a callee's `localDecls` (when non-empty) has at least `argCount`
parameter declarations after `_0` and matches the expected function-pointer
parameter types `fnInputs` and return type `fnOutput`.

When `localDecls` is `.nil` (as in synthetic stub bodies that omit
`localDecls`), returns `true`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L225-L246>

> "/// The first local is the return value pointer, followed by `arg_count`
> /// locals for the function arguments, followed by any user-declared
> /// variables and temporaries."
-/
def calleeLocalDeclsCompatible
    (typeArgs : List RigidTy)
    (localDecls : List LocalDecl)
    (argCount : Nat)
    (fnInputs : List RigidTy)
    (fnOutput : RigidTy) :
    Bool :=
  match localDecls with
  | .nil => true
  | retDecl :: paramDecls =>
    Bool.and
      (Nat.ble argCount (length paramDecls))
      (Bool.and
        (rigidTyMatchesCalleeDecl typeArgs 8 fnOutput retDecl.ty.kind)
        (calleeParamTysMatch typeArgs fnInputs paramDecls))

/--
Check whether an explicit `ReifyFnPointer(Safety)` or `ClosureFnPointer(Safety)`
coercion tag is compatible with the target function-pointer `Safety` qualifier
`fnSafety`.

Unparameterized `"ReifyFnPointer"` and `"ClosureFnPointer"` tags accept both
`.safe` and `.unsafe_`; `"ReifyFnPointer(Safe)"` / `"ClosureFnPointer(Safe)"`
require `fnSafety = .safe`; `"ReifyFnPointer(Unsafe)"` /
`"ClosureFnPointer(Unsafe)"` require `fnSafety = .unsafe_`.

Reference (`compiler/rustc_middle/src/ty/adjustment.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/adjustment.rs#L18-L41>

> "pub enum PointerCoercion {
>     /// Go from a fn-item type to a fn-pointer type.
>     ReifyFnPointer(Safety),
>
>     /// Go from a safe fn pointer to an unsafe fn pointer.
>     UnsafeFnPointer,
>
>     /// Go from a non-capturing closure to a fn pointer or an unsafe fn pointer.
>     /// It cannot convert a closure that requires unsafe.
>     ClosureFnPointer(Safety),"
-/
def reifyCoercionSafetyCompatible
    (coercionKind : String)
    (fnSafety : Safety) :
    Bool :=
  match
    Bool.or
      (stringEq coercionKind "ReifyFnPointer(Safe)")
      (stringEq coercionKind "ClosureFnPointer(Safe)")
  with
  | true => safetyEq fnSafety .safe
  | false =>
    match
      Bool.or
        (stringEq coercionKind "ReifyFnPointer(Unsafe)")
        (stringEq coercionKind "ClosureFnPointer(Unsafe)")
    with
    | true => safetyEq fnSafety .unsafe_
    | false => true

/--
Look up a callee `CapturedMir` body in `callees` by its canonical `DefPath`.
-/
def findCallee? : List CapturedMir → DefPath → Option CapturedMir
  | .nil, _ => .none
  | body :: rest, defPath =>
    match stringEq body.defPath defPath with
    | true => .some body
    | false => findCallee? rest defPath

mutual
/--
Match a potentially parametric pattern `pat : RigidTy` from a `TraitImplEntry`
header (`TraitRef.args`) against a call-site type argument `arg : RigidTy`,
accumulating `(paramIdx, boundTy)` bindings in `subst` and enforcing equality
when the same `RigidTy.param` index occurs multiple times (rejecting mismatched
diagonal instantiations such as `Pair<u32, u64>` against `Pair<T, T>`).

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def matchRigidTy (pat arg : RigidTy) (subst : List (Nat × RigidTy)) : Option (List (Nat × RigidTy)) :=
  match pat with
  | .param pIdx _ =>
    let rec lookupSubst (idx : Nat) : List (Nat × RigidTy) → Option RigidTy
      | .nil => Option.none
      | (k, v) :: rest => if k == idx then Option.some v else lookupSubst idx rest
    match lookupSubst pIdx subst with
    | Option.some existing => if rigidTyEq existing arg then Option.some subst else Option.none
    | Option.none => Option.some ((pIdx, arg) :: subst)
  | .tuple pFields =>
    match arg with
    | .tuple aFields => matchRigidTyList pFields aFields subst
    | _ => Option.none
  | .array pElem pLen =>
    match arg with
    | .array aElem aLen =>
      if pLen == aLen then matchRigidTy pElem aElem subst else Option.none
    | _ => Option.none
  | .slice pElem =>
    match arg with
    | .slice aElem => matchRigidTy pElem aElem subst
    | _ => Option.none
  | .ref pMut pPointee =>
    match arg with
    | .ref aMut aPointee =>
      if mutabilityEq pMut aMut then matchRigidTy pPointee aPointee subst else Option.none
    | _ => Option.none
  | .rawPtr pMut pPointee =>
    match arg with
    | .rawPtr aMut aPointee =>
      if mutabilityEq pMut aMut then matchRigidTy pPointee aPointee subst else Option.none
    | _ => Option.none
  | .adt pDefPath pArgs =>
    match arg with
    | .adt aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | .fnDef pDefPath pArgs =>
    match arg with
    | .fnDef aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | .fnPtr pIns pOut pSaf pAbi =>
    match arg with
    | .fnPtr aIns aOut aSaf aAbi =>
      if Bool.and (safetyEq pSaf aSaf) (callConvEq pAbi aAbi) then
        match matchRigidTyList pIns aIns subst with
        | Option.some s => matchRigidTy pOut aOut s
        | Option.none => Option.none
      else
        Option.none
    | _ => Option.none
  | .closure pDefPath pUpvars =>
    match arg with
    | .closure aDefPath aUpvars =>
      if stringEq pDefPath aDefPath then matchRigidTyList pUpvars aUpvars subst else Option.none
    | _ => Option.none
  | .alias pDefPath pArgs =>
    match arg with
    | .alias aDefPath aArgs =>
      if stringEq pDefPath aDefPath then matchRigidTyList pArgs aArgs subst else Option.none
    | _ => Option.none
  | _ =>
    if rigidTyEq pat arg then Option.some subst else Option.none

/--
Pointwise pattern matching of `pats : List RigidTy` against `args : List RigidTy`,
threading parameter bindings `subst`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def matchRigidTyList (pats args : List RigidTy) (subst : List (Nat × RigidTy)) : Option (List (Nat × RigidTy)) :=
  match pats, args with
  | .nil, .nil => Option.some subst
  | p :: ps, a :: as =>
    match matchRigidTy p a subst with
    | Option.some s => matchRigidTyList ps as s
    | Option.none => Option.none
  | _, _ => Option.none
end

/--
Match a non-empty trait-header pattern list `pats : List RigidTy` against a
prefix of call-site type arguments `args : List RigidTy`, returning the
accumulated `impl`-level substitution `subst` together with any trailing
method-level generic type arguments `restArgs`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def matchRigidTyPrefix
    (pats args : List RigidTy)
    (subst : List (Nat × RigidTy)) :
    Option (List (Nat × RigidTy) × List RigidTy) :=
  match pats, args with
  | .nil, restArgs => Option.some (subst, restArgs)
  | p :: ps, a :: as =>
    match matchRigidTy p a subst with
    | Option.some s => matchRigidTyPrefix ps as s
    | Option.none => Option.none
  | _ :: _, .nil => Option.none

/--
Extract the `count` generic type arguments of an `impl` method body in canonical
parameter-index order `0 .. count - 1` from pattern-matching substitution `subst`.

Reference (The Rust Reference, "Generic parameters"):
<https://doc.rust-lang.org/1.98.0/reference/items/generics.html>

> "Functions, type aliases, structs, enumerations, unions, traits, and
> implementations may be parameterized by types, constants, and lifetimes."
-/
def extractImplTypeArgs (subst : List (Nat × RigidTy)) (count : Nat) : Option (List RigidTy) :=
  if subst.length != count then
    Option.none
  else
    let rec loop : Nat → List RigidTy → Option (List RigidTy)
      | 0, acc => Option.some acc
      | i + 1, acc =>
        let rec lookupSubst (idx : Nat) : List (Nat × RigidTy) → Option RigidTy
          | .nil => Option.none
          | (k, v) :: rest => if k == idx then Option.some v else lookupSubst idx rest
        match lookupSubst i subst with
        | Option.some t => loop i (t :: acc)
        | Option.none => Option.none
    loop count .nil

mutual
/--
Check that every `RigidTy.param idx _` occurring in `argTy` satisfies
`idx < numCallerEntries`, ensuring that generic type arguments containing
unbound parameters (even inside `.ref`, `.rawPtr`, `.fnPtr`, or `.fnDef`) cannot
bypass layout resolution when `callerLayouts` lacks an entry for `idx`.

Reference (`compiler/rustc_middle/src/ty/sty.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/sty.rs#L282-L285>

> "pub struct ParamTy {
>     pub index: u32,
>     pub name: Symbol,
> }"
-/
def allParamsInCallerLayouts (numCallerEntries : Nat) : RigidTy → Bool
  | .param idx _ => Nat.blt idx numCallerEntries
  | .alias _ a => allParamsInCallerLayoutsList numCallerEntries a
  | .tuple fields => allParamsInCallerLayoutsList numCallerEntries fields
  | .array elem _ => allParamsInCallerLayouts numCallerEntries elem
  | .slice elem => allParamsInCallerLayouts numCallerEntries elem
  | .ref _ pointee => allParamsInCallerLayouts numCallerEntries pointee
  | .rawPtr _ pointee => allParamsInCallerLayouts numCallerEntries pointee
  | .adt _ a => allParamsInCallerLayoutsList numCallerEntries a
  | .fnDef _ a => allParamsInCallerLayoutsList numCallerEntries a
  | .fnPtr inputs output _ _ =>
    Bool.and
      (allParamsInCallerLayoutsList numCallerEntries inputs)
      (allParamsInCallerLayouts numCallerEntries output)
  | .closure _ upvars => allParamsInCallerLayoutsList numCallerEntries upvars
  | .bool => true
  | .char => true
  | .int _ => true
  | .uint _ => true
  | .float _ => true
  | .never => true
  | .str => true
  | .dynamic _ => true
  | .foreign _ => true
  | .other _ => true

/--
Check that every `RigidTy` in a list satisfies `allParamsInCallerLayouts`.

Reference (`compiler/rustc_middle/src/ty/sty.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/sty.rs#L282-L285>

> "pub struct ParamTy {
>     pub index: u32,
>     pub name: Symbol,
> }"
-/
def allParamsInCallerLayoutsList (numCallerEntries : Nat) : List RigidTy → Bool
  | .nil => true
  | t :: ts =>
    Bool.and
      (allParamsInCallerLayouts numCallerEntries t)
      (allParamsInCallerLayoutsList numCallerEntries ts)
end

/--
Collect all `TraitImplEntry` records attached to `callees`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def flatMapTraitImpls : List CapturedMir → List TraitImplEntry
  | .nil => .nil
  | c :: cs => c.traitImpls ++ flatMapTraitImpls cs

/--
Check whether any `TraitImplEntry` in `traitImpls` targets trait method
`defPath`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def hasTraitImplForDefPath
    (traitImpls : List TraitImplEntry)
    (defPath : DefPath) :
    Bool :=
  match traitImpls with
  | .nil => false
  | entry :: rest =>
    match stringEq entry.traitRef.defPath defPath with
    | true => true
    | false => hasTraitImplForDefPath rest defPath

/--
Insert `(entry, implTypeArgsOpt)` into `acc` when no entry with the same
`implPath` is present, or upgrade an existing `(existingEntry, Option.none)`
with the same `implPath` when `implTypeArgsOpt` is `Option.some _`.

This deduplicates `TraitImplEntry` records by `implPath` while ensuring that an
already-instantiated copy of a generic `TraitImplEntry` (whose parameter-free
`traitRef.args` produces `Option.none` against the uninstantiated generic
callee's `typeParamCount`) cannot shadow the raw generic `TraitImplEntry` for
the same `implPath`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def upsertMatchingTraitImpl
    (entry : TraitImplEntry)
    (implTypeArgsOpt : Option (List RigidTy)) :
    List (TraitImplEntry × Option (List RigidTy)) →
    List (TraitImplEntry × Option (List RigidTy))
  | .nil => [(entry, implTypeArgsOpt)]
  | (existingEntry, existingArgsOpt) :: rest =>
    match stringEq existingEntry.implPath entry.implPath with
    | true =>
      match existingArgsOpt, implTypeArgsOpt with
      | Option.none, Option.some _ =>
        (entry, implTypeArgsOpt) :: rest
      | _, _ =>
        (existingEntry, existingArgsOpt) :: rest
    | false =>
      (existingEntry, existingArgsOpt) ::
        upsertMatchingTraitImpl entry implTypeArgsOpt rest

/--
Collect all `TraitImplEntry` records in `traitImpls` whose `traitRef.defPath`
equals `defPath` and whose non-empty `traitRef.args` pattern-matches a prefix of
`typeArgs`, deduplicating by `entry.implPath` via `upsertMatchingTraitImpl` and
pairing each matched entry with its validated effective type arguments (or
`Option.none` if parameter indices are not contiguous, the target `implPath` is
not in `callees`, or the extracted type-argument count does not match the
target callee's `typeParamCount`).

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def collectMatchingTraitImpls
    (callees : List CapturedMir)
    (traitImpls : List TraitImplEntry)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (acc : List (TraitImplEntry × Option (List RigidTy)) := .nil) :
    List (TraitImplEntry × Option (List RigidTy)) :=
  match traitImpls with
  | .nil => acc
  | entry :: rest =>
    if stringEq entry.traitRef.defPath defPath then
      match entry.traitRef.args with
      | .nil => collectMatchingTraitImpls callees rest defPath typeArgs acc
      | _ :: _ =>
        match matchRigidTyPrefix entry.traitRef.args typeArgs .nil with
        | Option.none =>
          collectMatchingTraitImpls callees rest defPath typeArgs acc
        | Option.some (subst, methodTypeArgs) =>
          let rawImplTypeArgsOpt :=
            match extractImplTypeArgs subst subst.length with
            | Option.some implHeaderArgs =>
              Option.some (implHeaderArgs ++ methodTypeArgs)
            | Option.none => Option.none
          let implTypeArgsOpt :=
            match rawImplTypeArgsOpt, findCallee? callees entry.implPath with
            | Option.some rawArgs, Option.some c =>
              let effectiveTypeArgs :=
                match stringEq entry.implPath defPath with
                | true => typeArgs
                | false => rawArgs
              if effectiveTypeArgs.length == c.typeParamCount then
                Option.some effectiveTypeArgs
              else
                Option.none
            | _, _ => Option.none
          collectMatchingTraitImpls
            callees
            rest
            defPath
            typeArgs
            (upsertMatchingTraitImpl entry implTypeArgsOpt acc)
    else
      collectMatchingTraitImpls callees rest defPath typeArgs acc

/--
Check whether `candidateArgs` is a substitution instance of every matched
`TraitImplEntry`'s `traitRef.args` in `allMatches`
(`matchRigidTyList other.traitRef.args candidateArgs .nil ≠ Option.none`).

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def isTraitImplInstanceOfAll
    (candidateArgs : List RigidTy) :
    List (TraitImplEntry × Option (List RigidTy)) → Bool
  | .nil => true
  | (otherEntry, _) :: rest =>
    match matchRigidTyList otherEntry.traitRef.args candidateArgs .nil with
    | Option.some _ => isTraitImplInstanceOfAll candidateArgs rest
    | Option.none => false

/--
Filter `candidates` to those whose `traitRef.args` is an instance of every
matched `TraitImplEntry` in `allMatches`.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def filterMostSpecificTraitImpls
    (allMatches : List (TraitImplEntry × Option (List RigidTy))) :
    List (TraitImplEntry × Option (List RigidTy)) →
    List (TraitImplEntry × Option (List RigidTy))
  | .nil => .nil
  | (entry, implTypeArgsOpt) :: rest =>
    match isTraitImplInstanceOfAll entry.traitRef.args allMatches with
    | true =>
      (entry, implTypeArgsOpt) ::
        filterMostSpecificTraitImpls allMatches rest
    | false =>
      filterMostSpecificTraitImpls allMatches rest

/--
Resolve `(defPath, typeArgs)` against `callees` and registered `TraitImplEntry`
tables (`extraTraitImpls ++ flatMapTraitImpls callees`), returning the matched
uninstantiated `CapturedMir` body together with its effective `typeArgs`:
1. When `typeArgs` is `.nil`, looks up `defPath` directly in `callees`.
2. When `typeArgs` starts with an uninstantiated `.param _ _`, rejects resolution
   if `defPath` is a trait method in `allTraitImpls` (even if a default trait
   method body for `defPath` is in `callees`, because an arbitrary concrete
   `Self` may override the default method), and otherwise resolves direct free
   generic functions in `callees`.
3. When `typeArgs` starts with a non-`.param` `firstArg`, collects all
   `TraitImplEntry` header matches in `allTraitImpls` (deduplicated by
   `implPath`):
   - If no `TraitImplEntry` header matches, falls back to `findCallee? callees
     defPath` (unless `defPath` is a trait method in `allTraitImpls` and
     `firstArg` still contains an uninstantiated `RigidTy.param`).
   - If one or more `TraitImplEntry` headers match, selects the unique match
     whose `traitRef.args` is an instance of every matched entry's
     `traitRef.args` (never falling back to a default trait method body when a
     matching override is unlinked, has mismatched arity, or is ambiguous).
     A winning entry whose `implPath` is `defPath` itself records an `impl`
     that inherits the trait's default method body; that body is generic over
     `Self`, so it resolves with the full call-site `typeArgs`.

Header matching ignores `impl` where-clauses. The `TraitImplEntry` table is
therefore trusted to be complete: if a where-clause-bounded generic `impl`
(such as `impl<T: Copy> Trait for T`) overrides `defPath`, every more specific
`impl` that inherits the default method instead needs its own
`implPath := defPath` entry, or calls on that `impl`'s `Self` resolve to the
generic override.

Reference (The Rust Reference, "Trait implementations"):
<https://doc.rust-lang.org/1.98.0/reference/items/implementations.html#trait-implementations>

> "A trait implementation is defined like an inherent implementation except
> that the optional generic type declarations are followed by a trait, followed
> by the keyword `for`, followed by a path to a nominal type."
-/
def resolveCalleeBodyAndArgs?
    (callees : List CapturedMir)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    Option (CapturedMir × List RigidTy) :=
  match typeArgs with
  | .nil =>
    match findCallee? callees defPath with
    | Option.some c => Option.some (c, .nil)
    | Option.none => Option.none
  | .param _ _ :: _ =>
    match findCallee? callees defPath with
    | Option.none => Option.none
    | Option.some c =>
      let allTraitImpls := extraTraitImpls ++ flatMapTraitImpls callees
      match hasTraitImplForDefPath allTraitImpls defPath with
      | true => Option.none
      | false => Option.some (c, typeArgs)
  | firstArg :: restArgs =>
    let allTraitImpls := extraTraitImpls ++ flatMapTraitImpls callees
    let matchedImpls :=
      collectMatchingTraitImpls
        callees
        allTraitImpls
        defPath
        (firstArg :: restArgs)
    match matchedImpls with
    | .nil =>
      match findCallee? callees defPath with
      | Option.none => Option.none
      | Option.some c =>
        match
          Bool.and
            (hasTraitImplForDefPath allTraitImpls defPath)
            (Bool.not (allParamsInCallerLayouts 0 firstArg))
        with
        | true => Option.none
        | false => Option.some (c, firstArg :: restArgs)
    | _ :: _ =>
      match filterMostSpecificTraitImpls matchedImpls matchedImpls with
      | (winnerEntry, Option.some implTypeArgs) :: .nil =>
        match findCallee? callees winnerEntry.implPath with
        | Option.some c =>
          let effectiveTypeArgs :=
            match stringEq winnerEntry.implPath defPath with
            | true => firstArg :: restArgs
            | false => implTypeArgs
          if effectiveTypeArgs.length == c.typeParamCount then
            Option.some (c, effectiveTypeArgs)
          else
            Option.none
        | Option.none => Option.none
      | _ => Option.none

/--
Construct a placeholder `TypeSubst` pairing each `RigidTy` in `typeArgs` with a
zero-sized placeholder `TypeLayout` so `RigidTy.instantiate` can substitute
generic type parameters when checking function-pointer signatures in
`checkCalleeSig`.

Reference (`compiler/rustc_middle/src/ty/generic_args.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/generic_args.rs#L27-L28>

> "/// An entity in the Rust type system, which can be one of
> /// several kinds (types, lifetimes, and consts)."
-/
def typeSubstOfRigidTys : List RigidTy → TypeSubst
  | .nil => .nil
  | ty :: rest =>
    (ty,
      { size := ⟨0⟩
        align := ⟨1⟩
        backendRepr := .memory
        fields := .primitive
        variants := .single 0
        isUninhabited := false }) :: typeSubstOfRigidTys rest

/--
Substitute generic type parameters (`RigidTy.param`) in the `ty.kind` of each
`LocalDecl` using `subst`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L967-L1065>

> "pub struct LocalDecl<'tcx> {
> ...
>     pub mutability: Mutability,
> ...
>     pub local_info: ClearCrossCrate<Box<LocalInfo<'tcx>>>,
> ...
>     pub ty: Ty<'tcx>,
> ...
>     pub user_ty: Option<Box<UserTypeProjections>>,
> ...
>     pub source_info: SourceInfo,
> }"
-/
def instantiateLocalDeclKinds
    (subst : TypeSubst) :
    List LocalDecl → List LocalDecl
  | .nil => .nil
  | d :: rest =>
    { d with ty := { d.ty with kind := d.ty.kind.instantiate subst } } ::
      instantiateLocalDeclKinds subst rest

/--
Validate that a linked callee `p` in `callees` or `extraTraitImpls` (when
present) is compatible with the target function-pointer signature
`(fnInputs, fnOutput, fnAbi)` during `ReifyFnPointer`:
1. Resolves `(p, typeArgs)` via `resolveCalleeBodyAndArgs?` across both direct
   `callees` and `TraitImplEntry` tables (`extraTraitImpls` and `c.traitImpls`).
2. Rejects `CallConv.rustIntrinsic` callees (compiler intrinsics cannot be
   coerced to function pointers).
3. Requires `length fnInputs == c.argCount` and `callConvEq fnAbi c.fnAbi.conv`.
4. Requires `length effectiveTypeArgs == c.typeParamCount` and checks
   `calleeLocalDeclsCompatible` on `c.localDecls` (instantiated with
   `effectiveTypeArgs` when `c.typeParamCount > 0`).

Reference (The Rust Reference, "Function pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-pointer.html>

> "Two function pointer types are compatible if they have the same ABI, safety,
> parameter types, and return type."
-/
def checkCalleeSig
    (callees : List CapturedMir)
    (p : DefPath)
    (fnInputs : List RigidTy)
    (fnOutput : RigidTy)
    (fnAbi : CallConv)
    (typeArgs : List RigidTy := .nil)
    (extraTraitImpls : List TraitImplEntry := .nil) :
    Bool :=
  match callees with
  | .nil => true
  | _ :: _ =>
    match resolveCalleeBodyAndArgs? callees p typeArgs extraTraitImpls with
    | .none => true
    | .some (c, effectiveTypeArgs) =>
      let declsCompatible :=
        match c.typeParamCount, effectiveTypeArgs with
        | 0, .nil =>
          calleeLocalDeclsCompatible
            .nil
            c.localDecls
            c.argCount
            fnInputs
            fnOutput
        | 0, _ :: _ => false
        | .succ _, _ =>
          Bool.and
            (Nat.beq (length effectiveTypeArgs) c.typeParamCount)
            (calleeLocalDeclsCompatible
              effectiveTypeArgs
              (instantiateLocalDeclKinds
                (typeSubstOfRigidTys effectiveTypeArgs)
                c.localDecls)
              c.argCount
              fnInputs
              fnOutput)
      Bool.and
        (Bool.not (callConvEq c.fnAbi.conv .rustIntrinsic))
        (Bool.and
          (Nat.beq (length fnInputs) c.argCount)
          (Bool.and
            (callConvEq fnAbi c.fnAbi.conv)
            declsCompatible))

/--
Evaluate `CastKind.pointerCoercion "UnsafeFnPointer"`, coercing a safe
function pointer (`RigidTy.fnPtr inputs output .safe abi`) into an `unsafe`
function pointer (`RigidTy.fnPtr inputs output .unsafe_ abi`) while preserving
its `ProvenancePtr`.

Faults with `.ub` if `targetTy.kind` is not an `unsafe` function pointer with a
non-intrinsic `CallConv`, if `op`'s known `operandTy` is not a compatible safe
function pointer, or if `op` does not evaluate to a valid 8-byte function
pointer at offset `0` (disjoint from stack borrows in `mem.borrows`).

Reference (`compiler/rustc_middle/src/ty/adjustment.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/adjustment.rs#L21-L22>

> "/// Go from a safe fn pointer to an unsafe fn pointer.
> UnsafeFnPointer,"

Reference (The Rust Reference, "Type coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#coercion-types>

> "* Safe function pointer types to `unsafe` function pointer types"
-/
def evalUnsafeFnPointer
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
  | .ok (.ptr ptrVal sz) locals' =>
    match targetTy.kind with
    | .fnPtr dstInputs dstOutput .unsafe_ dstAbi =>
      match callConvEq dstAbi .rustIntrinsic with
      | true => .ub
      | false =>
        let validSrcTy :=
          match operandTy localDecls layouts op with
          | .none => true
          | .some { kind := .fnPtr srcInputs srcOutput .safe srcAbi, .. } =>
            Bool.and
              (callConvEq srcAbi dstAbi)
              (Bool.and
                (rigidTyListEq srcInputs dstInputs)
                (rigidTyEq srcOutput dstOutput))
          | .some _ => false
        let validPtr :=
          Bool.and
            (Nat.beq sz 8)
            (Bool.and
              (Nat.beq ptrVal.offsetBytes 0)
              (match lookupBorrow mem.borrows ptrVal.tag with
               | .some _ => false
               | .none =>
                 match mem.fnPtrs with
                 | .nil => isFnPtrAllocId ptrVal.allocId
                 | _ :: _ =>
                   match lookupFnPtr mem.fnPtrs ptrVal.allocId with
                   | .none => false
                   | .some entry =>
                     match entry.fnSig with
                     | .none => true
                     | .some (.fnPtr sigInputs sigOutput .safe sigAbi) =>
                       Bool.and
                         (callConvEq sigAbi dstAbi)
                         (Bool.and
                           (rigidTyListEq sigInputs dstInputs)
                           (rigidTyEq sigOutput dstOutput))
                     | .some _ => false))
        match Bool.and validSrcTy validPtr with
        | true => .ok (.ptr ptrVal 8) locals' mem
        | false => .ub
    | _ => .ub
  | .ok _ _ => .ub

/--
Evaluate `CastKind.pointerCoercion` when `isReifyFnPointerCoercion` holds,
coercing a zero-sized function item (`RigidTy.fnDef defPath typeArgs`, whose
runtime value is `Value.unit` or `Value.aggregate 0 .nil`) into an 8-byte
function-pointer `Value.ptr` backed by an `FnPtrEntry` in `Memory.fnPtrs`
(or delegating `"UnsafeFnPointer"` to `evalUnsafeFnPointer`).

Faults with `.ub` if `op` does not evaluate to a zero-sized value, if `op`'s
type is not a function item or non-capturing closure, if `targetTy.kind` is not
`RigidTy.fnPtr` with a non-intrinsic `CallConv`, or if a linked callee in
`mem.callees` has an incompatible signature (`checkCalleeSig = false`).

Reference (The Rust Reference, "Function pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-pointer.html>

> "Function pointer types, written using the `fn` keyword, refer to a function
> whose identity is not necessarily known at compile-time. They can be created
> via a coercion from both function items and non-capturing closures."
-/
def evalReifyFnPointer
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (coercionKind : String := "ReifyFnPointer") :
    RvalueEvalResult :=
  match isReifyFnPointerCoercion coercionKind with
  | false =>
    let opTy := operandTy localDecls layouts op
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal sz) locals' =>
      match
        unsizeArrayLen?
          coercionKind
          opTy
          targetTy.kind
          mem.borrows
          ptrVal.tag
      with
      | .some n =>
        .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar ⟨n, 8⟩ :: .nil)) locals' mem
      | .none =>
        match isSlicePtrOrRefKind targetTy.kind with
        | true => .ub
        | false =>
          match
            Bool.and
              (unsizeBorrowPermCompatible mem.borrows ptrVal.tag targetTy.kind)
              (pointerCoercionTypesCompatible opTy targetTy.kind)
          with
          | false => .ub
          | true =>
            match isDynPtrOrRefKind targetTy.kind with
            | true => .unsupported
            | false => .ok (.ptr ptrVal sz) locals' mem
    | .ok (.aggregate 0 (.ptr ptrVal sz :: metaVal :: .nil)) locals' =>
      match isWidePtrMetadata metaVal with
      | true =>
        match
          Bool.and
            (unsizeBorrowPermCompatible mem.borrows ptrVal.tag targetTy.kind)
            (Bool.and
              (pointerCoercionTypesCompatible opTy targetTy.kind)
              (Bool.not (isStrictlyThinPtrOrRefKind targetTy.kind)))
        with
        | true =>
          .ok (.aggregate 0 (.ptr ptrVal sz :: metaVal :: .nil)) locals' mem
        | false => .ub
      | false => .unsupported
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | true =>
    match stringEq coercionKind "UnsafeFnPointer" with
    | true =>
      evalUnsafeFnPointer locals op targetTy mem localDecls layouts
    | false =>
      match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok v locals' =>
        let isZstVal :=
          match v with
          | .unit => true
          | .aggregate 0 .nil => true
          | _ => false
        match isZstVal with
        | false => .ub
        | true =>
          match targetTy.kind with
          | .fnPtr fnInputs fnOutput fnSafety fnAbi =>
            match
              Bool.and
                (Bool.not (callConvEq fnAbi .rustIntrinsic))
                (reifyCoercionSafetyCompatible coercionKind fnSafety)
            with
            | false => .ub
            | true =>
              match
                extractReifyCoercionTarget?
                  coercionKind
                  (operandTy localDecls layouts op)
              with
              | .some (defPath, typeArgs) =>
                match
                  checkCalleeSig
                    mem.callees
                    defPath
                    fnInputs
                    fnOutput
                    fnAbi
                    typeArgs
                    mem.traitImpls
                with
                | false => .ub
                | true =>
                  let (allocId, mem') :=
                    internFnPtr mem defPath typeArgs (.some targetTy.kind)
                  let p : ProvenancePtr := {
                    allocId := allocId
                    offsetBytes := 0
                  }
                  .ok (.ptr p 8) locals' mem'
              | .none => .ub
          | _ => .ub

/--
Evaluate `CastKind.fnPtrToPtr`, casting an 8-byte function pointer (`Value.ptr`)
to a thin raw pointer (`*const T` or `*mut T`), preserving its `ProvenancePtr`
(`allocId` and `offsetBytes = 0`) so subsequent `CastKind.ptrToPtr` or
`CastKind.pointerExposeProvenance` casts succeed deterministically.

Faults with `.ub` if `targetTy` is not a thin raw pointer, if `op`'s known
`operandTy` is not `RigidTy.fnPtr` with a non-intrinsic `CallConv`, or if `op`
does not evaluate to an 8-byte function pointer at offset `0` (disjoint from
stack borrows in `mem.borrows`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1522-L1523>

> "FnPtrToPtr,"

Reference (The Rust Reference, "Type cast expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#type-cast-expressions>

> "* Function pointer types can be cast to any thin pointer type"
-/
def evalFnPtrToPtr
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
  | .ok (.ptr ptrVal sz) locals' =>
    let validTargetTy := isThinRawPtrTy targetTy
    let validSrcTy :=
      match operandTy localDecls layouts op with
      | .none => true
      | .some { kind := .fnPtr _ _ _ srcAbi, .. } =>
        Bool.not (callConvEq srcAbi .rustIntrinsic)
      | .some _ => false
    let validPtr :=
      Bool.and
        (Nat.beq sz 8)
        (Bool.and
          (Nat.beq ptrVal.offsetBytes 0)
          (match lookupBorrow mem.borrows ptrVal.tag with
           | .some _ => false
           | .none =>
             match mem.fnPtrs with
             | .nil => isFnPtrAllocId ptrVal.allocId
             | _ :: _ =>
               match lookupFnPtr mem.fnPtrs ptrVal.allocId with
               | .some entry =>
                 match entry.fnSig with
                 | .none => true
                 | .some (.fnPtr _ _ _ sigAbi) =>
                   Bool.not (callConvEq sigAbi .rustIntrinsic)
                 | .some _ => false
               | .none => false))
    match Bool.and validTargetTy (Bool.and validSrcTy validPtr) with
    | true => .ok (.ptr ptrVal 8) locals' mem
    | false => .ub
  | .ok _ _ => .ub

/--
Resolve every dynamic `.index idxLocal` projection element in a projection path
at borrow or address-of creation time by reading the current `usize` scalar in
`locals[idxLocal]` and replacing `.index idxLocal` with
`.constantIndex sc.bits 0 false`.

Because MIR evaluates `.index idxLocal` at the point the place expression is
evaluated (when the reference or raw pointer is created), subsequent mutations to
`idxLocal` must not shift the target element of an already-created borrow.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1160-L1165>

> "- [`Index`](ProjectionElem::Index): Like `ConstantIndex`, only legal on
>   `[T; N]` or `[T]`. However, `Index` additionally takes a local from which
>   the value of the index is computed at runtime. Computing the value of the
>   index involves interpreting the `Local` as a
>   `Place { local, projection: [] }`, and then computing its value as if done
>   via [`Operand::Copy`]. The array/slice is then indexed with the resulting
>   value. The local must have type `usize`."
-/
def resolveIndexProjections (locals : List LocalSlot) :
    List ProjectionElem → Option (List ProjectionElem)
  | .nil => .some .nil
  | .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match resolveIndexProjections locals rest with
      | .some rest' => .some (.constantIndex sc.bits 0 false :: rest')
      | .none => .none
    | _ => .none
  | p :: rest =>
    match resolveIndexProjections locals rest with
    | .some rest' => .some (p :: rest')
    | .none => .none

/--
Check whether a `RigidTy` implements the `Freeze` auto trait (that is, is not
rooted at `core::cell::UnsafeCell` or `std::cell::UnsafeCell`).

Reference (`library/core/src/marker.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/marker.rs#L890-L909>

> "/// Used to determine whether a type contains
> /// any `UnsafeCell` internally, but not through an indirection.
> ...
> #[lang = \"freeze\"]
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> pub unsafe auto trait Freeze {}
>
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}"
-/
def rigidTyIsFreeze : RigidTy → Bool
  | .adt defPath _ =>
    Bool.not
      (Bool.or
        (stringEq defPath "core::cell::UnsafeCell")
        (stringEq defPath "std::cell::UnsafeCell"))
  | _ => true

/--
Check whether a MIR `Ty` implements the `Freeze` auto trait.

Reference (`library/core/src/marker.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/marker.rs#L890-L909>

> "/// Used to determine whether a type contains
> /// any `UnsafeCell` internally, but not through an indirection.
> ...
> #[lang = \"freeze\"]
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> pub unsafe auto trait Freeze {}
>
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}"
-/
def tyIsFreeze (ty : Ty) : Bool :=
  rigidTyIsFreeze ty.kind

/--
Determine whether the pointee type of `Place` `p` is `Freeze` (`true`, meaning
shared borrows freeze the target) or `!Freeze` (`false` for `UnsafeCell`,
meaning shared borrows start in `.reserved` permission to allow interior
mutability). Defaults to `true` when `placeTy` cannot resolve a type.

Reference (`library/core/src/cell.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/cell.rs#L2200-L2205>

> "Note that whilst mutating the contents of an `&UnsafeCell<T>` (even while
> other `&UnsafeCell<T>` references alias the cell) is ok (provided you enforce
> the above invariants some other way), it is still undefined behavior to have
> multiple `&mut UnsafeCell<T>` aliases."

Reference (`library/core/src/marker.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/marker.rs#L890-L909>

> "/// Used to determine whether a type contains
> /// any `UnsafeCell` internally, but not through an indirection.
> ...
> #[lang = \"freeze\"]
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> pub unsafe auto trait Freeze {}
>
> #[unstable(feature = \"freeze\", issue = \"121675\")]
> impl<T: PointeeSized> !Freeze for UnsafeCell<T> {}"
-/
def placeIsFreeze
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place) :
    Bool :=
  match placeTy localDecls layouts p with
  | .some ty => tyIsFreeze ty
  | .none => true

/--
Evaluate an `Rvalue` in `locals` and `mem`, using `localDecls` and `layouts` to
resolve operand types, signedness, and byte layouts for `Rvalue.binaryOp`,
`Rvalue.unaryOp`, `Rvalue.cast`, and `Rvalue.aggregate`.

Tree Borrows modeling in `Rvalue.use`, `Rvalue.copyForDeref`, `Rvalue.ref`, and
`Rvalue.rawPtr`:
- Dereference reads (`.use (.copy/.move (.deref :: _))` and `.copyForDeref
  (.deref :: _)`) apply `freezeDerefReadBorrowsAt` when two or more borrow
  entries exist, freezing any overlapping foreign `.active` borrow to `.frozen`.
- Dereference reborrows (`.ref borrowKind (.deref :: restProj)`) link the new
  tag to `parentTag := .some parentPtr.tag`, perform an initial read via
  `freezeTreeBorrowsOnReadAtProj` (matching `PermissionUnprot::init_access`),
  and initialize mutable reborrows (`BorrowKind.mut _`) in
  `TreeBorrowPerm.reserved` (lazy activation upon first child write).
- Root borrows of a stack local (`.ref (.mut false) local` with
  `parentTag := .none`) start in `TreeBorrowPerm.active` because direct reads or
  writes to the root local carry `writerTag = .none` (which is foreign to all
  borrow tags rather than a parent tag in `mem.borrows`), whereas two-phase root
  borrows (`.ref (.mut true) local`) start in `TreeBorrowPerm.reserved`.

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

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L87-L94>

> "fn init_access(self) -> Option<AccessKind> {
>     // Everything except for `Cell` gets an initial read access.
>     // We never perform implicit writes for unprotected references.
>     match self {
>         PermissionUnprot::Cell => None,
>         _ => Some(AccessKind::Read)
>     }
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
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
    | .ok v locals' =>
      match op, mem.borrows with
      | .copy { local_ := ptrLoc, projection := .deref :: restProj },
        b₁ :: b₂ :: restBorrows =>
        .ok
          v
          locals'
          { mem with
            borrows :=
              freezeDerefReadBorrowsAt
                locals
                ptrLoc
                restProj
                (b₁ :: b₂ :: restBorrows) }
      | .move { local_ := ptrLoc, projection := .deref :: restProj },
        b₁ :: b₂ :: restBorrows =>
        .ok
          v
          locals'
          { mem with
            borrows :=
              freezeDerefReadBorrowsAt
                locals
                ptrLoc
                restProj
                (b₁ :: b₂ :: restBorrows) }
      | _, _ => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
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
  | .aggregate .tuple ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .copyForDeref place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' =>
      match place.projection, mem.borrows with
      | .deref :: restProj, b₁ :: b₂ :: restBorrows =>
        .ok
          v
          locals'
          { mem with
            borrows :=
              freezeDerefReadBorrowsAt
                locals
                place.local_
                restProj
                (b₁ :: b₂ :: restBorrows) }
      | _, _ => .ok v locals' mem
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
      | .shared =>
        match placeIsFreeze localDecls layouts place with
        | true => TreeBorrowPerm.frozen
        | false => TreeBorrowPerm.reserved
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
            match resolveIndexProjections locals restProj with
            | .none => .ub
            | .some resolvedProj =>
              let tag := mem.nextTag
              let fullProj :=
                match parentEntry.targetProjection with
                | .nil => resolvedProj
                | ph :: pt => ph :: appendProjections pt resolvedProj
              let reborrowPerm :=
                match borrowKind with
                | .shared => perm
                | .mut _ => TreeBorrowPerm.reserved
              let borrowsAfterRead :=
                freezeTreeBorrowsOnReadAtProj
                  mem.borrows
                  mem.borrows
                  parentEntry.targetLocal
                  (.some parentPtr.tag)
                  fullProj
                  parentEntry.rangeOffset
                  parentEntry.rangeLen
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := fullProj
                perm := reborrowPerm
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
                parentTag := .some parentPtr.tag
              }
              let mem' := {
                mem with
                borrows := entry :: borrowsAfterRead
                nextTag := Nat.add tag 1
              }
              .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | .none => .ub
      | .some (.init (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil))) =>
        match isWidePtrMetadata metaVal, restProj with
        | true, .nil =>
          match lookupBorrow mem.borrows parentPtr.tag with
          | .some parentEntry =>
            match parentEntry.perm, borrowKind with
            | .disabled, _ => .ub
            | .frozen, .mut _ => .ub
            | _, _ =>
              let tag := mem.nextTag
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := parentEntry.targetProjection
                perm := perm
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok
                (.aggregate 0
                  (.ptr { allocId := tag, offsetBytes := parentPtr.offsetBytes } sz ::
                    metaVal :: .nil))
                locals
                mem'
          | .none =>
            match borrowKind, lookupGlobalAlloc mem.globals parentPtr.allocId with
            | .shared, .some _ =>
              .ok (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil)) locals mem
            | .mut _, .some alloc =>
              match alloc.mutability with
              | .mut =>
                .ok (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil)) locals mem
              | .not => .ub
            | _, _ => .ub
        | _, _ => .ub
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        match resolveIndexProjections locals place.projection with
        | .none => .ub
        | .some resolvedProj =>
          let tag := mem.nextTag
          let entry : BorrowEntry := {
            tag := tag
            targetLocal := place.local_
            targetProjection := resolvedProj
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
            match resolveIndexProjections locals restProj with
            | .none => .ub
            | .some resolvedProj =>
              let tag := mem.nextTag
              let fullProj :=
                match parentEntry.targetProjection with
                | .nil => resolvedProj
                | ph :: pt => ph :: appendProjections pt resolvedProj
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := fullProj
                perm := perm
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
                parentTag := .some parentPtr.tag
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | .none => .ub
      | .some (.init (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil))) =>
        match isWidePtrMetadata metaVal, restProj with
        | true, .nil =>
          match lookupBorrow mem.borrows parentPtr.tag with
          | .some parentEntry =>
            match parentEntry.perm, mutability with
            | .disabled, _ => .ub
            | .frozen, .mut => .ub
            | _, _ =>
              let tag := mem.nextTag
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := parentEntry.targetProjection
                perm := perm
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok
                (.aggregate 0
                  (.ptr { allocId := tag, offsetBytes := parentPtr.offsetBytes } sz ::
                    metaVal :: .nil))
                locals
                mem'
          | .none =>
            match mutability, lookupGlobalAlloc mem.globals parentPtr.allocId with
            | .not, .some _ =>
              .ok (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil)) locals mem
            | .mut, .some alloc =>
              match alloc.mutability with
              | .mut =>
                .ok (.aggregate 0 (.ptr parentPtr sz :: metaVal :: .nil)) locals mem
              | .not => .ub
            | _, _ => .ub
        | _, _ => .ub
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        match resolveIndexProjections locals place.projection with
        | .none => .ub
        | .some resolvedProj =>
          let tag := mem.nextTag
          let entry : BorrowEntry := {
            tag := tag
            targetLocal := place.local_
            targetProjection := resolvedProj
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
  | .cast .ptrToPtr op targetTy =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.ptr ptrVal sz) locals' =>
      match isThinRawPtrTy targetTy with
      | true => .ok (.ptr ptrVal sz) locals' mem
      | false => .ub
    | .ok (.aggregate 0 (.ptr ptrVal sz :: metaVal :: .nil)) locals' =>
      match isWidePtrMetadata metaVal with
      | true =>
        match isThinRawPtrTy targetTy with
        | true => .ok (.ptr ptrVal sz) locals' mem
        | false =>
          match isWideRawPtrTy targetTy with
          | true =>
            .ok (.aggregate 0 (.ptr ptrVal sz :: metaVal :: .nil)) locals' mem
          | false => .ub
      | false => .unsupported
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast (.pointerCoercion coercionKind) op targetTy =>
    evalReifyFnPointer locals op targetTy mem localDecls layouts coercionKind
  | .cast .fnPtrToPtr op targetTy =>
    evalFnPtrToPtr locals op targetTy mem localDecls layouts
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

end Trusted.Rustc.V2026_08_01.MirSemantics
