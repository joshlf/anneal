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
Structural helper for `normalizeSubsliceProjections` that folds nested
`.subslice` and `.constantIndex` projections into an active half-open subslice
window `.some (fromA, toA)`.
-/
@[reducible]
def normalizeSubsliceProjectionsAux :
    Option (Nat × Nat) → List ProjectionElem → List ProjectionElem
  | .none, .nil => .nil
  | .some (fromA, toA), .nil => .subslice fromA toA false :: .nil
  | .none, .subslice fromA toA false :: rest =>
    match Nat.ble fromA toA with
    | true => normalizeSubsliceProjectionsAux (.some (fromA, toA)) rest
    | false =>
      .subslice fromA toA false :: normalizeSubsliceProjectionsAux .none rest
  | .none, elem :: rest =>
    elem :: normalizeSubsliceProjectionsAux .none rest
  | .some (fromA, toA), .subslice relFrom relTo false :: rest =>
    let subLen := Nat.sub toA fromA
    match Bool.and (Nat.ble relFrom relTo) (Nat.ble relTo subLen) with
    | true =>
      normalizeSubsliceProjectionsAux
        (.some (Nat.add fromA relFrom, Nat.add fromA relTo))
        rest
    | false =>
      .subslice fromA toA false ::
        .subslice relFrom relTo false ::
        normalizeSubsliceProjectionsAux .none rest
  | .some (fromA, toA), .subslice relFrom relTo true :: rest =>
    let subLen := Nat.sub toA fromA
    let endIdx := Nat.sub subLen relTo
    match Bool.and (Nat.ble relTo subLen) (Nat.ble relFrom endIdx) with
    | true =>
      normalizeSubsliceProjectionsAux
        (.some (Nat.add fromA relFrom, Nat.add fromA endIdx))
        rest
    | false =>
      .subslice fromA toA false ::
        .subslice relFrom relTo true ::
        normalizeSubsliceProjectionsAux .none rest
  | .some (fromA, toA), .constantIndex relIdx minLen false :: rest =>
    let subLen := Nat.sub toA fromA
    match Bool.and (Nat.ble minLen subLen) (Nat.ble (.succ relIdx) subLen) with
    | true =>
      .constantIndex (Nat.add fromA relIdx) minLen false ::
        normalizeSubsliceProjectionsAux .none rest
    | false =>
      .subslice fromA toA false ::
        .constantIndex relIdx minLen false ::
        normalizeSubsliceProjectionsAux .none rest
  | .some (fromA, toA), .constantIndex relOff minLen true :: rest =>
    let subLen := Nat.sub toA fromA
    match
      Bool.and
        (Nat.ble minLen subLen)
        (Bool.and (Nat.ble 1 relOff) (Nat.ble relOff subLen))
    with
    | true =>
      .constantIndex (Nat.add fromA (Nat.sub subLen relOff)) minLen false ::
        normalizeSubsliceProjectionsAux .none rest
    | false =>
      .subslice fromA toA false ::
        .constantIndex relOff minLen true ::
        normalizeSubsliceProjectionsAux .none rest
  | .some (fromA, toA), elem :: rest =>
    .subslice fromA toA false :: elem :: normalizeSubsliceProjectionsAux .none rest

/--
Normalize adjacent `.subslice` and `.constantIndex` projections in a
transparent-stripped projection path so nested subslice/element accesses carry
root-relative indices for overlap and projection evaluation.
-/
@[reducible]
def normalizeSubsliceProjections (proj : List ProjectionElem) : List ProjectionElem :=
  normalizeSubsliceProjectionsAux .none proj

/--
Test whether two transparent-stripped, subslice-normalized projection paths
within the same root local overlap.

- If either list is `.nil`, one projection is a prefix of the other, so they
  overlap (`true`).
- Distinct `.field` indices (`idxA != idxB`), distinct `.constantIndex` offsets
  with matching `fromEnd` polarity, disjoint `.subslice` intervals
  (`[fromA, toA)` vs `[fromB, toB)` with `toA <= fromB` or `toB <= fromA`),
  a `.subslice [fromA, toA)` and `.constantIndex idxB` outside `[fromA, toA)`
  (`idxB < fromA` or `idxB >= toA`), and distinct `.downcast` enum variants are
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
  | .subslice fromA toA false :: restA,
    .subslice fromB toB false :: restB =>
    match
      Bool.or
        (Nat.ble toA fromB)
        (Nat.ble toB fromA)
    with
    | true => false
    | false =>
      match Bool.and (Nat.beq fromA fromB) (Nat.beq toA toB) with
      | true => projectionsOverlapAux restA restB
      | false => true
  | .subslice fromA toA false :: _,
    .constantIndex idxB _ false :: _ =>
    match
      Bool.or
        (Bool.not (Nat.ble fromA idxB))
        (Nat.ble toA idxB)
    with
    | true => false
    | false => true
  | .constantIndex idxA _ false :: _,
    .subslice fromB toB false :: _ =>
    match
      Bool.or
        (Bool.not (Nat.ble fromB idxA))
        (Nat.ble toB idxA)
    with
    | true => false
    | false => true
  | .downcast _ varA :: restA, .downcast _ varB :: restB =>
    match Nat.beq varA varB with
    | true => projectionsOverlapAux restA restB
    | false => false
  | _ :: _, _ :: _ => true

/--
Test whether two projection paths within the same root local overlap after
stripping transparent `.opaqueCast` and `.unwrapUnsafeBinder` projections and
normalizing nested `.subslice` projections.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1278>

> "/// A field (e.g., `f` in `_1.f`) is one variant of [`ProjectionElem`]. Conceptually,
> /// rustc can identify that a field projection refers to either two different regions of memory
> /// or the same one between base and projectedmir type."
-/
def projectionsOverlap (projA projB : List ProjectionElem) : Bool :=
  projectionsOverlapAux
    (normalizeSubsliceProjections (stripTransparentProjections projA))
    (normalizeSubsliceProjections (stripTransparentProjections projB))

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
Byte width of a thin pointer or fat-pointer metadata word in `layouts`,
defaulting to `8` bytes (64-bit target) when `layouts.pointerBits == 0`.
-/
@[reducible]
def layoutPointerBytes (layouts : LayoutTable) : Nat :=
  match Nat.beq layouts.pointerBits 0 with
  | true => 8
  | false => Nat.div layouts.pointerBits 8

/--
Evaluate a `ConstValue` to a runtime `Value`, decoding `ConstValue.slice` to the
2-element fat-pointer aggregate `Value.aggregate 0 [dataVal, Value.scalar ⟨meta, ptrBytes⟩]`
and `ConstValue.indirect allocId offset` by decoding `ty` from `globals` via
`decodeValueFromBytes`.

Reference (`compiler/rustc_middle/src/mir/interpret/value.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/value.rs#L31-L65>

> "pub enum ConstValue {
>     ZeroSized,
>     Scalar(Scalar),
>     Slice { alloc_id: AllocId, meta: u64 },
>     Indirect { alloc_id: AllocId, offset: Size },
> }"
-/
def evalConstValue
    (cv : ConstValue)
    (ty : Ty := { kind := .tuple .nil, layoutIdx := 0 })
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Option Value :=
  let ptrBytes := layoutPointerBytes layouts
  match cv with
  | .zeroSized => .some .unit
  | .scalar (.int s) => .some (.scalar s)
  | .scalar (.ptr p sz) => .some (.ptr p sz)
  | .slice (.ptr p sz) lenMeta =>
    .some (.aggregate 0 (.ptr p sz :: .scalar ⟨lenMeta, ptrBytes⟩ :: .nil))
  | .slice (.int s) lenMeta =>
    let p : ProvenancePtr := {
      allocId := Nat.div s.bits 65536
      offsetBytes := Nat.mod s.bits 65536
    }
    .some (.aggregate 0 (.ptr p ptrBytes :: .scalar ⟨lenMeta, ptrBytes⟩ :: .nil))
  | .indirect allocId offset =>
    match lookupGlobalAlloc globals allocId with
    | .none => .none
    | .some alloc =>
      let sz :=
        match rigidTyByteSize layouts ty with
        | .some n => n
        | .none =>
          match tyScalarBytes ty with
          | .some n => n
          | .none => Nat.sub (length alloc.bytes) offset
      match globalAllocSliceToAbstractBytes alloc offset sz with
      | .some absBytes =>
        match decodeValueFromBytes defaultCodecFuel layouts ty absBytes with
        | .some v => .some v
        | .none =>
          match intCastTargetBytes ty.kind with
          | .some n =>
            match readGlobalScalar alloc offset n with
            | .some sc => .some (.scalar sc)
            | .none => .none
          | .none => .none
      | .none => .none
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
  | val, .unwrapUnsafeBinder _ :: rest =>
    readProjectedValue locals val rest
  | _, _ :: _ => .unsupported

/--
Concatenate two `List Value` sequences in order.
-/
@[reducible]
def appendValueList : List Value → List Value → List Value
  | .nil, ys => ys
  | x :: xs, ys => x :: appendValueList xs ys

/--
Replace the subslice of `elems` specified by `ProjectionElem.subslice fromIdx
toIdx fromEnd` with `newSubElems`, returning `.none` if the indices are out of
bounds, inverted, or if `length newSubElems` does not equal the subslice length.
-/
def replaceSubslice
    (elems : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (newSubElems : List Value) :
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
      match Nat.beq (length newSubElems) count with
      | false => .none
      | true =>
        let prefixElems := takeValues fromIdx elems
        let suffixElems := dropValues endIdx elems
        .some (appendValueList prefixElems (appendValueList newSubElems suffixElems))

/--
Update the `Value` at index `idx` in `fields`, extending `fields` with
`.unit` padding elements when `idx` exceeds the current list length (for
example, when writing a non-zero field index of a union aggregate
previously initialized via field `0`).

Reference (The Rust Reference, "Union types"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html#reading-and-writing-union-fields>

> "Unions have no notion of an \"active field\". Instead, every union access
> just interprets the storage as the type of the field used for the access."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
@[reducible]
def setOrExtendFields : List Value → Nat → Value → List Value
  | .nil, .zero, v => v :: .nil
  | .nil, .succ n, v => .unit :: setOrExtendFields .nil n v
  | _ :: rest, .zero, v => v :: rest
  | hd :: rest, .succ n, v => hd :: setOrExtendFields rest n v

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
  | .aggregate 0 fields,
    .subslice fromIdx toIdx fromEnd :: rest,
    newVal =>
    match extractSubslice fields fromIdx toIdx fromEnd with
    | .some subElems =>
      match writeProjectedValue locals (.aggregate 0 subElems) rest newVal with
      | .ok (.aggregate 0 updatedSubElems) =>
        match replaceSubslice fields fromIdx toIdx fromEnd updatedSubElems with
        | .some fields' => .ok (.aggregate 0 fields')
        | .none => .ub
      | .ok _ => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .none => .ub
  | _, .subslice _ _ _ :: _, _ => .ub
  | val, .opaqueCast _ :: rest, newVal =>
    writeProjectedValue locals val rest newVal
  | val, .unwrapUnsafeBinder _ :: rest, newVal =>
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
Determine whether a trailing projection path `restProj` after a dereference can
be satisfied directly on a scalar value (`[]`, `.opaqueCast`, `.unwrapUnsafeBinder`,
or zero-index newtype `.field 0`).
-/
@[reducible]
def isScalarCompatibleProj : List ProjectionElem → Bool
  | .nil => true
  | .opaqueCast _ :: rest => isScalarCompatibleProj rest
  | .unwrapUnsafeBinder _ :: rest => isScalarCompatibleProj rest
  | .field .zero _ :: rest => isScalarCompatibleProj rest
  | _ :: _ => false

/--
Infer an unsigned integer `RigidTy` from a primitive byte stride (`1`, `2`, `4`,
`8`, or `16`).
-/
@[reducible]
def uintRigidTyOfStride (strideBytes : Nat) : RigidTy :=
  match strideBytes with
  | 2 => .uint .u16
  | 4 => .uint .u32
  | 8 => .uint .u64
  | 16 => .uint .u128
  | _ => .uint .u8

/--
Decode and project a dereferenced global allocation `alloc` at `offset` with
pointer/access width `sz` and trailing projections `restProj`.

When `pointeeTyOpt` resolves to a scalar type (or when `pointeeTyOpt` is `.none`,
`layouts` has no aggregate entry at index `0`, `restProj` is scalar-compatible,
and `readGlobalScalar alloc offset sz` succeeds), reads the scalar directly via
`readGlobalScalar`. When `readGlobalScalar` does not apply (non-scalar aggregate,
tuple, or array `pointeeTy`, non-primitive layout in `layouts`, non-scalar width
`sz`, or aggregate/array projection in `restProj`), decodes the global bytes via
`decodeValueFromBytes` and projects `restProj`.
-/
def evalGlobalDerefRead
    (locals : List LocalSlot)
    (alloc : CapturedAllocation)
    (offset sz : Nat)
    (restProj : List ProjectionElem)
    (layouts : LayoutTable := emptyLayoutTable)
    (pointeeTyOpt : Option Ty := .none) :
    PlaceReadResult :=
  match pointeeTyOpt with
  | .some pointeeTy =>
    match intCastTargetBytes pointeeTy.kind with
    | .some n =>
      match readGlobalScalar alloc offset n with
      | .some sc =>
        match readProjectedValue locals (.scalar sc) restProj with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | .none =>
      let byteSz :=
        match rigidTyByteSize layouts pointeeTy with
        | .some n => n
        | .none => Nat.sub (length alloc.bytes) offset
      match globalAllocSliceToAbstractBytes alloc offset byteSz with
      | .some absBytes =>
        match decodeValueFromBytes defaultCodecFuel layouts pointeeTy absBytes with
        | .some decodedVal =>
          match readProjectedValue locals decodedVal restProj with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .none => .ub
      | .none => .ub
  | .none =>
    let nonPrimLayoutOpt : Option (Ty × Nat) :=
      match LayoutTable.lookup layouts 0 with
      | .some l =>
        match l.fields with
        | .primitive => .none
        | .array stride count =>
          .some
            ({ kind := .array (uintRigidTyOfStride stride.bytes) count, layoutIdx := 0 },
             l.size.bytes)
        | _ =>
          .some ({ kind := .adt "" .nil, layoutIdx := 0 }, l.size.bytes)
      | .none => .none
    match nonPrimLayoutOpt with
    | .some (inferredTy, byteSz) =>
      match globalAllocSliceToAbstractBytes alloc offset byteSz with
      | .some absBytes =>
        match decodeValueFromBytes defaultCodecFuel layouts inferredTy absBytes with
        | .some decodedVal =>
          match readProjectedValue locals decodedVal restProj with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .none => .ub
      | .none => .ub
    | .none =>
      match isScalarCompatibleProj restProj with
      | true =>
        match readGlobalScalar alloc offset sz with
        | .some sc =>
          match readProjectedValue locals (.scalar sc) restProj with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | .none =>
          match Nat.beq sz 0 with
          | true =>
            match Nat.ble offset (length alloc.bytes) with
            | true =>
              match readProjectedValue locals .unit restProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | false => .ub
          | false =>
            match globalAllocSliceToAbstractBytes alloc offset sz with
            | .some absBytes =>
              let arrTy : Ty := { kind := .array (.uint .u8) sz, layoutIdx := 0 }
              match decodeValueFromBytes defaultCodecFuel layouts arrTy absBytes with
              | .some decodedVal =>
                match readProjectedValue locals decodedVal restProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
              | .none => .ub
            | .none => .ub
      | false =>
        match Nat.ble offset (length alloc.bytes) with
        | false => .ub
        | true =>
          let remBytes := Nat.sub (length alloc.bytes) offset
          match globalAllocSliceToAbstractBytes alloc offset remBytes with
          | .some absBytes =>
            let arrTy : Ty := { kind := .array (.uint .u8) remBytes, layoutIdx := 0 }
            match decodeValueFromBytes defaultCodecFuel layouts arrTy absBytes with
            | .some decodedVal =>
              match readProjectedValue locals decodedVal restProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
            | .none => .ub
          | .none => .ub

/--
Compute the total byte size of a runtime `Value` using structural recursion on
`fuel` (supporting nested tuple, struct, and multi-dimensional array
aggregates).
-/
@[reducible]
def inferValueByteSizeAux : Nat → Value → Option Nat
  | _, .unit => .some 0
  | _, .scalar sc => .some sc.sizeBytes
  | _, .ptr _ sz => .some sz
  | _, .aggregate _ .nil => .some 0
  | .zero, .aggregate _ (_ :: _) => .none
  | .succ fuel, .aggregate 0 (f :: fs) =>
    match inferValueByteSizeAux fuel f, inferValueByteSizeAux fuel (.aggregate 0 fs) with
    | .some szF, .some szFs => .some (Nat.add szF szFs)
    | _, _ => .none
  | _, .aggregate (.succ _) (_ :: _) => .none

/--
Infer the element byte stride of a runtime array/slice element list `elems` when
no static `pointeeTyOpt` is available, defaulting to `1` byte.
-/
@[reducible]
def inferElemListByteStride : List Value → Nat
  | .scalar sc :: _ => sc.sizeBytes
  | .ptr _ sz :: _ => sz
  | .unit :: _ => 0
  | .aggregate 0 fields :: _ =>
    match inferValueByteSizeAux 8 (.aggregate 0 fields) with
    | .some sz => sz
    | .none => 1
  | _ => 1

/--
Divide `rem` by positive `stride` using structural recursion on `fuel`,
returning `.some acc` when `stride` divides `rem` evenly and `.none` otherwise.
-/
@[reducible]
def exactByteDivAux : Nat → Nat → Nat → Nat → Option Nat
  | _, .zero, _, acc => .some acc
  | .zero, .succ _, _, _ => .none
  | .succ fuel, rem, stride, acc =>
    match Nat.ble stride rem with
    | false => .none
    | true => exactByteDivAux fuel (Nat.sub rem stride) stride (.succ acc)

/--
Convert a byte offset `offsetBytes` into an element index given element byte
stride `elemSz`, returning `.some 0` when `offsetBytes == 0`,
`.some (offsetBytes / elemSz)` when `elemSz > 0` divides `offsetBytes`, and
`.none` otherwise.
-/
@[reducible]
def byteOffsetToElemIdx? (offsetBytes elemSz : Nat) : Option Nat :=
  match Nat.beq offsetBytes 0 with
  | true => .some 0
  | false =>
    match Nat.beq elemSz 0 with
    | true => .none
    | false => exactByteDivAux offsetBytes offsetBytes elemSz 0

/--
If `proj` ends with a forward `.constantIndex baseIdx minLen false`, split `proj`
into `(initProj, baseIdx, minLen)`; otherwise return `.none`.
-/
@[reducible]
def splitLastConstantIndex? : List ProjectionElem → Option (List ProjectionElem × Nat × Nat)
  | .nil => .none
  | .constantIndex baseIdx minLen false :: .nil => .some (.nil, baseIdx, minLen)
  | elem :: rest =>
    match splitLastConstantIndex? rest with
    | .some (initProj, baseIdx, minLen) => .some (elem :: initProj, baseIdx, minLen)
    | .none => .none

/--
Resolve the backing array/subslice element list `(containerProj, baseIdx, elems)`
for a slice fat pointer or thin element pointer whose `BorrowEntry` has
`targetProjection`:
- When `targetProjection` (after stripping transparent projections and
  normalizing subslices) ends with `.constantIndex baseIdx minLen false`
  (e.g. `&raw const arr[baseIdx]` passed to `core::ptr::slice_from_raw_parts`,
  including when each array element is itself a tuple or struct
  `.aggregate 0 fields`), resolves the parent aggregate at `initProj`, validates
  `minLen <= length elems` and `baseIdx <= length elems`, and returns
  `.some (initProj, baseIdx, elems)`.
- Otherwise, when `readProjectedValue indexLocals targetRootVal targetProjection`
  yields `.ok (.aggregate 0 elems)`, returns `.some (targetProjection, 0, elems)`.
-/
@[reducible]
def readSliceBackingAggregate?
    (indexLocals : List LocalSlot)
    (targetRootVal : Value)
    (targetProjection : List ProjectionElem)
    (minCount : Nat := 0)
    (expectedElemSzOpt : Option Nat := .none) :
    Option (List ProjectionElem × Nat × List Value) :=
  let normProj :=
    normalizeSubsliceProjections (stripTransparentProjections targetProjection)
  match splitLastConstantIndex? normProj with
  | .some (initProj, baseIdx, minLen) =>
    match readProjectedValue indexLocals targetRootVal initProj with
    | .ok (.aggregate 0 outerElems) =>
      let outerValid :=
        Bool.and
          (Nat.ble minLen (length outerElems))
          (Nat.ble (Nat.add baseIdx minCount) (length outerElems))
      let preferInner :=
        match readProjectedValue indexLocals targetRootVal targetProjection with
        | .ok (.aggregate 0 innerElems) =>
          match expectedElemSzOpt with
          | .some expSz =>
            let outerStride := inferElemListByteStride outerElems
            let innerStride := inferElemListByteStride innerElems
            Bool.and
              (Bool.not (Nat.beq outerStride expSz))
              (Bool.and
                (Nat.beq innerStride expSz)
                (Nat.ble minCount (length innerElems)))
          | .none =>
            Bool.and
              (Bool.not outerValid)
              (Bool.and
                (Nat.ble 1 minCount)
                (Nat.ble minCount (length innerElems)))
        | _ => false
      match preferInner with
      | true =>
        match readProjectedValue indexLocals targetRootVal targetProjection with
        | .ok (.aggregate 0 innerElems) => .some (targetProjection, 0, innerElems)
        | _ => .none
      | false =>
        match
          Bool.and
            (Nat.ble minLen (length outerElems))
            (Nat.ble baseIdx (length outerElems))
        with
        | true => .some (initProj, baseIdx, outerElems)
        | false => .none
    | _ => .none
  | .none =>
    match readProjectedValue indexLocals targetRootVal targetProjection with
    | .ok (.aggregate 0 elems) => .some (targetProjection, 0, elems)
    | _ => .none

/--
If `proj` ends with `.subslice fromIdx toIdx fromEnd`, split `proj` into
`(initProj, fromIdx, toIdx, fromEnd)`; otherwise return `.none`.
-/
@[reducible]
def splitLastSubslice? : List ProjectionElem → Option (List ProjectionElem × Nat × Nat × Bool)
  | .nil => .none
  | .subslice fromIdx toIdx fromEnd :: .nil => .some (.nil, fromIdx, toIdx, fromEnd)
  | elem :: rest =>
    match splitLastSubslice? rest with
    | .some (initProj, fromIdx, toIdx, fromEnd) =>
      .some (elem :: initProj, fromIdx, toIdx, fromEnd)
    | .none => .none

/--
Return `true` when `proj` ends with `.subslice`.
-/
@[reducible, simp]
def endsWithSubslice : List ProjectionElem → Bool
  | .nil => false
  | .subslice _ _ _ :: .nil => true
  | _ :: rest => endsWithSubslice rest

/--
Return `true` when dereferencing a stack-backed thin pointer with `BorrowEntry`
`targetProjection` at `offsetBytes` requires array/subslice element offset
resolution (`targetProjection` is non-empty and either ends with `.subslice` or
has `offsetBytes > 0`). Reduces immediately to `false` when `targetProjection`
is `.nil`.
-/
@[reducible, simp]
def needsThinPtrElemResolution
    (targetProjection : List ProjectionElem)
    (offsetBytes : Nat) :
    Bool :=
  match targetProjection with
  | .nil => false
  | pHead :: pTail =>
    let norm :=
      normalizeSubsliceProjections (stripTransparentProjections (pHead :: pTail))
    match endsWithSubslice norm with
    | true => true
    | false => Bool.not (Nat.beq offsetBytes 0)

/--
Return `true` when `proj` (after stripping transparent projections) begins with
`.constantIndex`, `.index`, or `.subslice`.
-/
@[reducible]
def startsWithArrayOrSliceProj (proj : List ProjectionElem) : Bool :=
  match stripTransparentProjections proj with
  | .constantIndex _ _ _ :: _ => true
  | .index _ :: _ => true
  | .subslice _ _ _ :: _ => true
  | _ => false

/--
Resolve the effective target projection path on `entry.targetLocal` when
dereferencing, writing through, or reborrowing a stack-backed thin pointer
`Value.ptr ptrVal sz` (`BorrowEntry` `entry`) with post-deref projection suffix
`restProj`.

- When `ptrVal.offsetBytes == 0` and the pointer is not an element pointer into
  a subslice or array (`isElemPtrAtZero == false`), returns the direct
  concatenation `entry.targetProjection ++ restProj`.
- When `ptrVal.offsetBytes > 0` (e.g. after `BinOp.offset` on `&raw const arr[i]`
  or `slice.as_ptr().offset(k)`), or when `ptrVal.offsetBytes == 0` on an element
  pointer into a `.subslice` (or into an `.array` when `pointeeTyOpt` is a
  non-array element type), translates `ptrVal.offsetBytes` into an element index
  via `byteOffsetToElemIdx?`, verifies in-bounds access against the backing
  array/subslice aggregate (`elemIdx < length elems`), and returns the
  normalized projection path (or `.none` on misaligned or out-of-bounds offset).
-/
@[reducible]
def resolveStackThinPtrTargetProj?
    (indexLocals : List LocalSlot)
    (targetRootVal : Value)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (pointeeTyOpt : Option Ty := .none) :
    Option (List ProjectionElem) :=
  let rawFullProj :=
    match entry.targetProjection with
    | .nil => restProj
    | ph :: pt => ph :: appendProjections pt restProj
  let normTargetProj :=
    normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
  let isElemPtrAtZero : Bool :=
    match endsWithSubslice normTargetProj, pointeeTyOpt with
    | false, .none => false
    | _, _ =>
      match startsWithArrayOrSliceProj restProj with
      | true => false
      | false =>
        match endsWithSubslice normTargetProj with
        | true => true
        | false =>
          match pointeeTyOpt with
          | .none => false
          | .some pointeeTy =>
            let pointeeIsNotSeq :=
              match pointeeTy.kind with
              | .array _ _ => false
              | .slice _ => false
              | _ => true
            match pointeeIsNotSeq with
            | false => false
            | true =>
              match
                placeTy
                  localDecls
                  layouts
                  { local_ := entry.targetLocal, projection := normTargetProj }
              with
              | .some { kind := .array _ _, .. } => true
              | .some { kind := .slice _, .. } => true
              | _ => false
  match Nat.beq ptrVal.offsetBytes 0, isElemPtrAtZero with
  | true, false => .some rawFullProj
  | _, _ =>
    match splitLastConstantIndex? normTargetProj with
    | .some (initProj, baseIdx, minLen) =>
      match readProjectedValue indexLocals targetRootVal initProj with
      | .ok (.aggregate 0 elems) =>
        let elemSz := inferElemListByteStride elems
        match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
        | .none => .none
        | .some elemDelta =>
          let idx := Nat.add baseIdx elemDelta
          match
            Bool.and
              (Nat.ble minLen (length elems))
              (Nat.ble (.succ idx) (length elems))
          with
          | false => .none
          | true =>
            let elemProj := ProjectionElem.constantIndex idx 0 false :: restProj
            let combined :=
              match initProj with
              | .nil => elemProj
              | ph :: pt => ph :: appendProjections pt elemProj
            .some (normalizeSubsliceProjections combined)
      | _ => .none
    | .none =>
      match readProjectedValue indexLocals targetRootVal normTargetProj with
      | .ok (.aggregate 0 elems) =>
        let elemSz := inferElemListByteStride elems
        match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
        | .none => .none
        | .some elemOffset =>
          match endsWithSubslice normTargetProj, stripTransparentProjections restProj with
          | false, .constantIndex relIdx minLen false :: tailProj =>
            let idx := Nat.add elemOffset relIdx
            let remLen := Nat.sub (length elems) elemOffset
            match
              Bool.and
                (Nat.ble minLen remLen)
                (Nat.ble (.succ idx) (length elems))
            with
            | false => .none
            | true =>
              let elemProj := ProjectionElem.constantIndex idx 0 false :: tailProj
              let combined :=
                match normTargetProj with
                | .nil => elemProj
                | ph :: pt => ph :: appendProjections pt elemProj
              .some (normalizeSubsliceProjections combined)
          | _, _ =>
            match Nat.ble (.succ elemOffset) (length elems) with
            | false => .none
            | true =>
              let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: restProj
              let combined :=
                match normTargetProj with
                | .nil => elemProj
                | ph :: pt => ph :: appendProjections pt elemProj
              .some (normalizeSubsliceProjections combined)
      | _ => .none

/--
Dereference and project a slice fat pointer
`Value.aggregate 0 [Value.ptr ptrVal ptrSz, Value.scalar lenSc]` through
`borrows` or `globals`.
-/
def evalSliceFatPtrDerefRead
    (locals : List LocalSlot)
    (ptrVal : ProvenancePtr)
    (ptrSz : Nat)
    (lenSc : ScalarInt)
    (restProj : List ProjectionElem)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (pointeeTyOpt : Option Ty := .none) :
    PlaceReadResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    Bool.and
      (Nat.beq ptrSz ptrBytes)
      (Nat.beq lenSc.sizeBytes ptrBytes)
  with
  | false => .ub
  | true =>
    let elemKind : RigidTy :=
      match pointeeTyOpt with
      | .some { kind := .slice ek, .. } => ek
      | .some { kind := .array ek _, .. } => ek
      | .some { kind := .str, .. } => .uint .u8
      | _ =>
        match LayoutTable.lookup layouts 0 with
        | .some l =>
          match l.fields with
          | .primitive => uintRigidTyOfStride l.size.bytes
          | .array stride _ => uintRigidTyOfStride stride.bytes
          | _ => .uint .u8
        | .none => .uint .u8
    match lookupBorrow borrows ptrVal.tag with
    | .some entry =>
      match entry.perm with
      | .disabled => .ub
      | _ =>
        let targetRootOpt : Option Value :=
          match get? locals entry.targetLocal with
          | .some (.init v) => .some v
          | .some _ => .none
          | .none =>
            match get? callerLocals entry.targetLocal with
            | .some (.init v) => .some v
            | _ => .none
        match targetRootOpt with
        | .some targetRootVal =>
          let expSzOpt : Option Nat :=
            match pointeeTyOpt with
            | .some _ => rigidTyKindByteSize elemKind
            | .none => .none
          match
            readSliceBackingAggregate?
              locals
              targetRootVal
              entry.targetProjection
              lenSc.bits
              expSzOpt
          with
          | .some (_, baseIdx, elems) =>
            let elemSz :=
              match pointeeTyOpt with
              | .some _ =>
                match rigidTyKindByteSize elemKind with
                | .some n => n
                | .none => inferElemListByteStride elems
              | .none => inferElemListByteStride elems
            match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
            | .none => .ub
            | .some rawElemOffset =>
              let elemOffset := Nat.add rawElemOffset baseIdx
              let remElems := dropValues elemOffset elems
              match Nat.ble lenSc.bits (length remElems) with
              | false => .ub
              | true =>
                let sliceVal := Value.aggregate 0 (takeValues lenSc.bits remElems)
                match readProjectedValue locals sliceVal restProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
          | .none =>
            match readProjectedValue locals targetRootVal entry.targetProjection with
            | .ok .unit =>
              match
                Bool.and
                  (Nat.beq ptrVal.offsetBytes 0)
                  (Nat.beq lenSc.bits 0)
              with
              | false => .ub
              | true =>
                match readProjectedValue locals (.aggregate 0 .nil) restProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
            | _ => .ub
        | .none => .ub
    | .none =>
      match lookupGlobalAlloc globals ptrVal.allocId with
      | .some alloc =>
        let elemSz :=
          match rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
          | .some n => n
          | .none => 1
        let totalBytes := Nat.mul lenSc.bits elemSz
        match globalAllocSliceToAbstractBytes alloc ptrVal.offsetBytes totalBytes with
        | .some absBytes =>
          let sliceArrTy : Ty := { kind := .array elemKind lenSc.bits, layoutIdx := 0 }
          match decodeValueFromBytes defaultCodecFuel layouts sliceArrTy absBytes with
          | .some decodedVal =>
            match readProjectedValue locals decodedVal restProj with
            | .ok fieldVal => .ok fieldVal locals
            | .ub => .ub
            | .unsupported => .unsupported
          | .none => .ub
        | .none => .ub
      | .none =>
        let isNonNullEmptySlice :=
          Bool.and
            (Nat.beq lenSc.bits 0)
            (Bool.not
              (Bool.and
                (Nat.beq ptrVal.allocId 0)
                (Nat.beq ptrVal.offsetBytes 0)))
        match isNonNullEmptySlice with
        | false => .ub
        | true =>
          match readProjectedValue locals (.aggregate 0 .nil) restProj with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported

/--
Evaluate a `Place` read in `locals` with active borrow table `borrows`, global
allocations `globals`, layout table `layouts`, caller locals `callerLocals`, and
local declarations `localDecls`.

When `p.projection` begins with `.deref` and targets a global allocation in
`globals` (not backed by a stack borrow in `borrows`), uses `pointeeTy` from
`localDecls` (or `layouts` / projection structure) to decode non-scalar
aggregates and arrays via `decodeValueFromBytes` when `readGlobalScalar` does
not apply.
-/
def evalPlaceRead
    (locals : List LocalSlot)
    (p : Place)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil) :
    PlaceReadResult :=
  match p.projection with
  | .deref :: restProj =>
    let pointeeTyOpt :=
      placeTy localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
    match get? locals p.local_ with
    | .some (.init (.ptr ptrVal sz)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .disabled => .ub
        | _ =>
          match get? locals entry.targetLocal with
          | .some (.init targetRootVal) =>
            match
              resolveStackThinPtrTargetProj?
                locals
                targetRootVal
                entry
                ptrVal
                restProj
                localDecls
                layouts
                pointeeTyOpt
            with
            | .none => .ub
            | .some fullProj =>
              match readProjectedValue locals targetRootVal fullProj with
              | .ok fieldVal => .ok fieldVal locals
              | .ub => .ub
              | .unsupported => .unsupported
          | .some _ => .ub
          | .none =>
            match get? callerLocals entry.targetLocal with
            | .some (.init targetRootVal) =>
              match
                resolveStackThinPtrTargetProj?
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
                  localDecls
                  layouts
                  pointeeTyOpt
              with
              | .none => .ub
              | .some fullProj =>
                match readProjectedValue locals targetRootVal fullProj with
                | .ok fieldVal => .ok fieldVal locals
                | .ub => .ub
                | .unsupported => .unsupported
            | _ => .ub
      | .none =>
        match lookupGlobalAlloc globals ptrVal.allocId with
        | .some alloc =>
          evalGlobalDerefRead
            locals
            alloc
            ptrVal.offsetBytes
            sz
            restProj
            layouts
            pointeeTyOpt
        | .none => .ub
    | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
      evalSliceFatPtrDerefRead
        locals
        ptrVal
        ptrSz
        lenSc
        restProj
        borrows
        globals
        layouts
        callerLocals
        pointeeTyOpt
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

/--
Evaluate an `Operand` in `locals` with active borrow table `borrows`, global
allocations `globals`, and layout table `layouts`, supporting root locals
(`projection = []`), dereferences (`ProjectionElem.deref` resolved through
`borrows` or `globals`), indirect and slice global constants
(`ConstValue.indirect` and `ConstValue.slice`), and nested `.field`, `.downcast`,
`.index`, `.constantIndex`, `.subslice`, `.opaqueCast`, and `.unwrapUnsafeBinder`
projections.

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
      | .some _ =>
        match evalConstValue (.indirect allocId offset) c.ty globals layouts with
        | .some v => .ok v locals
        | .none => .ub
      | .none => .unsupported
    | .unevaluated _ => .unsupported
    | cv =>
      match evalConstValue cv c.ty globals layouts with
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
            match
              needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
            with
            | false =>
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
            | true =>
              match get? locals entry.targetLocal with
              | .some (.init targetRootVal) =>
                match
                  resolveStackThinPtrTargetProj?
                    locals
                    targetRootVal
                    entry
                    ptrVal
                    restProj
                with
                | .none => .ub
                | .some fullProj =>
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
              | .some _ => .ub
              | .none =>
                match get? callerLocals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                | _ => .ub
        | .none =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            evalGlobalDerefRead
              locals
              alloc
              ptrVal.offsetBytes
              sz
              restProj
              layouts
              .none
          | .none => .ub
      | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
        evalSliceFatPtrDerefRead
          locals
          ptrVal
          ptrSz
          lenSc
          restProj
          borrows
          globals
          layouts
          callerLocals
          .none
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
            match
              needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
            with
            | false =>
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
            | true =>
              match get? locals entry.targetLocal with
              | .some (.init targetRootVal) =>
                match
                  resolveStackThinPtrTargetProj?
                    locals
                    targetRootVal
                    entry
                    ptrVal
                    restProj
                with
                | .none => .ub
                | .some fullProj =>
                  match readProjectedValue locals targetRootVal fullProj with
                  | .ok fieldVal => .ok fieldVal locals
                  | .ub => .ub
                  | .unsupported => .unsupported
              | .some _ => .ub
              | .none =>
                match get? callerLocals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                | _ => .ub
        | .none =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            evalGlobalDerefRead
              locals
              alloc
              ptrVal.offsetBytes
              sz
              restProj
              layouts
              .none
          | .none => .ub
      | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
        evalSliceFatPtrDerefRead
          locals
          ptrVal
          ptrSz
          lenSc
          restProj
          borrows
          globals
          layouts
          callerLocals
          .none
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
Extract the underlying `ProvenancePtr` from either a thin pointer (`Value.ptr`)
or a 2-element slice fat pointer
(`Value.aggregate 0 [Value.ptr ptrVal 8, Value.scalar ⟨_, 8⟩]`).
-/
@[reducible]
def extractDerefPtrVal? : Value → Option ProvenancePtr
  | .ptr ptrVal _ => .some ptrVal
  | .aggregate 0 (.ptr ptrVal 8 :: .scalar ⟨_, 8⟩ :: .nil) => .some ptrVal
  | _ => .none

/--
Resolve dynamic `.index idxLocal` projection elements against the current
`locals` state, converting each `.index idxLocal` whose index local holds an
initialized `.scalar sc` into `.constantIndex sc.bits 0 false` so subsequent
dereferences and overlap checks do not depend on whether the temporary index
local remains live.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1166-L1185>

> "- [`Index`](ProjectionElem::Index): `Index` projections take their parent
>   place and create a place referring to an element of an array or slice,
>   indexed by the given `Local`. Note that the `Local` must be initialized
>   before the projection is used."

Reference (The Rust Reference, "Array and slice indexing expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/array-expr.html#array-and-slice-indexing-expressions>

> "Array and slice-typed values can be indexed by writing a
> square-bracket-enclosed expression of type usize (the index) after them."
-/
@[reducible]
def resolveBorrowProjectionElems
    (locals : List LocalSlot) :
    List ProjectionElem → Option (List ProjectionElem)
  | .nil => .some .nil
  | .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match resolveBorrowProjectionElems locals rest with
      | .some rest' => .some (.constantIndex sc.bits 0 false :: rest')
      | .none => .none
    | _ => .none
  | elem :: rest =>
    match resolveBorrowProjectionElems locals rest with
    | .some rest' => .some (elem :: rest')
    | .none => .none

/--
Alias for `resolveBorrowProjectionElems`.
-/
abbrev resolveIndexProjections := resolveBorrowProjectionElems

/--
Compute the effective root projection path on `entry.targetLocal` accessed by a
dereferenced write through `ptrOrFatVal` (`BorrowEntry` `entry`) with post-deref
projection suffix `restProj`.

Resolves dynamic `.index idxLocal` projections against `indexLocals` and, when
`ptrOrFatVal` is a 2-element slice fat pointer with `ptrVal.offsetBytes > 0`,
prepends `.subslice elemOffset (elemOffset + lenSc.bits) false` to the suffix.
-/
@[reducible]
def resolveDerefWriteFullProj
    (indexLocals : List LocalSlot)
    (targetLocals : List LocalSlot)
    (ptrOrFatVal : Value)
    (entry : BorrowEntry)
    (restProj : List ProjectionElem)
    (callerLocals : List LocalSlot := .nil) :
    List ProjectionElem :=
  let resolvedRest :=
    match resolveBorrowProjectionElems indexLocals restProj with
    | .some rp => rp
    | .none => restProj
  let targetRootOpt : Option Value :=
    match get? targetLocals entry.targetLocal with
    | .some (.init v) => .some v
    | .some _ => .none
    | .none =>
      match get? callerLocals entry.targetLocal with
      | .some (.init v) => .some v
      | _ => .none
  match ptrOrFatVal with
  | .ptr ptrVal _ =>
    match
      needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
    with
    | false =>
      let rawFull :=
        match entry.targetProjection with
        | .nil => resolvedRest
        | ph :: pt => ph :: appendProjections pt resolvedRest
      normalizeSubsliceProjections (stripTransparentProjections rawFull)
    | true =>
      match targetRootOpt with
      | .some targetRootVal =>
        match
          resolveStackThinPtrTargetProj?
            indexLocals
            targetRootVal
            entry
            ptrVal
            resolvedRest
        with
        | .some resolvedFull => resolvedFull
        | .none =>
          let rawFull :=
            match entry.targetProjection with
            | .nil => resolvedRest
            | ph :: pt => ph :: appendProjections pt resolvedRest
          normalizeSubsliceProjections (stripTransparentProjections rawFull)
      | .none =>
        let rawFull :=
          match entry.targetProjection with
          | .nil => resolvedRest
          | ph :: pt => ph :: appendProjections pt resolvedRest
        normalizeSubsliceProjections (stripTransparentProjections rawFull)
  | _ =>
    let (containerProj, effectiveSuffix) :=
      match ptrOrFatVal with
      | .aggregate 0 (.ptr ptrVal 8 :: .scalar lenSc :: .nil) =>
        match targetRootOpt with
        | .some targetRootVal =>
          match
            readSliceBackingAggregate?
              indexLocals
              targetRootVal
              entry.targetProjection
              lenSc.bits
          with
          | .some (cProj, baseIdx, elems) =>
            let elemSz := inferElemListByteStride elems
            match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
            | .some rawElemOffset =>
              let elemOffset := Nat.add rawElemOffset baseIdx
              (cProj,
               ProjectionElem.subslice
                 elemOffset
                 (Nat.add elemOffset lenSc.bits)
                 false ::
                 resolvedRest)
            | .none => (entry.targetProjection, resolvedRest)
          | .none => (entry.targetProjection, resolvedRest)
        | .none => (entry.targetProjection, resolvedRest)
      | _ => (entry.targetProjection, resolvedRest)
    let rawFull :=
      match containerProj with
      | .nil => effectiveSuffix
      | ph :: pt => ph :: appendProjections pt effectiveSuffix
    normalizeSubsliceProjections (stripTransparentProjections rawFull)

/--
Update the referent root aggregate `targetRootVal` at `targetProjection` when
writing `val` through a dereferenced slice fat pointer
`Value.aggregate 0 [Value.ptr ptrVal ptrSz, Value.scalar lenSc]` with trailing
projection `restProj`.

Enforces 8-byte pointer and metadata widths, converts `ptrVal.offsetBytes` into
an element offset `elemOffset`, bounds-checks the `[elemOffset .. elemOffset +
lenSc.bits)` slice window within the backing aggregate, applies
`writeProjectedValue` on that `lenSc.bits`-element slice window, and splices the
updated slice elements back into `targetRootVal`.
-/
def writeSliceFatPtrTargetValue
    (indexLocals : List LocalSlot)
    (targetRootVal : Value)
    (targetProjection : List ProjectionElem)
    (ptrVal : ProvenancePtr)
    (ptrSz : Nat)
    (lenSc : ScalarInt)
    (restProj : List ProjectionElem)
    (val : Value) :
    ProjWriteResult :=
  match
    Bool.and
      (Nat.beq ptrSz 8)
      (Nat.beq lenSc.sizeBytes 8)
  with
  | false => .ub
  | true =>
    match
      readSliceBackingAggregate?
        indexLocals
        targetRootVal
        targetProjection
        lenSc.bits
    with
    | .some (containerProj, baseIdx, elems) =>
      let elemSz := inferElemListByteStride elems
      match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
      | .none => .ub
      | .some rawElemOffset =>
        let elemOffset := Nat.add rawElemOffset baseIdx
        let endOffset := Nat.add elemOffset lenSc.bits
        match Nat.ble endOffset (length elems) with
        | false => .ub
        | true =>
          let sliceElems := takeValues lenSc.bits (dropValues elemOffset elems)
          match
            writeProjectedValue
              indexLocals
              (.aggregate 0 sliceElems)
              restProj
              val
          with
          | .ok (.aggregate 0 updatedSliceElems) =>
            match
              replaceSubslice
                elems
                elemOffset
                endOffset
                false
                updatedSliceElems
            with
            | .some elems' =>
              writeProjectedValue
                indexLocals
                targetRootVal
                containerProj
                (.aggregate 0 elems')
            | .none => .ub
          | .ok _ => .ub
          | .ub => .ub
          | .unsupported => .unsupported
    | .none =>
      match readProjectedValue indexLocals targetRootVal targetProjection with
      | .ok .unit =>
        match
          Bool.and
            (Nat.beq ptrVal.offsetBytes 0)
            (Nat.beq lenSc.bits 0)
        with
        | false => .ub
        | true =>
          match
            writeProjectedValue
              indexLocals
              (.aggregate 0 .nil)
              restProj
              val
          with
          | .ok (.aggregate 0 .nil) => .ok targetRootVal
          | .ok _ => .ub
          | .ub => .ub
          | .unsupported => .unsupported
      | _ => .ub

/--
Write `val` to `dst` in `locals` using active borrow table `borrows`, supporting
root locals (`projection = []`), dereference projections (`ProjectionElem.deref`
checked against `TreeBorrowPerm`), and nested `.field`, `.downcast`, `.index`,
`.constantIndex`, `.subslice`, `.opaqueCast`, and `.unwrapUnsafeBinder`
projections.

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
          match
            needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
          with
          | false =>
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
          | true =>
            match get? locals entry.targetLocal with
            | .some (.init targetRootVal) =>
              match
                resolveStackThinPtrTargetProj?
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
              with
              | .some (pHead :: pTail) =>
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
            | _ => .ub
      | .none => .ub
    | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .frozen => .ub
        | .disabled => .ub
        | _ =>
          match get? locals entry.targetLocal with
          | .some (.init targetRootVal) =>
            match
              writeSliceFatPtrTargetValue
                locals
                targetRootVal
                entry.targetProjection
                ptrVal
                ptrSz
                lenSc
                restProj
                val
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
        | .some (.init ptrOrFatVal) =>
          match extractDerefPtrVal? ptrOrFatVal with
          | .some ptrVal =>
            match lookupBorrow borrows ptrVal.tag with
            | .some entry =>
              let fullProj :=
                resolveDerefWriteFullProj
                  locals
                  locals
                  ptrOrFatVal
                  entry
                  restProj
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
              | _ => false
            | .none => false
          | .none => false
        | _ => false
      | proj :: rest =>
        let resolvedLocalProj :=
          match resolveBorrowProjectionElems locals (proj :: rest) with
          | .some rp => rp
          | .none => proj :: rest
        hasProtectedWriteConflict
          borrows
          activeProtectors
          dst.local_
          .none
          resolvedLocalProj
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
            match
              needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
            with
            | false =>
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
            | true =>
              match get? callerLocals entry.targetLocal with
              | .some (.init targetRootVal) =>
                match
                  resolveStackThinPtrTargetProj?
                    frameLocals
                    targetRootVal
                    entry
                    ptrVal
                    restProj
                with
                | .some (pHead :: pTail) =>
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
              | _ => .ub
      | .none => .ub
    | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .frozen => .ub
        | .disabled => .ub
        | _ =>
          match get? frameLocals entry.targetLocal with
          | .some _ => .ub
          | .none =>
            match get? callerLocals entry.targetLocal with
            | .some (.init targetRootVal) =>
              match
                writeSliceFatPtrTargetValue
                  frameLocals
                  targetRootVal
                  entry.targetProjection
                  ptrVal
                  ptrSz
                  lenSc
                  restProj
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
        | .some (.init ptrOrFatVal) =>
          match extractDerefPtrVal? ptrOrFatVal with
          | .some ptrVal =>
            match lookupBorrow borrows ptrVal.tag with
            | .some entry =>
              let fullProj :=
                resolveDerefWriteFullProj
                  frameLocals
                  callerLocals
                  ptrOrFatVal
                  entry
                  restProj
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
              | _ => false
            | .none => false
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
    (restProj : List ProjectionElem)
    (callerLocals : List LocalSlot := .nil) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | single :: .nil =>
    let b := single :: .nil
    match get? locals₁ dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow b ptrVal.tag with
        | .some entry =>
          let fullProj :=
            resolveDerefWriteFullProj
              locals₁
              locals₁
              ptrOrFatVal
              entry
              restProj
              callerLocals
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
      | .none => b
    | _ => b
  | b₁ :: b₂ :: restBorrows =>
    let allBorrows := b₁ :: b₂ :: restBorrows
    match get? locals₁ dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow allBorrows ptrVal.tag with
        | .some entry =>
          let fullProj :=
            resolveDerefWriteFullProj
              locals₁
              locals₁
              ptrOrFatVal
              entry
              restProj
              callerLocals
          invalidateTreeBorrowsAtProj
            allBorrows
            allBorrows
            entry.targetLocal
            (.some ptrVal.tag)
            fullProj
            entry.rangeOffset
            entry.rangeLen
        | .none => allBorrows
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
Check that `fnInputs` pointwise match the `RigidTy` kinds of the leading
parameter declarations in `paramDecls`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L225-L246>

> "/// The first local is the return value pointer, followed by `arg_count`
> /// locals for the function arguments, followed by any user-declared
> /// variables and temporaries."
-/
def calleeParamTysMatch : List RigidTy → List LocalDecl → Bool
  | .nil, _ => true
  | _ :: _, .nil => false
  | inputTy :: restInputs, decl :: restDecls =>
    Bool.and
      (rigidTyEq inputTy decl.ty.kind)
      (calleeParamTysMatch restInputs restDecls)

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
        (rigidTyEq fnOutput retDecl.ty.kind)
        (calleeParamTysMatch fnInputs paramDecls))

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
            c.localDecls
            c.argCount
            fnInputs
            fnOutput
        | 0, _ :: _ => false
        | .succ _, _ =>
          Bool.and
            (Nat.beq (length effectiveTypeArgs) c.typeParamCount)
            (calleeLocalDeclsCompatible
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
Check whether `srcKind` and `dstKind` form a valid array-to-slice pointer or
reference unsizing coercion (`&[T; N]` / `&mut [T; N]` / `*const [T; N]` /
`*mut [T; N]` to `&[T]` / `&mut [T]` / `*const [T]` / `*mut [T]`), returning
`.some N` when element types and mutabilities are compatible and `.none`
otherwise.

Reference (The Rust Reference, "Unsized coercions"):
<https://doc.rust-lang.org/1.98.0/reference/type-coercions.html#unsized-coercions>

> "The following coercions are built-in:
> * `[T; n]` to `[T]`."
-/
@[reducible]
def unsizeArrayToSliceSpec? (srcKind dstKind : RigidTy) : Option Nat :=
  match srcKind, dstKind with
  | .ref .mut (.array srcElem n), .ref _ (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | .ref .mut (.array srcElem n), .rawPtr _ (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | .ref .not (.array srcElem n), .ref .not (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | .ref .not (.array srcElem n), .rawPtr .not (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | .rawPtr .mut (.array srcElem n), .rawPtr _ (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | .rawPtr .not (.array srcElem n), .rawPtr .not (.slice dstElem) =>
    match rigidTyEq srcElem dstElem with
    | true => .some n
    | false => .none
  | _, _ => .none

/--
Evaluate `CastKind.pointerCoercion "Unsize"`, coercing an array reference or
raw pointer (`Value.ptr p sz` of type `&[T; N]`, `&mut [T; N]`, `*const [T; N]`,
or `*mut [T; N]`) to a slice fat pointer
`Value.aggregate 0 [Value.ptr p sz, Value.scalar ⟨N, ptrBytes⟩]`.

Faults with `.ub` if `op` does not evaluate to a pointer of width `ptrBytes`,
if `targetTy` is a reference whose borrow tag is `.disabled`, or if source and
target types are incompatible for slice unsizing.
-/
def evalUnsizeCoercion
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok (.ptr ptrVal sz) locals' =>
    match Nat.beq sz ptrBytes with
    | false => .ub
    | true =>
      let isTargetMutSlicePtr :=
        match targetTy.kind with
        | .ref .mut (.slice _) => true
        | .rawPtr .mut (.slice _) => true
        | _ => false
      let isTargetSlicePtr :=
        match targetTy.kind with
        | .ref _ (.slice _) => true
        | .rawPtr _ (.slice _) => true
        | _ => false
      let borrowValid :=
        match isTargetSlicePtr with
        | false => true
        | true =>
          match lookupBorrow mem.borrows ptrVal.tag with
          | .some { perm := .disabled, .. } => false
          | .some { perm := .frozen, .. } => Bool.not isTargetMutSlicePtr
          | _ => true
      match Bool.and isTargetSlicePtr borrowValid with
      | false => .ub
      | true =>
        match operandTy localDecls layouts op with
        | .some srcTy =>
          match unsizeArrayToSliceSpec? srcTy.kind targetTy.kind with
          | .some n =>
            let stackTargetValid :=
              match lookupBorrow mem.borrows ptrVal.tag with
              | .none =>
                match lookupGlobalAlloc mem.globals ptrVal.allocId with
                | .some alloc =>
                  let mutOk :=
                    match isTargetMutSlicePtr, alloc.mutability with
                    | true, .not => false
                    | _, _ => true
                  let elemSz :=
                    match targetTy.kind with
                    | .ref _ (.slice dstElem) =>
                      match rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 } with
                      | .some sz => sz
                      | .none => 1
                    | .rawPtr _ (.slice dstElem) =>
                      match rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 } with
                      | .some sz => sz
                      | .none => 1
                    | _ => 1
                  let alignedOk :=
                    match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
                    | .some _ => true
                    | .none => false
                  Bool.and
                    mutOk
                    (Bool.and
                      alignedOk
                      (Nat.ble
                        (Nat.add ptrVal.offsetBytes (Nat.mul n elemSz))
                        (length alloc.bytes)))
                | .none =>
                  match Nat.beq ptrVal.allocId 0 with
                  | true =>
                    Bool.and
                      (Bool.not (Nat.beq ptrVal.offsetBytes 0))
                      (Nat.beq n 0)
                  | false => true
              | .some entry =>
                let rootValOpt : Option Value :=
                  match get? locals' entry.targetLocal with
                  | .some (.init v) => .some v
                  | .some _ => .none
                  | .none =>
                    match get? mem.callerLocals entry.targetLocal with
                    | .some (.init v) => .some v
                    | _ => .none
                match rootValOpt with
                | .some rootVal =>
                  let dstElemSzOpt : Option Nat :=
                    match targetTy.kind with
                    | .ref _ (.slice dstElem) =>
                      rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 }
                    | .rawPtr _ (.slice dstElem) =>
                      rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 }
                    | _ => .none
                  match
                    readSliceBackingAggregate?
                      locals'
                      rootVal
                      entry.targetProjection
                      n
                      dstElemSzOpt
                  with
                  | .some (_, baseIdx, elems) =>
                    let elemSz := inferElemListByteStride elems
                    match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
                    | .some rawElemOffset =>
                      let elemOffset := Nat.add rawElemOffset baseIdx
                      Nat.ble (Nat.add elemOffset n) (length elems)
                    | .none => false
                  | .none =>
                    match readProjectedValue locals' rootVal entry.targetProjection with
                    | .ok .unit =>
                      Bool.and
                        (Nat.beq ptrVal.offsetBytes 0)
                        (Nat.beq n 0)
                    | .ok (.ptr _ _) => true
                    | _ => false
                | .none => false
            match stackTargetValid with
            | true =>
              .ok
                (.aggregate 0 (.ptr ptrVal sz :: .scalar ⟨n, ptrBytes⟩ :: .nil))
                locals'
                mem
            | false => .ub
          | .none => .ub
        | .none =>
          match lookupBorrow mem.borrows ptrVal.tag with
          | .some entry =>
            let permOk :=
              match entry.perm, isTargetMutSlicePtr with
              | .disabled, _ => false
              | .frozen, true => false
              | _, _ => true
            match permOk with
            | false => .ub
            | true =>
              let rootValOpt : Option Value :=
                match get? locals' entry.targetLocal with
                | .some (.init v) => .some v
                | .some _ => .none
                | .none =>
                  match get? mem.callerLocals entry.targetLocal with
                  | .some (.init v) => .some v
                  | _ => .none
              match rootValOpt with
              | .some rootVal =>
                let dstElemSzOpt : Option Nat :=
                  match targetTy.kind with
                  | .ref _ (.slice dstElem) =>
                    rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 }
                  | .rawPtr _ (.slice dstElem) =>
                    rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 }
                  | _ => .none
                match
                  readSliceBackingAggregate?
                    locals'
                    rootVal
                    entry.targetProjection
                    0
                    dstElemSzOpt
                with
                | .some (_, baseIdx, elems) =>
                  let elemSz := inferElemListByteStride elems
                  match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
                  | .some rawElemOffset =>
                    let elemOffset := Nat.add rawElemOffset baseIdx
                    match Nat.ble elemOffset (length elems) with
                    | true =>
                      .ok
                        (.aggregate 0
                          (.ptr ptrVal sz ::
                            .scalar ⟨Nat.sub (length elems) elemOffset, ptrBytes⟩ ::
                            .nil))
                        locals'
                        mem
                    | false => .ub
                  | .none => .ub
                | .none =>
                  match readProjectedValue locals' rootVal entry.targetProjection with
                  | .ok .unit =>
                    match Nat.beq ptrVal.offsetBytes 0 with
                    | true =>
                      .ok
                        (.aggregate 0
                          (.ptr ptrVal sz ::
                            .scalar ⟨0, ptrBytes⟩ ::
                            .nil))
                        locals'
                        mem
                    | false => .ub
                  | _ => .ub
              | .none => .ub
          | .none =>
            match lookupGlobalAlloc mem.globals ptrVal.allocId with
            | .some alloc =>
              let mutOk :=
                match isTargetMutSlicePtr, alloc.mutability with
                | true, .not => false
                | _, _ => true
              let dstElemOpt : Option RigidTy :=
                match targetTy.kind with
                | .ref _ (.slice dstElem) => .some dstElem
                | .rawPtr _ (.slice dstElem) => .some dstElem
                | _ => .none
              match Bool.and mutOk (Nat.ble ptrVal.offsetBytes (length alloc.bytes)), dstElemOpt with
              | true, .some dstElem =>
                let elemSz :=
                  match rigidTyByteSize layouts { kind := dstElem, layoutIdx := 0 } with
                  | .some n => n
                  | .none => 1
                let remBytes := Nat.sub (length alloc.bytes) ptrVal.offsetBytes
                match Nat.beq elemSz 0 with
                | true => .ub
                | false =>
                  match
                    byteOffsetToElemIdx? ptrVal.offsetBytes elemSz,
                    byteOffsetToElemIdx? remBytes elemSz
                  with
                  | .some _, .some elemCount =>
                    .ok
                      (.aggregate 0
                        (.ptr ptrVal sz ::
                          .scalar ⟨elemCount, ptrBytes⟩ ::
                          .nil))
                      locals'
                      mem
                  | _, _ => .ub
              | _, _ => .ub
            | .none => .ub
  | .ok _ _ => .ub

/--
Resolve a stack-backed array or slice borrow `parentEntry` at `ptrVal` into a
thin element pointer (`*const T` / `*mut T`) whose `BorrowEntry.targetProjection`
ends with `.subslice elemOffset endOffset false`, so dereferencing at
`offsetBytes = 0` (e.g. `*slice.as_ptr()`) or after `BinOp.offset` accesses
individual elements within `[elemOffset .. endOffset)` rather than the whole
enclosing array aggregate.
-/
def deriveStackElemThinPtr
    (locals : List LocalSlot)
    (mem : Memory)
    (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry)
    (elemCountOpt : Option Nat) :
    RvalueEvalResult :=
  match parentEntry.perm with
  | .disabled => .ub
  | _ =>
    let normProj :=
      normalizeSubsliceProjections (stripTransparentProjections parentEntry.targetProjection)
    let rootValOpt : Option Value :=
      match get? locals parentEntry.targetLocal with
      | .some (.init v) => .some v
      | .some _ => .none
      | .none =>
        match get? mem.callerLocals parentEntry.targetLocal with
        | .some (.init v) => .some v
        | _ => .none
    match rootValOpt with
    | .none => .ub
    | .some targetRootVal =>
      let minCnt :=
        match elemCountOpt with
        | .some n => n
        | .none => 0
      match readSliceBackingAggregate? locals targetRootVal normProj minCnt with
      | .some (containerProj, baseIdx, elems) =>
        let elemSz := inferElemListByteStride elems
        match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
        | .none => .ub
        | .some rawElemOffset =>
          let elemOffset := Nat.add rawElemOffset baseIdx
          let sliceLen :=
            match elemCountOpt with
            | .some n => n
            | .none => Nat.sub (length elems) elemOffset
          let endOffset := Nat.add elemOffset sliceLen
          match Nat.ble endOffset (length elems) with
          | false => .ub
          | true =>
            let alreadySubslice :=
              Bool.and
                (endsWithSubslice containerProj)
                (Bool.and
                  (Nat.beq elemOffset 0)
                  (Nat.beq sliceLen (length elems)))
            match alreadySubslice with
            | true => .ok (.ptr ptrVal 8) locals mem
            | false =>
              let subProj := ProjectionElem.subslice elemOffset endOffset false :: .nil
              let fullProj :=
                match containerProj with
                | .nil => subProj
                | ph :: pt => ph :: appendProjections pt subProj
              let normFullProj := normalizeSubsliceProjections fullProj
              let tag := mem.nextTag
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := normFullProj
                perm := parentEntry.perm
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
      | .none =>
        match readProjectedValue locals targetRootVal normProj with
        | .ok .unit =>
          let isZeroSlice :=
            match elemCountOpt with
            | .some n => Nat.beq n 0
            | .none => true
          match Bool.and (Nat.beq ptrVal.offsetBytes 0) isZeroSlice with
          | false => .ub
          | true =>
            match endsWithSubslice normProj with
            | true => .ok (.ptr ptrVal 8) locals mem
            | false =>
              let subProj := ProjectionElem.subslice 0 0 false :: .nil
              let fullProj :=
                match normProj with
                | .nil => subProj
                | ph :: pt => ph :: appendProjections pt subProj
              let normFullProj := normalizeSubsliceProjections fullProj
              let tag := mem.nextTag
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetProjection := normFullProj
                perm := parentEntry.perm
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | _ => .ub

/--
Evaluate `CastKind.pointerCoercion` for function-pointer reification
(`"ReifyFnPointer"`, `"ClosureFnPointer"`, `"UnsafeFnPointer"`), slice unsizing
(`"Unsize"`), or pointer-preserving coercions (`"MutToConstPointer"`,
`"ArrayToPointer"`).

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
    match stringEq coercionKind "Unsize" with
    | true =>
      evalUnsizeCoercion locals op targetTy mem localDecls layouts
    | false =>
      match stringEq coercionKind "ArrayToPointer" with
      | true =>
        match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
        | .ok (.ptr ptrVal sz) locals' =>
          match Bool.and (Nat.beq sz 8) (isThinRawPtrTy targetTy) with
          | false => .ub
          | true =>
            match lookupBorrow mem.borrows ptrVal.tag with
            | .some parentEntry =>
              deriveStackElemThinPtr locals' mem ptrVal parentEntry .none
            | .none => .ok (.ptr ptrVal sz) locals' mem
        | .ok _ _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | false =>
        match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
        | .ok (.ptr ptrVal sz) locals' => .ok (.ptr ptrVal sz) locals' mem
        | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
          .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' mem
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
Determine whether a monomorphized `RigidTy` is `Freeze` (contains no
`UnsafeCell` interior mutability or raw pointer), using structural recursion
with `fuel`.

Returns `false` (`!Freeze`) for `.rawPtr`, for `core::cell::UnsafeCell` /
`std::cell::UnsafeCell`, and for any `.adt`, `.tuple`, `.array`, or `.slice`
whose type arguments or element types contain a `!Freeze` component; returns
`true` (`Freeze`) otherwise.
Modeling choice: Because `RigidTy.adt` carries generic `args` rather than full
field declarations, `rigidTyIsFreeze` recurses structurally on `args` and also
classifies `.rawPtr` as `!Freeze` so raw-pointer wrapper cells (such as `Cell`
or custom interior-mutable wrappers) conservatively receive `.reserved`.

Reference (The Rust Reference, "Interior mutability"):
<https://doc.rust-lang.org/1.98.0/reference/interior-mutability.html>

> "Shared references in Rust disallow mutation by default, and &mut is called an
> exclusive reference. However, there are situations where it would be helpful
> to mutate data behind a shared reference. This is known as interior mutability
> in Rust, in contrast with exterior mutability, which happens through &mut or
> directly on a value.
>
> All interior mutability in Rust is enabled by the UnsafeCell<T> type, which is
> defined in the standard library. Any type that contains an UnsafeCell<T> (with
> the exception of types that only contain it behind a pointer, such as
> &UnsafeCell<T> or *const UnsafeCell<T>) is considered to have interior
> mutability."
-/
@[reducible]
def rigidTyIsFreeze : Nat → RigidTy → Bool
  | .zero, _ => true
  | .succ _, .rawPtr _ _ => false
  | .succ fuel, .adt defPath args =>
    match
      Bool.or
        (stringEq defPath "core::cell::UnsafeCell")
        (stringEq defPath "std::cell::UnsafeCell")
    with
    | true => false
    | false =>
      match args with
      | .nil => true
      | arg :: restArgs =>
        Bool.and
          (rigidTyIsFreeze fuel arg)
          (rigidTyIsFreeze fuel (.tuple restArgs))
  | .succ fuel, .tuple fields =>
    match fields with
    | .nil => true
    | f :: restFields =>
      Bool.and
        (rigidTyIsFreeze fuel f)
        (rigidTyIsFreeze fuel (.tuple restFields))
  | .succ fuel, .array elem _ => rigidTyIsFreeze fuel elem
  | .succ fuel, .slice elem => rigidTyIsFreeze fuel elem
  | .succ _, _ => true

/--
Determine whether a `Ty` is `Freeze` (contains no `UnsafeCell` interior
mutability or raw pointer) by inspecting `ty.kind` with fuel `16`.

Reference (The Rust Reference, "Interior mutability"):
<https://doc.rust-lang.org/1.98.0/reference/interior-mutability.html>

> "All interior mutability in Rust is enabled by the UnsafeCell<T> type, which
> is defined in the standard library."
-/
@[reducible]
def tyIsFreeze (ty : Ty) : Bool :=
  rigidTyIsFreeze 16 ty.kind

/--
Determine whether the resolved type of `p` in `localDecls` and `layouts` is
`Freeze` (defaulting to `true` when `placeTy` returns `.none`).
-/
@[reducible]
def placeIsFreeze
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place) :
    Bool :=
  match placeTy localDecls layouts p with
  | .some ty => tyIsFreeze ty
  | .none => true

/--
Determine the initial Tree Borrows permission for a shared borrow (`&place`)
based on whether `place`'s resolved type in `localDecls` and `layouts` is
`Freeze`.

When `placeTy localDecls layouts place` resolves to a `!Freeze` type (such as
`core::cell::UnsafeCell<T>`), a shared borrow starts in
`TreeBorrowPerm.reserved` instead of `TreeBorrowPerm.frozen` so interior
mutation through `&UnsafeCell<T>` is permitted; when `place` is `Freeze` (or
when `localDecls` is omitted / does not declare a type for `place`), the shared
borrow defaults to `TreeBorrowPerm.frozen`.

Reference (The Rust Reference, "Interior mutability"):
<https://doc.rust-lang.org/1.98.0/reference/interior-mutability.html>

> "Shared references in Rust disallow mutation by default, and &mut is called an
> exclusive reference. However, there are situations where it would be helpful
> to mutate data behind a shared reference. This is known as interior mutability
> in Rust, in contrast with exterior mutability, which happens through &mut or
> directly on a value."
-/
@[reducible]
def sharedBorrowPerm
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place) :
    TreeBorrowPerm :=
  match placeTy localDecls layouts place with
  | .some ty =>
    match tyIsFreeze ty with
    | true => TreeBorrowPerm.frozen
    | false => TreeBorrowPerm.reserved
  | .none => TreeBorrowPerm.frozen

/--
If `proj` ends with `.deref`, return the prefix projection path before the final
`.deref`; otherwise return `.none`.
-/
@[reducible]
def splitLastDeref? : List ProjectionElem → Option (List ProjectionElem)
  | .nil => .none
  | .deref :: .nil => .some .nil
  | .deref :: rest =>
    match stripTransparentProjections rest with
    | .nil => .some .nil
    | _ =>
      match splitLastDeref? rest with
      | .some initProj => .some (.deref :: initProj)
      | .none => .none
  | .opaqueCast _ :: rest => splitLastDeref? rest
  | .unwrapUnsafeBinder _ :: rest => splitLastDeref? rest
  | elem :: rest =>
    match splitLastDeref? rest with
    | .some initProj => .some (elem :: initProj)
    | .none => .none

/--
Evaluate `Rvalue.len place` on either a fixed-size array (`Value.aggregate 0 elems`)
or a dereferenced slice (`*slice_ptr` where `slice_ptr` evaluates to the 2-element
fat-pointer aggregate `Value.aggregate 0 [Value.ptr ptrVal ptrSz, Value.scalar lenSc]`).

Faults with `.ub` if `place`'s resolved `placeTy` is neither `.array` nor
`.slice`, if `slice_ptr` has a `.disabled` borrow tag or non-pointer-width
fields, or if an un-dereferenced fat pointer is passed directly to `Rvalue.len`.
-/
def evalPlaceLen
    (locals : List LocalSlot)
    (place : Place)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  let pTy := placeTy localDecls layouts place
  let tyOk : Bool :=
    match pTy with
    | .none => true
    | .some { kind := .array _ _, .. } => true
    | .some { kind := .slice _, .. } => true
    | .some _ => false
  match tyOk with
  | false => .ub
  | true =>
    match splitLastDeref? place.projection with
    | .some initProj =>
      let ptrPlace : Place := { local_ := place.local_, projection := initProj }
      match
        evalPlaceRead
          locals
          ptrPlace
          mem.borrows
          mem.globals
          layouts
          mem.callerLocals
          localDecls
      with
      | .ok (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil)) locals' =>
        let sizesOk :=
          Bool.and
            (Nat.beq ptrSz ptrBytes)
            (Nat.beq lenSc.sizeBytes ptrBytes)
        let borrowOk :=
          match lookupBorrow mem.borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => false
            | _ =>
              let targetRootOpt : Option Value :=
                match get? locals' entry.targetLocal with
                | .some (.init v) => .some v
                | .some _ => .none
                | .none =>
                  match get? mem.callerLocals entry.targetLocal with
                  | .some (.init v) => .some v
                  | _ => .none
              match targetRootOpt with
              | .some rootVal =>
                let expSzOpt : Option Nat :=
                  match pTy with
                  | .some { kind := .slice elemKind, .. } =>
                    rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 }
                  | _ => .none
                match
                  readSliceBackingAggregate?
                    locals'
                    rootVal
                    entry.targetProjection
                    lenSc.bits
                    expSzOpt
                with
                | .some (_, baseIdx, elems) =>
                  let elemSz := inferElemListByteStride elems
                  match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
                  | .some rawElemOffset =>
                    let elemOffset := Nat.add rawElemOffset baseIdx
                    Nat.ble (Nat.add elemOffset lenSc.bits) (length elems)
                  | .none => false
                | .none =>
                  match readProjectedValue locals' rootVal entry.targetProjection with
                  | .ok .unit =>
                    Bool.and
                      (Nat.beq ptrVal.offsetBytes 0)
                      (Nat.beq lenSc.bits 0)
                  | _ => false
              | .none => false
          | .none =>
            match lookupGlobalAlloc mem.globals ptrVal.allocId with
            | .some alloc =>
              let elemSz :=
                match pTy with
                | .some { kind := .slice elemKind, .. } =>
                  match rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
                  | .some n => n
                  | .none => 1
                | _ => 1
              Nat.ble
                (Nat.add ptrVal.offsetBytes (Nat.mul lenSc.bits elemSz))
                (length alloc.bytes)
            | .none =>
              match Nat.beq ptrVal.allocId 0 with
              | true =>
                Bool.and
                  (Bool.not (Nat.beq ptrVal.offsetBytes 0))
                  (Nat.beq lenSc.bits 0)
              | false => true
        let notFixedArrayPlace :=
          match pTy with
          | .some { kind := .array _ _, .. } => false
          | _ => true
        match Bool.and sizesOk (Bool.and borrowOk notFixedArrayPlace) with
        | true => .ok (.scalar ⟨lenSc.bits, ptrBytes⟩) locals' mem
        | false => .ub
      | .ok (.ptr _ _) _ =>
        match
          evalPlaceRead
            locals
            place
            mem.borrows
            mem.globals
            layouts
            mem.callerLocals
            localDecls
        with
        | .ok (.aggregate 0 (.ptr _ _ :: .scalar _ :: .nil)) _ => .ub
        | .ok (.aggregate 0 elems) locals' =>
          .ok (.scalar ⟨length elems, ptrBytes⟩) locals' mem
        | .ok .unit locals' =>
          match pTy with
          | .some { kind := .array _ .zero, .. } =>
            .ok (.scalar ⟨0, ptrBytes⟩) locals' mem
          | _ => .ub
        | .ok _ _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .ok _ _ => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .none =>
      match pTy with
      | .some { kind := .array _ n, .. } =>
        match
          evalPlaceRead
            locals
            place
            mem.borrows
            mem.globals
            layouts
            mem.callerLocals
            localDecls
        with
        | .ok (.aggregate 0 elems) locals' =>
          .ok (.scalar ⟨length elems, ptrBytes⟩) locals' mem
        | .ok .unit locals' =>
          match n with
          | .zero => .ok (.scalar ⟨0, ptrBytes⟩) locals' mem
          | .succ _ => .ub
        | .ok _ _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | _ =>
        match
          evalPlaceRead
            locals
            place
            mem.borrows
            mem.globals
            layouts
            mem.callerLocals
            localDecls
        with
        | .ok (.aggregate 0 (.ptr _ _ :: .scalar _ :: .nil)) _ => .ub
        | .ok (.aggregate 0 elems) locals' =>
          .ok (.scalar ⟨length elems, ptrBytes⟩) locals' mem
        | .ok _ _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported

/--
Look up the first `LocalDecl` in `localDecls` whose `decl.ty.kind` structurally
matches `kind`, returning its `Ty` (including its `LayoutIdx`).
-/
@[reducible]
def findDeclTyWithKind? : List LocalDecl → RigidTy → Option Ty
  | .nil, _ => .none
  | decl :: rest, kind =>
    match rigidTyEq decl.ty.kind kind with
    | true => .some decl.ty
    | false => findDeclTyWithKind? rest kind

/--
Resolve the pointee element byte stride `size_of::<T>()` for the pointer operand
`lhsOp` of `BinOp.offset`, defaulting to `1` byte when `localDecls` does not
declare a type for `lhsOp`.
-/
@[reducible]
def pointeeElemByteStride
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp : Operand) :
    Option Nat :=
  match operandTy localDecls layouts lhsOp with
  | .none => .some 1
  | .some ptrTy =>
    match pointeeTyOf ptrTy with
    | .some pointeeTy =>
      match rigidTyKindByteSize pointeeTy.kind with
      | .some sz => .some sz
      | .none =>
        let resolvedPointeeTy :=
          match findDeclTyWithKind? localDecls pointeeTy.kind with
          | .some declTy => declTy
          | .none => pointeeTy
        rigidTyByteSize layouts resolvedPointeeTy
    | .none => .none

/--
Compute the default byte size of an untyped runtime `Value` when `localDecls`
does not provide a `LocalDecl` for a stack allocation.
-/
@[reducible]
def valueDefaultByteSize : Value → Option Nat
  | .unit => .some 0
  | .scalar sc => .some sc.sizeBytes
  | .ptr _ sz => .some sz
  | .aggregate 0 .nil => .some 0
  | .aggregate 0 (.scalar sc :: rest) =>
    .some (Nat.mul (Nat.add (length rest) 1) sc.sizeBytes)
  | .aggregate 0 (.ptr _ sz :: rest) =>
    .some (Nat.mul (Nat.add (length rest) 1) sz)
  | .aggregate 0 (.unit :: _) => .some 0
  | .aggregate 0 (.aggregate 0 fields :: rest) =>
    inferValueByteSizeAux 8 (.aggregate 0 (.aggregate 0 fields :: rest))
  | _ => .none

/--
Resolve the byte bound of a projected value `rootVal` at `proj` using
`readProjectedValue` and `valueDefaultByteSize`.
-/
@[reducible]
def projectedValueDefaultByteSize
    (locals : List LocalSlot)
    (rootVal : Value)
    (proj : List ProjectionElem) :
    Option Nat :=
  match readProjectedValue locals rootVal proj with
  | .ok projVal => valueDefaultByteSize projVal
  | _ => .some 0

/--
Resolve the byte bound of the allocation backing `ptrVal` from `mem.borrows`
(using `entry.rangeOffset + entry.rangeLen`, `localDecls`, or `locals`) or
`mem.globals` (`length alloc.bytes`).
-/
def ptrAllocByteBound?
    (locals : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrVal : ProvenancePtr) :
    Option Nat :=
  match lookupBorrow mem.borrows ptrVal.tag with
  | .some entry =>
    match entry.perm with
    | .disabled => .some 0
    | _ =>
      match Nat.beq entry.rangeLen 0 with
      | false => .some (Nat.add entry.rangeOffset entry.rangeLen)
      | true =>
        let rootValOpt : Option Value :=
          match get? locals entry.targetLocal with
          | .some (.init v) => .some v
          | .some _ => .none
          | .none =>
            match get? mem.callerLocals entry.targetLocal with
            | .some (.init v) => .some v
            | _ => .none
        let normTargetProj :=
          normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
        match splitLastConstantIndex? normTargetProj with
        | .some (initProj, baseIdx, minLen) =>
          match rootValOpt with
          | .some rootVal =>
            match readProjectedValue locals rootVal initProj with
            | .ok (.aggregate 0 elems) =>
              match
                Bool.and
                  (Nat.ble minLen (length elems))
                  (Nat.ble baseIdx (length elems))
              with
              | false => .some 0
              | true =>
                let remElems := Nat.sub (length elems) baseIdx
                let elemPlace : Place := {
                  local_ := entry.targetLocal
                  projection := normTargetProj
                }
                let elemSz :=
                  match placeTy localDecls layouts elemPlace with
                  | .some elemTy =>
                    match rigidTyByteSize layouts elemTy with
                    | .some n => n
                    | .none => inferElemListByteStride elems
                  | .none => inferElemListByteStride elems
                .some (Nat.mul remElems elemSz)
            | _ => .some 0
          | .none =>
            let initPlace : Place := {
              local_ := entry.targetLocal
              projection := initProj
            }
            match placeTy localDecls layouts initPlace with
            | .some { kind := .array elemKind arrLen, .. } =>
              match
                Bool.and
                  (Nat.ble minLen arrLen)
                  (Nat.ble baseIdx arrLen)
              with
              | false => .some 0
              | true =>
                let remElems := Nat.sub arrLen baseIdx
                match rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
                | .some elemSz => .some (Nat.mul remElems elemSz)
                | .none => .some 0
            | _ => .some 0
        | .none =>
          match splitLastSubslice? normTargetProj with
          | .some (initProj, fromIdx, toIdx, fromEnd) =>
            match rootValOpt with
            | .some rootVal =>
              match readProjectedValue locals rootVal normTargetProj with
              | .ok (.aggregate 0 subElems) =>
                let initPlace : Place := {
                  local_ := entry.targetLocal
                  projection := initProj
                }
                let elemSz :=
                  match placeTy localDecls layouts initPlace with
                  | .some parentTy =>
                    match elemTyOf parentTy with
                    | .some elemTy =>
                      match rigidTyByteSize layouts elemTy with
                      | .some n => n
                      | .none => inferElemListByteStride subElems
                    | .none => inferElemListByteStride subElems
                  | .none => inferElemListByteStride subElems
                .some (Nat.mul (length subElems) elemSz)
              | _ => .some 0
            | .none =>
              let initPlace : Place := {
                local_ := entry.targetLocal
                projection := initProj
              }
              match placeTy localDecls layouts initPlace with
              | .some { kind := .array elemKind arrLen, .. } =>
                let subLenOpt : Option Nat :=
                  match fromEnd with
                  | false =>
                    match Bool.and (Nat.ble fromIdx toIdx) (Nat.ble toIdx arrLen) with
                    | true => .some (Nat.sub toIdx fromIdx)
                    | false => .none
                  | true =>
                    match Nat.ble (Nat.add fromIdx toIdx) arrLen with
                    | true => .some (Nat.sub (Nat.sub arrLen toIdx) fromIdx)
                    | false => .none
                match subLenOpt, rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
                | .some subLen, .some elemSz => .some (Nat.mul subLen elemSz)
                | _, _ => .some 0
              | _ => .some 0
          | .none =>
            let targetPlace : Place := {
              local_ := entry.targetLocal
              projection := entry.targetProjection
            }
            match placeTy localDecls layouts targetPlace with
            | .some projTy =>
              match rigidTyByteSize layouts projTy with
              | .some n => .some n
              | .none =>
                match rootValOpt with
                | .some rootVal =>
                  projectedValueDefaultByteSize locals rootVal entry.targetProjection
                | .none => .some 0
            | .none =>
              match rootValOpt with
              | .some rootVal =>
                projectedValueDefaultByteSize locals rootVal entry.targetProjection
              | .none => .some 0
  | .none =>
    match lookupGlobalAlloc mem.globals ptrVal.allocId with
    | .some alloc => .some (length alloc.bytes)
    | .none =>
      match Nat.beq ptrVal.allocId 0 with
      | true => .some 0
      | false =>
        match mem.borrows, mem.globals with
        | .nil, .nil => .none
        | _, _ => .some 0

/--
Evaluate in-bounds pointer arithmetic `BinOp.offset` (`ptr::offset` / inbounds
GEP) on 64-bit pointer `ptrVal` (`ptrSizeBytes == 8`) and signed 64-bit `isize`
offset `offsetSc` (`offsetSc.sizeBytes == 8`) scaled by pointee byte stride
`elemStride` within optional allocation byte bound `allocBoundOpt`.

Returns `.none` (undefined behavior) if:
- `ptrSizeBytes != 8` or `offsetSc.sizeBytes != 8`,
- the signed byte offset `count * elemStride` overflows 64-bit signed `isize`
  (`|count| * elemStride >= 2^63`),
- a negative offset underflows below allocation offset `0` (`byteDelta > ptrVal.offsetBytes`),
- a positive offset overflows `isize::MAX` (`ptrVal.offsetBytes + byteDelta >= 2^63`), or
- `allocBoundOpt = .some bound` and either `ptrVal.offsetBytes > bound` or
  `newOffset > bound`.

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L380-L430>

> "/// Adds a signed offset to a pointer.
> ///
> /// `count` is in units of T; e.g., a `count` of 3 represents a pointer
> /// offset of `3 * size_of::<T>()` bytes.
> ///
> /// # Safety
> ///
> /// If any of the following conditions are violated, the result is Undefined
> /// Behavior:
> ///
> /// * The computed offset, `count * size_of::<T>()` bytes, must not overflow `isize`.
> ///
> /// * If the computed offset is non-zero, then `self` must be derived from a
> ///   pointer to some allocated object, and the entire memory range between
> ///   `self` and the result must be in bounds of that allocated object."
-/
def evalBinOpOffset
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (offsetSc : ScalarInt)
    (elemStride : Nat)
    (allocBoundOpt : Option Nat := .none) :
    Option ProvenancePtr :=
  match
    Bool.and
      (Nat.beq ptrSizeBytes 8)
      (Nat.beq offsetSc.sizeBytes 8)
  with
  | false => .none
  | true =>
    let modulus := scalarModulus 8
    let halfMod := signedHalfModulus 8
    let offsetBits := wrapScalarBits offsetSc.bits modulus
    let newOffsetOpt : Option Nat :=
      match isSignedNegative offsetBits 8 with
      | false =>
        let byteDelta := Nat.mul offsetBits elemStride
        match Nat.ble halfMod byteDelta with
        | true => .none
        | false =>
          let candidate := Nat.add ptrVal.offsetBytes byteDelta
          match Nat.ble halfMod candidate with
          | true => .none
          | false => .some candidate
      | true =>
        let countMag := Nat.sub modulus offsetBits
        let byteDelta := Nat.mul countMag elemStride
        match
          Bool.and
            (Bool.not (Nat.ble halfMod byteDelta))
            (Nat.ble byteDelta ptrVal.offsetBytes)
        with
        | false => .none
        | true => .some (Nat.sub ptrVal.offsetBytes byteDelta)
    match newOffsetOpt with
    | .none => .none
    | .some newOffset =>
      let inBounds :=
        match allocBoundOpt with
        | .none =>
          Bool.not (Nat.ble halfMod ptrVal.offsetBytes)
        | .some bound =>
          Bool.or
            (Bool.and
              (Nat.beq ptrVal.allocId 0)
              (Bool.and
                (Nat.beq bound 0)
                (Bool.and
                  (Nat.beq newOffset ptrVal.offsetBytes)
                  (Bool.not (Nat.ble halfMod ptrVal.offsetBytes)))))
            (Bool.and
              (Bool.not (Nat.ble halfMod bound))
              (Bool.and
                (Nat.ble ptrVal.offsetBytes bound)
                (Nat.ble newOffset bound)))
      match inBounds with
      | true => .some { ptrVal with offsetBytes := newOffset }
      | false => .none

/--
Evaluate `BinOp.offset` in `evalRvalue` after operand evaluation, checking that
`ptrVal.tag` is not `.disabled` in `mem.borrows`, resolving the pointee byte
stride `pointeeElemByteStride localDecls layouts lhsOp`, resolving the
allocation byte bound `ptrAllocByteBound? locals₂ mem localDecls layouts ptrVal`,
and delegating to `evalBinOpOffset`.
-/
@[reducible]
def evalPtrOffsetBinOp
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp : Operand)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (offsetSc : ScalarInt) :
    RvalueEvalResult :=
  let borrowDisabled :=
    match lookupBorrow mem.borrows ptrVal.tag with
    | .some { perm := .disabled, .. } => true
    | _ => false
  match borrowDisabled with
  | true => .ub
  | false =>
    match pointeeElemByteStride localDecls layouts lhsOp with
    | .none => .ub
    | .some elemStride =>
      match
        evalBinOpOffset
          ptrVal
          sz
          offsetSc
          elemStride
          (ptrAllocByteBound? locals₂ mem localDecls layouts ptrVal)
      with
      | .some newPtrVal => .ok (.ptr newPtrVal sz) locals₂ mem
      | .none => .ub

/--
Evaluate a borrow (`Rvalue.ref`) or raw address-of (`Rvalue.rawPtr`) through a
dereferenced slice fat pointer
`Value.aggregate 0 [Value.ptr parentPtr ptrSz, Value.scalar lenSc]` with
post-deref projection suffix `restProj`.

Supports:
1. Whole-slice reborrows (`&*s`, `&mut *s`, `&raw const *s`, `&raw mut *s` when
   `stripTransparentProjections restProj = .nil`), returning a new 2-element
   slice fat pointer with fresh borrow tag `mem.nextTag` (or preserving a
   read-only global / empty-slice fat pointer),
2. Subslice borrows (`&(*s)[from..to]` when `restProj` is a single `.subslice`),
   returning a new 2-element slice fat pointer of length `subLen` within
   `lenSc.bits`, and
3. Element/field borrows (`&(*s)[i]` or `&(*s)[i].field` when `restProj` begins
   with `.index` or `.constantIndex`), checking `idx < lenSc.bits` and returning
   a thin pointer `.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8`.
-/
def evalSliceFatPtrDerefBorrow
    (locals : List LocalSlot)
    (mem : Memory)
    (parentPtr : ProvenancePtr)
    (ptrSz : Nat)
    (lenSc : ScalarInt)
    (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm)
    (isMut : Bool)
    (pointeeTyOpt : Option Ty := .none)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  match
    Bool.and
      (Nat.beq ptrSz 8)
      (Nat.beq lenSc.sizeBytes 8)
  with
  | false => .ub
  | true =>
    match
      resolveBorrowProjectionElems
        locals
        (stripTransparentProjections restProj)
    with
    | .none => .ub
    | .some rawResolvedRest =>
      let resolvedRest := normalizeSubsliceProjections rawResolvedRest
      match lookupBorrow mem.borrows parentPtr.tag with
      | .some parentEntry =>
        let permOk :=
          match parentEntry.perm, isMut with
          | .disabled, _ => false
          | .frozen, true => false
          | _, _ => true
        match permOk with
        | false => .ub
        | true =>
          let targetRootOpt : Option Value :=
            match get? locals parentEntry.targetLocal with
            | .some (.init v) => .some v
            | .some _ => .none
            | .none =>
              match get? mem.callerLocals parentEntry.targetLocal with
              | .some (.init v) => .some v
              | _ => .none
          match targetRootOpt with
          | .none => .ub
          | .some targetRootVal =>
            let expSzOpt : Option Nat :=
              match pointeeTyOpt with
              | .some { kind := .slice elemKind, .. } =>
                rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 }
              | _ => .none
            match
              readSliceBackingAggregate?
                locals
                targetRootVal
                parentEntry.targetProjection
                lenSc.bits
                expSzOpt
            with
            | .some (containerProj, baseIdx, elems) =>
              let elemSz := inferElemListByteStride elems
              match byteOffsetToElemIdx? parentPtr.offsetBytes elemSz with
              | .none => .ub
              | .some rawElemOffset =>
                let elemOffset := Nat.add rawElemOffset baseIdx
                match Nat.ble (Nat.add elemOffset lenSc.bits) (length elems) with
                | false => .ub
                | true =>
                  match resolvedRest with
                  | .nil =>
                    let tag := mem.nextTag
                    let (newTargetProj, newOffsetBytes, newRangeOff, newRangeLen) :=
                      match Nat.beq baseIdx 0 with
                      | true =>
                        (parentEntry.targetProjection,
                         parentPtr.offsetBytes,
                         parentEntry.rangeOffset,
                         parentEntry.rangeLen)
                      | false =>
                        let subProj :=
                          ProjectionElem.subslice
                            elemOffset
                            (Nat.add elemOffset lenSc.bits)
                            false :: .nil
                        let rawFullProj :=
                          match containerProj with
                          | .nil => subProj
                          | ph :: pt => ph :: appendProjections pt subProj
                        (normalizeSubsliceProjections rawFullProj, 0, 0, 0)
                    let entry : BorrowEntry := {
                      tag := tag
                      targetLocal := parentEntry.targetLocal
                      targetProjection := newTargetProj
                      perm := perm
                      rangeOffset := newRangeOff
                      rangeLen := newRangeLen
                    }
                    let mem' := {
                      mem with
                      borrows := entry :: mem.borrows
                      nextTag := Nat.add tag 1
                    }
                    .ok
                      (.aggregate 0
                        (.ptr { allocId := tag, offsetBytes := newOffsetBytes } 8 ::
                          .scalar ⟨lenSc.bits, 8⟩ ::
                          .nil))
                      locals
                      mem'
                  | .subslice fromIdx toIdx fromEnd :: .nil =>
                    match Nat.ble toIdx lenSc.bits with
                    | false => .ub
                    | true =>
                      let endIdx :=
                        match fromEnd with
                        | true => Nat.sub lenSc.bits toIdx
                        | false => toIdx
                      match Nat.ble fromIdx endIdx with
                      | false => .ub
                      | true =>
                        let subLen := Nat.sub endIdx fromIdx
                        let absFrom := Nat.add elemOffset fromIdx
                        let absEnd := Nat.add elemOffset endIdx
                        let subProj := ProjectionElem.subslice absFrom absEnd false :: .nil
                        let rawFullProj :=
                          match containerProj with
                          | .nil => subProj
                          | ph :: pt => ph :: appendProjections pt subProj
                        let fullProj := normalizeSubsliceProjections rawFullProj
                        let tag := mem.nextTag
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
                        .ok
                          (.aggregate 0
                            (.ptr { allocId := tag, offsetBytes := 0 } 8 ::
                              .scalar ⟨subLen, 8⟩ ::
                              .nil))
                          locals
                          mem'
                  | .constantIndex offset minLen fromEnd :: tailProj =>
                    let fromEndBoundsOk :=
                      match fromEnd with
                      | false => true
                      | true =>
                        Bool.and
                          (Nat.ble 1 offset)
                          (Nat.ble offset lenSc.bits)
                    match Bool.and (Nat.ble minLen lenSc.bits) fromEndBoundsOk with
                    | false => .ub
                    | true =>
                      let idx :=
                        match fromEnd with
                        | true => Nat.sub lenSc.bits offset
                        | false => offset
                      match Nat.ble (.succ idx) lenSc.bits with
                      | false => .ub
                      | true =>
                        let absIdx := Nat.add elemOffset idx
                        let normProj := ProjectionElem.constantIndex absIdx 0 false :: tailProj
                        let rawFullProj :=
                          match containerProj with
                          | .nil => normProj
                          | ph :: pt => ph :: appendProjections pt normProj
                        let fullProj := normalizeSubsliceProjections rawFullProj
                        let tag := mem.nextTag
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
                  | _ => .ub
            | .none =>
              match readProjectedValue locals targetRootVal parentEntry.targetProjection with
              | .ok .unit =>
                match
                  Bool.and
                    (Nat.beq parentPtr.offsetBytes 0)
                    (Nat.beq lenSc.bits 0)
                with
                | false => .ub
                | true =>
                  let isZeroEmptySliceProj :=
                    match resolvedRest with
                    | .nil => true
                    | .subslice 0 0 _ :: .nil => true
                    | _ => false
                  match isZeroEmptySliceProj with
                  | false => .ub
                  | true =>
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
                        (.ptr { allocId := tag, offsetBytes := 0 } 8 ::
                          .scalar ⟨0, 8⟩ ::
                          .nil))
                      locals
                      mem'
              | _ => .ub
      | .none =>
        match lookupGlobalAlloc mem.globals parentPtr.allocId with
        | .some alloc =>
          let elemKind : RigidTy :=
            match pointeeTyOpt with
            | .some { kind := .slice ek, .. } => ek
            | .some { kind := .array ek _, .. } => ek
            | .some { kind := .str, .. } => .uint .u8
            | _ =>
              match LayoutTable.lookup layouts 0 with
              | .some l =>
                match l.fields with
                | .primitive => uintRigidTyOfStride l.size.bytes
                | .array stride _ => uintRigidTyOfStride stride.bytes
                | _ => .uint .u8
              | .none => .uint .u8
          let elemSz :=
            match rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
            | .some n => n
            | .none => 1
          let mutOk :=
            match isMut, alloc.mutability with
            | true, .not => false
            | _, _ => true
          let sliceInBounds :=
            Nat.ble
              (Nat.add parentPtr.offsetBytes (Nat.mul lenSc.bits elemSz))
              (length alloc.bytes)
          match Bool.and mutOk sliceInBounds with
          | false => .ub
          | true =>
            match resolvedRest with
            | .nil =>
              .ok
                (.aggregate 0
                  (.ptr parentPtr 8 :: .scalar ⟨lenSc.bits, 8⟩ :: .nil))
                locals
                mem
            | .subslice fromIdx toIdx fromEnd :: .nil =>
              match Nat.ble toIdx lenSc.bits with
              | false => .ub
              | true =>
                let endIdx :=
                  match fromEnd with
                  | true => Nat.sub lenSc.bits toIdx
                  | false => toIdx
                match Nat.ble fromIdx endIdx with
                | false => .ub
                | true =>
                  let subLen := Nat.sub endIdx fromIdx
                  let newOffset :=
                    Nat.add parentPtr.offsetBytes (Nat.mul fromIdx elemSz)
                  .ok
                    (.aggregate 0
                      (.ptr { parentPtr with offsetBytes := newOffset } 8 ::
                        .scalar ⟨subLen, 8⟩ ::
                        .nil))
                    locals
                    mem
            | .constantIndex offset minLen fromEnd :: .nil =>
              let fromEndBoundsOk :=
                match fromEnd with
                | false => true
                | true =>
                  Bool.and
                    (Nat.ble 1 offset)
                    (Nat.ble offset lenSc.bits)
              match Bool.and (Nat.ble minLen lenSc.bits) fromEndBoundsOk with
              | false => .ub
              | true =>
                let idx :=
                  match fromEnd with
                  | true => Nat.sub lenSc.bits offset
                  | false => offset
                match Nat.ble (.succ idx) lenSc.bits with
                | false => .ub
                | true =>
                  let newOffset :=
                    Nat.add parentPtr.offsetBytes (Nat.mul idx elemSz)
                  .ok
                    (.ptr { parentPtr with offsetBytes := newOffset } 8)
                    locals
                    mem
            | _ => .ub
        | .none =>
          let emptySliceOk :=
            Bool.and
              (Bool.not isMut)
              (Bool.and
                (Nat.beq lenSc.bits 0)
                (Bool.not
                  (Bool.and
                    (Nat.beq parentPtr.allocId 0)
                    (Nat.beq parentPtr.offsetBytes 0))))
          let isZeroEmptySliceProj :=
            match resolvedRest with
            | .nil => true
            | .subslice 0 0 _ :: .nil => true
            | _ => false
          match Bool.and emptySliceOk isZeroEmptySliceProj with
          | true =>
            .ok
              (.aggregate 0
                (.ptr parentPtr 8 :: .scalar ⟨0, 8⟩ :: .nil))
              locals
              mem
          | false => .ub

/--
Evaluate a dereferenced borrow or raw-address-of (`&(*p)...` or `&raw (*p)...`)
when `p` holds a thin pointer `Value.ptr parentPtr ptrSz` backed by a global
allocation `alloc` in `mem.globals`.
-/
def evalGlobalThinPtrDerefBorrow
    (locals : List LocalSlot)
    (mem : Memory)
    (alloc : CapturedAllocation)
    (parentPtr : ProvenancePtr)
    (ptrSz : Nat)
    (restProj : List ProjectionElem)
    (isMut : Bool)
    (pointeeTyOpt : Option Ty := .none)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  let mutOk :=
    match isMut, alloc.mutability with
    | true, .not => false
    | _, _ => true
  match
    Bool.and
      (Nat.beq ptrSz 8)
      (Bool.and mutOk (Nat.ble parentPtr.offsetBytes (length alloc.bytes)))
  with
  | false => .ub
  | true =>
    match resolveBorrowProjectionElems locals restProj with
    | .none => .ub
    | .some rawResolvedRest =>
      let resolvedRest :=
        normalizeSubsliceProjections (stripTransparentProjections rawResolvedRest)
      let remBytes := Nat.sub (length alloc.bytes) parentPtr.offsetBytes
      let (elemSz, maxElems) :=
        match pointeeTyOpt with
        | .some { kind := .array elemKind arrLen, .. } =>
          let sz :=
            match rigidTyByteSize layouts { kind := elemKind, layoutIdx := 0 } with
            | .some n => n
            | .none => 1
          (sz, arrLen)
        | _ =>
          match LayoutTable.lookup layouts 0 with
          | .some l =>
            match l.fields with
            | .array stride count => (stride.bytes, count)
            | _ => (1, remBytes)
          | .none => (1, remBytes)
      match resolvedRest with
      | .nil =>
        let reqBytes :=
          match pointeeTyOpt with
          | .some pointeeTy =>
            match rigidTyByteSize layouts pointeeTy with
            | .some n => n
            | .none => 0
          | .none => 0
        match Nat.ble reqBytes remBytes with
        | true => .ok (.ptr parentPtr 8) locals mem
        | false => .ub
      | .constantIndex offset minLen fromEnd :: .nil =>
        let fromEndBoundsOk :=
          match fromEnd with
          | false => true
          | true =>
            Bool.and
              (Nat.ble 1 offset)
              (Nat.ble offset maxElems)
        let idx :=
          match fromEnd with
          | true => Nat.sub maxElems offset
          | false => offset
        let neededBytes := Nat.mul (.succ idx) elemSz
        match
          Bool.and
            (Nat.ble minLen maxElems)
            (Bool.and
              fromEndBoundsOk
              (Bool.and
                (Nat.ble (.succ idx) maxElems)
                (Nat.ble neededBytes remBytes)))
        with
        | true =>
          let newOff := Nat.add parentPtr.offsetBytes (Nat.mul idx elemSz)
          .ok (.ptr { parentPtr with offsetBytes := newOff } 8) locals mem
        | false => .ub
      | .subslice fromIdx toIdx fromEnd :: .nil =>
        match Nat.ble toIdx maxElems with
        | false => .ub
        | true =>
          let endIdx :=
            match fromEnd with
            | true => Nat.sub maxElems toIdx
            | false => toIdx
          let neededBytes := Nat.mul endIdx elemSz
          match
            Bool.and
              (Nat.ble fromIdx endIdx)
              (Bool.and
                (Nat.ble endIdx maxElems)
                (Nat.ble neededBytes remBytes))
          with
          | true =>
            let newOff := Nat.add parentPtr.offsetBytes (Nat.mul fromIdx elemSz)
            .ok (.ptr { parentPtr with offsetBytes := newOff } 8) locals mem
          | false => .ub
      | _ => .ub

/--
Compute the MIR `Rvalue.discriminant` scalar for `val` read from `place`.

- For `core::cmp::Ordering` (`#[repr(i8)] enum Ordering { Less = -1, Equal = 0, Greater = 1 }`),
  maps both `Value.scalar sc` (produced by `BinOp.cmp` and `three_way_compare`,
  where `Less = ⟨255, 1⟩`, `Equal = ⟨0, 1⟩`, `Greater = ⟨1, 1⟩`) and zero-field
  `Value.aggregate variantIdx []` (`0 ↦ ⟨255, 1⟩`, `1 ↦ ⟨0, 1⟩`, `2 ↦ ⟨1, 1⟩`)
  to the signed 1-byte `Ordering` discriminant scalar, faulting with `.ub` on
  out-of-range scalar bit patterns or widths.
- For general multi-variant ADTs (`VariantsShape.multiple` or untyped `.adt` layout)
  stored as `Value.scalar sc` (C-like scalar-encoded enums), checks `validRange`
  when present and preserves `Value.scalar sc`.
- For uninhabited types (`.never`, `isUninhabited = true`, or `VariantsShape.empty`),
  returns `.ub`.
- For `Value.aggregate variantIdx _`, validates `variantIdx` against
  `VariantsShape.single` / `VariantsShape.multiple` when layout metadata is
  available and returns `Value.scalar ⟨variantIdx, 8⟩`.
- For single-variant ADTs (`VariantsShape.single`) and non-ADT types (`Value.unit`,
  `Value.scalar`, `Value.ptr`), returns `Value.scalar ⟨0, 8⟩` per `rustc_middle`
  (`Rvalue::Discriminant` "returns `0` if the type does not have a discriminant").
-/
def evalPlaceDiscriminant
    (val : Value)
    (locals' : List LocalSlot)
    (mem : Memory)
    (place : Place)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  match val with
  | .aggregate variantIdx fields =>
    match placeTy localDecls layouts place with
    | .some pTy =>
      match pTy.kind with
      | .never => .ub
      | .adt defPath _ =>
        let evalOrderingOrVariant : RvalueEvalResult :=
          match Bool.and (stringEq defPath "core::cmp::Ordering") (Nat.beq (length fields) 0) with
          | true =>
            match variantIdx with
            | 0 => .ok (.scalar ⟨255, 1⟩) locals' mem
            | 1 => .ok (.scalar ⟨0, 1⟩) locals' mem
            | 2 => .ok (.scalar ⟨1, 1⟩) locals' mem
            | _ => .ub
          | false => .ok (.scalar ⟨variantIdx, 8⟩) locals' mem
        match LayoutTable.lookup layouts pTy.layoutIdx with
        | .some { isUninhabited := true, .. } => .ub
        | .some { variants := .empty, .. } => .ub
        | .some { variants := .single expectedIdx, .. } =>
          match Nat.beq variantIdx expectedIdx with
          | true => .ok (.scalar ⟨0, 8⟩) locals' mem
          | false => .ub
        | .some { variants := .multiple _ _ variants, .. } =>
          let varBoundsOk :=
            match variants with
            | .nil => true
            | _ :: _ => Nat.ble (.succ variantIdx) (length variants)
          match varBoundsOk with
          | true => evalOrderingOrVariant
          | false => .ub
        | .none => evalOrderingOrVariant
      | .tuple _ =>
        match Nat.beq variantIdx 0 with
        | true => .ok (.scalar ⟨0, 8⟩) locals' mem
        | false => .ub
      | .array _ _ =>
        match Nat.beq variantIdx 0 with
        | true => .ok (.scalar ⟨0, 8⟩) locals' mem
        | false => .ub
      | .slice _ =>
        match Nat.beq variantIdx 0 with
        | true => .ok (.scalar ⟨0, 8⟩) locals' mem
        | false => .ub
      | .str =>
        match Nat.beq variantIdx 0 with
        | true => .ok (.scalar ⟨0, 8⟩) locals' mem
        | false => .ub
      | _ => .ok (.scalar ⟨variantIdx, 8⟩) locals' mem
    | .none => .ok (.scalar ⟨variantIdx, 8⟩) locals' mem
  | .scalar sc =>
    match placeTy localDecls layouts place with
    | .some pTy =>
      match pTy.kind with
      | .never => .ub
      | .adt defPath _ =>
        match LayoutTable.lookup layouts pTy.layoutIdx with
        | .some { isUninhabited := true, .. } => .ub
        | .some { variants := .empty, .. } => .ub
        | .some { variants := .single _, .. } => .ok (.scalar ⟨0, 8⟩) locals' mem
        | .some { variants := .multiple (.initialized _ validRange) _ _, .. } =>
          match ScalarInt.inRange sc validRange with
          | true => .ok (.scalar sc) locals' mem
          | false => .ub
        | _ =>
          match stringEq defPath "core::cmp::Ordering" with
          | true =>
            let isOrderingSc :=
              Bool.and
                (Nat.beq sc.sizeBytes 1)
                (Bool.or
                  (Nat.beq sc.bits 0)
                  (Bool.or (Nat.beq sc.bits 1) (Nat.beq sc.bits 255)))
            match isOrderingSc with
            | true => .ok (.scalar sc) locals' mem
            | false => .ub
          | false => .ok (.scalar sc) locals' mem
      | _ => .ok (.scalar ⟨0, 8⟩) locals' mem
    | .none => .ok (.scalar ⟨0, 8⟩) locals' mem
  | .unit => .ok (.scalar ⟨0, 8⟩) locals' mem
  | .ptr _ _ => .ok (.scalar ⟨0, 8⟩) locals' mem

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
- Raw pointer creation (`.rawPtr mutability place`) checks `placeIsFreeze
  localDecls layouts place` when `mutability = .not` (preserving
  `TreeBorrowPerm.reserved` for `!Freeze` interior-mutable pointees such as
  `core::cell::UnsafeCell<T>` and inheriting `.reserved` from a `.reserved`
  parent on `.deref :: restProj`, matching `ReborrowSettings::new` returning
  `None` for `PtrType::Raw` in MiniRust `spec/mem/tree_borrows/reborrow_settings.md`).

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
            evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc
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
      | .shared => sharedBorrowPerm localDecls layouts place
      | .mut false => TreeBorrowPerm.active
      | .mut true => TreeBorrowPerm.reserved
    match place.projection with
    | .deref :: restProj =>
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr ptrSz)) =>
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, borrowKind with
          | .disabled, _ => .ub
          | .frozen, .mut _ => .ub
          | _, _ =>
            match resolveBorrowProjectionElems locals restProj with
            | .none => .ub
            | .some resolvedProj =>
              match
                needsThinPtrElemResolution
                  parentEntry.targetProjection
                  parentPtr.offsetBytes
              with
              | false =>
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
              | true =>
                let targetRootOpt : Option Value :=
                  match get? locals parentEntry.targetLocal with
                  | .some (.init v) => .some v
                  | .some _ => .none
                  | .none =>
                    match get? mem.callerLocals parentEntry.targetLocal with
                    | .some (.init v) => .some v
                    | _ => .none
                match targetRootOpt with
                | .none => .ub
                | .some targetRootVal =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      parentEntry
                      parentPtr
                      resolvedProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    let tag := mem.nextTag
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
        | .none =>
          match lookupGlobalAlloc mem.globals parentPtr.allocId with
          | .some alloc =>
            let isMut :=
              match borrowKind with
              | .shared => false
              | .mut _ => true
            let pointeeTyOpt :=
              placeTy localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
            evalGlobalThinPtrDerefBorrow
              locals
              mem
              alloc
              parentPtr
              ptrSz
              restProj
              isMut
              pointeeTyOpt
              layouts
          | .none => .ub
      | .some (.init (.aggregate 0 (.ptr parentPtr ptrSz :: .scalar lenSc :: .nil))) =>
        let isMut :=
          match borrowKind with
          | .shared => false
          | .mut _ => true
        let pointeeTyOpt :=
          placeTy localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
        evalSliceFatPtrDerefBorrow
          locals
          mem
          parentPtr
          ptrSz
          lenSc
          restProj
          perm
          isMut
          pointeeTyOpt
          layouts
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        match resolveBorrowProjectionElems locals place.projection with
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
      | .not =>
        match placeIsFreeze localDecls layouts place with
        | true => TreeBorrowPerm.frozen
        | false => TreeBorrowPerm.reserved
      | .mut => TreeBorrowPerm.active
    match place.projection with
    | .deref :: restProj =>
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr ptrSz)) =>
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, mutability with
          | .disabled, _ => .ub
          | .frozen, .mut => .ub
          | _, _ =>
            match resolveBorrowProjectionElems locals restProj with
            | .none => .ub
            | .some resolvedProj =>
              match
                needsThinPtrElemResolution
                  parentEntry.targetProjection
                  parentPtr.offsetBytes
              with
              | false =>
                let tag := mem.nextTag
                let fullProj :=
                  match parentEntry.targetProjection with
                  | .nil => resolvedProj
                  | ph :: pt => ph :: appendProjections pt resolvedProj
                let rawPerm :=
                  match mutability, parentEntry.perm with
                  | .not, .reserved => TreeBorrowPerm.reserved
                  | _, _ => perm
                let entry : BorrowEntry := {
                  tag := tag
                  targetLocal := parentEntry.targetLocal
                  targetProjection := fullProj
                  perm := rawPerm
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
              | true =>
                let targetRootOpt : Option Value :=
                  match get? locals parentEntry.targetLocal with
                  | .some (.init v) => .some v
                  | .some _ => .none
                  | .none =>
                    match get? mem.callerLocals parentEntry.targetLocal with
                    | .some (.init v) => .some v
                    | _ => .none
                match targetRootOpt with
                | .none => .ub
                | .some targetRootVal =>
                  match
                    resolveStackThinPtrTargetProj?
                      locals
                      targetRootVal
                      parentEntry
                      parentPtr
                      resolvedProj
                  with
                  | .none => .ub
                  | .some fullProj =>
                    let tag := mem.nextTag
                    let rawPerm :=
                      match mutability, parentEntry.perm with
                      | .not, .reserved => TreeBorrowPerm.reserved
                      | _, _ => perm
                    let entry : BorrowEntry := {
                      tag := tag
                      targetLocal := parentEntry.targetLocal
                      targetProjection := fullProj
                      perm := rawPerm
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
        | .none =>
          match lookupGlobalAlloc mem.globals parentPtr.allocId with
          | .some alloc =>
            let isMut :=
              match mutability with
              | .not => false
              | .mut => true
            let pointeeTyOpt :=
              placeTy localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
            evalGlobalThinPtrDerefBorrow
              locals
              mem
              alloc
              parentPtr
              ptrSz
              restProj
              isMut
              pointeeTyOpt
              layouts
          | .none => .ub
      | .some (.init (.aggregate 0 (.ptr parentPtr ptrSz :: .scalar lenSc :: .nil))) =>
        let isMut :=
          match mutability with
          | .not => false
          | .mut => true
        let pointeeTyOpt :=
          placeTy localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
        evalSliceFatPtrDerefBorrow
          locals
          mem
          parentPtr
          ptrSz
          lenSc
          restProj
          perm
          isMut
          pointeeTyOpt
          layouts
      | _ => .ub
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some _ =>
        match resolveBorrowProjectionElems locals place.projection with
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
    evalPlaceLen locals place mem localDecls layouts
  | .wrapUnsafeBinder op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' => .ok v locals' mem
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
      match targetTy.kind with
      | .rawPtr _ (.slice _) => .ub
      | .rawPtr _ .str => .ub
      | .rawPtr _ (.dynamic _) => .ub
      | .rawPtr _ dstElem =>
        let arrayCastLenOpt : Option Nat :=
          match operandTy localDecls layouts op with
          | .some { kind := .rawPtr _ (.array srcElem arrLen), .. } =>
            match rigidTyEq srcElem dstElem with
            | true => .some arrLen
            | false => .none
          | .some { kind := .ref _ (.array srcElem arrLen), .. } =>
            match rigidTyEq srcElem dstElem with
            | true => .some arrLen
            | false => .none
          | _ => .none
        match arrayCastLenOpt, lookupBorrow mem.borrows ptrVal.tag with
        | .some arrLen, .some parentEntry =>
          match Nat.beq sz 8 with
          | true =>
            deriveStackElemThinPtr locals' mem ptrVal parentEntry (.some arrLen)
          | false => .ub
        | _, _ => .ok (.ptr ptrVal sz) locals' mem
      | _ => .ok (.ptr ptrVal sz) locals' mem
    | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
      match
        Bool.and
          (Nat.beq sz 8)
          (Nat.beq metaSc.sizeBytes 8)
      with
      | false => .ub
      | true =>
        match isThinRawPtrTy targetTy with
        | true =>
          match lookupBorrow mem.borrows ptrVal.tag with
          | .some parentEntry =>
            deriveStackElemThinPtr locals' mem ptrVal parentEntry (.some metaSc.bits)
          | .none => .ok (.ptr ptrVal sz) locals' mem
        | false =>
          match targetTy.kind with
          | .rawPtr _ _ =>
            .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' mem
          | _ => .ub
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
    let ptrBytes := layoutPointerBytes layouts
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok (.aggregate 0 (.ptr _ ptrSz :: .scalar metaSc :: .nil)) locals' =>
      match
        Bool.and
          (Nat.beq ptrSz ptrBytes)
          (Nat.beq metaSc.sizeBytes ptrBytes)
      with
      | true => .ok (.scalar ⟨metaSc.bits, ptrBytes⟩) locals' mem
      | false => .ub
    | .ok (.aggregate 0 elems) locals' =>
      .ok (.scalar ⟨length elems, ptrBytes⟩) locals' mem
    | .ok (.ptr _ ptrSz) locals' =>
      match Nat.beq ptrSz ptrBytes with
      | true => .ok .unit locals' mem
      | false => .ub
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .discriminant place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
    | .ok val locals' =>
      evalPlaceDiscriminant val locals' mem place localDecls layouts
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
  | .aggregate (.closure _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
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
