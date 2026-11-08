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
Normalize adjacent `.subslice` projections without collapsing a trailing
`.constantIndex` into an enclosing `.subslice`, preserving the narrowest
enclosing subslice window for spatial provenance bounds in
`ptrAllocByteBound?`, `resolveStackThinPtrFieldOffsetProj?`, and
`resolveStackThinPtrTargetProjWithResidual?`.
-/
@[reducible]
def normalizeAdjacentSubslicesAux :
    Option (Nat × Nat) → List ProjectionElem → List ProjectionElem
  | .none, .nil => .nil
  | .some (fromA, toA), .nil => .subslice fromA toA false :: .nil
  | .none, .subslice fromA toA false :: rest =>
    match Nat.ble fromA toA with
    | true => normalizeAdjacentSubslicesAux (.some (fromA, toA)) rest
    | false =>
      .subslice fromA toA false :: normalizeAdjacentSubslicesAux .none rest
  | .none, elem :: rest =>
    elem :: normalizeAdjacentSubslicesAux .none rest
  | .some (fromA, toA), .subslice relFrom relTo false :: rest =>
    let subLen := Nat.sub toA fromA
    match Bool.and (Nat.ble relFrom relTo) (Nat.ble relTo subLen) with
    | true =>
      normalizeAdjacentSubslicesAux
        (.some (Nat.add fromA relFrom, Nat.add fromA relTo))
        rest
    | false =>
      .subslice fromA toA false ::
        .subslice relFrom relTo false ::
        normalizeAdjacentSubslicesAux .none rest
  | .some (fromA, toA), .subslice relFrom relTo true :: rest =>
    let subLen := Nat.sub toA fromA
    let endIdx := Nat.sub subLen relTo
    match Bool.and (Nat.ble relTo subLen) (Nat.ble relFrom endIdx) with
    | true =>
      normalizeAdjacentSubslicesAux
        (.some (Nat.add fromA relFrom, Nat.add fromA endIdx))
        rest
    | false =>
      .subslice fromA toA false ::
        .subslice relFrom relTo true ::
        normalizeAdjacentSubslicesAux .none rest
  | .some (fromA, toA), elem :: rest =>
    .subslice fromA toA false :: elem :: normalizeAdjacentSubslicesAux .none rest

/--
Normalize adjacent `.subslice` projections while retaining `.subslice` window
boundaries ahead of `.constantIndex` / `.field` projections.
-/
@[reducible]
def normalizeAdjacentSubslices (proj : List ProjectionElem) : List ProjectionElem :=
  normalizeAdjacentSubslicesAux .none proj

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L47-L55>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L101-L106>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_unprotected.md#L37-L62>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_unprotected.md#L64-L75>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L89-L125>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_unprotected.md#L27-L53>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L89-L125>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_unprotected.md#L46-L53>

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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L7-L8>

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
  match layouts.pointerBits with
  | 0 => 8
  | n + 1 => Nat.div (n + 1) 8

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
      match writeProjectedValue locals .unit rest newVal with
      | .ok updatedFieldVal =>
        .ok
          (.aggregate
            variantIdx
            (setOrExtendFields fields idx updatedFieldVal))
      | .ub => .ub
      | .unsupported => .unsupported
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
Check that every element in `elems` has byte size `elemSz` according to
`inferValueByteSizeAux 8` (returning `false` when `elemSz == 0` or any element
differs from `elemSz`). Used to distinguish homogeneous array/slice element
lists from heterogeneous variant-0 aggregates (such as `(u8, u32)` tuples) when
no static array/slice `placeTy` is in scope.
-/
@[reducible]
def elemsHaveUniformByteStride : List Value → Nat → Bool
  | .nil, elemSz => Bool.not (Nat.beq elemSz 0)
  | e :: rest, elemSz =>
    match Nat.beq elemSz 0 with
    | true => false
    | false =>
      match inferValueByteSizeAux 8 e with
      | .some eSz =>
        match Nat.beq eSz elemSz with
        | true => elemsHaveUniformByteStride rest elemSz
        | false => false
      | .none => false

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
`targetProjection` at `offsetBytes` requires element or byte-offset resolution:
`targetProjection` is non-empty and either ends with `.subslice` or has
`offsetBytes > 0`. Reduces immediately to `false` when `targetProjection` is
`.nil` (the legacy untyped deref paths therefore ignore `offsetBytes` on
borrows of whole locals; the typed paths resolve offsets through
`resolveStackThinPtrTargetProj?` instead).
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
If `proj` ends with `.field fieldIdx fieldTy`, split `proj` into
`(initProj, fieldIdx, fieldTy)`; otherwise return `.none`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1226>

> "Field(FieldIdx, T),"
-/
@[reducible]
def splitLastField? :
    List ProjectionElem → Option (List ProjectionElem × FieldIdx × Ty)
  | .nil => .none
  | .field fieldIdx fieldTy :: .nil => .some (.nil, fieldIdx, fieldTy)
  | elem :: rest =>
    match splitLastField? rest with
    | .some (initProj, fieldIdx, fieldTy) =>
      .some (elem :: initProj, fieldIdx, fieldTy)
    | .none => .none

/--
Split `proj` into `(encProj, relProj)` immediately after its last `.subslice`
projection element, returning `(.nil, proj)` when `proj` contains no
`.subslice`.

Modeling choice: Subslice projections narrow provenance bounds to the subslice
window (`[fromIdx .. toIdx)`), whereas `.field`, `.constantIndex`, and
`.downcast` steps after `encProj` offset within the enclosing allocation or
subslice container.

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L380-L430>

> "/// * If the computed offset is non-zero, then `self` must be derived from a
> ///   pointer to some allocated object, and the entire memory range between
> ///   `self` and the result must be in bounds of that allocated object."
-/
@[reducible]
def splitAfterLastSeqProj :
    List ProjectionElem → (List ProjectionElem × List ProjectionElem)
  | .nil => (.nil, .nil)
  | .subslice fromIdx toIdx fromEnd :: rest =>
    let (subPrefix, suffix) := splitAfterLastSeqProj rest
    (.subslice fromIdx toIdx fromEnd :: subPrefix, suffix)
  | elem :: rest =>
    match splitAfterLastSeqProj rest with
    | (.nil, suffix) => (.nil, elem :: suffix)
    | (subHead :: subTail, suffix) => (elem :: subHead :: subTail, suffix)
/--
Compute `(rem / stride, rem % stride)` for positive `stride` using structural
recursion on `fuel` so symbolic reduction (`whnf`/`isDefEq`) never unfolds
well-founded `Nat.div` or `Nat.mod`.
-/
@[reducible]
def divModBytesAux : Nat → Nat → Nat → Nat → (Nat × Nat)
  | .zero, rem, _, quot => (quot, rem)
  | .succ fuel, rem, stride, quot =>
    match Nat.ble stride rem with
    | false => (quot, rem)
    | true => divModBytesAux fuel (Nat.sub rem stride) stride (.succ quot)

/--
Round byte offset `off` up to the next multiple of alignment `align` (returning
`off` unchanged when `align <= 1`).
-/
@[reducible]
def alignUpBytes (off align : Nat) : Nat :=
  match Nat.ble align 1 with
  | true => off
  | false =>
    let (_, rem) := divModBytesAux off off align 0
    match Nat.beq rem 0 with
    | true => off
    | false => Nat.add off (Nat.sub align rem)

/--
Natural byte alignment of a scalar of width `sizeBytes` on 64-bit targets.
-/
@[reducible]
def scalarNaturalAlignBytes (sz : Nat) : Nat :=
  match Nat.beq sz 2 with
  | true => 2
  | false =>
    match Nat.beq sz 4 with
    | true => 4
    | false =>
      match Nat.beq sz 8 with
      | true => 8
      | false =>
        match Nat.beq sz 16 with
        | true => 16
        | false => 1

/--
Accumulate `#[repr(C)]` `(sizeBytes, alignBytes)` across `fields` given
per-field analyzer `elemLayout?`.
-/
@[reducible]
def foldCReprFieldsAux
    (elemLayout? : Value → Option (Nat × Nat))
    (runningOff maxAlign : Nat) :
    List Value → Option (Nat × Nat)
  | .nil => .some (alignUpBytes runningOff maxAlign, maxAlign)
  | fv :: rest =>
    match elemLayout? fv with
    | .none => .none
    | .some (fSz, fAlign) =>
      let alignedOff := alignUpBytes runningOff fAlign
      let nextMax :=
        match Nat.ble maxAlign fAlign with
        | true => fAlign
        | false => maxAlign
      foldCReprFieldsAux
        elemLayout?
        (Nat.add alignedOff fSz)
        nextMax
        rest

/--
Single fuel step of `inferValueCReprSizeAndAlignAux`, parameterized by nested
field analyzer `recVal`.
-/
@[reducible]
def inferValueCReprStep
    (recVal : Value → Option (Nat × Nat)) :
    Value → Option (Nat × Nat)
  | .unit => .some (0, 1)
  | .scalar sc => .some (sc.sizeBytes, scalarNaturalAlignBytes sc.sizeBytes)
  | .ptr _ sz =>
    match Nat.beq sz 0 with
    | true => .some (0, 1)
    | false => .some (sz, sz)
  | .aggregate 0 fields => foldCReprFieldsAux recVal 0 1 fields
  | .aggregate (.succ _) _ => .none

/--
Infer the fallback `#[repr(C)]` `(sizeBytes, alignBytes)` of runtime `Value` `v`
up to nesting depth `fuel` when no compiler `TypeLayout` entry is available.
-/
@[reducible]
def inferValueCReprSizeAndAlignAux : Nat → Value → Option (Nat × Nat)
  | .zero => fun _ => .none
  | .succ fuel' => inferValueCReprStep (inferValueCReprSizeAndAlignAux fuel')

/--
Infer the fallback `#[repr(C)]` byte size of runtime `Value` `v` when no
compiler `TypeLayout` entry is available.
-/
@[reducible]
def inferValueCReprBytes (v : Value) : Option Nat :=
  match inferValueCReprSizeAndAlignAux 8 v with
  | .some (sz, _) => .some sz
  | .none => .none

/--
Sum the `#[repr(C)]`-aligned byte offsets of the first `count` elements of
`kinds` starting from `runningOff` when each prefix element has a known
structural byte size.
-/
@[reducible]
def sumPrefixTupleKindBytesAux : Nat → Nat → List RigidTy → Option Nat
  | _, _, .nil => .none
  | .zero, runningOff, kind :: _ =>
    match rigidTyKindByteSize kind with
    | .some sz => .some (alignUpBytes runningOff (scalarNaturalAlignBytes sz))
    | .none => .none
  | .succ k, runningOff, kind :: rest =>
    match rigidTyKindByteSize kind with
    | .some sz =>
      let fAlign := scalarNaturalAlignBytes sz
      let alignedOff := alignUpBytes runningOff fAlign
      sumPrefixTupleKindBytesAux k (Nat.add alignedOff sz) rest
    | .none => .none

/--
Compute the `#[repr(C)]`-aligned byte offset of element `fieldIdx` within tuple
element kinds `kinds` when `fieldIdx < length kinds` (returning `.some 0` when
`fieldIdx == 0`).
-/
@[reducible]
def sumPrefixTupleKindBytes : Nat → List RigidTy → Option Nat
  | .zero, _ => .some 0
  | .succ k, kinds => sumPrefixTupleKindBytesAux (.succ k) 0 kinds

/--
Compute the `#[repr(C)]`-aligned byte offset of source field `fieldIdx` within
runtime field list `fields` starting from `runningOff`.
-/
@[reducible]
def sumPrefixFieldValueBytesAux : Nat → Nat → List Value → Option Nat
  | _, _, .nil => .none
  | .zero, runningOff, fv :: _ =>
    match inferValueCReprSizeAndAlignAux 8 fv with
    | .some (_, fAlign) => .some (alignUpBytes runningOff fAlign)
    | .none => .none
  | .succ k, runningOff, fv :: rest =>
    match inferValueCReprSizeAndAlignAux 8 fv with
    | .some (fSz, fAlign) =>
      let alignedOff := alignUpBytes runningOff fAlign
      sumPrefixFieldValueBytesAux k (Nat.add alignedOff fSz) rest
    | .none => .none

/--
Compute the `#[repr(C)]`-aligned byte offset of source field `fieldIdx` within
runtime field list `fields` when no compiler `TypeLayout` entry is available.
-/
@[reducible]
def sumPrefixFieldValueBytes (fieldIdx : Nat) (fields : List Value) : Option Nat :=
  sumPrefixFieldValueBytesAux fieldIdx 0 fields

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
Test whether `layout` is a valid aggregate `TypeLayout` for runtime variant
`aggVar` and field count `fieldCount`.
-/
@[reducible]
def layoutMatchesAggregateVariant
    (layout : TypeLayout)
    (aggVar fieldCount : Nat) :
    Bool :=
  match layout.isUninhabited, layout.variants, layout.fields with
  | true, _, _ => false
  | false, .multiple _ _ variants, _ =>
    match get? variants aggVar with
    | .some (.arbitrary offsets _) => Nat.beq (length offsets) fieldCount
    | _ => false
  | false, .single singleVar, .arbitrary offsets _ =>
    Bool.and
      (Nat.beq aggVar singleVar)
      (Nat.beq (length offsets) fieldCount)
  | _, _, _ => false

/--
Out-of-range `LayoutIdx` (`length layouts.entries`) used for synthesized `Ty`s
whose compiler layout is unknown (array/slice element types rebuilt from a
`RigidTy` kind without a container `fieldLayouts` entry or a structurally equal
`LocalDecl`). Unlike `0`, which is also the index of the first real
`TypeLayout`, it never adopts an unrelated entry: `LayoutTable.lookup` returns
`.none`.
-/
@[reducible]
def unresolvedLayoutIdx (layouts : LayoutTable) : Nat :=
  length layouts.entries

/--
`true` for the primitive scalar kinds (`bool`, `char`, integers, floats), whose
`encodeValueToBytes` image never consults a `LayoutTable` entry.
-/
@[reducible]
def isPrimitiveScalarKind : RigidTy → Bool
  | .bool => true
  | .char => true
  | .int _ => true
  | .uint _ => true
  | .float _ => true
  | _ => false

/--
Layout index for a synthesized `Ty` of `kind` when no compiler layout index is
in scope: `0` for primitive scalar kinds (matching standard MIR scalar `Ty`s
such as `{ kind := .uint .u32, layoutIdx := 0 }`), and `unresolvedLayoutIdx
layouts` for aggregate/sequence kinds so they never adopt `layouts.entries[0]`.
-/
@[reducible]
def synthKindLayoutIdx (layouts : LayoutTable) (kind : RigidTy) : Nat :=
  match isPrimitiveScalarKind kind with
  | true => 0
  | false => unresolvedLayoutIdx layouts

/--
`true` when every `RigidTy` in `ks` is structurally equal to `k0`.
-/
@[reducible]
def allSameRigidTy (k0 : RigidTy) : List RigidTy → Bool
  | .nil => true
  | k :: rest =>
    match rigidTyEq k0 k with
    | true => allSameRigidTy k0 rest
    | false => false

/--
`true` when tuple element kinds `ks` have compiler-independent field layout even
without a captured `TypeLayout` entry: empty `()`, single-field `(T,)` (cannot
be reordered), or homogeneous primitive scalar tuples `(T, T, ...)` (identical
size, alignment, and niche across all fields, with zero padding). Heterogeneous
multi-field tuples such as `(u8, u32)` or `(u8, u16, u8)` are reordered by
`rustc` (`repr(Rust)`), so their field offsets and padded size require a
captured `TypeLayout`.
-/
@[reducible]
def isLayoutFreeTupleKinds : List RigidTy → Bool
  | .nil => true
  | _ :: .nil => true
  | k0 :: k1 :: rest =>
    Bool.and (isPrimitiveScalarKind k0) (allSameRigidTy k0 (k1 :: rest))

/--
Exact byte width of a flat runtime scalar or thin pointer value (`.none` for
aggregates or unit).
-/
@[reducible]
def flatValueByteSize? : Value → Option Nat
  | .scalar sc => .some sc.sizeBytes
  | .ptr _ sz => .some sz
  | _ => .none

/--
`true` when every runtime value in `vs` is a flat scalar or thin pointer of byte
width `sz`.
-/
@[reducible]
def allFlatValuesOfSize : Nat → List Value → Bool
  | _, .nil => true
  | sz, v :: rest =>
    match flatValueByteSize? v with
    | .some vSz =>
      match Nat.beq sz vSz with
      | true => allFlatValuesOfSize sz rest
      | false => false
    | .none => false

/--
`true` when an untyped runtime field/element list consists exclusively of flat
scalars or thin pointers of a single uniform positive byte width (or at most one
flat field), refusing heterogeneous or nested-aggregate runtime lists whose
`repr(Rust)` layout cannot be inferred without static `TypeLayout` metadata.
-/
@[reducible]
def isHomogeneousUntypedFields : List Value → Bool
  | .nil => true
  | v :: .nil =>
    match flatValueByteSize? v with
    | .some _ => true
    | .none => false
  | v0 :: v1 :: rest =>
    match flatValueByteSize? v0 with
    | .some sz =>
      match Nat.ble 1 sz with
      | true => allFlatValuesOfSize sz (v1 :: rest)
      | false => false
    | .none => false

/--
`true` when `l` is structurally plausible as the `TypeLayout` of an `.adt` or
`.closure` (rejecting `.array` layouts and non-ZST single-variant `.primitive`
entries such as `u8` at `layouts.entries[0]`).
-/
@[reducible]
def layoutValidForAdt (l : TypeLayout) : Bool :=
  match l.fields, l.variants with
  | .array _ _, _ => false
  | .primitive, .single _ => Nat.beq l.size.bytes 0
  | _, _ => true

/--
`true` when `idx` is either `0` (the default index assigned to `Ty`s synthesized
by `pointeeTyOf` / `elemTyOf`) or an out-of-range index in `layouts` (such as
`unresolvedLayoutIdx layouts`).
-/
@[reducible]
def isUnresolvedLayoutIdx (layouts : LayoutTable) (idx : Nat) : Bool :=
  match Nat.beq idx 0 with
  | true => true
  | false =>
    match LayoutTable.lookup layouts idx with
    | .some _ => false
    | .none => true

/--
Search `localDecls` for an array or slice declaration whose element kind
structurally matches `kind` and whose `TypeLayout` in `layouts` records an
element layout index `flIdx :: _`, returning `{ kind := kind, layoutIdx := flIdx }`.
-/
@[reducible]
def findContainerElemTyWithKind?
    (layouts : LayoutTable) :
    List LocalDecl → RigidTy → Option Ty
  | .nil, _ => .none
  | decl :: rest, kind =>
    let elemKindOpt : Option RigidTy :=
      match decl.ty.kind with
      | .array ek _ => .some ek
      | .slice ek => .some ek
      | _ => .none
    match elemKindOpt with
    | .some ek =>
      match rigidTyEq ek kind with
      | false => findContainerElemTyWithKind? layouts rest kind
      | true =>
        match LayoutTable.lookup layouts decl.ty.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          .some { kind := kind, layoutIdx := flIdx }
        | _ => findContainerElemTyWithKind? layouts rest kind
    | .none => findContainerElemTyWithKind? layouts rest kind

/--
Look up `kind` in `localDecls` first by exact `LocalDecl` match
(`findDeclTyWithKind?`), then by array/slice container `fieldLayouts`
(`findContainerElemTyWithKind?`).
-/
@[reducible]
def findDeclOrContainerElemTyWithKind?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (kind : RigidTy) :
    Option Ty :=
  match findDeclTyWithKind? localDecls kind with
  | .some declTy => .some declTy
  | .none => findContainerElemTyWithKind? layouts localDecls kind

/--
Resolve a `Ty` whose `layoutIdx` may be unresolved (`isUnresolvedLayoutIdx
layouts ty.layoutIdx`) against `localDecls` and `layouts`:
- If `ty.layoutIdx` is a valid non-zero index in `layouts`, returns `ty`.
- Otherwise, looks up `ty.kind` via `findDeclOrContainerElemTyWithKind? localDecls layouts`.
- If `ty.layoutIdx == 0` and no declaration in a non-empty `localDecls` matches a
  non-primitive aggregate/sequence `ty.kind`, replaces the synthetic `0` with
  `unresolvedLayoutIdx layouts` so `ty` never accidentally adopts `layouts.entries[0]`.
-/
@[reducible]
def resolveTyWithLocalDecls
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Ty :=
  match isUnresolvedLayoutIdx layouts ty.layoutIdx with
  | false => ty
  | true =>
    match findDeclOrContainerElemTyWithKind? localDecls layouts ty.kind with
    | .some declTy => declTy
    | .none =>
      match Nat.beq ty.layoutIdx 0, localDecls with
      | true, _ :: _ =>
        match isPrimitiveScalarKind ty.kind with
        | true => ty
        | false => { ty with layoutIdx := unresolvedLayoutIdx layouts }
      | _, _ => ty

/--
Walk `proj` from `baseTy` like `resolveProjectedTy`, but resolve `.deref` and
`.index`/`.constantIndex` inner types through container `fieldLayouts` and
`findDeclOrContainerElemTyWithKind?`, assigning `unresolvedLayoutIdx layouts`
instead of `0` when no compiler layout is in scope.
-/
@[reducible]
def resolveProjectedTyResolved
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (baseTy : Ty) :
    List ProjectionElem → Option Ty
  | .nil => .some baseTy
  | .field fieldIdx fieldTy :: rest =>
    let nextTy : Ty :=
      match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
      | false => fieldTy
      | true =>
        match LayoutTable.lookup layouts baseTy.layoutIdx with
        | .some l =>
          match l.variants with
          | .single _ =>
            match get? l.fieldLayouts fieldIdx with
            | .some flIdx => { fieldTy with layoutIdx := flIdx }
            | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
          | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
        | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
    resolveProjectedTyResolved localDecls layouts nextTy rest
  | .opaqueCast castTy :: rest =>
    resolveProjectedTyResolved
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
  | .unwrapUnsafeBinder innerTy :: rest =>
    resolveProjectedTyResolved
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
  | .deref :: rest =>
    match pointeeTyOf baseTy with
    | .some { kind := inner, .. } =>
      let innerTy : Ty :=
        match findDeclOrContainerElemTyWithKind? localDecls layouts inner with
        | .some declTy => declTy
        | .none => { kind := inner, layoutIdx := synthKindLayoutIdx layouts inner }
      resolveProjectedTyResolved localDecls layouts innerTy rest
    | .none => .none
  | .index _ :: rest =>
    match elemTyOf baseTy with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts baseTy.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          match findDeclOrContainerElemTyWithKind? localDecls layouts ek with
          | .some declTy => declTy
          | .none => { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      resolveProjectedTyResolved localDecls layouts elemTy rest
    | .none => .none
  | .constantIndex _ _ _ :: rest =>
    match elemTyOf baseTy with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts baseTy.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          match findDeclOrContainerElemTyWithKind? localDecls layouts ek with
          | .some declTy => declTy
          | .none => { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      resolveProjectedTyResolved localDecls layouts elemTy rest
    | .none => .none
  | .subslice _ _ _ :: rest =>
    resolveProjectedTyResolved localDecls layouts baseTy rest
  | .downcast _ _ :: rest =>
    resolveProjectedTyResolved localDecls layouts baseTy rest

/--
Resolve the `Ty` of `p` from `localDecls` and `layouts` without conflating
synthesized pointee/element `layoutIdx` values with `layouts.entries[0]`.
-/
@[reducible]
def placeTyResolved
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place) :
    Option Ty :=
  match get? localDecls p.local_ with
  | .some decl => resolveProjectedTyResolved localDecls layouts decl.ty p.projection
  | .none => .none

/--
Resolve the `Ty` of `op` using `placeTyResolved` for place operands and `c.ty`
for constants.
-/
@[reducible]
def operandTyResolved
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Ty :=
  match op with
  | .copy p => placeTyResolved localDecls layouts p
  | .move p => placeTyResolved localDecls layouts p
  | .constant c => .some c.ty

/--
Search `localDecls` for an array or slice declaration whose element kind
structurally matches `kind` and whose `TypeLayout` in `layouts` has
`fields = .array stride _`, returning `(stride.bytes, layout.align.bytes)`.
-/
@[reducible]
def findArrayElemStrideAndAlign?
    (layouts : LayoutTable) :
    List LocalDecl → RigidTy → Option (Nat × Nat)
  | .nil, _ => .none
  | decl :: rest, kind =>
    let elemKindOpt : Option RigidTy :=
      match decl.ty.kind with
      | .array ek _ => .some ek
      | .slice ek => .some ek
      | _ => .none
    match elemKindOpt with
    | .some ek =>
      match rigidTyEq ek kind with
      | false => findArrayElemStrideAndAlign? layouts rest kind
      | true =>
        match LayoutTable.lookup layouts decl.ty.layoutIdx with
        | .some l =>
          match l.fields with
          | .array stride _ =>
            match Nat.ble 1 stride.bytes with
            | true =>
              let a :=
                match Nat.ble 1 l.align.bytes with
                | true => l.align.bytes
                | false => 1
              .some (stride.bytes, a)
            | false => findArrayElemStrideAndAlign? layouts rest kind
          | _ => findArrayElemStrideAndAlign? layouts rest kind
        | .none => findArrayElemStrideAndAlign? layouts rest kind
    | .none => findArrayElemStrideAndAlign? layouts rest kind

/--
Accumulate the `#[repr(C)]` `(sizeBytes, alignBytes)` across tuple element
kinds `ks` using recursive element analyzer `recKind`.
-/
@[reducible]
def foldTupleKindsCReprAux
    (recKind : RigidTy → Option (Nat × Nat))
    (runningOff maxAlign : Nat) :
    List RigidTy → Option (Nat × Nat)
  | .nil => .some (alignUpBytes runningOff maxAlign, maxAlign)
  | k :: rest =>
    match recKind k with
    | .none => .none
    | .some (fSz, fAlign) =>
      let alignedOff := alignUpBytes runningOff fAlign
      let nextMax :=
        match Nat.ble maxAlign fAlign with
        | true => fAlign
        | false => maxAlign
      foldTupleKindsCReprAux
        recKind
        (Nat.add alignedOff fSz)
        nextMax
        rest

/--
Compute `(sizeBytes, alignBytes)` of `ty` using `localDecls` and `layouts` with
structural recursion on `fuel`:
- Resolves `ty` via `resolveTyWithLocalDecls localDecls layouts ty`.
- Checks structural compatibility of `LayoutTable.lookup layouts rTy.layoutIdx`
  with `rTy.kind`.
- Falls back to structural tuple layout only for `isLayoutFreeTupleKinds`
  (`()`, `(T,)`, or homogeneous primitive `(T, T, ...)`), refusing unlaid-out
  heterogeneous tuples whose `repr(Rust)` layout depends on compiler reordering.
-/
@[reducible]
def tyByteSizeAndAlignAux
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Option (Nat × Nat)
  | .zero, _ => .none
  | .succ fuel, ty =>
    let rTy := resolveTyWithLocalDecls localDecls layouts ty
    match rTy.kind with
    | .tuple .nil | .fnDef _ _ | .never => .some (0, 1)
    | .array elemKind n =>
      let layoutSizeAlignOpt : Option (Nat × Nat) :=
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some l =>
          match l.fields with
          | .array stride count =>
            match Nat.beq count n with
            | false => .none
            | true =>
              let a :=
                match Nat.ble 1 l.align.bytes with
                | true => l.align.bytes
                | false => 1
              let sz :=
                match Nat.beq l.size.bytes 0, Nat.ble 1 stride.bytes with
                | true, true => Nat.mul n stride.bytes
                | _, _ => l.size.bytes
              .some (sz, a)
          | _ => .none
        | .none => .none
      match layoutSizeAlignOpt with
      | .some sa => .some sa
      | .none =>
        let elemTy : Ty :=
          match LayoutTable.lookup layouts rTy.layoutIdx with
          | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
            { kind := elemKind, layoutIdx := flIdx }
          | _ =>
            resolveTyWithLocalDecls
              localDecls
              layouts
              { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
        match tyByteSizeAndAlignAux localDecls layouts fuel elemTy with
        | .some (elemSz, elemAlign) => .some (Nat.mul n elemSz, elemAlign)
        | .none => .none
    | .tuple (k :: ks) =>
      let layoutSizeAlignOpt : Option (Nat × Nat) :=
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some l =>
          match layoutMatchesAggregateVariant l 0 (length (k :: ks)) with
          | false => .none
          | true =>
            let a :=
              match Nat.ble 1 l.align.bytes with
              | true => l.align.bytes
              | false => 1
            .some (l.size.bytes, a)
        | .none => .none
      match layoutSizeAlignOpt with
      | .some sa => .some sa
      | .none =>
        match isLayoutFreeTupleKinds (k :: ks) with
        | false => .none
        | true =>
          foldTupleKindsCReprAux
            (fun fk =>
              tyByteSizeAndAlignAux
                localDecls
                layouts
                fuel
                (resolveTyWithLocalDecls
                  localDecls
                  layouts
                  { kind := fk, layoutIdx := unresolvedLayoutIdx layouts }))
            0
            1
            (k :: ks)
    | .adt _ _ | .closure _ _ =>
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .some l =>
        match layoutValidForAdt l with
        | false => findArrayElemStrideAndAlign? layouts localDecls rTy.kind
        | true =>
          let a :=
            match Nat.ble 1 l.align.bytes with
            | true => l.align.bytes
            | false => 1
          .some (l.size.bytes, a)
      | .none => findArrayElemStrideAndAlign? layouts localDecls rTy.kind
    | _ =>
      match rigidTyByteSize layouts rTy with
      | .none => .none
      | .some sz =>
        let a :=
          match LayoutTable.lookup layouts rTy.layoutIdx with
          | .some l =>
            match l.fields, Nat.beq l.size.bytes sz with
            | .primitive, true =>
              match Nat.ble 1 l.align.bytes with
              | true => l.align.bytes
              | false => 1
            | _, _ =>
              let ptrBytes := layoutPointerBytes layouts
              match rTy.kind with
              | .int .isize | .uint .usize | .rawPtr _ _ | .ref _ _ | .fnPtr _ _ _ _ => ptrBytes
              | _ => scalarNaturalAlignBytes sz
          | .none =>
            let ptrBytes := layoutPointerBytes layouts
            match rTy.kind with
            | .int .isize | .uint .usize | .rawPtr _ _ | .ref _ _ | .fnPtr _ _ _ _ => ptrBytes
            | _ => scalarNaturalAlignBytes sz
        .some (sz, a)

/--
Determine the byte size of `ty` using `localDecls` and `layouts`
(`tyByteSizeAndAlignAux`).
-/
@[reducible]
def tyByteSize
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option Nat :=
  match tyByteSizeAndAlignAux localDecls layouts 8 ty with
  | .some (sz, _) => .some sz
  | .none => .none

/--
Resolve the `TypeLayout` of an aggregate `.aggregate aggVar fields` of static
type `curTy` in `layouts`: the entry at `curTy.layoutIdx` is used only when it
is shaped like `(aggVar, length fields)` (`layoutMatchesAggregateVariant`), and
`.none` is returned otherwise. In particular, a synthesized `layoutIdx == 0`
whose `entries[0]` does not match is *not* replaced by some other entry of the
same shape: two distinct types with equal field counts and sizes routinely have
different field offsets (`repr(Rust)` reordering), so a shape-matched guess
would resolve the wrong field.
-/
@[reducible]
def lookupAggregateLayout?
    (layouts : LayoutTable)
    (curTy : Ty)
    (aggVar : VariantIdx)
    (fields : List Value) :
    Option TypeLayout :=
  let directOpt := LayoutTable.lookup layouts curTy.layoutIdx
  match curTy.kind with
  | .tuple ks =>
    match directOpt with
    | .some l =>
      match
        Bool.and
          (layoutMatchesAggregateVariant l aggVar (length fields))
          (Nat.beq (length ks) (length fields))
      with
      | true => .some l
      | false => .none
    | .none => .none
  | .adt _ _ | .closure _ _ =>
    match directOpt with
    | .some l =>
      match l.fields with
      | .union _ => .some l
      | _ =>
        match layoutMatchesAggregateVariant l aggVar (length fields) with
        | true => .some l
        | false => .none
    | .none => .none
  | _ => directOpt

/--
Compute the byte offset of source field `fieldIdx` within an enclosing aggregate
of optional type `encTyOpt`, active downcast variant `activeVariant`, and
optional runtime value `encValOpt`.

Uses `TypeLayout` (`FieldsShape.arbitrary`, `FieldsShape.union`,
`FieldsShape.array`, or `VariantsShape.multiple`) from `layouts` when present,
falling back to structural tuple element widths or prior runtime field sizes.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1643-L1679>

> "/// Offsets for the first byte of each field,
> /// ordered to match the source definition order."
-/
@[reducible]
def aggregateFieldByteOffset?
    (layouts : LayoutTable)
    (encTyOpt : Option Ty)
    (activeVariant : Option VariantIdx)
    (encValOpt : Option Value)
    (fieldIdx : FieldIdx) :
    Option Nat :=
  let layoutOffOpt : Option Nat :=
    match encTyOpt with
    | .none => .none
    | .some encTy =>
      let layoutOpt : Option TypeLayout :=
        match encValOpt with
        | .some (.aggregate aggVar fields) =>
          lookupAggregateLayout? layouts encTy aggVar fields
        | _ => LayoutTable.lookup layouts encTy.layoutIdx
      match layoutOpt with
      | .none => .none
      | .some layout =>
        let shape :=
          match activeVariant, layout.variants with
          | .some vIdx, .multiple _ _ variants =>
            match get? variants vIdx with
            | .some vShape => vShape
            | .none => layout.fields
          | _, _ => layout.fields
        match shape with
        | .arbitrary offsets _ =>
          match get? offsets fieldIdx with
          | .some off => .some off.bytes
          | .none => .none
        | .union count =>
          match Nat.ble (.succ fieldIdx) count with
          | true => .some 0
          | false => .none
        | .array stride count =>
          match Nat.ble (.succ fieldIdx) count with
          | true => .some (Nat.mul fieldIdx stride.bytes)
          | false => .none
        | .primitive =>
          match encValOpt, Nat.beq fieldIdx 0 with
          | .none, true => .some 0
          | _, _ => .none
  match layoutOffOpt with
  | .some off => .some off
  | .none =>
    match encTyOpt with
    | .some { kind := .tuple ks, .. } =>
      match activeVariant, isLayoutFreeTupleKinds ks with
      | .none, true =>
        match Nat.ble (.succ fieldIdx) (length ks) with
        | true => sumPrefixTupleKindBytes fieldIdx ks
        | false => .none
      | _, _ => .none
    | .some { kind := .adt _ _, .. } | .some { kind := .closure _ _, .. } =>
      match activeVariant, encValOpt with
      | .none, .some (.aggregate 0 (_ :: .nil)) =>
        match Nat.beq fieldIdx 0 with
        | true => .some 0
        | false => .none
      | _, _ => .none
    | .some _ => .none
    | .none =>
      match activeVariant, encValOpt with
      | .none, .some (.aggregate 0 fields) =>
        match
          Bool.and
            (isHomogeneousUntypedFields fields)
            (Nat.ble (.succ fieldIdx) (length fields))
        with
        | true => sumPrefixFieldValueBytes fieldIdx fields
        | false => .none
      | _, _ => .none

/--
Accumulate the byte offset of projection chain `proj` relative to an enclosing
container with optional type `curTyOpt` and optional runtime value `curValOpt`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1226>

> "/// Reading from or writing to the projected place reads or writes the subset
> /// of bytes of the base place described by the layout of the base place's
> /// type (adjusted by active `Downcast` projection if any)."
-/
@[reducible]
def projectionChainByteOffset?
    (layouts : LayoutTable)
    (curTyOpt : Option Ty)
    (curValOpt : Option Value)
    (activeVariant : Option VariantIdx)
    (accOff : Nat)
    (localDecls : List LocalDecl := .nil) :
    List ProjectionElem → Option Nat
  | .nil => .some accOff
  | .opaqueCast castTy :: rest =>
    projectionChainByteOffset?
      layouts
      (.some (resolveTyWithLocalDecls localDecls layouts castTy))
      curValOpt
      .none
      accOff
      localDecls
      rest
  | .unwrapUnsafeBinder innerTy :: rest =>
    projectionChainByteOffset?
      layouts
      (.some (resolveTyWithLocalDecls localDecls layouts innerTy))
      curValOpt
      .none
      accOff
      localDecls
      rest
  | .downcast _ variantIdx :: rest =>
    projectionChainByteOffset?
      layouts
      curTyOpt
      curValOpt
      (.some variantIdx)
      accOff
      localDecls
      rest
  | .field fieldIdx fieldTy :: rest =>
    let resolvedCurTyOpt : Option Ty :=
      match curTyOpt with
      | .some rawCurTy => .some (resolveTyWithLocalDecls localDecls layouts rawCurTy)
      | .none => .none
    match
      aggregateFieldByteOffset?
        layouts
        resolvedCurTyOpt
        activeVariant
        curValOpt
        fieldIdx
    with
    | .none => .none
    | .some stepOff =>
      let nextValOpt : Option Value :=
        match curValOpt with
        | .some (.aggregate aggVar fields) =>
          let varOk :=
            match activeVariant with
            | .some expVar => Nat.beq aggVar expVar
            | .none => Nat.beq aggVar 0
          match varOk with
          | true => get? fields fieldIdx
          | false => .none
        | _ => .none
      let rawNextFieldTy : Ty :=
        match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx, activeVariant, resolvedCurTyOpt with
        | true, .none, .some curTy =>
          match LayoutTable.lookup layouts curTy.layoutIdx with
          | .some layout =>
            match get? layout.fieldLayouts fieldIdx with
            | .some flIdx => { fieldTy with layoutIdx := flIdx }
            | .none => fieldTy
          | .none => fieldTy
        | _, _, _ => fieldTy
      let nextFieldTy := resolveTyWithLocalDecls localDecls layouts rawNextFieldTy
      projectionChainByteOffset?
        layouts
        (.some nextFieldTy)
        nextValOpt
        .none
        (Nat.add accOff stepOff)
        localDecls
        rest
  | .constantIndex elemIdx minLen false :: rest =>
    let resolvedCurTyOpt : Option Ty :=
      match curTyOpt with
      | .some rawCurTy => .some (resolveTyWithLocalDecls localDecls layouts rawCurTy)
      | .none => .none
    let nextElemTyOpt : Option Ty :=
      match resolvedCurTyOpt with
      | .some curTy =>
        let elemKindOpt : Option RigidTy :=
          match curTy.kind with
          | .array ek _ => .some ek
          | .slice ek => .some ek
          | _ => .none
        match elemKindOpt with
        | .none => .none
        | .some ek =>
          let flIdxOpt : Option Nat :=
            match LayoutTable.lookup layouts curTy.layoutIdx with
            | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } => .some flIdx
            | _ => .none
          match flIdxOpt with
          | .some flIdx => .some { kind := ek, layoutIdx := flIdx }
          | .none =>
            .some
              (resolveTyWithLocalDecls
                localDecls
                layouts
                { kind := ek, layoutIdx := unresolvedLayoutIdx layouts })
      | .none => .none
    let layoutStrideOpt : Option Nat :=
      match resolvedCurTyOpt with
      | .some curTy =>
        match LayoutTable.lookup layouts curTy.layoutIdx with
        | .some { fields := .array stride _, .. } =>
          match Nat.ble 1 stride.bytes with
          | true => .some stride.bytes
          | false => .none
        | _ => .none
      | .none => .none
    match curValOpt with
    | .some (.aggregate 0 elems) =>
      match
        Bool.and
          (Nat.ble minLen (length elems))
          (Nat.ble (.succ elemIdx) (length elems))
      with
      | false => .none
      | true =>
        let elemSz :=
          match layoutStrideOpt with
          | .some s => s
          | .none =>
            match nextElemTyOpt with
            | .some elemTy =>
              match tyByteSize localDecls layouts elemTy with
              | .some sz => sz
              | .none => inferElemListByteStride elems
            | .none => inferElemListByteStride elems
        projectionChainByteOffset?
          layouts
          nextElemTyOpt
          (get? elems elemIdx)
          .none
          (Nat.add accOff (Nat.mul elemIdx elemSz))
          localDecls
          rest
    | .some _ => .none
    | .none =>
      let layoutElemStrideOpt : Option (Nat × Nat) :=
        match resolvedCurTyOpt with
        | .some curTy =>
          match LayoutTable.lookup layouts curTy.layoutIdx with
          | .some layout =>
            match layout.fields with
            | .array stride count => .some (stride.bytes, count)
            | _ => .none
          | .none => .none
        | .none => .none
      match layoutElemStrideOpt with
      | .some (elemSz, arrLen) =>
        match
          Bool.and
            (Nat.ble minLen arrLen)
            (Nat.ble (.succ elemIdx) arrLen)
        with
        | false => .none
        | true =>
          projectionChainByteOffset?
            layouts
            nextElemTyOpt
            .none
            .none
            (Nat.add accOff (Nat.mul elemIdx elemSz))
            localDecls
            rest
      | .none =>
        match resolvedCurTyOpt with
        | .some { kind := .array elemKind arrLen, .. } =>
          match
            Bool.and
              (Nat.ble minLen arrLen)
              (Nat.ble (.succ elemIdx) arrLen)
          with
          | false => .none
          | true =>
            let fallbackElemTy :=
              match nextElemTyOpt with
              | .some et => et
              | .none => { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
            match tyByteSize localDecls layouts fallbackElemTy with
            | .some elemSz =>
              projectionChainByteOffset?
                layouts
                nextElemTyOpt
                .none
                .none
                (Nat.add accOff (Nat.mul elemIdx elemSz))
                localDecls
                rest
            | .none => .none
        | _ => .none
  | _ :: _ => .none

/--
Check whether candidate aggregate field `idx` at byte span
`[fOff .. fOff + fSize)` matches a cross-field pointer access of
`expectedElemBytes` bytes at `relOff` (either directly at leaf `idx`, at an
intra-scalar byte offset `relOff - fOff` within a scalar leaf `idx`, or by
descending into a nested aggregate via `recurse`).
-/
def matchAggregateCandidateField?
    (recurse : Value → Option Ty → Nat → Option (List ProjectionElem × Nat))
    (idx : FieldIdx)
    (fVal : Value)
    (fOff fSize relOff expectedElemBytes : Nat)
    (leafIsAggregate : Bool)
    (leafProjTy : Ty)
    (nestedProjTy : Ty)
    (nestedTyOpt : Option Ty) :
    Option (List ProjectionElem × Nat) :=
  match
    Bool.and
      (Nat.beq relOff fOff)
      (Nat.beq fSize expectedElemBytes)
  with
  | true =>
    let fIsAgg :=
      match fVal with
      | .aggregate _ _ => true
      | _ => false
    match Bool.or (Bool.not fIsAgg) leafIsAggregate with
    | true => .some (.field idx leafProjTy :: .nil, 0)
    | false =>
      match fVal with
      | .aggregate _ _ =>
        match recurse fVal nestedTyOpt 0 with
        | .some (innerProj, resOff) => .some (.field idx nestedProjTy :: innerProj, resOff)
        | .none => .none
      | _ => .none
  | false =>
    match
      Bool.and
        (Nat.ble fOff relOff)
        (Nat.ble (Nat.add relOff expectedElemBytes) (Nat.add fOff fSize))
    with
    | false => .none
    | true =>
      match fVal with
      | .aggregate _ _ =>
        match recurse fVal nestedTyOpt (Nat.sub relOff fOff) with
        | .some (innerProj, resOff) => .some (.field idx nestedProjTy :: innerProj, resOff)
        | .none => .none
      | .scalar sc =>
        match leafIsAggregate with
        | true => .none
        | false =>
          let resOff := Nat.sub relOff fOff
          match Nat.ble (Nat.add resOff expectedElemBytes) sc.sizeBytes with
          | true => .some (.field idx nestedProjTy :: .nil, resOff)
          | false => .none
      | _ => .none

/--
Scan fields of a `FieldsShape.arbitrary` aggregate in source field order to
resolve a cross-field byte offset `relOff` of size `expectedElemBytes`.
-/
def scanArbitraryLayoutFields?
    (recurse : Value → Option Ty → Nat → Option (List ProjectionElem × Nat))
    (layouts : LayoutTable)
    (relOff expectedElemBytes : Nat)
    (leafIsAggregate : Bool)
    (defaultLeafTy : Ty) :
    Nat → List Size → List Nat → List RigidTy → List Value →
      Option (List ProjectionElem × Nat)
  | _, .nil, _, _, _ => .none
  | _, _, _, _, .nil => .none
  | idx, off :: offRest, fieldLayouts, tupleKinds, fVal :: fRest =>
    let flIdxOpt : Option Nat :=
      match fieldLayouts with
      | flIdx :: _ => .some flIdx
      | .nil => .none
    let nextFieldLayouts : List Nat :=
      match fieldLayouts with
      | _ :: flRest => flRest
      | .nil => .nil
    let fkOpt : Option RigidTy :=
      match tupleKinds with
      | fk :: _ => .some fk
      | .nil => .none
    let nextTupleKinds : List RigidTy :=
      match tupleKinds with
      | _ :: tkRest => tkRest
      | .nil => .nil
    let fSizeOpt : Option Nat :=
      match flIdxOpt with
      | .some flIdx =>
        match LayoutTable.lookup layouts flIdx with
        | .some fl => .some fl.size.bytes
        | .none =>
          match fkOpt with
          | .some fk =>
            match rigidTyKindByteSize fk with
            | .some sz => .some sz
            | .none => flatValueByteSize? fVal
          | .none =>
            match fVal with
            | .unit => .some 0
            | _ => flatValueByteSize? fVal
      | .none =>
        match fkOpt with
        | .some fk =>
          match rigidTyKindByteSize fk with
          | .some sz => .some sz
          | .none => flatValueByteSize? fVal
        | .none =>
          match fVal with
          | .unit => .some 0
          | _ => flatValueByteSize? fVal
    let nestedProjTy : Ty :=
      match flIdxOpt, fkOpt with
      | .some flIdx, .some fk => { kind := fk, layoutIdx := flIdx }
      | .some flIdx, .none => { kind := defaultLeafTy.kind, layoutIdx := flIdx }
      | .none, .some fk => { kind := fk, layoutIdx := synthKindLayoutIdx layouts fk }
      | .none, .none =>
        { kind := defaultLeafTy.kind, layoutIdx := synthKindLayoutIdx layouts defaultLeafTy.kind }
    let nestedTyOpt : Option Ty :=
      match flIdxOpt, fkOpt with
      | .some flIdx, .some fk => .some { kind := fk, layoutIdx := flIdx }
      | .some flIdx, .none =>
        .some { kind := defaultLeafTy.kind, layoutIdx := flIdx }
      | .none, .some fk =>
        .some { kind := fk, layoutIdx := synthKindLayoutIdx layouts fk }
      | .none, .none => .none
    match fSizeOpt with
    | .none => .none
    | .some fSize =>
      match
        matchAggregateCandidateField?
          recurse
          idx
          fVal
          off.bytes
          fSize
          relOff
          expectedElemBytes
          leafIsAggregate
          defaultLeafTy
          nestedProjTy
          nestedTyOpt
      with
      | .some resolved => .some resolved
      | .none =>
        scanArbitraryLayoutFields?
          recurse
          layouts
          relOff
          expectedElemBytes
          leafIsAggregate
          defaultLeafTy
          (.succ idx)
          offRest
          nextFieldLayouts
          nextTupleKinds
          fRest

/--
Scan fields of a runtime `.aggregate 0 fields` sequentially by accumulated field
byte offsets (`#[repr(C)]`-aligned when `useCAlign == true`, or unaligned tuple
structural widths when `useCAlign == false`) when no `FieldsShape.arbitrary`
layout table entry is available.
-/
def scanSequentialFields?
    (recurse : Value → Option Ty → Nat → Option (List ProjectionElem × Nat))
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (useCAlign : Bool)
    (relOff expectedElemBytes : Nat)
    (leafIsAggregate : Bool)
    (defaultLeafTy : Ty) :
    Nat → Nat → List RigidTy → List Value → Option (List ProjectionElem × Nat)
  | _, _, _, .nil => .none
  | idx, runningOff, tupleKinds, fVal :: fRest =>
    let fkOpt : Option RigidTy :=
      match tupleKinds with
      | fk :: _ => .some fk
      | .nil => .none
    let nextTupleKinds : List RigidTy :=
      match tupleKinds with
      | _ :: tkRest => tkRest
      | .nil => .nil
    let unresIdx := unresolvedLayoutIdx layouts
    let fSizeAndAlignOpt : Option (Nat × Nat) :=
      match fkOpt with
      | .some fk =>
        match
          tyByteSizeAndAlignAux
            localDecls
            layouts
            4
            { kind := fk, layoutIdx := unresIdx }
        with
        | .some (sz, a) =>
          match useCAlign with
          | true => .some (sz, a)
          | false => .some (sz, 1)
        | .none => .none
      | .none =>
        match fVal with
        | .unit => .some (0, 1)
        | _ =>
          match flatValueByteSize? fVal with
          | .some sz => .some (sz, scalarNaturalAlignBytes sz)
          | .none => .none
    let nestedProjTy : Ty :=
      match fkOpt with
      | .some fk =>
        resolveTyWithLocalDecls localDecls layouts { kind := fk, layoutIdx := synthKindLayoutIdx layouts fk }
      | .none => defaultLeafTy
    let nestedTyOpt : Option Ty :=
      match fkOpt with
      | .some fk =>
        .some (resolveTyWithLocalDecls localDecls layouts { kind := fk, layoutIdx := synthKindLayoutIdx layouts fk })
      | .none => .none
    match fSizeAndAlignOpt with
    | .none => .none
    | .some (fSize, fAlign) =>
      let fOff :=
        match useCAlign with
        | true => alignUpBytes runningOff fAlign
        | false => runningOff
      match
        matchAggregateCandidateField?
          recurse
          idx
          fVal
          fOff
          fSize
          relOff
          expectedElemBytes
          leafIsAggregate
          defaultLeafTy
          nestedProjTy
          nestedTyOpt
      with
      | .some resolved => .some resolved
      | .none =>
        scanSequentialFields?
          recurse
          localDecls
          layouts
          useCAlign
          relOff
          expectedElemBytes
          leafIsAggregate
          defaultLeafTy
          (.succ idx)
          (Nat.add fOff fSize)
          nextTupleKinds
          fRest

/--
Single fuel step of `resolveAggregateAtByteOffset?`, parameterized by nested
aggregate resolver `recurse`.
-/
def resolveAggregateAtByteOffsetStep
    (recurse : Value → Option Ty → Nat → Option (List ProjectionElem × Nat))
    (layouts : LayoutTable)
    (curVal : Value)
    (curTyOpt : Option Ty)
    (relOff expectedElemBytes : Nat)
    (leafIsAggregate : Bool)
    (defaultLeafTy : Ty)
    (forceSeqRoot : Bool)
    (localDecls : List LocalDecl := .nil) :
    Option (List ProjectionElem × Nat) :=
  match curVal with
  | .aggregate aggVar fields =>
    let resolvedCurTyOpt : Option Ty :=
      match curTyOpt with
      | .some rawCurTy => .some (resolveTyWithLocalDecls localDecls layouts rawCurTy)
      | .none => .none
    let (tupleKinds, useCAlign) : (List RigidTy × Bool) :=
      match resolvedCurTyOpt with
      | .some { kind := .tuple ks, .. } => (ks, true)
      | _ => (.nil, true)
    let isArrayContainer : Option (Option Ty × Nat) :=
      match Nat.beq aggVar 0, resolvedCurTyOpt with
      | false, _ => .none
      | true, .some curTy =>
        match curTy.kind with
        | .array elemKind _ | .slice elemKind =>
          let elemLayoutIdx : Nat :=
            match LayoutTable.lookup layouts curTy.layoutIdx with
            | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } => flIdx
            | _ =>
              match findDeclOrContainerElemTyWithKind? localDecls layouts elemKind with
              | .some declTy => declTy.layoutIdx
              | .none => unresolvedLayoutIdx layouts
          let elemTy : Ty := { kind := elemKind, layoutIdx := elemLayoutIdx }
          let elemSz :=
            match LayoutTable.lookup layouts curTy.layoutIdx with
            | .some { fields := .array stride _, .. } =>
              match Nat.ble 1 stride.bytes with
              | true => stride.bytes
              | false =>
                match tyByteSize localDecls layouts elemTy with
                | .some sz => sz
                | .none => 0
            | _ =>
              match tyByteSize localDecls layouts elemTy with
              | .some sz => sz
              | .none => 0
          .some (.some elemTy, elemSz)
        | .adt _ _ | .tuple _ | .closure _ _ => .none
        | _ =>
          match isUnresolvedLayoutIdx layouts curTy.layoutIdx, LayoutTable.lookup layouts curTy.layoutIdx with
          | false, .some { fields := .array stride _, .. } => .some (.none, stride.bytes)
          | _, _ => .none
      | true, .none =>
        match forceSeqRoot, isHomogeneousUntypedFields fields with
        | true, true =>
          let elemSz :=
            match fields with
            | f0 :: _ =>
              match flatValueByteSize? f0 with
              | .some sz => sz
              | .none => 0
            | .nil => 0
          .some (.none, elemSz)
        | _, _ => .none
    match isArrayContainer with
    | .some (elemTyOpt, elemSz) =>
      match Nat.beq elemSz 0 with
      | true => .none
      | false =>
        let (elemIdx, innerOff) := divModBytesAux relOff relOff elemSz 0
        match get? fields elemIdx with
        | .none => .none
        | .some elemVal =>
          match
            Bool.and
              (Nat.beq innerOff 0)
              (Nat.beq elemSz expectedElemBytes)
          with
          | true =>
            let elemIsAgg :=
              match elemVal with
              | .aggregate _ _ => true
              | _ => false
            match Bool.or (Bool.not elemIsAgg) leafIsAggregate with
            | true => .some (.constantIndex elemIdx 0 false :: .nil, 0)
            | false =>
              match recurse elemVal elemTyOpt 0 with
              | .some (innerProj, resOff) =>
                .some (.constantIndex elemIdx 0 false :: innerProj, resOff)
              | .none => .none
          | false =>
            match Nat.ble (Nat.add innerOff expectedElemBytes) elemSz with
            | false => .none
            | true =>
              match elemVal with
              | .aggregate _ _ =>
                match recurse elemVal elemTyOpt innerOff with
                | .some (innerProj, resOff) =>
                  .some (.constantIndex elemIdx 0 false :: innerProj, resOff)
                | .none => .none
              | .scalar sc =>
                match leafIsAggregate with
                | true => .none
                | false =>
                  match Nat.ble (Nat.add innerOff expectedElemBytes) sc.sizeBytes with
                  | true => .some (.constantIndex elemIdx 0 false :: .nil, innerOff)
                  | false => .none
              | _ => .none
    | .none =>
      match resolvedCurTyOpt with
      | .some curTy =>
        match lookupAggregateLayout? layouts curTy aggVar fields with
        | .some layout =>
          match layout.variants, layout.fields with
          | .multiple _ _ variants, _ =>
            match get? variants aggVar with
            | .some (.arbitrary offsets _) =>
              match Nat.beq (length offsets) (length fields) with
              | false => .none
              | true =>
                match
                  scanArbitraryLayoutFields?
                    recurse
                    layouts
                    relOff
                    expectedElemBytes
                    leafIsAggregate
                    defaultLeafTy
                    0
                    offsets
                    .nil
                    .nil
                    fields
                with
                | .some (innerProj, resOff) => .some (.downcast "" aggVar :: innerProj, resOff)
                | .none => .none
            | _ => .none
          | .single singleVar, .arbitrary offsets _ =>
            match Nat.beq aggVar singleVar with
            | false => .none
            | true =>
              match Nat.beq (length offsets) (length fields) with
              | true =>
                scanArbitraryLayoutFields?
                  recurse
                  layouts
                  relOff
                  expectedElemBytes
                  leafIsAggregate
                  defaultLeafTy
                  0
                  offsets
                  layout.fieldLayouts
                  tupleKinds
                  fields
              | false => .none
          | _, .union _ => .none
          | .single singleVar, _ =>
            match Nat.beq aggVar singleVar, isLayoutFreeTupleKinds tupleKinds with
            | true, true =>
              match curTy.kind with
              | .tuple _ =>
                scanSequentialFields?
                  recurse
                  localDecls
                  layouts
                  useCAlign
                  relOff
                  expectedElemBytes
                  leafIsAggregate
                  defaultLeafTy
                  0
                  0
                  tupleKinds
                  fields
              | _ => .none
            | _, _ => .none
          | .empty, _ => .none
        | .none =>
          let allowSeqWithoutLayout : Bool :=
            match Nat.beq aggVar 0 with
            | false => false
            | true =>
              match curTy.kind with
              | .tuple ks => isLayoutFreeTupleKinds ks
              | .adt _ _ | .closure _ _ => Nat.beq (length fields) 1
              | _ => false
          match allowSeqWithoutLayout with
          | false => .none
          | true =>
            scanSequentialFields?
              recurse
              localDecls
              layouts
              useCAlign
              relOff
              expectedElemBytes
              leafIsAggregate
              defaultLeafTy
              0
              0
              tupleKinds
              fields
      | .none =>
        match Bool.and (Nat.beq aggVar 0) (isHomogeneousUntypedFields fields) with
        | false => .none
        | true =>
          scanSequentialFields?
            recurse
            localDecls
            layouts
            true
            relOff
            expectedElemBytes
            leafIsAggregate
            defaultLeafTy
            0
            0
            .nil
            fields
  | _ => .none

/--
Resolve byte offset `relOff` of access size `expectedElemBytes` within aggregate
`curVal`, descending into nested struct, tuple, enum-variant, or array fields up
to `fuel` levels using structural recursion on `fuel`, and returning the
resolved relative projection path together with any intra-scalar residual byte
offset `residualBytes`.
-/
def resolveAggregateAtByteOffset?
    (fuel : Nat)
    (layouts : LayoutTable)
    (curVal : Value)
    (curTyOpt : Option Ty)
    (relOff expectedElemBytes : Nat)
    (leafIsAggregate : Bool)
    (defaultLeafTy : Ty)
    (forceSeqRoot : Bool := false)
    (localDecls : List LocalDecl := .nil) :
    Option (List ProjectionElem × Nat) :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    let recurse (v : Value) (tyOpt : Option Ty) (innerOff : Nat) :
        Option (List ProjectionElem × Nat) :=
      resolveAggregateAtByteOffset?
        fuel'
        layouts
        v
        tyOpt
        innerOff
        expectedElemBytes
        leafIsAggregate
        defaultLeafTy
        false
        localDecls
    resolveAggregateAtByteOffsetStep
      recurse
      layouts
      curVal
      curTyOpt
      relOff
      expectedElemBytes
      leafIsAggregate
      defaultLeafTy
      forceSeqRoot
      localDecls

/--
Resolve the element byte stride of a sequence container at
`(targetLocal, containerProj)` whose runtime elements are `elems`.
-/
@[reducible]
def resolveSeqContainerElemByteStride
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (targetLocal : Local)
    (containerProj : List ProjectionElem)
    (elems : List Value) :
    Nat :=
  let containerTyOpt :=
    placeTyResolved localDecls layouts { local_ := targetLocal, projection := containerProj }
  match containerTyOpt with
  | .some cTy =>
    let resolvedCTy := resolveTyWithLocalDecls localDecls layouts cTy
    match LayoutTable.lookup layouts resolvedCTy.layoutIdx with
    | .some { fields := .array stride _, .. } =>
      match Nat.ble 1 stride.bytes with
      | true => stride.bytes
      | false => 0
    | _ =>
      match resolvedCTy.kind with
      | .array ek _ | .slice ek =>
        match
          tyByteSize
            localDecls
            layouts
            { kind := ek, layoutIdx := unresolvedLayoutIdx layouts }
        with
        | .some s => s
        | .none => 0
      | _ => 0
  | .none =>
    match isHomogeneousUntypedFields elems, elems with
    | true, e0 :: _ =>
      match flatValueByteSize? e0 with
      | .some sz => sz
      | .none => 0
    | _, _ => 0

/--
Resolve the element `Ty` of a sequence container at `(targetLocal,
containerProj)`: the element layout index recorded by the container's own
`TypeLayout` (`fieldLayouts`), else a structurally equal `LocalDecl` or array
container layout (`findDeclOrContainerElemTyWithKind?`), else the bare element
kind with the out-of-range `unresolvedLayoutIdx`. Untyped containers yield
`.none`. The runtime elements and stride are not consulted: no layout is ever
guessed from the shape of the values.
-/
@[reducible]
def resolveSeqContainerElemTyOpt
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (targetLocal : Local)
    (containerProj : List ProjectionElem)
    (_elems : List Value)
    (_elemSz : Nat) :
    Option Ty :=
  let containerTyOpt :=
    placeTyResolved localDecls layouts { local_ := targetLocal, projection := containerProj }
  let elemKindOpt : Option RigidTy :=
    match containerTyOpt with
    | .some { kind := .array ek _, .. } => .some ek
    | .some { kind := .slice ek, .. } => .some ek
    | _ => .none
  let fromFieldLayoutsOpt : Option Nat :=
    match containerTyOpt with
    | .some cTy =>
      let resolvedCTy := resolveTyWithLocalDecls localDecls layouts cTy
      match LayoutTable.lookup layouts resolvedCTy.layoutIdx with
      | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } => .some flIdx
      | _ => .none
    | .none => .none
  match elemKindOpt with
  | .some ek =>
    match fromFieldLayoutsOpt with
    | .some flIdx => .some { kind := ek, layoutIdx := flIdx }
    | .none =>
      match findDeclOrContainerElemTyWithKind? localDecls layouts ek with
      | .some declTy => .some declTy
      | .none => .some { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
  | .none => .none

/--
Resolve a non-zero intra-allocation byte offset `offsetBytes` from a field-based
`BorrowEntry` projection `normTargetProj` ending in `.field _ leafFieldTy` onto
the sibling or nested field at `startByteOff + offsetBytes` (plus any
intra-scalar residual byte offset `residualBytes`), returning `.none` when
`targetByteOff` is one-past-the-end, out-of-bounds, misaligned, or
size-mismatched.

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L380-L430>

> "/// * If the computed offset is non-zero, then `self` must be derived from a
> ///   pointer to some allocated object, and the entire memory range between
> ///   `self` and the result must be in bounds of that allocated object."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Evaluating a dereference expression (`*expr`) on a raw pointer that is
>   dangling or unaligned, even in place expression context (e.g.
>   `addr_of!(*expr)`)."
-/
def resolveStackThinPtrFieldOffsetProj?
    (indexLocals : List LocalSlot)
    (targetRootVal : Value)
    (targetLocal : Local)
    (windowTargetProj : List ProjectionElem)
    (leafFieldTy : Ty)
    (offsetBytes : Nat)
    (restProj : List ProjectionElem)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointeeTyOpt : Option Ty)
    (reqBytesOpt : Option Nat := .none) :
    Option (List ProjectionElem × Nat) :=
  let (encProj, rawRelProj) := splitAfterLastSeqProj windowTargetProj
  let relProj := normalizeSubsliceProjections rawRelProj
  match readProjectedValue indexLocals targetRootVal encProj with
  | .ok (.aggregate encVar encFields) =>
    let encVal := Value.aggregate encVar encFields
    let encTyOpt : Option Ty :=
      match
        placeTyResolved
          localDecls
          layouts
          { local_ := targetLocal, projection := encProj }
      with
      | .some rawEncTy => .some (resolveTyWithLocalDecls localDecls layouts rawEncTy)
      | .none => .none
    match
      projectionChainByteOffset? layouts encTyOpt (.some encVal) .none 0 localDecls relProj
    with
    | .none => .none
    | .some startByteOff =>
      let leafValOpt : Option Value :=
        match readProjectedValue indexLocals targetRootVal windowTargetProj with
        | .ok lv => .some lv
        | _ => .none
      let expectedElemBytesOpt : Option Nat :=
        match restProj, reqBytesOpt with
        | .nil, .some reqB => .some reqB
        | _, _ =>
          match pointeeTyOpt with
          | .some pt =>
            match tyByteSize localDecls layouts pt with
            | .some sz => .some sz
            | .none =>
              match tyByteSize localDecls layouts leafFieldTy with
              | .some sz => .some sz
              | .none =>
                match leafValOpt with
                | .some lv => flatValueByteSize? lv
                | .none => .none
          | .none =>
            match tyByteSize localDecls layouts leafFieldTy with
            | .some sz => .some sz
            | .none =>
              match leafValOpt with
              | .some lv => flatValueByteSize? lv
              | .none => .none
      match expectedElemBytesOpt with
      | .none => .none
      | .some expectedElemBytes =>
        match Nat.beq expectedElemBytes 0 with
        | true => .none
        | false =>
          let targetByteOff := Nat.add startByteOff offsetBytes
          let enclosingBytesOpt : Option Nat :=
            match splitLastSubslice? encProj with
            | .some (subInitProj, _, _, _) =>
              match Nat.beq encVar 0 with
              | false => .some 0
              | true =>
                let elemSz :=
                  resolveSeqContainerElemByteStride
                    localDecls
                    layouts
                    targetLocal
                    subInitProj
                    encFields
                .some (Nat.mul (length encFields) elemSz)
            | .none =>
              match encTyOpt with
              | .some encTy =>
                match lookupAggregateLayout? layouts encTy encVar encFields with
                | .some l => .some l.size.bytes
                | .none =>
                  match tyByteSize localDecls layouts encTy with
                  | .some sz => .some sz
                  | .none =>
                    match encVar, encFields with
                    | 0, onlyField :: .nil => flatValueByteSize? onlyField
                    | _, _ => .some 0
              | .none =>
                match Bool.and (Nat.beq encVar 0) (isHomogeneousUntypedFields encFields) with
                | true => inferValueCReprBytes encVal
                | false => .some 0
          let inBounds : Bool :=
            match enclosingBytesOpt with
            | .some encBytes =>
              Nat.ble (Nat.add targetByteOff expectedElemBytes) encBytes
            | .none => false
          match inBounds with
          | false => .none
          | true =>
            let defaultLeafTy : Ty :=
              match pointeeTyOpt with
              | .some pt => resolveTyWithLocalDecls localDecls layouts pt
              | .none => resolveTyWithLocalDecls localDecls layouts leafFieldTy
            let leafIsAggregate : Bool :=
              match defaultLeafTy.kind with
              | .adt _ _ => true
              | .tuple (_ :: _) => true
              | .array _ _ => true
              | .closure _ _ => true
              | _ =>
                match pointeeTyOpt, leafValOpt with
                | .none, .some (.aggregate _ _) => true
                | _, _ => false
            match
              resolveAggregateAtByteOffset?
                8
                layouts
                encVal
                encTyOpt
                targetByteOff
                expectedElemBytes
                leafIsAggregate
                defaultLeafTy
                (endsWithSubslice encProj)
                localDecls
            with
            | .none => .none
            | .some (resolvedRelProj, resOff) =>
              let validRes : Bool :=
                match restProj with
                | .nil => true
                | _ :: _ => Nat.beq resOff 0
              match validRes with
              | false => .none
              | true =>
                let combined :=
                  appendProjections
                    encProj
                    (appendProjections resolvedRelProj restProj)
                .some (normalizeSubsliceProjections combined, resOff)
  | _ => .none

/--
Resolve the effective target projection path `(fullProj, residualBytes)` on
`entry.targetLocal` when dereferencing, writing through, or reborrowing a
stack-backed thin pointer `Value.ptr ptrVal sz` (`BorrowEntry` `entry`) with
post-deref projection suffix `restProj`.

- `residualBytes` is `0` when the pointer lands on an exact element or field
  boundary, and `> 0` when `restProj = .nil` and the access lands at an
  intra-element or intra-field byte offset within a wider scalar leaf.
- Heterogeneous variant-0 aggregates (such as `(u8, u32)` tuples without an
  in-scope `LocalDecl`) are guarded by `isHomogeneousUntypedFields` so they are
  never misclassified as homogeneous `[T; N]` arrays.
-/
def resolveStackThinPtrTargetProjWithResidual?
    (indexLocals : List LocalSlot)
    (targetRootVal : Value)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (pointeeTyOpt : Option Ty := .none)
    (reqBytesOpt : Option Nat := .none) :
    Option (List ProjectionElem × Nat) :=
  let effReqBytesOpt : Option Nat :=
    match reqBytesOpt with
    | .some n => .some n
    | .none =>
      match pointeeTyOpt with
      | .some pt => tyByteSize localDecls layouts pt
      | .none => .none
  let leafIsAgg : Bool :=
    match pointeeTyOpt with
    | .some { kind := .adt _ _, .. } => true
    | .some { kind := .tuple (_ :: _), .. } => true
    | .some { kind := .array _ _, .. } => true
    | .some { kind := .closure _ _, .. } => true
    | _ => false
  let rawFullProj :=
    match entry.targetProjection with
    | .nil => restProj
    | ph :: pt => ph :: appendProjections pt restProj
  let normTargetProj :=
    normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
  let windowTargetProj :=
    normalizeAdjacentSubslices (stripTransparentProjections entry.targetProjection)
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
                placeTyResolved
                  localDecls
                  layouts
                  { local_ := entry.targetLocal, projection := normTargetProj }
              with
              | .some { kind := .array _ _, .. } => true
              | .some { kind := .slice _, .. } => true
              | _ =>
                match restProj, tyScalarBytes pointeeTy with
                | .nil, .some _ =>
                  match readProjectedValue indexLocals targetRootVal normTargetProj with
                  | .ok (.aggregate _ _) => true
                  | _ => false
                | _, _ => false
  match Nat.beq ptrVal.offsetBytes 0, isElemPtrAtZero with
  | true, false => .some (rawFullProj, 0)
  | _, _ =>
    match splitLastConstantIndex? windowTargetProj with
    | .some (initProj, baseIdx, minLen) =>
      match readProjectedValue indexLocals targetRootVal initProj with
      | .ok (.aggregate 0 elems) =>
        let elemSz :=
          resolveSeqContainerElemByteStride
            localDecls
            layouts
            entry.targetLocal
            initProj
            elems
        let elemTyOpt :=
          resolveSeqContainerElemTyOpt
            localDecls
            layouts
            entry.targetLocal
            initProj
            elems
            elemSz
        match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
        | .some elemDelta =>
          let idx := Nat.add baseIdx elemDelta
          match
            Bool.and
              (Nat.ble minLen (length elems))
              (Nat.ble (.succ idx) (length elems))
          with
          | false => .none
          | true =>
            match restProj, effReqBytesOpt, get? elems idx with
            | .nil, .some reqB, .some (.aggregate eVar eFields) =>
              match Bool.or (Bool.not leafIsAgg) (Bool.not (Nat.beq reqB elemSz)) with
              | false =>
                let elemProj := ProjectionElem.constantIndex idx 0 false :: .nil
                let combined :=
                  match initProj with
                  | .nil => elemProj
                  | ph :: pt => ph :: appendProjections pt elemProj
                .some (normalizeSubsliceProjections combined, 0)
              | true =>
                let defaultLeafTy : Ty :=
                  match pointeeTyOpt with
                  | .some pt => resolveTyWithLocalDecls localDecls layouts pt
                  | .none => { kind := uintRigidTyOfStride reqB, layoutIdx := unresolvedLayoutIdx layouts }
                match
                  resolveAggregateAtByteOffset?
                    8
                    layouts
                    (.aggregate eVar eFields)
                    elemTyOpt
                    0
                    reqB
                    leafIsAgg
                    defaultLeafTy
                    false
                    localDecls
                with
                | .some (innerProj, innerRes) =>
                  let elemProj := ProjectionElem.constantIndex idx 0 false :: innerProj
                  let combined :=
                    match initProj with
                    | .nil => elemProj
                    | ph :: pt => ph :: appendProjections pt elemProj
                  .some (normalizeSubsliceProjections combined, innerRes)
                | .none => .none
            | _, _, _ =>
              let elemProj := ProjectionElem.constantIndex idx 0 false :: restProj
              let combined :=
                match initProj with
                | .nil => elemProj
                | ph :: pt => ph :: appendProjections pt elemProj
              .some (normalizeSubsliceProjections combined, 0)
        | .none =>
          match restProj, Nat.ble 1 elemSz with
          | .nil, true =>
            let (elemDelta, remBytes) :=
              divModBytesAux ptrVal.offsetBytes ptrVal.offsetBytes elemSz 0
            let idx := Nat.add baseIdx elemDelta
            match
              Bool.and
                (Nat.ble minLen (length elems))
                (Nat.ble (.succ idx) (length elems))
            with
            | false => .none
            | true =>
              let reqB :=
                match effReqBytesOpt with
                | .some n => n
                | .none => 1
              match
                Bool.and
                  (Nat.ble 1 reqB)
                  (Nat.ble (Nat.add remBytes reqB) elemSz)
              with
              | false => .none
              | true =>
                match get? elems idx with
                | .some (.scalar sc) =>
                  match Nat.ble (Nat.add remBytes reqB) sc.sizeBytes with
                  | false => .none
                  | true =>
                    let elemProj := ProjectionElem.constantIndex idx 0 false :: .nil
                    let combined :=
                      match initProj with
                      | .nil => elemProj
                      | ph :: pt => ph :: appendProjections pt elemProj
                    .some (normalizeSubsliceProjections combined, remBytes)
                | .some (.aggregate eVar eFields) =>
                  let defaultLeafTy : Ty :=
                    match pointeeTyOpt with
                    | .some pt => resolveTyWithLocalDecls localDecls layouts pt
                    | .none => { kind := uintRigidTyOfStride reqB, layoutIdx := unresolvedLayoutIdx layouts }
                  match
                    resolveAggregateAtByteOffset?
                      8
                      layouts
                      (.aggregate eVar eFields)
                      elemTyOpt
                      remBytes
                      reqB
                      leafIsAgg
                      defaultLeafTy
                      false
                      localDecls
                  with
                  | .some (innerProj, innerRes) =>
                    let elemProj := ProjectionElem.constantIndex idx 0 false :: innerProj
                    let combined :=
                      match initProj with
                      | .nil => elemProj
                      | ph :: pt => ph :: appendProjections pt elemProj
                    .some (normalizeSubsliceProjections combined, innerRes)
                  | .none => .none
                | _ => .none
          | _, _ => .none
      | _ => .none
    | .none =>
      let resolveSeqAtNormTarget : Option (List ProjectionElem × Nat) :=
        match readProjectedValue indexLocals targetRootVal normTargetProj with
        | .ok (.aggregate 0 elems) =>
          let isSeqCandidate : Bool :=
            match endsWithSubslice normTargetProj with
            | true => true
            | false =>
              match
                placeTyResolved
                  localDecls
                  layouts
                  { local_ := entry.targetLocal, projection := normTargetProj }
              with
              | .some { kind := .array _ _, .. } => true
              | .some { kind := .slice _, .. } => true
              | .some { kind := .adt _ _, .. } => false
              | .some { kind := .tuple _, .. } => false
              | .some { kind := .closure _ _, .. } => false
              | _ => Bool.and (Nat.ble 1 (length elems)) (isHomogeneousUntypedFields elems)
          match isSeqCandidate with
          | false => .none
          | true =>
            let elemSz :=
              resolveSeqContainerElemByteStride
                localDecls
                layouts
                entry.targetLocal
                normTargetProj
                elems
            let elemTyOpt :=
              resolveSeqContainerElemTyOpt
                localDecls
                layouts
                entry.targetLocal
                normTargetProj
                elems
                elemSz
            match byteOffsetToElemIdx? ptrVal.offsetBytes elemSz with
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
                  .some (normalizeSubsliceProjections combined, 0)
              | _, _ =>
                match Nat.ble (.succ elemOffset) (length elems) with
                | false => .none
                | true =>
                  match restProj, effReqBytesOpt, get? elems elemOffset with
                  | .nil, .some reqB, .some (.aggregate eVar eFields) =>
                    match Bool.or (Bool.not leafIsAgg) (Bool.not (Nat.beq reqB elemSz)) with
                    | false =>
                      let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: .nil
                      let combined :=
                        match normTargetProj with
                        | .nil => elemProj
                        | ph :: pt => ph :: appendProjections pt elemProj
                      .some (normalizeSubsliceProjections combined, 0)
                    | true =>
                      let defaultLeafTy : Ty :=
                        match pointeeTyOpt with
                        | .some pt => resolveTyWithLocalDecls localDecls layouts pt
                        | .none => { kind := uintRigidTyOfStride reqB, layoutIdx := unresolvedLayoutIdx layouts }
                      match
                        resolveAggregateAtByteOffset?
                          8
                          layouts
                          (.aggregate eVar eFields)
                          elemTyOpt
                          0
                          reqB
                          leafIsAgg
                          defaultLeafTy
                          false
                          localDecls
                      with
                      | .some (innerProj, innerRes) =>
                        let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: innerProj
                        let combined :=
                          match normTargetProj with
                          | .nil => elemProj
                          | ph :: pt => ph :: appendProjections pt elemProj
                        .some (normalizeSubsliceProjections combined, innerRes)
                      | .none => .none
                  | _, _, _ =>
                    let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: restProj
                    let combined :=
                      match normTargetProj with
                      | .nil => elemProj
                      | ph :: pt => ph :: appendProjections pt elemProj
                    .some (normalizeSubsliceProjections combined, 0)
            | .none =>
              match restProj, Nat.ble 1 elemSz with
              | .nil, true =>
                let (elemOffset, remBytes) :=
                  divModBytesAux ptrVal.offsetBytes ptrVal.offsetBytes elemSz 0
                match Nat.ble (.succ elemOffset) (length elems) with
                | false => .none
                | true =>
                  let reqB :=
                    match effReqBytesOpt with
                    | .some n => n
                    | .none => 1
                  match
                    Bool.and
                      (Nat.ble 1 reqB)
                      (Nat.ble (Nat.add remBytes reqB) elemSz)
                  with
                  | false => .none
                  | true =>
                    match get? elems elemOffset with
                    | .some (.scalar sc) =>
                      match Nat.ble (Nat.add remBytes reqB) sc.sizeBytes with
                      | false => .none
                      | true =>
                        let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: .nil
                        let combined :=
                          match normTargetProj with
                          | .nil => elemProj
                          | ph :: pt => ph :: appendProjections pt elemProj
                        .some (normalizeSubsliceProjections combined, remBytes)
                    | .some (.aggregate eVar eFields) =>
                      let defaultLeafTy : Ty :=
                        match pointeeTyOpt with
                        | .some pt => resolveTyWithLocalDecls localDecls layouts pt
                        | .none => { kind := uintRigidTyOfStride reqB, layoutIdx := unresolvedLayoutIdx layouts }
                      match
                        resolveAggregateAtByteOffset?
                          8
                          layouts
                          (.aggregate eVar eFields)
                          elemTyOpt
                          remBytes
                          reqB
                          leafIsAgg
                          defaultLeafTy
                          false
                          localDecls
                      with
                      | .some (innerProj, innerRes) =>
                        let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: innerProj
                        let combined :=
                          match normTargetProj with
                          | .nil => elemProj
                          | ph :: pt => ph :: appendProjections pt elemProj
                        .some (normalizeSubsliceProjections combined, innerRes)
                      | .none => .none
                    | _ => .none
              | _, _ => .none
        | _ => .none
      match Nat.beq ptrVal.offsetBytes 0, splitLastField? normTargetProj with
      | false, .some (_, _, leafFieldTy) =>
        let leafIsSeqField : Bool :=
          match leafFieldTy.kind with
          | .array _ _ => true
          | .slice _ => true
          | _ => false
        match leafIsSeqField with
        | true =>
          let pointeeMatchesArray : Bool :=
            match pointeeTyOpt, leafFieldTy.kind with
            | .some { kind := .array pk pn, .. }, .array lk ln =>
              Bool.and
                (Nat.beq pn ln)
                (match rigidTyKindByteSize pk, rigidTyKindByteSize lk with
                 | .some psz, .some lsz => Nat.beq psz lsz
                 | _, _ => true)
            | _, _ => false
          match pointeeMatchesArray with
          | true =>
            resolveStackThinPtrFieldOffsetProj?
              indexLocals
              targetRootVal
              entry.targetLocal
              windowTargetProj
              leafFieldTy
              ptrVal.offsetBytes
              restProj
              localDecls
              layouts
              pointeeTyOpt
              reqBytesOpt
          | false =>
            match resolveSeqAtNormTarget with
            | .some resolved => .some resolved
            | .none =>
              resolveStackThinPtrFieldOffsetProj?
                indexLocals
                targetRootVal
                entry.targetLocal
                windowTargetProj
                leafFieldTy
                ptrVal.offsetBytes
                restProj
                localDecls
                layouts
                pointeeTyOpt
                reqBytesOpt
        | false =>
          resolveStackThinPtrFieldOffsetProj?
            indexLocals
            targetRootVal
            entry.targetLocal
            windowTargetProj
            leafFieldTy
            ptrVal.offsetBytes
            restProj
            localDecls
            layouts
            pointeeTyOpt
            reqBytesOpt
      | false, .none =>
        let fallbackLeafTyOpt : Option Ty :=
          match pointeeTyOpt with
          | .some pt => .some pt
          | .none =>
            match reqBytesOpt with
            | .some reqB =>
              .some { kind := uintRigidTyOfStride reqB, layoutIdx := unresolvedLayoutIdx layouts }
            | .none => .none
        match endsWithSubslice normTargetProj, fallbackLeafTyOpt with
        | false, .some pt =>
          let targetIsStructLike : Bool :=
            match
              placeTyResolved
                localDecls
                layouts
                { local_ := entry.targetLocal, projection := normTargetProj }
            with
            | .some { kind := .adt _ _, .. } => true
            | .some { kind := .tuple _, .. } => true
            | .some { kind := .closure _ _, .. } => true
            | _ => false
          match targetIsStructLike with
          | true =>
            resolveStackThinPtrFieldOffsetProj?
              indexLocals
              targetRootVal
              entry.targetLocal
              windowTargetProj
              pt
              ptrVal.offsetBytes
              restProj
              localDecls
              layouts
              pointeeTyOpt
              reqBytesOpt
          | false =>
            match resolveSeqAtNormTarget with
            | .some resolved => .some resolved
            | .none =>
              resolveStackThinPtrFieldOffsetProj?
                indexLocals
                targetRootVal
                entry.targetLocal
                windowTargetProj
                pt
                ptrVal.offsetBytes
                restProj
                localDecls
                layouts
                pointeeTyOpt
                reqBytesOpt
        | _, _ => resolveSeqAtNormTarget
      | true, _ =>
        match resolveSeqAtNormTarget with
        | .some resolved => .some resolved
        | .none =>
          match pointeeTyOpt with
          | .some pt =>
            resolveStackThinPtrFieldOffsetProj?
              indexLocals
              targetRootVal
              entry.targetLocal
              windowTargetProj
              pt
              ptrVal.offsetBytes
              restProj
              localDecls
              layouts
              pointeeTyOpt
              reqBytesOpt
          | .none => .none

/--
Resolve the effective target projection path on `entry.targetLocal` when
dereferencing, writing through, or reborrowing a stack-backed thin pointer
`Value.ptr ptrVal sz` (`BorrowEntry` `entry`) with post-deref projection suffix
`restProj` and zero intra-scalar residual offset (`residualBytes == 0`).
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
  match
    resolveStackThinPtrTargetProjWithResidual?
      indexLocals
      targetRootVal
      entry
      ptrVal
      restProj
      localDecls
      layouts
      pointeeTyOpt
      .none
  with
  | .some (fullProj, .zero) => .some fullProj
  | _ => .none

/--
Compute the ABI byte alignment of a `RigidTy` when statically known from its
type structure (`fuel`-bounded recursion for arrays, slices, and tuples).
Returns `.none` for ADTs or tuples/arrays containing ADTs whose alignment must
be looked up in `LayoutTable`.
-/
@[reducible]
def tyKindByteAlignAux (ptrBytes : Nat) : Nat → RigidTy → Option Nat
  | .zero, _ => .none
  | .succ _, .bool => .some 1
  | .succ _, .char => .some 4
  | .succ _, .int .isize => .some ptrBytes
  | .succ _, .uint .usize => .some ptrBytes
  | .succ _, .int k => intCastTargetBytes (.int k)
  | .succ _, .uint k => intCastTargetBytes (.uint k)
  | .succ _, .float .f16 => .some 2
  | .succ _, .float .f32 => .some 4
  | .succ _, .float .f64 => .some 8
  | .succ _, .float .f128 => .some 16
  | .succ _, .rawPtr _ _ => .some ptrBytes
  | .succ _, .ref _ _ => .some ptrBytes
  | .succ _, .fnPtr _ _ _ _ => .some ptrBytes
  | .succ _, .tuple .nil => .some 1
  | .succ _, .fnDef _ _ => .some 1
  | .succ _, .never => .some 1
  | .succ _, .str => .some 1
  | .succ fuel, .array elem _ => tyKindByteAlignAux ptrBytes fuel elem
  | .succ fuel, .slice elem => tyKindByteAlignAux ptrBytes fuel elem
  | .succ fuel, .tuple (k :: ks) =>
    match tyKindByteAlignAux ptrBytes fuel k, tyKindByteAlignAux ptrBytes fuel (.tuple ks) with
    | .some a1, .some a2 =>
      match Nat.ble a1 a2 with
      | true => .some a2
      | false => .some a1
    | _, _ => .none
  | .succ _, _ => .none

/--
Compute the ABI byte alignment of a `RigidTy` when structurally determined,
with pointer-width-sized kinds (`isize`, `usize`, thin `*T`/`&T`, `fn` pointers)
aligned to `layoutPointerBytes layouts`.
-/
@[reducible]
def tyKindByteAlign (layouts : LayoutTable) (kind : RigidTy) : Option Nat :=
  tyKindByteAlignAux (layoutPointerBytes layouts) 16 kind

/--
Resolve the required byte alignment of `ty`: the captured compiler layout
entry `LayoutTable.lookup layouts ty.layoutIdx` is authoritative when
`ty.layoutIdx ≠ 0` (index `0` doubles as the "unresolved" index of synthesized
`Ty`s); otherwise use the structural `tyKindByteAlign`, then the layout of a
`LocalDecl` of the same kind (`findDeclTyWithKind?`), defaulting to `1` when
unconstrained.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Dangling or unaligned pointers. Evaluating a dereference expression (`*expr`)
> on a raw pointer that is dangling or unaligned is undefined behavior, even in
> place expression context."
-/
@[reducible]
def foldTupleMaxAlignAux
    (recKind : RigidTy → Nat)
    (acc : Nat) :
    List RigidTy → Nat
  | .nil => acc
  | fk :: rest =>
    let fa := recKind fk
    let next :=
      match Nat.ble acc fa with
      | true => fa
      | false => acc
    foldTupleMaxAlignAux recKind next rest

@[reducible]
def tyByteAlignAux
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Nat
  | .zero, _ => 1
  | .succ fuel, ty =>
    let rTy := resolveTyWithLocalDecls localDecls layouts ty
    let directLayoutAlignOpt : Option Nat :=
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .none => .none
      | .some l =>
        let ok : Bool :=
          match rTy.kind with
          | .adt _ _ | .closure _ _ => layoutValidForAdt l
          | .tuple ks => layoutMatchesAggregateVariant l 0 (length ks)
          | .array _ n =>
            match l.fields with
            | .array _ count => Nat.beq count n
            | _ => false
          | _ =>
            match l.fields, rigidTyByteSize layouts rTy with
            | .primitive, .some sz =>
              Bool.and (Bool.not (isUnresolvedLayoutIdx layouts rTy.layoutIdx)) (Nat.beq l.size.bytes sz)
            | _, _ => false
        match ok with
        | false => .none
        | true =>
          match Nat.ble 1 l.align.bytes with
          | true => .some l.align.bytes
          | false => .some 1
    match directLayoutAlignOpt with
    | .some a => a
    | .none =>
      match tyKindByteAlign layouts rTy.kind with
      | .some a =>
        match Nat.ble 1 a with
        | true => a
        | false => 1
      | .none =>
        match findArrayElemStrideAndAlign? layouts localDecls rTy.kind with
        | .some (_, a) => a
        | .none =>
          match rTy.kind with
          | .array elem _ | .slice elem =>
            tyByteAlignAux
              localDecls
              layouts
              fuel
              { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
          | .tuple (k :: ks) =>
            foldTupleMaxAlignAux
              (fun fk =>
                tyByteAlignAux
                  localDecls
                  layouts
                  fuel
                  { kind := fk, layoutIdx := unresolvedLayoutIdx layouts })
              1
              (k :: ks)
          | _ => 1

@[reducible]
def tyByteAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Nat :=
  tyByteAlignAux localDecls layouts 8 ty

/--
Check whether byte offset `offsetBytes` satisfies the required alignment of
`tyOpt` (defaulting to `true` when `offsetBytes = 0` or `tyOpt = .none`).
-/
@[reducible]
def checkDerefAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (tyOpt : Option Ty)
    (offsetBytes : Nat) :
    Bool :=
  match Nat.beq offsetBytes 0 with
  | true => true
  | false =>
    match tyOpt with
    | .none => true
    | .some ty =>
      let align := tyByteAlign localDecls layouts ty
      match Nat.ble align 1 with
      | true => true
      | false =>
        let (_, rem) := divModBytesAux offsetBytes offsetBytes align 0
        Nat.beq rem 0

/--
Address-level alignment check for an access whose required alignment is that of
`tyOpt`, through a stack pointer `ptrVal` whose `BorrowEntry` `entry` targets the
place `(entry.targetLocal, entry.targetProjection)` described by `targetDecls`
(the active frame's `LocalDecl`s; `.nil` for caller-frame targets, whose
declarations are not in scope, skips the check).

`checkDerefAlign` only checks `ptrVal.offsetBytes`, which is relative to the
borrowed place. The accessed address is `base + placeOff + ptrVal.offsetBytes`,
where:
- `base` is the allocation address of `entry.targetLocal`, an arbitrary multiple
  of the local's alignment `localAlign`;
- `placeOff` is the byte offset of `entry.targetProjection` within the local
  (`projectionChainByteOffset?`).

The access is aligned in every execution iff `reqAlign ≤ localAlign` and
`(placeOff + ptrVal.offsetBytes) % reqAlign = 0` (alignments are powers of two).
So reading a `u32` through `buf.as_ptr() as *const u32` with `buf : [u8; 8]` is
undefined behavior even at offset `0`. When `placeOff` cannot be computed, only
the `reqAlign ≤ localAlign` part is checked.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."
-/
def checkTargetPlaceAlign
    (targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (tyOpt : Option Ty)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (targetRootValOpt : Option Value) :
    Bool :=
  match tyOpt, get? targetDecls entry.targetLocal with
  | .some ty, .some decl =>
    let reqAlign := tyByteAlign targetDecls layouts ty
    match Nat.ble reqAlign 1 with
    | true => true
    | false =>
      let localAlign := tyByteAlign targetDecls layouts decl.ty
      match Nat.ble reqAlign localAlign with
      | false => false
      | true =>
        match
          projectionChainByteOffset?
            layouts
            (.some decl.ty)
            targetRootValOpt
            .none
            0
            targetDecls
            entry.targetProjection
        with
        | .none => true
        | .some placeOff =>
          let absOff := Nat.add placeOff ptrVal.offsetBytes
          let (_, rem) := divModBytesAux absOff absOff reqAlign 0
          Nat.beq rem 0
  | _, _ => true

/--
Validate that runtime `Value` `v` satisfies the bit-level validity invariant of
static type `tyOpt`:
- `RigidTy.bool`: `v` is `.scalar sc` with `sc.sizeBytes == 1 ∧ sc.bits ≤ 1`.
- `RigidTy.char`: `v` is `.scalar sc` with `sc.sizeBytes == 4 ∧ isValidCharCode sc.bits`.
- All other types (or `tyOpt = .none`): returns `true`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Invalid values in primitive types, even in private fields and locals:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`."
-/
@[reducible]
def validateValueForTy?
    (_layouts : LayoutTable)
    (tyOpt : Option Ty)
    (v : Value) :
    Bool :=
  match tyOpt with
  | .some { kind := .bool, .. } =>
    match v with
    | .scalar sc => Bool.and (Nat.beq sc.sizeBytes 1) (Nat.ble sc.bits 1)
    | _ => false
  | .some { kind := .char, .. } =>
    match v with
    | .scalar sc => Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits)
    | _ => false
  | _ => true

/--
Extract a `targetBytes`-wide little-endian sub-scalar from `sc` at `byteOffset`
when `1 ≤ targetBytes` and `byteOffset + targetBytes ≤ sc.sizeBytes`.
-/
@[reducible]
def extractScalarSlice?
    (sc : ScalarInt)
    (byteOffset targetBytes : Nat) :
    Option ScalarInt :=
  match
    Bool.and
      (Nat.ble 1 targetBytes)
      (Nat.ble (Nat.add byteOffset targetBytes) sc.sizeBytes)
  with
  | false => .none
  | true =>
    match
      Bool.and
        (Nat.beq byteOffset 0)
        (Nat.beq targetBytes sc.sizeBytes)
    with
    | true => .some sc
    | false =>
      let shifted := shiftRightUnsignedBits sc.bits (Nat.mul 8 byteOffset)
      let sliced := wrapScalarBits shifted (scalarModulus targetBytes)
      .some ⟨sliced, targetBytes⟩

/--
Splice a narrower-width scalar `patchSc` into `oldSc` at `byteOffset` (in
little-endian byte order) when `1 ≤ patchSc.sizeBytes` and
`byteOffset + patchSc.sizeBytes ≤ oldSc.sizeBytes`.
-/
@[reducible]
def spliceScalarSlice?
    (oldSc : ScalarInt)
    (byteOffset : Nat)
    (patchSc : ScalarInt) :
    Option ScalarInt :=
  match
    Bool.and
      (Nat.ble 1 patchSc.sizeBytes)
      (Nat.ble (Nat.add byteOffset patchSc.sizeBytes) oldSc.sizeBytes)
  with
  | false => .none
  | true =>
    match
      Bool.and
        (Nat.beq byteOffset 0)
        (Nat.beq patchSc.sizeBytes oldSc.sizeBytes)
    with
    | true => .some patchSc
    | false =>
      let oldBytes := encodeLittleEndianBytes oldSc.bits oldSc.sizeBytes .none
      let patchBytes := encodeLittleEndianBytes patchSc.bits patchSc.sizeBytes .none
      match writeAbstractBytesAt oldBytes byteOffset patchBytes with
      | .none => .none
      | .some mergedBytes =>
        match decodeLittleEndianBytes mergedBytes with
        | .some (mergedBits, _) => .some ⟨mergedBits, oldSc.sizeBytes⟩
        | .none => .none

/--
`true` when every value in `fields` is a scalar or a thin pointer.
-/
@[reducible]
def allFlatScalarValues : List Value → Bool
  | .nil => true
  | .scalar _ :: rest => allFlatScalarValues rest
  | .ptr _ _ :: rest => allFlatScalarValues rest
  | _ :: _ => false

/--
Resolve a layout-faithful `Ty` for an aggregate `baseTy` with runtime variant
`varIdx` and field list `fields`:
- For arrays/slices of a primitive scalar kind, `baseTy` is layout-faithful directly.
- Otherwise, resolves `baseTy` via `resolveTyWithLocalDecls localDecls layouts`,
  requires a captured `TypeLayout` entry at the resolved `layoutIdx` that matches
  `(varIdx, length fields)` (`layoutMatchesAggregateVariant`), and requires all
  field values to be flat scalars (`allFlatScalarValues fields`).
-/
@[reducible]
def resolveFaithfulAggregateTy?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (baseTy : Ty)
    (varIdx : Nat)
    (fields : List Value) :
    Option Ty :=
  match baseTy.kind with
  | .array elemKind _ =>
    match isPrimitiveScalarKind elemKind with
    | true => .some baseTy
    | false => .none
  | .slice elemKind =>
    match isPrimitiveScalarKind elemKind with
    | true => .some baseTy
    | false => .none
  | _ =>
    match allFlatScalarValues fields with
    | false => .none
    | true =>
      let resolvedTy := resolveTyWithLocalDecls localDecls layouts baseTy
      match LayoutTable.lookup layouts resolvedTy.layoutIdx with
      | .some l =>
        match layoutMatchesAggregateVariant l varIdx (length fields) with
        | true => .some resolvedTy
        | false => .none
      | .none => .none

/--
`true` when `encodeValueToBytes layouts baseTy` of an aggregate with field
values `fields` reproduces the compiler's memory image.
-/
@[reducible]
def isLayoutFaithfulAggregate
    (layouts : LayoutTable)
    (baseTy : Ty)
    (fields : List Value)
    (localDecls : List LocalDecl := .nil)
    (varIdx : Nat := 0) :
    Bool :=
  match resolveFaithfulAggregateTy? localDecls layouts baseTy varIdx fields with
  | .some _ => true
  | .none => false

/--
Attempt to read a value of static type `accTy` at byte offset `offsetBytes`
within `baseVal` by encoding `baseVal` to `List AbstractByte`, slicing the
`size_of::<accTy>()` bytes starting at `offsetBytes`, and decoding at `accTy`.

Only byte images that are faithful to the compiler's memory layout are sliced:
- a scalar or thin-pointer `baseVal` is encoded as its exact little-endian
  bytes (`encodeUntypedValueToBytes`);
- an aggregate `baseVal` is encoded only when its static type `baseTyOpt` is
  known and resolves to a layout-faithful `Ty` (`resolveFaithfulAggregateTy?`),
  through `encodeValueToBytes` (field offsets from `layouts`, padding as `.uninit`,
  enum tags).

An aggregate of unknown static type returns `.none` instead of slicing the
declaration-order field concatenation produced by `encodeUntypedValueToBytes`,
which ignores padding, field reordering, and enum tags and would therefore
decode bytes that do not exist at `offsetBytes` in the real allocation.
-/
def decodeSubValueAtByteOffset?
    (layouts : LayoutTable)
    (baseTyOpt : Option Ty)
    (baseVal : Value)
    (offsetBytes : Nat)
    (accTy : Ty)
    (localDecls : List LocalDecl := .nil) :
    Option Value :=
  let rAccTy := resolveTyWithLocalDecls localDecls layouts accTy
  match tyByteSize localDecls layouts rAccTy with
  | .none => .none
  | .some reqBytes =>
    let encodedOpt : Option (List AbstractByte) :=
      match baseVal, baseTyOpt with
      | .scalar _, _ => encodeUntypedValueToBytes defaultCodecFuel baseVal
      | .ptr _ _, _ => encodeUntypedValueToBytes defaultCodecFuel baseVal
      | .aggregate varIdx fields, .some baseTy =>
        match resolveFaithfulAggregateTy? localDecls layouts baseTy varIdx fields with
        | .some resolvedTy => encodeValueToBytes defaultCodecFuel layouts resolvedTy baseVal
        | .none => .none
      | _, _ => .none
    match encodedOpt with
    | .none => .none
    | .some encodedBytes =>
      match sliceAbstractBytes encodedBytes offsetBytes reqBytes with
      | .none => .none
      | .some sliceBytes =>
        decodeValueFromBytes defaultCodecFuel layouts rAccTy sliceBytes

/--
Byte-offset decoding fallback for a typed thin-pointer dereference read `*ptr`
(empty post-deref projection `restProj`) whose byte offset does not land on an
element or field boundary of a compatible width: decode the accessed type
`accessedTyOpt` at `ptrVal.offsetBytes` within the borrow target value
(`entry.targetProjection` of `targetRootVal`, of static type `targetTyOpt`) via
`decodeSubValueAtByteOffset?`.
-/
def decodeAtBorrowTargetOffset?
    (locals : List LocalSlot)
    (targetRootVal : Value)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (layouts : LayoutTable)
    (accessedTyOpt : Option Ty)
    (targetTyOpt : Option Ty)
    (localDecls : List LocalDecl := .nil) :
    Option Value :=
  match restProj, accessedTyOpt with
  | .nil, .some accTy =>
    match readProjectedValue locals targetRootVal entry.targetProjection with
    | .ok baseVal =>
      decodeSubValueAtByteOffset? layouts targetTyOpt baseVal ptrVal.offsetBytes accTy localDecls
    | _ => .none
  | _, _ => .none

/--
Dereference and project a stack-backed thin pointer `ptrVal` (`BorrowEntry`
`entry`, referent root `targetRootVal`) with alignment, scalar width slicing,
out-of-bounds offset detection, and bit-validity checks.

- An access of static scalar type of width `W` (`accessedTyOpt`, empty
  post-deref projection) that stays within a scalar referent
  (`ptrVal.offsetBytes + W ≤ sc.sizeBytes`) extracts the little-endian `W`-byte
  slice `(sc.bits / 2^(8 * ptrVal.offsetBytes)) % 2^(8 * W)`.
- An access that leaves the scalar referent is resolved as element or field
  pointer arithmetic (`resolveStackThinPtrTargetProj?`, e.g. `p.add(1)` derived
  from `&arr[0]` or `&tuple.0`), and is `.ub` when no in-bounds sub-value of a
  compatible width exists at the offset (in particular whenever
  `ptrVal.offsetBytes + W > sc.sizeBytes` on a scalar referent that is not an
  array element or struct field with an in-bounds neighbor).
- `targetTyOpt` is the static type of the borrow target place
  (`entry.targetLocal` projected by `entry.targetProjection`) when it lives in
  the active frame (`.none` for caller-frame targets, whose `LocalDecl`s are not
  in scope); it is used only to encode an aggregate referent to bytes for
  byte-offset sub-value decoding (`decodeAtBorrowTargetOffset?`).
- A field projection through a pointer whose static pointee type is a scalar
  (`isSyntheticFieldOnScalarPointee`, the captured shape of transparent
  single-field wrappers such as `Unalign<u16>` typed as `&mut u16`) on a borrow
  of a whole local (`entry.targetProjection = []`) reads `restProj` directly,
  matching the legacy untyped convention that whole-local borrow targets ignore
  `ptrVal.offsetBytes` (`needsThinPtrElemResolution [] _ = false`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."
-/
def evalStackThinPtrTypedDerefRead
    (locals : List LocalSlot)
    (targetRootVal : Value)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointeeTyOpt : Option Ty)
    (accessedTyOpt : Option Ty)
    (targetTyOpt : Option Ty := .none)
    (targetDecls : List LocalDecl := localDecls) :
    PlaceReadResult :=
  let isSyntheticFieldOnScalarPointee : Bool :=
    match stripTransparentProjections restProj, pointeeTyOpt with
    | .field _ _ :: _, .some { kind := .bool, .. } => true
    | .field _ _ :: _, .some { kind := .char, .. } => true
    | .field _ _ :: _, .some { kind := .int _, .. } => true
    | .field _ _ :: _, .some { kind := .uint _, .. } => true
    | .field _ _ :: _, .some { kind := .float _, .. } => true
    | _, _ => false
  let effPointeeTyOpt : Option Ty :=
    match isSyntheticFieldOnScalarPointee, pointeeTyOpt with
    | true, _ => .none
    | false, .some pt => .some (resolveTyWithLocalDecls localDecls layouts pt)
    | false, .none => .none
  let resolvedAccTyOpt : Option Ty :=
    match accessedTyOpt with
    | .some accTy => .some (resolveTyWithLocalDecls localDecls layouts accTy)
    | .none => .none
  let alignTyOpt : Option Ty :=
    match effPointeeTyOpt, restProj with
    | .some pt, _ => .some pt
    | .none, .nil => resolvedAccTyOpt
    | .none, _ :: _ => .none
  match
    Bool.and
      (checkDerefAlign localDecls layouts alignTyOpt ptrVal.offsetBytes)
      (checkTargetPlaceAlign
        targetDecls
        layouts
        alignTyOpt
        entry
        ptrVal
        (.some targetRootVal))
  with
  | false => .ub
  | true =>
    let rawFullProj :=
      match entry.targetProjection with
      | .nil => restProj
      | ph :: pt => ph :: appendProjections pt restProj
    match isSyntheticFieldOnScalarPointee, entry.targetProjection with
    | true, .nil =>
      match readProjectedValue locals targetRootVal rawFullProj with
      | .ok fieldVal =>
        match validateValueForTy? layouts resolvedAccTyOpt fieldVal with
        | true => .ok fieldVal locals
        | false => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | _, _ =>
      let scalarSliceFastOpt : Option PlaceReadResult :=
        match restProj, resolvedAccTyOpt with
        | .nil, .some accTy =>
          match tyScalarBytes accTy with
          | .some reqBytes =>
            match readProjectedValue locals targetRootVal rawFullProj with
            | .ok (.scalar sc) =>
              match extractScalarSlice? sc ptrVal.offsetBytes reqBytes with
              | .some slicedSc =>
                let v := Value.scalar slicedSc
                match validateValueForTy? layouts resolvedAccTyOpt v with
                | true => .some (.ok v locals)
                | false => .some .ub
              | .none => .none
            | _ => .none
          | .none => .none
        | _, _ => .none
      match scalarSliceFastOpt with
      | .some res => res
      | .none =>
        let reqBytesOpt : Option Nat :=
          match restProj, resolvedAccTyOpt with
          | .nil, .some accTy => tyByteSize localDecls layouts accTy
          | _, _ => .none
        match
          resolveStackThinPtrTargetProjWithResidual?
            locals
            targetRootVal
            entry
            ptrVal
            restProj
            targetDecls
            layouts
            effPointeeTyOpt
            reqBytesOpt
        with
        | .none =>
          match
            decodeAtBorrowTargetOffset?
              locals
              targetRootVal
              entry
              ptrVal
              restProj
              layouts
              resolvedAccTyOpt
              targetTyOpt
              targetDecls
          with
          | .some decodedVal =>
            match validateValueForTy? layouts resolvedAccTyOpt decodedVal with
            | true => .ok decodedVal locals
            | false => .ub
          | .none => .ub
        | .some (fullProj, residualBytes) =>
          match readProjectedValue locals targetRootVal fullProj with
          | .ok fieldVal =>
            let finalValOpt : Option Value :=
              match resolvedAccTyOpt, fieldVal with
              | .some accTy, .scalar fSc =>
                match tyScalarBytes accTy with
                | .some reqBytes =>
                  match
                    Bool.and
                      (Nat.beq residualBytes 0)
                      (Nat.beq reqBytes fSc.sizeBytes)
                  with
                  | true => .some (.scalar fSc)
                  | false =>
                    match extractScalarSlice? fSc residualBytes reqBytes with
                    | .some slicedSc => .some (.scalar slicedSc)
                    | .none =>
                      decodeAtBorrowTargetOffset?
                        locals
                        targetRootVal
                        entry
                        ptrVal
                        restProj
                        layouts
                        resolvedAccTyOpt
                        targetTyOpt
                        targetDecls
                | .none =>
                  match Nat.beq residualBytes 0 with
                  | true => .some fieldVal
                  | false => .none
              | .some accTy, .aggregate _ _ =>
                match tyScalarBytes accTy with
                | .some _ =>
                  decodeAtBorrowTargetOffset?
                    locals
                    targetRootVal
                    entry
                    ptrVal
                    restProj
                    layouts
                    resolvedAccTyOpt
                    targetTyOpt
                    targetDecls
                | .none =>
                  match Nat.beq residualBytes 0 with
                  | true => .some fieldVal
                  | false => .none
              | _, _ =>
                match Nat.beq residualBytes 0 with
                | true => .some fieldVal
                | false => .none
            match finalValOpt with
            | .none => .ub
            | .some finalVal =>
              match validateValueForTy? layouts resolvedAccTyOpt finalVal with
              | true => .ok finalVal locals
              | false => .ub
          | .ub => .ub
          | .unsupported => .unsupported

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
    (pointeeTyOpt : Option Ty := .none)
    (localDecls : List LocalDecl := .nil)
    (accessedTyOpt : Option Ty := .none) :
    PlaceReadResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    Bool.and
      (Nat.beq ptrSz ptrBytes)
      (Bool.and
        (Nat.beq lenSc.sizeBytes ptrBytes)
        (Bool.and
          (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
          (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)))
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
                | .ok fieldVal =>
                  match validateValueForTy? layouts accessedTyOpt fieldVal with
                  | true => .ok fieldVal locals
                  | false => .ub
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
                | .ok fieldVal =>
                  match validateValueForTy? layouts accessedTyOpt fieldVal with
                  | true => .ok fieldVal locals
                  | false => .ub
                | .ub => .ub
                | .unsupported => .unsupported
            | _ => .ub
        | .none => .ub
    | .none =>
      match lookupGlobalAlloc globals ptrVal.allocId with
      | .some alloc =>
        let elemSz :=
          match
            tyByteSize
              localDecls
              layouts
              { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
          with
          | .some n => n
          | .none => 1
        let totalBytes := Nat.mul lenSc.bits elemSz
        match globalAllocSliceToAbstractBytes alloc ptrVal.offsetBytes totalBytes with
        | .some absBytes =>
          let sliceArrTy : Ty :=
            { kind := .array elemKind lenSc.bits, layoutIdx := unresolvedLayoutIdx layouts }
          match decodeValueFromBytes defaultCodecFuel layouts sliceArrTy absBytes with
          | .some decodedVal =>
            match readProjectedValue locals decodedVal restProj with
            | .ok fieldVal =>
              match validateValueForTy? layouts accessedTyOpt fieldVal with
              | true => .ok fieldVal locals
              | false => .ub
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
          | .ok fieldVal =>
            match validateValueForTy? layouts accessedTyOpt fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
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
    let accessedTyOpt := placeTyResolved localDecls layouts p
    let pointeeTyOpt :=
      placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
    match get? locals p.local_ with
    | .some (.init (.ptr ptrVal sz)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .disabled => .ub
        | _ =>
          match get? locals entry.targetLocal with
          | .some (.init targetRootVal) =>
            evalStackThinPtrTypedDerefRead
              locals
              targetRootVal
              entry
              ptrVal
              restProj
              localDecls
              layouts
              pointeeTyOpt
              accessedTyOpt
              (placeTyResolved
                localDecls
                layouts
                { local_ := entry.targetLocal, projection := entry.targetProjection })
          | .some _ => .ub
          | .none =>
            match get? callerLocals entry.targetLocal with
            | .some (.init targetRootVal) =>
              evalStackThinPtrTypedDerefRead
                locals
                targetRootVal
                entry
                ptrVal
                restProj
                localDecls
                layouts
                pointeeTyOpt
                accessedTyOpt
                .none
                .nil
            | _ => .ub
      | .none =>
        match
          Bool.and
            (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
            (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)
        with
        | false => .ub
        | true =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            match
              evalGlobalDerefRead
                locals
                alloc
                ptrVal.offsetBytes
                sz
                restProj
                layouts
                pointeeTyOpt
            with
            | .ok fieldVal locals' =>
              match validateValueForTy? layouts accessedTyOpt fieldVal with
              | true => .ok fieldVal locals'
              | false => .ub
            | .ub => .ub
            | .unsupported => .unsupported
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
        localDecls
        accessedTyOpt
    | _ => .ub
  | _ =>
    match get? locals p.local_ with
    | .some (.init rootVal) =>
      match readProjectedValue locals rootVal p.projection with
      | .ok fieldVal =>
        match validateValueForTy? layouts (placeTy localDecls layouts p) fieldVal with
        | true => .ok fieldVal locals
        | false => .ub
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
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil) :
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
      match localDecls with
      | .nil =>
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
      | _ :: _ =>
        let pointeeTyOpt :=
          placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
        let accessedTyOpt := placeTyResolved localDecls layouts p
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match get? locals entry.targetLocal with
              | .some (.init targetRootVal) =>
                evalStackThinPtrTypedDerefRead
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
                  localDecls
                  layouts
                  pointeeTyOpt
                  accessedTyOpt
                  (placeTyResolved
                    localDecls
                    layouts
                    { local_ := entry.targetLocal, projection := entry.targetProjection })
              | .some _ => .ub
              | .none =>
                match get? callerLocals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
                  with
                  | false =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | true =>
                    evalStackThinPtrTypedDerefRead
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                      localDecls
                      layouts
                      pointeeTyOpt
                      accessedTyOpt
                      .none
                      .nil
                | _ => .ub
          | .none =>
            match
              Bool.and
                (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
                (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)
            with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  evalGlobalDerefRead
                    locals
                    alloc
                    ptrVal.offsetBytes
                    sz
                    restProj
                    layouts
                    pointeeTyOpt
                with
                | .ok fieldVal locals' =>
                  match validateValueForTy? layouts accessedTyOpt fieldVal with
                  | true => .ok fieldVal locals'
                  | false => .ub
                | .ub => .ub
                | .unsupported => .unsupported
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
            localDecls
            accessedTyOpt
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
      match localDecls with
      | .nil =>
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
      | _ :: _ =>
        let pointeeTyOpt :=
          placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
        let accessedTyOpt := placeTyResolved localDecls layouts p
        match get? locals p.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupBorrow borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => .ub
            | _ =>
              match get? locals entry.targetLocal with
              | .some (.init targetRootVal) =>
                evalStackThinPtrTypedDerefRead
                  locals
                  targetRootVal
                  entry
                  ptrVal
                  restProj
                  localDecls
                  layouts
                  pointeeTyOpt
                  accessedTyOpt
                  (placeTyResolved
                    localDecls
                    layouts
                    { local_ := entry.targetLocal, projection := entry.targetProjection })
              | .some _ => .ub
              | .none =>
                match get? callerLocals entry.targetLocal with
                | .some (.init targetRootVal) =>
                  match
                    needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
                  with
                  | false =>
                    let fullProj :=
                      match entry.targetProjection with
                      | .nil => restProj
                      | ph :: pt => ph :: appendProjections pt restProj
                    match readProjectedValue locals targetRootVal fullProj with
                    | .ok fieldVal => .ok fieldVal locals
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | true =>
                    evalStackThinPtrTypedDerefRead
                      locals
                      targetRootVal
                      entry
                      ptrVal
                      restProj
                      localDecls
                      layouts
                      pointeeTyOpt
                      accessedTyOpt
                      .none
                      .nil
                | _ => .ub
          | .none =>
            match
              Bool.and
                (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
                (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)
            with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  evalGlobalDerefRead
                    locals
                    alloc
                    ptrVal.offsetBytes
                    sz
                    restProj
                    layouts
                    pointeeTyOpt
                with
                | .ok fieldVal locals' =>
                  match validateValueForTy? layouts accessedTyOpt fieldVal with
                  | true => .ok fieldVal locals'
                  | false => .ub
                | .ub => .ub
                | .unsupported => .unsupported
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
            localDecls
            accessedTyOpt
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
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil) :
    OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperand locals op borrows globals layouts callerLocals localDecls with
    | .ok v locals₁ =>
      match evalOperands locals₁ rest borrows globals layouts callerLocals localDecls with
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
Fit a scalar store `val` into the existing scalar sub-value `oldRead` at byte
offset `residualBytes` of the resolved destination: a store of the same width
at offset `0` replaces the scalar, a narrower store (or intra-scalar store) is
spliced into `oldSc` via `spliceScalarSlice? oldSc residualBytes wSc`, and a
wider or out-of-bounds store returns `.none`. Non-scalar stores require
`residualBytes == 0`.
-/
@[reducible]
def fitScalarStoreAtResolved?
    (oldRead : ProjReadResult)
    (residualBytes : Nat)
    (val : Value) :
    Option Value :=
  match val, oldRead with
  | .scalar wSc, .ok (.scalar oldSc) =>
    match spliceScalarSlice? oldSc residualBytes wSc with
    | .some mergedSc => .some (.scalar mergedSc)
    | .none => .none
  | .scalar _, .ok (.aggregate _ _) => .none
  | _, _ =>
    match Nat.beq residualBytes 0 with
    | true => .some val
    | false => .none

/--
Write `val` through a stack-backed thin pointer `ptrVal` (`BorrowEntry` `entry`,
into `targetLocals` at `entry.targetLocal`) with alignment, narrower-width
scalar splicing, out-of-bounds offset detection, and bit-validity checks.

- The stored value must be valid for the static type of the written place
  `accessedTyOpt` (`validateValueForTy?`). The static type of the borrow target
  is deliberately not consulted: storing the byte `2` through a type-punned
  `*mut u8` into the storage of a `bool` is not undefined behavior until that
  storage is read at type `bool` (where the read-side check fires), and the
  target of a caller-frame borrow is not described by the active frame's
  `localDecls`.
- A scalar store of width `W` that stays within a scalar referent
  (`ptrVal.offsetBytes + W ≤ oldSc.sizeBytes`) splices its `W` little-endian
  bytes into the referent at `ptrVal.offsetBytes`.
- Any other store resolves its destination with
  `resolveStackThinPtrTargetProjWithResidual?` (element, intra-element, field, or
  intra-field pointer arithmetic such as `*p.add(1) = v` derived from
  `&mut arr[0]`, and element-zero resolution of a `*mut T` cast from
  `&mut [T; N]`), using `targetDecls` (the `LocalDecl`s that describe
  `entry.targetLocal`: `localDecls` for active-frame targets, `.nil` for
  caller-frame targets). A scalar store into aresolved scalar sub-value is
  spliced at `residualBytes` (or `.ub` if wider/out-of-bounds) via
  `fitScalarStoreAtResolved?`.
- A field projection through a pointer whose static pointee type is a scalar
  (`isSyntheticFieldOnScalarPointee`) on a borrow of a whole local writes
  `restProj` directly, mirroring `evalStackThinPtrTypedDerefRead`.
- A store into an uninitialized target local initializes it only when it
  covers the whole local (`entry.targetProjection ++ restProj = []` at byte
  offset `0`); partial initialization is not representable and is `.ub`
  (consistent with `PlaceWriteResult.ub` for uninitialized aggregates).
-/
def writeStackThinPtrTypedDeref
    (indexLocals : List LocalSlot)
    (targetLocals : List LocalSlot)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (val : Value)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointeeTyOpt : Option Ty)
    (accessedTyOpt : Option Ty)
    (targetDecls : List LocalDecl := localDecls) :
    PlaceWriteResult :=
  let isSyntheticFieldOnScalarPointee : Bool :=
    match stripTransparentProjections restProj, pointeeTyOpt with
    | .field _ _ :: _, .some { kind := .bool, .. } => true
    | .field _ _ :: _, .some { kind := .char, .. } => true
    | .field _ _ :: _, .some { kind := .int _, .. } => true
    | .field _ _ :: _, .some { kind := .uint _, .. } => true
    | .field _ _ :: _, .some { kind := .float _, .. } => true
    | _, _ => false
  let effPointeeTyOpt : Option Ty :=
    match isSyntheticFieldOnScalarPointee, pointeeTyOpt with
    | true, _ => .none
    | false, .some pt => .some (resolveTyWithLocalDecls localDecls layouts pt)
    | false, .none => .none
  let resolvedAccTyOpt : Option Ty :=
    match accessedTyOpt with
    | .some accTy => .some (resolveTyWithLocalDecls localDecls layouts accTy)
    | .none => .none
  let alignTyOpt : Option Ty :=
    match effPointeeTyOpt, restProj with
    | .some pt, _ => .some pt
    | .none, .nil => resolvedAccTyOpt
    | .none, _ :: _ => .none
  let targetRootValOpt : Option Value :=
    match get? targetLocals entry.targetLocal with
    | .some (.init v) => .some v
    | _ => .none
  match
    Bool.and
      (checkDerefAlign localDecls layouts alignTyOpt ptrVal.offsetBytes)
      (Bool.and
        (checkTargetPlaceAlign
          targetDecls
          layouts
          alignTyOpt
          entry
          ptrVal
          targetRootValOpt)
        (validateValueForTy? layouts resolvedAccTyOpt val))
  with
  | false => .ub
  | true =>
    let rawFullProj :=
      match entry.targetProjection with
      | .nil => restProj
      | ph :: pt => ph :: appendProjections pt restProj
    let inScalarSpliceOpt : Option PlaceWriteResult :=
      match restProj, val, get? targetLocals entry.targetLocal with
      | .nil, .scalar wSc, .some (.init targetRootVal) =>
        match readProjectedValue indexLocals targetRootVal rawFullProj with
        | .ok (.scalar oldSc) =>
          match spliceScalarSlice? oldSc ptrVal.offsetBytes wSc with
          | .none => .none
          | .some mergedSc =>
            match rawFullProj with
            | .nil =>
              match set? targetLocals entry.targetLocal (.init (.scalar mergedSc)) with
              | .some targetLocals' => .some (.ok targetLocals')
              | .none => .some .ub
            | pHead :: pTail =>
              match
                writeProjectedValue
                  indexLocals
                  targetRootVal
                  (pHead :: pTail)
                  (.scalar mergedSc)
              with
              | .ok targetRootVal' =>
                match set? targetLocals entry.targetLocal (.init targetRootVal') with
                | .some targetLocals' => .some (.ok targetLocals')
                | .none => .some .ub
              | .ub => .some .ub
              | .unsupported => .some .unsupported
        | _ => .none
      | _, _, _ => .none
    match inScalarSpliceOpt with
    | .some res => res
    | .none =>
      match get? targetLocals entry.targetLocal with
      | .some (.init targetRootVal) =>
        let reqBytesOpt : Option Nat :=
          match restProj, val with
          | .nil, .scalar wSc => .some wSc.sizeBytes
          | .nil, _ =>
            match resolvedAccTyOpt with
            | .some accTy => tyByteSize localDecls layouts accTy
            | .none => .none
          | _ :: _, _ => .none
        let resolvedProjOpt : Option (List ProjectionElem × Nat) :=
          match isSyntheticFieldOnScalarPointee, entry.targetProjection with
          | true, .nil => .some (rawFullProj, 0)
          | _, _ =>
            resolveStackThinPtrTargetProjWithResidual?
              indexLocals
              targetRootVal
              entry
              ptrVal
              restProj
              targetDecls
              layouts
              effPointeeTyOpt
              reqBytesOpt
        match resolvedProjOpt with
        | .none => .ub
        | .some (.nil, residualBytes) =>
          match fitScalarStoreAtResolved? (.ok targetRootVal) residualBytes val with
          | .none => .ub
          | .some storeVal =>
            match set? targetLocals entry.targetLocal (.init storeVal) with
            | .some targetLocals' => .ok targetLocals'
            | .none => .ub
        | .some (pHead :: pTail, residualBytes) =>
          match
            fitScalarStoreAtResolved?
              (readProjectedValue indexLocals targetRootVal (pHead :: pTail))
              residualBytes
              val
          with
          | .none => .ub
          | .some storeVal =>
            match
              writeProjectedValue indexLocals targetRootVal (pHead :: pTail) storeVal
            with
            | .ok targetRootVal' =>
              match set? targetLocals entry.targetLocal (.init targetRootVal') with
              | .some targetLocals' => .ok targetLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
      | .some .uninit =>
        match rawFullProj, Nat.beq ptrVal.offsetBytes 0 with
        | .nil, true =>
          match set? targetLocals entry.targetLocal (.init val) with
          | .some targetLocals' => .ok targetLocals'
          | .none => .ub
        | _, _ => .ub
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
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    PlaceWriteResult :=
  match dst.projection with
  | .nil =>
    let tyValid :=
      match localDecls with
      | .nil => true
      | _ :: _ => validateValueForTy? layouts (placeTy localDecls layouts dst) val
    match tyValid with
    | false => .ub
    | true =>
      match get? locals dst.local_ with
      | .some .dead => .ub
      | .some _ =>
        match set? locals dst.local_ (.init val) with
        | .some locals' => .ok locals'
        | .none => .ub
      | .none => .ub
  | .deref :: restProj =>
    let pointeeTyOpt :=
      placeTyResolved localDecls layouts { local_ := dst.local_, projection := .deref :: .nil }
    let accessedTyOpt := placeTyResolved localDecls layouts dst
    match get? locals dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .frozen => .ub
        | .disabled => .ub
        | _ =>
          match localDecls with
          | .nil =>
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
          | _ :: _ =>
            writeStackThinPtrTypedDeref
              locals
              locals
              entry
              ptrVal
              restProj
              val
              localDecls
              layouts
              pointeeTyOpt
              accessedTyOpt
      | .none => .ub
    | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
      match
        Bool.and
          (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
          (Bool.and
            (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)
            (validateValueForTy? layouts accessedTyOpt val))
      with
      | false => .ub
      | true =>
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
    let tyValid :=
      match localDecls with
      | .nil => true
      | _ :: _ => validateValueForTy? layouts (placeTy localDecls layouts dst) val
    match tyValid with
    | false => .ub
    | true =>
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
    (activeProtectors : List Nat := .nil)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    PlaceWriteResult :=
  match activeProtectors with
  | .nil => writePlaceValue locals borrows dst val localDecls layouts
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
    | false => writePlaceValue locals borrows dst val localDecls layouts

/--
When `activeProtectors` is `.nil`, `evalPlaceWrite` reduces definitionally to
`writePlaceValue`.
-/
@[simp]
theorem evalPlaceWrite_nil_protectors
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    evalPlaceWrite locals borrows dst val .nil localDecls layouts =
      writePlaceValue locals borrows dst val localDecls layouts := rfl

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
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    PlaceWriteResult :=
  match dst.projection with
  | .deref :: restProj =>
    let pointeeTyOpt :=
      placeTyResolved localDecls layouts { local_ := dst.local_, projection := .deref :: .nil }
    let accessedTyOpt := placeTyResolved localDecls layouts dst
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
            match localDecls with
            | .nil =>
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
            | _ :: _ =>
              writeStackThinPtrTypedDeref
                frameLocals
                callerLocals
                entry
                ptrVal
                restProj
                val
                localDecls
                layouts
                pointeeTyOpt
                accessedTyOpt
                .nil
      | .none => .ub
    | .some (.init (.aggregate 0 (.ptr ptrVal ptrSz :: .scalar lenSc :: .nil))) =>
      match
        Bool.and
          (checkDerefAlign localDecls layouts pointeeTyOpt ptrVal.offsetBytes)
          (Bool.and
            (checkDerefAlign localDecls layouts accessedTyOpt ptrVal.offsetBytes)
            (validateValueForTy? layouts accessedTyOpt val))
      with
      | false => .ub
      | true =>
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
    (activeProtectors : List Nat := .nil)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    PlaceWriteResult :=
  match activeProtectors with
  | .nil =>
    writeCallerPlaceValue
      frameLocals
      callerLocals
      borrows
      dst
      val
      localDecls
      layouts
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
          | .none => false
        | _ => false
      | _ => false
    match conflict with
    | true => .ub
    | false =>
      writeCallerPlaceValue
        frameLocals
        callerLocals
        borrows
        dst
        val
        localDecls
        layouts

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
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
                      match tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts } with
                      | .some sz => sz
                      | .none => 1
                    | .rawPtr _ (.slice dstElem) =>
                      match tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts } with
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
                      tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts }
                    | .rawPtr _ (.slice dstElem) =>
                      tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts }
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
                    tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts }
                  | .rawPtr _ (.slice dstElem) =>
                    tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts }
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
                  match tyByteSize localDecls layouts { kind := dstElem, layoutIdx := unresolvedLayoutIdx layouts } with
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

When `parentEntry` projects a field at byte offset `0` whose value is not yet
initialized (such as an inactive array field of a `union` before
`copy_nonoverlapping`), pointer-to-pointer casts do not dereference memory and
preserve the thin pointer `ptrVal` unchanged so untyped byte operations can
inspect `parentEntry.targetProjection` while typed dereferences still fault with
`.ub`.

Reference (The Rust Reference, "Pointer-to-pointer cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast>

> "`*const T` / `*mut T` can be cast to `*const U` / `*mut U` with the
> following behavior:
> - If `T` and `U` are both sized, the pointer is returned unchanged.
> - If `T` is unsized and `U` is sized, the cast discards all metadata that
>   completes the wide pointer `T` and produces a thin pointer `U` consisting
>   of the data part of the unsized pointer."
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
        | .ub =>
          match normProj, Nat.beq ptrVal.offsetBytes 0 with
          | .field _ _ :: _, true => .ok (.ptr ptrVal 8) locals mem
          | _, _ => .ub
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
                    tyByteSize localDecls layouts { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
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
                  match tyByteSize localDecls layouts { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts } with
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
    | .some { kind := inner, .. } =>
      match rigidTyKindByteSize inner with
      | .some sz => .some sz
      | .none =>
        let resolvedPointeeTy : Ty :=
          match findDeclOrContainerElemTyWithKind? localDecls layouts inner with
          | .some declTy => declTy
          | .none => { kind := inner, layoutIdx := unresolvedLayoutIdx layouts }
        tyByteSize localDecls layouts resolvedPointeeTy
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
  | .aggregate 0 fields => inferValueCReprBytes (.aggregate 0 fields)
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

When `entry.targetProjection` ends in `.field`, computes the remaining byte
capacity `enclosingByteSize - fieldByteOffset` from that field's byte offset to
the end of the enclosing allocation (or enclosing subslice window), permitting
intra-allocation cross-field and one-past-the-end pointer arithmetic via
`BinOp.offset`.

Reference (`library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L380-L430>

> "/// * If the computed offset is non-zero, then `self` must be derived from a
> ///   pointer to some allocated object, and the entire memory range between
> ///   `self` and the result must be in bounds of that allocated object."
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
        let windowTargetProj :=
          normalizeAdjacentSubslices (stripTransparentProjections entry.targetProjection)
        match splitLastConstantIndex? windowTargetProj with
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
                let elemSz :=
                  resolveSeqContainerElemByteStride
                    localDecls
                    layouts
                    entry.targetLocal
                    initProj
                    elems
                .some (Nat.mul remElems elemSz)
            | _ => .some 0
          | .none =>
            let initPlace : Place := {
              local_ := entry.targetLocal
              projection := initProj
            }
            match placeTyResolved localDecls layouts initPlace with
            | .some arrTy =>
              match arrTy.kind with
              | .array elemKind arrLen =>
                let containerLenOpt : Option Nat :=
                  match splitLastSubslice? initProj with
                  | .none => .some arrLen
                  | .some (_, fromIdx, toIdx, fromEnd) =>
                    match fromEnd with
                    | false =>
                      match Bool.and (Nat.ble fromIdx toIdx) (Nat.ble toIdx arrLen) with
                      | true => .some (Nat.sub toIdx fromIdx)
                      | false => .none
                    | true =>
                      match Nat.ble (Nat.add fromIdx toIdx) arrLen with
                      | true => .some (Nat.sub (Nat.sub arrLen toIdx) fromIdx)
                      | false => .none
                match containerLenOpt with
                | .none => .some 0
                | .some cLen =>
                  match
                    Bool.and
                      (Nat.ble minLen cLen)
                      (Nat.ble baseIdx cLen)
                  with
                  | false => .some 0
                  | true =>
                    let remElems := Nat.sub cLen baseIdx
                    match LayoutTable.lookup layouts arrTy.layoutIdx with
                    | .some layout =>
                      match layout.fields with
                      | .array stride _ => .some (Nat.mul remElems stride.bytes)
                      | _ =>
                        match
                          tyByteSize
                            localDecls
                            layouts
                            { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                        with
                        | .some elemSz => .some (Nat.mul remElems elemSz)
                        | .none => .some 0
                    | .none =>
                      match
                        tyByteSize
                          localDecls
                          layouts
                          { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                      with
                      | .some elemSz => .some (Nat.mul remElems elemSz)
                      | .none => .some 0
              | _ => .some 0
            | _ => .some 0
        | .none =>
          match splitLastSubslice? normTargetProj with
          | .some (initProj, fromIdx, toIdx, fromEnd) =>
            match rootValOpt with
            | .some rootVal =>
              match readProjectedValue locals rootVal normTargetProj with
              | .ok (.aggregate 0 subElems) =>
                let elemSz :=
                  resolveSeqContainerElemByteStride
                    localDecls
                    layouts
                    entry.targetLocal
                    initProj
                    subElems
                .some (Nat.mul (length subElems) elemSz)
              | _ => .some 0
            | .none =>
              let initPlace : Place := {
                local_ := entry.targetLocal
                projection := initProj
              }
              match placeTyResolved localDecls layouts initPlace with
              | .some arrTy =>
                match arrTy.kind with
                | .array elemKind arrLen =>
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
                  match subLenOpt with
                  | .some subLen =>
                    match LayoutTable.lookup layouts arrTy.layoutIdx with
                    | .some layout =>
                      match layout.fields with
                      | .array stride _ => .some (Nat.mul subLen stride.bytes)
                      | _ =>
                        match
                          tyByteSize
                            localDecls
                            layouts
                            { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                        with
                        | .some elemSz => .some (Nat.mul subLen elemSz)
                        | .none => .some 0
                    | .none =>
                      match
                        tyByteSize
                          localDecls
                          layouts
                          { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                      with
                      | .some elemSz => .some (Nat.mul subLen elemSz)
                      | .none => .some 0
                  | .none => .some 0
                | _ => .some 0
              | _ => .some 0
          | .none =>
            let fallbackTargetPlaceBytes : Option Nat :=
              let targetPlace : Place := {
                local_ := entry.targetLocal
                projection := entry.targetProjection
              }
              match placeTyResolved localDecls layouts targetPlace with
              | .some projTy =>
                match tyByteSize localDecls layouts projTy with
                | .some n => .some n
                | .none => .some 0
              | .none =>
                match rootValOpt with
                | .some rootVal =>
                  match readProjectedValue locals rootVal entry.targetProjection with
                  | .ok (.aggregate 0 fs) =>
                    match isHomogeneousUntypedFields fs with
                    | true => inferValueCReprBytes (.aggregate 0 fs)
                    | false => .some 0
                  | .ok pv => valueDefaultByteSize pv
                  | _ => .some 0
                | .none => .some 0
            match splitLastField? windowTargetProj with
            | .none => fallbackTargetPlaceBytes
            | .some _ =>
              let (encProj, rawRelProj) := splitAfterLastSeqProj windowTargetProj
              let relProj := normalizeSubsliceProjections rawRelProj
              let encTyOpt :=
                placeTyResolved
                  localDecls
                  layouts
                  { local_ := entry.targetLocal, projection := encProj }
              let encValOpt : Option Value :=
                match rootValOpt with
                | .some rootVal =>
                  match readProjectedValue locals rootVal encProj with
                  | .ok ev => .some ev
                  | _ => .none
                | .none => .none
              let enclosingBytesOpt : Option Nat :=
                match splitLastSubslice? encProj with
                | .some (subInitProj, fromIdx, toIdx, fromEnd) =>
                  let subInitPlace : Place := {
                    local_ := entry.targetLocal
                    projection := subInitProj
                  }
                  let subInitValOpt : Option Value :=
                    match rootValOpt with
                    | .some rootVal =>
                      match readProjectedValue locals rootVal subInitProj with
                      | .ok v => .some v
                      | _ => .none
                    | .none => .none
                  match subInitValOpt with
                  | .some (.aggregate 0 subElems) =>
                    let elemSz :=
                      resolveSeqContainerElemByteStride
                        localDecls
                        layouts
                        entry.targetLocal
                        subInitProj
                        subElems
                    let subLenOpt : Option Nat :=
                      match fromEnd with
                      | false =>
                        match Bool.and (Nat.ble fromIdx toIdx) (Nat.ble toIdx (length subElems)) with
                        | true => .some (Nat.sub toIdx fromIdx)
                        | false => .none
                      | true =>
                        match Nat.ble (Nat.add fromIdx toIdx) (length subElems) with
                        | true => .some (Nat.sub (Nat.sub (length subElems) toIdx) fromIdx)
                        | false => .none
                    match subLenOpt with
                    | .some subLen => .some (Nat.mul subLen elemSz)
                    | .none => .some 0
                  | .some _ => .some 0
                  | .none =>
                    match placeTyResolved localDecls layouts subInitPlace with
                    | .some parentTy =>
                      match parentTy.kind with
                      | .array elemKind arrLen =>
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
                        let elemSzOpt : Option Nat :=
                          match LayoutTable.lookup layouts parentTy.layoutIdx with
                          | .some layout =>
                            match layout.fields with
                            | .array stride _ => .some stride.bytes
                            | _ =>
                              tyByteSize
                                localDecls
                                layouts
                                { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                          | .none =>
                            tyByteSize
                              localDecls
                              layouts
                              { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
                        match subLenOpt, elemSzOpt with
                        | .some subLen, .some elemSz => .some (Nat.mul subLen elemSz)
                        | _, _ => .some 0
                      | _ => .some 0
                    | .none => .none
                | .none =>
                  let encSzOpt_fromArray : Option Nat :=
                    match splitLastConstantIndex? encProj with
                    | .some (arrProj, _, _) =>
                      match placeTyResolved localDecls layouts { local_ := entry.targetLocal, projection := arrProj } with
                      | .some arrTy =>
                        match LayoutTable.lookup layouts arrTy.layoutIdx with
                        | .some layout =>
                          match layout.fields with
                          | .array stride _ => .some stride.bytes
                          | _ => .none
                        | .none => .none
                      | .none => .none
                    | .none => .none
                  match encSzOpt_fromArray with
                  | .some sz => .some sz
                  | .none =>
                    match encTyOpt with
                    | .some encTy => tyByteSize localDecls layouts encTy
                    | .none =>
                      match encValOpt with
                      | .some (.aggregate 0 fs) =>
                        match isHomogeneousUntypedFields fs with
                        | true => inferValueCReprBytes (.aggregate 0 fs)
                        | false => .none
                      | .some ev => valueDefaultByteSize ev
                      | .none => .none
              match enclosingBytesOpt with
              | .none => fallbackTargetPlaceBytes
              | .some encBytes =>
                match
                  projectionChainByteOffset?
                    layouts
                    encTyOpt
                    encValOpt
                    .none
                    0
                    localDecls
                    relProj
                with
                | .none => .some 0
                | .some fieldOff =>
                  match Nat.ble fieldOff encBytes with
                  | true => .some (Nat.sub encBytes fieldOff)
                  | false => .some 0
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
              | .some { kind := .slice elemKind, layoutIdx := pIdx } =>
                let elemIdx :=
                  match LayoutTable.lookup layouts pIdx with
                  | .some { fieldLayouts := flIdx :: _, .. } => flIdx
                  | _ => unresolvedLayoutIdx layouts
                tyByteSize .nil layouts { kind := elemKind, layoutIdx := elemIdx }
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
          let elemIdx :=
            match pointeeTyOpt with
            | .some { layoutIdx := pIdx, .. } =>
              match LayoutTable.lookup layouts pIdx with
              | .some { fieldLayouts := flIdx :: _, .. } => flIdx
              | _ => unresolvedLayoutIdx layouts
            | .none => unresolvedLayoutIdx layouts
          let elemSz :=
            match tyByteSize .nil layouts { kind := elemKind, layoutIdx := elemIdx } with
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
        | .some { kind := .array elemKind arrLen, layoutIdx := pIdx } =>
          let elemIdx :=
            match LayoutTable.lookup layouts pIdx with
            | .some { fieldLayouts := flIdx :: _, .. } => flIdx
            | _ => unresolvedLayoutIdx layouts
          let sz :=
            match tyByteSize .nil layouts { kind := elemKind, layoutIdx := elemIdx } with
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
            match tyByteSize .nil layouts pointeeTy with
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
    match placeTyResolved localDecls layouts place with
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
    match placeTyResolved localDecls layouts place with
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
Resolve the effective target projection path `(fullProj, residualOffset)` for a
reference reborrow (`Rvalue.ref _ (*ptr ...)`), returning `.none` on out-of-bounds
offset/width (`ub`), `.some .none` on `.unsupported` projection read, and
`.some (.some (fullProj, residualOffset))` when the reborrow target is live and
in bounds.
-/
def resolveRefDerefTargetCore?
    (locals : List LocalSlot)
    (targetRootVal : Value)
    (parentEntry : BorrowEntry)
    (parentPtr : ProvenancePtr)
    (resolvedRest : List ProjectionElem)
    (targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (effPointeeTyOpt : Option Ty)
    (accessedTyOpt : Option Ty)
    (isSyntheticFieldOnScalarPointee : Bool := false) :
    Option (Option (List ProjectionElem × Nat)) :=
  let reqBytesOpt : Option Nat :=
    match resolvedRest, accessedTyOpt with
    | .nil, .some accTy =>
      match tyByteSize targetDecls layouts accTy with
      | .some sz => .some sz
      | .none => tyByteSize .nil layouts accTy
    | _, _ => .none
  let rawFull :=
    match parentEntry.targetProjection with
    | .nil => resolvedRest
    | ph :: pt => ph :: appendProjections pt resolvedRest
  let resolvedFullProjOpt : Option (List ProjectionElem × Nat) :=
    match isSyntheticFieldOnScalarPointee, parentEntry.targetProjection with
    | true, .nil => .some (rawFull, 0)
    | _, _ =>
      match
        resolveStackThinPtrTargetProjWithResidual?
          locals
          targetRootVal
          parentEntry
          parentPtr
          resolvedRest
          targetDecls
          layouts
          effPointeeTyOpt
          reqBytesOpt
      with
      | .some (fp, resOff) => .some (fp, resOff)
      | .none =>
        match accessedTyOpt, readProjectedValue locals targetRootVal rawFull with
        | .some accTy, .ok (.scalar sc) =>
          match tyScalarBytes accTy with
          | .some reqBytes =>
            match
              Bool.and
                (Nat.ble 1 reqBytes)
                (Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) sc.sizeBytes)
            with
            | true => .some (rawFull, parentPtr.offsetBytes)
            | false => .none
          | .none => .none
        | _, _ => .none
  match resolvedFullProjOpt with
  | .none => .none
  | .some (fullProj, residualOffset) =>
    match readProjectedValue locals targetRootVal fullProj with
    | .ub => .none
    | .unsupported => .some .none
    | .ok targetSubVal =>
      let widthOk : Bool :=
        match accessedTyOpt, targetSubVal with
        | .some accTy, .scalar sc =>
          match tyScalarBytes accTy with
          | .some reqBytes =>
            Nat.ble (Nat.add residualOffset reqBytes) sc.sizeBytes
          | .none => true
        | .some accTy, .aggregate _ _ =>
          match tyScalarBytes accTy with
          | .some _ => false
          | .none => Nat.beq residualOffset 0
        | _, _ => Nat.beq residualOffset 0
      match widthOk with
      | false => .none
      | true => .some (.some (fullProj, residualOffset))

/--
Reference-reborrow target resolution (`Rvalue.ref _ (*ptr ...)`) with the
address-level alignment check `checkTargetPlaceAlign`: a reference must be
aligned for its pointee type in every execution. The check uses the pointee
type when it is known, else the accessed type of a bare `*ptr`. It returns
`.none` (`ub`) when the borrowed place cannot guarantee that alignment, and
otherwise defers to `resolveRefDerefTargetCore?`.
-/
def resolveRefDerefTarget?
    (locals : List LocalSlot)
    (targetRootVal : Value)
    (parentEntry : BorrowEntry)
    (parentPtr : ProvenancePtr)
    (resolvedRest : List ProjectionElem)
    (targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (effPointeeTyOpt : Option Ty)
    (accessedTyOpt : Option Ty)
    (isSyntheticFieldOnScalarPointee : Bool := false) :
    Option (Option (List ProjectionElem × Nat)) :=
  let alignTyOpt : Option Ty :=
    match effPointeeTyOpt, resolvedRest with
    | .some pt, _ => .some pt
    | .none, .nil => accessedTyOpt
    | .none, _ :: _ => .none
  match
    checkTargetPlaceAlign
      targetDecls
      layouts
      alignTyOpt
      parentEntry
      parentPtr
      (.some targetRootVal)
  with
  | false => .none
  | true =>
    resolveRefDerefTargetCore?
      locals
      targetRootVal
      parentEntry
      parentPtr
      resolvedRest
      targetDecls
      layouts
      effPointeeTyOpt
      accessedTyOpt
      isSyntheticFieldOnScalarPointee

/--
Resolve the effective target projection path `(fullProj, residualOffset)` for a
raw-pointer reborrow (`Rvalue.rawPtr _ (*ptr ...)`).
-/
def resolveRawPtrDerefTarget?
    (locals : List LocalSlot)
    (targetRootVal : Value)
    (parentEntry : BorrowEntry)
    (parentPtr : ProvenancePtr)
    (resolvedRest : List ProjectionElem)
    (targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (effPointeeTyOpt : Option Ty)
    (accessedTyOpt : Option Ty)
    (isSyntheticFieldOnScalarPointee : Bool) :
    Option (List ProjectionElem × Nat) :=
  let rawFull :=
    match parentEntry.targetProjection with
    | .nil => resolvedRest
    | ph :: pt => ph :: appendProjections pt resolvedRest
  let reqBytesOpt : Option Nat :=
    match resolvedRest, accessedTyOpt with
    | .nil, .some accTy =>
      match tyByteSize targetDecls layouts accTy with
      | .some sz => .some sz
      | .none => tyByteSize .nil layouts accTy
    | _, _ => .none
  match isSyntheticFieldOnScalarPointee, parentEntry.targetProjection with
  | true, .nil => .some (rawFull, 0)
  | _, _ =>
    match
      resolveStackThinPtrTargetProjWithResidual?
        locals
        targetRootVal
        parentEntry
        parentPtr
        resolvedRest
        targetDecls
        layouts
        effPointeeTyOpt
        reqBytesOpt
    with
    | .some (fp, resOff) => .some (fp, resOff)
    | .none =>
      match accessedTyOpt, readProjectedValue locals targetRootVal rawFull with
      | .some accTy, .ok (.scalar sc) =>
        match tyScalarBytes accTy with
        | .some reqBytes =>
          match
            Bool.and
              (Nat.ble 1 reqBytes)
              (Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) sc.sizeBytes)
          with
          | true => .some (rawFull, parentPtr.offsetBytes)
          | false => .none
        | .none => .none
      | _, _ =>
        match
          needsThinPtrElemResolution
            parentEntry.targetProjection
            parentPtr.offsetBytes,
          resolvedRest,
          Nat.beq parentPtr.offsetBytes 0
        with
        | false, .nil, _ => .some (rawFull, parentPtr.offsetBytes)
        | false, _ :: _, true => .some (rawFull, 0)
        | _, _, _ => .none

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
- Raw pointer creation (`.rawPtr mutability place`) assigns `sharedBorrowPerm
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
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_unprotected.md#L87-L94>

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
  | .use op | .wrapUnsafeBinder op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok lhsVal locals₁ =>
      match evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .copyForDeref place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
      let pointeeTyOpt :=
        placeTyResolved localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
      let accessedTyOpt := placeTyResolved localDecls layouts place
      let isSyntheticFieldOnScalarPointee : Bool :=
        match stripTransparentProjections restProj, pointeeTyOpt with
        | .field _ _ :: _, .some { kind := .bool, .. } => true
        | .field _ _ :: _, .some { kind := .char, .. } => true
        | .field _ _ :: _, .some { kind := .int _, .. } => true
        | .field _ _ :: _, .some { kind := .uint _, .. } => true
        | .field _ _ :: _, .some { kind := .float _, .. } => true
        | _, _ => false
      let effPointeeTyOpt : Option Ty :=
        match isSyntheticFieldOnScalarPointee with
        | true => .none
        | false => pointeeTyOpt
      let alignTyOpt : Option Ty :=
        match effPointeeTyOpt, restProj with
        | .some pt, _ => .some pt
        | .none, .nil => accessedTyOpt
        | .none, _ :: _ => .none
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr ptrSz)) =>
        match
          Bool.and
            (checkDerefAlign localDecls layouts alignTyOpt parentPtr.offsetBytes)
            (checkDerefAlign localDecls layouts accessedTyOpt parentPtr.offsetBytes)
        with
        | false => .ub
        | true =>
          match lookupBorrow mem.borrows parentPtr.tag with
          | .some parentEntry =>
            match parentEntry.perm, borrowKind with
            | .disabled, _ => .ub
            | .frozen, .mut _ => .ub
            | _, _ =>
              match resolveBorrowProjectionElems locals restProj with
              | .none => .ub
              | .some resolvedRest =>
                let targetRootAndDeclsOpt : Option (Value × List LocalDecl) :=
                  match get? locals parentEntry.targetLocal with
                  | .some (.init v) => .some (v, localDecls)
                  | .some _ => .none
                  | .none =>
                    match get? mem.callerLocals parentEntry.targetLocal with
                    | .some (.init v) => .some (v, .nil)
                    | _ => .none
                match targetRootAndDeclsOpt with
                | .none => .ub
                | .some (targetRootVal, targetDecls) =>
                  match
                    resolveRefDerefTarget?
                      locals
                      targetRootVal
                      parentEntry
                      parentPtr
                      resolvedRest
                      targetDecls
                      layouts
                      effPointeeTyOpt
                      accessedTyOpt
                      isSyntheticFieldOnScalarPointee
                  with
                  | .none => .ub
                  | .some .none => .unsupported
                  | .some (.some (fullProj, residualOffset)) =>
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
                    .ok (.ptr { allocId := tag, offsetBytes := residualOffset } 8) locals mem'
          | .none =>
            match lookupGlobalAlloc mem.globals parentPtr.allocId with
            | .some alloc =>
              let isMut :=
                match borrowKind with
                | .shared => false
                | .mut _ => true
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
        match
          Bool.and
            (checkDerefAlign localDecls layouts pointeeTyOpt parentPtr.offsetBytes)
            (checkDerefAlign localDecls layouts accessedTyOpt parentPtr.offsetBytes)
        with
        | false => .ub
        | true =>
          let isMut :=
            match borrowKind with
            | .shared => false
            | .mut _ => true
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
      | .not => sharedBorrowPerm localDecls layouts place
      | .mut => TreeBorrowPerm.active
    match place.projection with
    | .deref :: restProj =>
      let pointeeTyOpt :=
        placeTyResolved localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
      let accessedTyOpt := placeTyResolved localDecls layouts place
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr ptrSz)) =>
        let isSyntheticFieldOnScalarPointee : Bool :=
          match stripTransparentProjections restProj, pointeeTyOpt with
          | .field _ _ :: _, .some { kind := .bool, .. } => true
          | .field _ _ :: _, .some { kind := .char, .. } => true
          | .field _ _ :: _, .some { kind := .int _, .. } => true
          | .field _ _ :: _, .some { kind := .uint _, .. } => true
          | .field _ _ :: _, .some { kind := .float _, .. } => true
          | _, _ => false
        let effPointeeTyOpt : Option Ty :=
          match isSyntheticFieldOnScalarPointee with
          | true => .none
          | false => pointeeTyOpt
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, mutability with
          | .disabled, _ => .ub
          | .frozen, .mut => .ub
          | _, _ =>
            match resolveBorrowProjectionElems locals restProj with
            | .none => .ub
            | .some resolvedRest =>
              let targetSlotAndDeclsOpt : Option (LocalSlot × List LocalDecl) :=
                match get? locals parentEntry.targetLocal with
                | .some .dead => .none
                | .some slot => .some (slot, localDecls)
                | .none =>
                  match get? mem.callerLocals parentEntry.targetLocal with
                  | .some .dead => .none
                  | .some slot => .some (slot, .nil)
                  | .none => .none
              match targetSlotAndDeclsOpt with
              | .none => .ub
              | .some (.uninit, _) =>
                match
                  needsThinPtrElemResolution
                    parentEntry.targetProjection
                    parentPtr.offsetBytes,
                  Nat.beq parentPtr.offsetBytes 0
                with
                | false, true =>
                  let tag := mem.nextTag
                  let fullProj :=
                    match parentEntry.targetProjection with
                    | .nil => resolvedRest
                    | ph :: pt => ph :: appendProjections pt resolvedRest
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
                | _, _ => .ub
              | .some (.dead, _) => .ub
              | .some (.init targetRootVal, targetDecls) =>
                match
                  resolveRawPtrDerefTarget?
                    locals
                    targetRootVal
                    parentEntry
                    parentPtr
                    resolvedRest
                    targetDecls
                    layouts
                    effPointeeTyOpt
                    accessedTyOpt
                    isSyntheticFieldOnScalarPointee
                with
                | .none => .ub
                | .some (fullProj, residualOffset) =>
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
                  .ok (.ptr { allocId := tag, offsetBytes := residualOffset } 8) locals mem'
        | .none =>
          match lookupGlobalAlloc mem.globals parentPtr.allocId with
          | .some alloc =>
            let isMut :=
              match mutability with
              | .not => false
              | .mut => true
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
  | .cast .intToInt op targetTy =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok (.ptr ptrVal _) locals' =>
      let addr := Nat.add (Nat.mul ptrVal.allocId 65536) ptrVal.offsetBytes
      .ok (.scalar ⟨addr, 8⟩) locals' mem
    | .ok (.scalar sc) locals' => .ok (.scalar ⟨sc.bits, 8⟩) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast .pointerWithExposedProvenance op _ =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok (.scalar sc) locals' =>
      evalUnaryNot sc (operandTy localDecls layouts op) locals' mem
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .neg op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok (.aggregate 0 (.ptr _ ptrSz :: .scalar metaSc :: .nil)) locals' =>
      match
        Bool.and
          (Nat.beq ptrSz ptrBytes)
          (Nat.beq metaSc.sizeBytes ptrBytes)
      with
      | true => .ok (.scalar ⟨metaSc.bits, metaSc.sizeBytes⟩) locals' mem
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
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok val locals' =>
      evalPlaceDiscriminant val locals' mem place localDecls layouts
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.array _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.adt _ variantIdx _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok vals locals' => .ok (.aggregate variantIdx vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.closure _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.rawPtr _ _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
