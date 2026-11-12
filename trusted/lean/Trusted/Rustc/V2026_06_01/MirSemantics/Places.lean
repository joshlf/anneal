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
With no active protectors, no borrow entry is protected.
-/
@[simp]
theorem isBorrowProtected_nil (entry : BorrowEntry) :
    isBorrowProtected .nil entry = false := by
  unfold isBorrowProtected
  cases entry.protector <;> rfl

/--
Kind of a Tree Borrows memory access, mirroring Miri's `AccessKind`.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L219-L231>

> "pub(super) fn perform_access(
>     kind: AccessKind,
>     rel_pos: AccessRelatedness,
>     child: PermissionPriv,
>     protected: bool,
> ) -> Option<PermissionPriv> {"
-/
inductive TreeBorrowAccessKind : Type where
  /-- A read access. -/
  | read : TreeBorrowAccessKind
  /-- A write access. -/
  | write : TreeBorrowAccessKind

/--
Position of the accessed tag relative to the borrow-tree node being updated,
mirroring the `rel_pos.is_foreign()` test in Miri's `perform_access`.

`.localAccess` means the access goes through the node itself or one of its
descendants (a child access); `.foreignAccess` means every other access,
including accesses through ancestors, siblings, cousins, and direct accesses to
the borrowed local that do not go through any tag.

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L47-L55>

> "When a node is accessed, each node in the tree can be divided into two
> disjoint sets: *local nodes* and *foreign nodes*, based on its relative
> position to the accessed node. The *local* set includes the node itself and
> all its descendants, while the *foreign* set contains all other nodes."
-/
inductive TreeBorrowRelatedness : Type where
  /-- Access through the node or one of its descendants. -/
  | localAccess : TreeBorrowRelatedness
  /-- Any other access. -/
  | foreignAccess : TreeBorrowRelatedness

/--
Outcome of one per-node Tree Borrows transition, mirroring Miri's
`Option<PermissionPriv>` result plus its `assert!(!protected)` branches.

`.ub` is upstream `None` (a forbidden child access). `.protectedReservedIM` is
the upstream assertion failure for a protected `ReservedIM` node, which Miri
documents as unreachable because it never creates `ReservedIM` under a
protector. Anneal treats `.protectedReservedIM` as undefined behavior wherever
it consumes a transition, so a state that violates Miri's invariant fails
closed instead of being silently accepted.
-/
inductive TreeBorrowTransition : Type where
  /-- The access is permitted and the node moves to `perm`. -/
  | transition (perm : TreeBorrowPerm) : TreeBorrowTransition
  /-- The access is a forbidden child access (undefined behavior). -/
  | ub : TreeBorrowTransition
  /-- The access reached a protected `.reservedIM` node, which violates Miri's
      protector invariant. -/
  | protectedReservedIM : TreeBorrowTransition

/--
Child-read transition: undefined behavior on `.disabled`, no change otherwise.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L137-L145>

> "/// A child node was read-accessed: UB on Disabled, noop on the rest.
> fn child_read(state: PermissionPriv, _protected: bool) -> Option<PermissionPriv> {
>     Some(match state {
>         Disabled => return None,
>         // The inner data `ty_is_freeze` of `Reserved` is always irrelevant for Read
>         // accesses, since the data is not being mutated. Hence the `{ .. }`.
>         readable @ (Cell | ReservedFrz { .. } | ReservedIM | Unique | Frozen) => readable,
>     })
> }"
-/
@[simp]
def treeBorrowChildRead : TreeBorrowPerm → TreeBorrowTransition
  | .cell => .transition .cell
  | .reservedFrz conflicted => .transition (.reservedFrz conflicted)
  | .reservedIM => .transition .reservedIM
  | .unique => .transition .unique
  | .frozen => .transition .frozen
  | .disabled => .ub

/--
Foreign-read transition: `.cell`, `.frozen`, and `.disabled` are unchanged; a
protected `.reservedFrz` sets its conflict latch; an unprotected reservation is
unchanged; `.unique` freezes, or disables while protected.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L147-L182>

> "fn foreign_read(state: PermissionPriv, protected: bool) -> Option<PermissionPriv> {
>     Some(match state {
>         // Cell ignores foreign reads.
>         Cell => Cell,
>         // Non-writeable states just ignore foreign reads.
>         non_writeable @ (Frozen | Disabled) => non_writeable,
>         ...
>         ReservedFrz { .. } if protected => ReservedFrz { conflicted: true },
>         // Before activation and without protectors, foreign reads are fine.
>         // That's the entire point of 2-phase borrows.
>         res @ (ReservedFrz { .. } | ReservedIM) => {
>             // Even though we haven't checked `ReservedIM if protected` separately,
>             // it is a state that cannot occur because under a protector we only
>             // create `ReservedFrz` never `ReservedIM`.
>             assert!(!protected);
>             res
>         }
>         Unique =>
>             if protected {
>                 // We wrote, someone else reads -- that's bad.
>                 // (Since Unique is always initialized, this move-to-protected will mean insta-UB.)
>                 Disabled
>             } else {
>                 ...
>                 Frozen
>             },
>     })
> }"
-/
@[simp]
def treeBorrowForeignRead
    (perm : TreeBorrowPerm)
    (isProtected : Bool) :
    TreeBorrowTransition :=
  match perm with
  | .cell => .transition .cell
  | .frozen => .transition .frozen
  | .disabled => .transition .disabled
  | .reservedFrz conflicted =>
    match isProtected with
    | true => .transition (.reservedFrz true)
    | false => .transition (.reservedFrz conflicted)
  | .reservedIM =>
    match isProtected with
    | true => .protectedReservedIM
    | false => .transition .reservedIM
  | .unique =>
    match isProtected with
    | true => .transition .disabled
    | false => .transition .frozen

/--
Child-write transition: `.cell` is unchanged; a protected conflicted
`.reservedFrz` is undefined behavior; every other reservation and `.unique`
become `.unique`; `.frozen` and `.disabled` are undefined behavior.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L184-L199>

> "fn child_write(state: PermissionPriv, protected: bool) -> Option<PermissionPriv> {
>     Some(match state {
>         // Cell ignores child writes.
>         Cell => Cell,
>         // If the `conflicted` flag is set, then there was a foreign read during
>         // the function call that is still ongoing (still `protected`),
>         // this is UB (`noalias` violation).
>         ReservedFrz { conflicted: true } if protected => return None,
>         // A write always activates the 2-phase borrow, even with interior
>         // mutability
>         ReservedFrz { .. } | ReservedIM | Unique => Unique,
>         Frozen | Disabled => return None,
>     })
> }"
-/
@[simp]
def treeBorrowChildWrite
    (perm : TreeBorrowPerm)
    (isProtected : Bool) :
    TreeBorrowTransition :=
  match perm with
  | .cell => .transition .cell
  | .reservedFrz true =>
    match isProtected with
    | true => .ub
    | false => .transition .unique
  | .reservedFrz false => .transition .unique
  | .reservedIM => .transition .unique
  | .unique => .transition .unique
  | .frozen => .ub
  | .disabled => .ub

/--
Foreign-write transition: `.cell` is unchanged; an unprotected `.reservedIM` is
unchanged; every other state becomes `.disabled`.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L201-L217>

> "fn foreign_write(state: PermissionPriv, protected: bool) -> Option<PermissionPriv> {
>     ...
>     Some(match state {
>         // Cell ignores foreign writes.
>         Cell => Cell,
>         res @ ReservedIM => {
>             // We can never create a `ReservedIM` under a protector, only `ReservedFrz`.
>             assert!(!protected);
>             res
>         }
>         _ => Disabled,
>     })
> }"
-/
@[simp]
def treeBorrowForeignWrite
    (perm : TreeBorrowPerm)
    (isProtected : Bool) :
    TreeBorrowTransition :=
  match perm with
  | .cell => .transition .cell
  | .reservedIM =>
    match isProtected with
    | true => .protectedReservedIM
    | false => .transition .reservedIM
  | .reservedFrz _ => .transition .disabled
  | .unique => .transition .disabled
  | .frozen => .transition .disabled
  | .disabled => .transition .disabled

/--
Per-node Tree Borrows permission transition: the same four-way dispatch on
`(kind, rel)` as Miri's `perform_access`, over all six permission states and
both protector settings.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L219-L231>

> "match (kind, rel_pos.is_foreign()) {
>     (AccessKind::Write, true) => foreign_write(child, protected),
>     (AccessKind::Read, true) => foreign_read(child, protected),
>     (AccessKind::Write, false) => child_write(child, protected),
>     (AccessKind::Read, false) => child_read(child, protected),
> }"
-/
@[simp]
def treeBorrowPermTransition
    (kind : TreeBorrowAccessKind)
    (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm)
    (isProtected : Bool) :
    TreeBorrowTransition :=
  match kind, rel with
  | .write, .foreignAccess => treeBorrowForeignWrite perm isProtected
  | .read, .foreignAccess => treeBorrowForeignRead perm isProtected
  | .write, .localAccess => treeBorrowChildWrite perm isProtected
  | .read, .localAccess => treeBorrowChildRead perm

/--
Protector rule applied after a per-node transition: a protected node whose
transition produces `.disabled` is undefined behavior.

Every Anneal `BorrowEntry` stands for an accessed (initialized) location: its
creation performs the initial child access of its permission, except for
`.cell`, which no transition ever disables. Miri's `accessed` guard is
therefore always satisfied here.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/tree.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/tree.rs#L157-L159>

> "if protected && self.accessed && transition.produces_disabled() {
>     return Err(TransitionError::ProtectedDisabled(old_perm));
> }"
-/
@[simp]
def treeBorrowProtectorCheck
    (isProtected : Bool) :
    TreeBorrowTransition → TreeBorrowTransition
  | .transition .disabled =>
    match isProtected with
    | true => .ub
    | false => .transition .disabled
  | .transition .cell => .transition .cell
  | .transition (.reservedFrz conflicted) =>
    .transition (.reservedFrz conflicted)
  | .transition .reservedIM => .transition .reservedIM
  | .transition .unique => .transition .unique
  | .transition .frozen => .transition .frozen
  | .ub => .ub
  | .protectedReservedIM => .protectedReservedIM

/--
Full per-node access for one borrow entry: the permission transition, the
protector rule, and the tree visitor's rule that a foreign access skips a
`.disabled` node.

Child accesses never produce `.disabled`, so the protector rule only matters
for foreign accesses. Miri's visitor skips a foreign access to a `Disabled`
node (`skip_if_known_noop`), so a protected `.disabled` entry is not reported
again by later foreign accesses.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/tree.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/tree.rs#L130-L162>

> "fn perform_access(
>     &mut self,
>     access_kind: AccessKind,
>     rel_pos: AccessRelatedness,
>     protected: bool,
> ) -> Result<PermTransition, TransitionError> {
>     let old_perm = self.permission;
>     let transition = Permission::perform_access(access_kind, rel_pos, old_perm, protected)
>         .ok_or(TransitionError::ChildAccessForbidden(old_perm))?;"
-/
@[simp]
def treeBorrowNodeAccess
    (kind : TreeBorrowAccessKind)
    (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm)
    (isProtected : Bool) :
    TreeBorrowTransition :=
  match rel with
  | .localAccess => treeBorrowPermTransition kind .localAccess perm isProtected
  | .foreignAccess =>
    match perm with
    | .disabled => .transition .disabled
    | _ =>
      treeBorrowProtectorCheck isProtected
        (treeBorrowPermTransition kind .foreignAccess perm isProtected)

/--
`true` exactly for transition outcomes that Anneal treats as undefined
behavior (`.ub` and the fail-closed `.protectedReservedIM`).
-/
@[simp]
def treeBorrowTransitionIsUB : TreeBorrowTransition → Bool
  | .transition _ => false
  | .ub => true
  | .protectedReservedIM => true

/--
Apply a per-node transition outcome to `entry`. Undefined-behavior outcomes
leave `entry` unchanged; callers detect them separately before committing the
new borrow table.
-/
@[simp]
def applyTreeBorrowTransition
    (entry : BorrowEntry) :
    TreeBorrowTransition → BorrowEntry
  | .transition perm => { entry with perm := perm }
  | .ub => entry
  | .protectedReservedIM => entry

/--
`applyTreeBorrowTransition` changes only `perm`: every other `BorrowEntry`
field is preserved.
-/
@[simp]
theorem applyTreeBorrowTransition_fields
    (entry : BorrowEntry)
    (outcome : TreeBorrowTransition) :
    (applyTreeBorrowTransition entry outcome).tag = entry.tag ∧
    (applyTreeBorrowTransition entry outcome).targetLocal = entry.targetLocal ∧
    (applyTreeBorrowTransition entry outcome).targetProjection =
      entry.targetProjection ∧
    (applyTreeBorrowTransition entry outcome).rangeOffset = entry.rangeOffset ∧
    (applyTreeBorrowTransition entry outcome).rangeLen = entry.rangeLen ∧
    (applyTreeBorrowTransition entry outcome).protector = entry.protector ∧
    (applyTreeBorrowTransition entry outcome).parentTag = entry.parentTag := by
  cases outcome <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Relative position of a write through `writerTag` with respect to `entry` when
the writer has already been normalized against the borrow hierarchy
(`resolveTreeBorrowWriterTag`): a write through `entry`'s own tag is a child
access, while a direct write to the local (`writerTag = .none`) or a write
through any other tag is foreign.
-/
@[simp]
def treeBorrowWriterRelatedness
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    TreeBorrowRelatedness :=
  match writerTag with
  | .none => .foreignAccess
  | .some tag =>
    match Nat.beq entry.tag tag with
    | true => .localAccess
    | false => .foreignAccess

/--
Test whether a write with `writerTag` would be undefined behavior at `entry`
if `entry` is protected and its region overlaps the write.

The test runs the per-node access `treeBorrowNodeAccess` with
`isProtected := true`: it reports a forbidden child write (a protected
conflicted `.reservedFrz`, or `.frozen` / `.disabled`), a foreign write that
would disable a protected node, and the fail-closed protected `.reservedIM`
case. A protected `.cell` survives every write, and a foreign write skips a
`.disabled` node.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def borrowEntryWriteConflicts
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    Bool :=
  treeBorrowTransitionIsUB
    (treeBorrowNodeAccess
      .write
      (treeBorrowWriterRelatedness entry writerTag)
      entry.perm
      true)

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
  pointer), the write is a foreign write for every entry targeting
  `targetLocal`: `.cell` and `.reservedIM` are unchanged and every other state
  becomes `.disabled`.
- When `writerTag = .some tag`, the entry with `entry.tag == tag` receives a
  child write (reservations activate to `.unique`, `.cell` is unchanged), and
  any other entry targeting `targetLocal` receives a foreign write.

The update uses the unprotected transition. Whenever the protected transition
of a write is not undefined behavior it agrees with the unprotected one, and
callers reject protected undefined behavior (`hasProtectedWriteConflict`,
`hasProtectedTreeWriteConflict`) before committing this update.

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
    applyTreeBorrowTransition entry
      (treeBorrowNodeAccess
        .write
        (treeBorrowWriterRelatedness entry writerTag)
        entry.perm
        false)

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
        applyTreeBorrowTransition entry
          (treeBorrowNodeAccess
            .write
            (treeBorrowWriterRelatedness entry writerTag)
            entry.perm
            false)) := rfl

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
    match treeBorrowWriterRelatedness entry writerTag with
    | .localAccess =>
      applyTreeBorrowTransition entry
        (treeBorrowNodeAccess .write .localAccess entry.perm false)
    | .foreignAccess =>
      match
        borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen
      with
      | false => entry
      | true =>
        applyTreeBorrowTransition entry
          (treeBorrowNodeAccess .write .foreignAccess entry.perm false)

/--
When `writeProj = .nil` and `entry.targetProjection = .nil` (with default
unranged write `writeRangeLen = 0`), `updateBorrowPermAtProj` agrees with
`updateBorrowPerm`.
-/
@[simp]
theorem updateBorrowPermAtProj_nil_eq_updateBorrowPerm
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (h_proj : entry.targetProjection = .nil) :
    updateBorrowPermAtProj entry targetLocal writerTag .nil =
      updateBorrowPerm entry targetLocal writerTag := by
  have hov : borrowEntryOverlapsWrite entry .nil 0 0 = true := by
    unfold borrowEntryOverlapsWrite
    rw [h_proj]
    rfl
  unfold updateBorrowPermAtProj updateBorrowPerm
  cases Nat.beq entry.targetLocal targetLocal with
  | false => rfl
  | true =>
    cases hrel : treeBorrowWriterRelatedness entry writerTag with
    | localAccess => rfl
    | foreignAccess => simp only [hov]

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
Fuel-bounded walk up the `BorrowEntry.parentTag` chain starting at `startTag`,
testing whether an unprotected child access of kind `kind` is undefined
behavior at some entry on the chain: a child read of a `.disabled` entry, or a
child write of a `.frozen` or `.disabled` entry.

An access through a tag is a child (`NodeRelation::Local`) access for the tag's
own node and for every ancestor, so Miri applies the child transition to each
of them. A missing parent entry ends the walk, matching
`isBorrowDescendantOrSelfAux`. Protector-dependent child-write undefined
behavior (a protected conflicted `.reservedFrz`) is reported separately by
`hasProtectedTreeWriteConflict`.

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L101-L106>

> "// If `self` is an ancestor of the accessed node, the accessed node is local to `self`.
> // Otherwise, the accessed node is a `foreign` of `self`.
> let node_relation = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };"
-/
@[reducible]
def treeBorrowChainChildAccessUBAux
    (kind : TreeBorrowAccessKind) :
    Nat → List BorrowEntry → Option Nat → Bool
  | .zero, _, _ => false
  | .succ _, _, .none => false
  | .succ fuel, borrows, .some tag =>
    match lookupBorrow borrows tag with
    | .none => false
    | .some ancestor =>
      match
        treeBorrowTransitionIsUB
          (treeBorrowPermTransition kind .localAccess ancestor.perm false)
      with
      | true => true
      | false =>
        treeBorrowChainChildAccessUBAux kind fuel borrows ancestor.parentTag

/--
Test whether an unprotected child access of kind `kind` through a tag whose
parent is `parentTag` is undefined behavior at some strict ancestor in
`borrows` (`treeBorrowChainChildAccessUBAux` with fuel `length borrows`).
-/
@[reducible]
def treeBorrowAncestorsChildAccessUB
    (kind : TreeBorrowAccessKind)
    (borrows : List BorrowEntry)
    (parentTag : Option Nat) :
    Bool :=
  treeBorrowChainChildAccessUBAux kind (length borrows) borrows parentTag

/--
Resolve the effective writer provenance tag relative to `entry` in `borrows`
under the Tree Borrows parent/child hierarchy.

When `writerTag = .some wTag` and `wTag` is in the subtree rooted at `entry.tag`
(`isBorrowDescendantOrSelf borrows wTag entry.tag == true`), the write is a
child/self (`NodeRelation::Local`) write relative to `entry`, so
`resolveTreeBorrowWriterTag` normalizes the writer tag to `.some entry.tag`
(applying the child-write transition to `entry`: a reservation activates to
`.unique`, `.unique` and `.cell` are preserved).
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
reservations to `.unique` and preserving `.unique` and `.cell` on ancestors),
whereas writes through a non-descendant tag (`NodeRelation::Foreign` writes,
including writes through an ancestor tag relative to its children) disable
overlapping `.reservedFrz`, `.unique`, and `.frozen` entries while leaving
`.cell` and `.reservedIM` entries unchanged.

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
`entry.perm` (child reads never change a permission; a child read of a
`.disabled` entry is undefined behavior, which `hasTreeReadUB` reports before
this update is committed), whereas a `NodeRelation::Foreign` read (such as
reading through a parent pointer after a child mutable borrow has been
activated) applies `treeBorrowNodeAccess .read .foreignAccess` with the
entry's protector status in `activeProtectors`: `.unique` freezes when
unprotected, a protected `.reservedFrz` sets its conflict latch, and `.cell`,
`.frozen`, `.disabled`, and unprotected reservations are unchanged.

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
    (readRangeLen : Nat := 0)
    (activeProtectors : List Nat := .nil) :
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
        applyTreeBorrowTransition entry
          (treeBorrowNodeAccess
            .read
            .foreignAccess
            entry.perm
            (isBorrowProtected activeProtectors entry))

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
    (readRangeLen : Nat := 0)
    (activeProtectors : List Nat := .nil) :
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
      readRangeLen
      activeProtectors ::
      freezeTreeBorrowsOnReadAtProj
        allBorrows
        rest
        targetLocal
        readerTag
        readProj
        readRangeOff
        readRangeLen
        activeProtectors

/--
Update Tree Borrows permissions in `borrows` after a dereference read from
pointer local `ptrLoc` with post-deref projection suffix `restProj`, applying
the foreign-read transition (with protector status from `activeProtectors`) to
every borrow whose target region overlaps the read and that is not an ancestor
of (or equal to) the reader's tag.

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
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat := .nil) :
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
        activeProtectors
    | .none => borrows
  | _ => borrows

/--
Test whether a read through `readerTag` (or a direct read of the local when
`readerTag = .none`) at `targetLocal` / `readProj` and the optional byte range
is undefined behavior at `entry`: a child read of a `.disabled` entry, a
foreign read that disables a protected `.unique` entry, or a foreign read of a
protected `.reservedIM` entry (fail-closed).

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L7-L8>

> "When a reborrow occurs at function entry (i.e. the original reference is
> passed as an argument), we add a *protector* to the reborrow. When a node is
> protected, it is UB for this node to become `Disabled`."
-/
@[reducible]
def borrowEntryReadUB
    (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) :
    Bool :=
  match Nat.beq entry.targetLocal targetLocal with
  | false => false
  | true =>
    match
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen
    with
    | false => false
    | true =>
      let isLocalRead :=
        match readerTag with
        | .none => false
        | .some rTag => isBorrowDescendantOrSelf allBorrows rTag entry.tag
      match isLocalRead with
      | true =>
        treeBorrowTransitionIsUB
          (treeBorrowNodeAccess
            .read
            .localAccess
            entry.perm
            (isBorrowProtected activeProtectors entry))
      | false =>
        treeBorrowTransitionIsUB
          (treeBorrowNodeAccess
            .read
            .foreignAccess
            entry.perm
            (isBorrowProtected activeProtectors entry))

/--
Test whether a read through `readerTag` is undefined behavior at any entry of
`borrows` within full borrow hierarchy `allBorrows` (`borrowEntryReadUB`).

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L89-L125>

> "/// Recusively do state transition on `self` node and all its descendants.
> /// `path` is the path from `self` to the accessed node.
> /// `path` is None when the accessed node is not a descendant of `self`."
-/
@[reducible]
def hasTreeReadUB
    (allBorrows : List BorrowEntry)
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff : Nat := 0)
    (readRangeLen : Nat := 0) :
    Bool :=
  match borrows with
  | .nil => false
  | entry :: rest =>
    match
      borrowEntryReadUB
        allBorrows
        activeProtectors
        entry
        targetLocal
        readerTag
        readProj
        readRangeOff
        readRangeLen
    with
    | true => true
    | false =>
      hasTreeReadUB
        allBorrows
        rest
        activeProtectors
        targetLocal
        readerTag
        readProj
        readRangeOff
        readRangeLen

/--
Test whether a dereference read from pointer local `ptrLoc` with post-deref
projection suffix `restProj` is undefined behavior under the Tree Borrows
hierarchy `borrows` and active protectors `activeProtectors` (`hasTreeReadUB`
at the reader's region). Returns `false` when `ptrLoc` does not hold a tracked
pointer; `evalOperand` handles those cases.
-/
@[reducible]
def derefReadTreeUB
    (locals : List LocalSlot)
    (ptrLoc : Local)
    (restProj : List ProjectionElem)
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat) :
    Bool :=
  match get? locals ptrLoc with
  | .some (.init (.ptr ptrVal _)) =>
    match lookupBorrow borrows ptrVal.tag with
    | .some readerEntry =>
      hasTreeReadUB
        borrows
        borrows
        activeProtectors
        readerEntry.targetLocal
        (.some ptrVal.tag)
        (appendProjections readerEntry.targetProjection restProj)
        readerEntry.rangeOffset
        readerEntry.rangeLen
    | .none => false
  | _ => false

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
Return `true` when `proj` contains at least one `.subslice` element.
-/
@[reducible]
def projHasSubslice : List ProjectionElem → Bool
  | .nil => false
  | .subslice _ _ _ :: _ => true
  | _ :: rest => projHasSubslice rest

/--
Return `true` when `proj` contains a `.subslice _ _ true` (`fromEnd = true`).
-/
@[reducible]
def projHasFromEndSubslice : List ProjectionElem → Bool
  | .nil => false
  | .subslice _ _ true :: _ => true
  | _ :: rest => projHasFromEndSubslice rest

/--
Return `true` when every forward `.subslice fromIdx toIdx false` in `proj`
satisfies `fromIdx ≤ toIdx`.
-/
@[reducible]
def forwardSubslicesOrdered : List ProjectionElem → Bool
  | .nil => true
  | .subslice fromIdx toIdx false :: rest =>
    match Nat.ble fromIdx toIdx with
    | false => false
    | true => forwardSubslicesOrdered rest
  | _ :: rest => forwardSubslicesOrdered rest

/--
Validate every `.subslice` step along a deref-free projection chain `proj`
against runtime value `v` (returning `false` whenever a `.subslice` is inverted,
underflows `fromEnd = true`, exceeds the runtime slice/array length, or is
applied to a non-aggregate value).
-/
def subsliceChainValidOnVal
    (indexLocals : List LocalSlot) :
    Value → List ProjectionElem → Bool
  | _, .nil => true
  | v, .opaqueCast _ :: rest => subsliceChainValidOnVal indexLocals v rest
  | v, .unwrapUnsafeBinder _ :: rest => subsliceChainValidOnVal indexLocals v rest
  | .aggregate varIdx fields, .downcast _ targetVar :: rest =>
    match Nat.beq varIdx targetVar with
    | true => subsliceChainValidOnVal indexLocals (.aggregate varIdx fields) rest
    | false => false
  | _, .downcast _ _ :: _ => false
  | .aggregate _ fields, .field idx _ :: rest =>
    match get? fields idx with
    | .some .unit => forwardSubslicesOrdered rest
    | .some fv => subsliceChainValidOnVal indexLocals fv rest
    | .none => forwardSubslicesOrdered rest
  | .scalar sc, .field .zero _ :: rest =>
    subsliceChainValidOnVal indexLocals (.scalar sc) rest
  | .ptr p sz, .field .zero _ :: rest =>
    subsliceChainValidOnVal indexLocals (.ptr p sz) rest
  | _, .field _ _ :: _ => false
  | .aggregate 0 elems, .index idxLocal :: rest =>
    match get? indexLocals idxLocal with
    | .some (.init (.scalar idxSc)) =>
      match get? elems idxSc.bits with
      | .some ev => subsliceChainValidOnVal indexLocals ev rest
      | .none => false
    | _ => false
  | _, .index _ :: _ => false
  | .aggregate 0 elems, .constantIndex offset minLen fromEnd :: rest =>
    let len := length elems
    let fromEndOk :=
      match fromEnd with
      | false => true
      | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset len)
    match Bool.and (Nat.ble minLen len) fromEndOk with
    | false => false
    | true =>
      let idx :=
        match fromEnd with
        | true => Nat.sub len offset
        | false => offset
      match get? elems idx with
      | .some ev => subsliceChainValidOnVal indexLocals ev rest
      | .none => false
  | _, .constantIndex _ _ _ :: _ => false
  | .aggregate 0 elems, .subslice fromIdx toIdx fromEnd :: rest =>
    match extractSubslice elems fromIdx toIdx fromEnd with
    | .some subElems =>
      subsliceChainValidOnVal indexLocals (.aggregate 0 subElems) rest
    | .none => false
  | _, .subslice _ _ _ :: _ => false
  | _, .deref :: _ => false

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
    | .some declTy => { ty with layoutIdx := declTy.layoutIdx }
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
        | .none =>
          match LayoutTable.lookup layouts baseTy.layoutIdx with
          | .some { size := pSz, fields := .primitive, fieldLayouts := flIdx :: .nil, .. } =>
            match
              Bool.and
                (Nat.beq pSz.bytes (layoutPointerBytes layouts))
                (Nat.ble (.succ flIdx) (length layouts.entries))
            with
            | true => { kind := inner, layoutIdx := flIdx }
            | false => { kind := inner, layoutIdx := synthKindLayoutIdx layouts inner }
          | _ => { kind := inner, layoutIdx := synthKindLayoutIdx layouts inner }
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
  | .subslice fromIdx toIdx fromEnd :: rest =>
    match baseTy.kind with
    | .array ek arrLen =>
      match Nat.ble toIdx arrLen with
      | false => .none
      | true =>
        let endIdx :=
          match fromEnd with
          | true => Nat.sub arrLen toIdx
          | false => toIdx
        match Nat.ble fromIdx endIdx with
        | false => .none
        | true =>
          let subLen := Nat.sub endIdx fromIdx
          match Nat.beq subLen arrLen with
          | true => resolveProjectedTyResolved localDecls layouts baseTy rest
          | false =>
            match rest with
            | .index _ :: _ =>
              resolveProjectedTyResolved localDecls layouts baseTy rest
            | .constantIndex _ _ _ :: _ =>
              resolveProjectedTyResolved localDecls layouts baseTy rest
            | _ =>
              let subTy :=
                resolveTyWithLocalDecls
                  localDecls
                  layouts
                  { kind := .array ek subLen, layoutIdx := unresolvedLayoutIdx layouts }
              resolveProjectedTyResolved localDecls layouts subTy rest
    | .slice _ =>
      let orderOk :=
        match fromEnd with
        | false => Nat.ble fromIdx toIdx
        | true => true
      match orderOk with
      | false => .none
      | true => resolveProjectedTyResolved localDecls layouts baseTy rest
    | _ => .none
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
  | .constantIndex rawIdx minLen fromEnd :: rest =>
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
      let arrLen := length elems
      let fromEndOk : Bool :=
        match fromEnd with
        | false => true
        | true => Bool.and (Nat.ble 1 rawIdx) (Nat.ble rawIdx arrLen)
      let elemIdx : Nat :=
        match fromEnd with
        | false => rawIdx
        | true => Nat.sub arrLen rawIdx
      match
        Bool.and
          fromEndOk
          (Bool.and
            (Nat.ble minLen arrLen)
            (Nat.ble (.succ elemIdx) arrLen))
      with
      | false => .none
      | true =>
        let stepOffOpt : Option Nat :=
          match Nat.beq elemIdx 0 with
          | true => .some 0
          | false =>
            match layoutStrideOpt with
            | .some s => .some (Nat.mul elemIdx s)
            | .none =>
              match nextElemTyOpt with
              | .some elemTy =>
                match tyByteSize localDecls layouts elemTy with
                | .some sz => .some (Nat.mul elemIdx sz)
                | .none => .none
              | .none =>
                match isHomogeneousUntypedFields elems with
                | true => .some (Nat.mul elemIdx (inferElemListByteStride elems))
                | false => .none
        match stepOffOpt with
        | .none => .none
        | .some stepOff =>
          projectionChainByteOffset?
            layouts
            nextElemTyOpt
            (get? elems elemIdx)
            .none
            (Nat.add accOff stepOff)
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
        let fromEndOk : Bool :=
          match fromEnd with
          | false => true
          | true => Bool.and (Nat.ble 1 rawIdx) (Nat.ble rawIdx arrLen)
        let elemIdx : Nat :=
          match fromEnd with
          | false => rawIdx
          | true => Nat.sub arrLen rawIdx
        match
          Bool.and
            fromEndOk
            (Bool.and
              (Nat.ble minLen arrLen)
              (Nat.ble (.succ elemIdx) arrLen))
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
          let fromEndOk : Bool :=
            match fromEnd with
            | false => true
            | true => Bool.and (Nat.ble 1 rawIdx) (Nat.ble rawIdx arrLen)
          let elemIdx : Nat :=
            match fromEnd with
            | false => rawIdx
            | true => Nat.sub arrLen rawIdx
          match
            Bool.and
              fromEndOk
              (Bool.and
                (Nat.ble minLen arrLen)
                (Nat.ble (.succ elemIdx) arrLen))
          with
          | false => .none
          | true =>
            let fallbackElemTy :=
              match nextElemTyOpt with
              | .some et => et
              | .none => { kind := elemKind, layoutIdx := unresolvedLayoutIdx layouts }
            let stepOffOpt : Option Nat :=
              match Nat.beq elemIdx 0 with
              | true => .some 0
              | false =>
                match tyByteSize localDecls layouts fallbackElemTy with
                | .some elemSz => .some (Nat.mul elemIdx elemSz)
                | .none => .none
            match stepOffOpt with
            | .some stepOff =>
              projectionChainByteOffset?
                layouts
                nextElemTyOpt
                .none
                .none
                (Nat.add accOff stepOff)
                localDecls
                rest
            | .none => .none
        | _ => .none
  | .subslice fromIdx toIdx fromEnd :: rest =>
    let resolvedCurTyOpt : Option Ty :=
      match curTyOpt with
      | .some rawCurTy => .some (resolveTyWithLocalDecls localDecls layouts rawCurTy)
      | .none => .none
    let elemKindOpt : Option RigidTy :=
      match resolvedCurTyOpt with
      | .some { kind := .array ek _, .. } => .some ek
      | .some { kind := .slice ek, .. } => .some ek
      | _ => .none
    let elemTyOpt : Option Ty :=
      match resolvedCurTyOpt, elemKindOpt with
      | .some curTy, .some ek =>
        match LayoutTable.lookup layouts curTy.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          .some { kind := ek, layoutIdx := flIdx }
        | _ =>
          .some
            (resolveTyWithLocalDecls
              localDecls
              layouts
              { kind := ek, layoutIdx := unresolvedLayoutIdx layouts })
      | _, _ => .none
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
      match extractSubslice elems fromIdx toIdx fromEnd with
      | .none => .none
      | .some subElems =>
        let stepOffOpt : Option Nat :=
          match Nat.beq fromIdx 0 with
          | true => .some 0
          | false =>
            match layoutStrideOpt with
            | .some s => .some (Nat.mul fromIdx s)
            | .none =>
              match elemTyOpt with
              | .some elemTy =>
                match tyByteSize localDecls layouts elemTy with
                | .some sz => .some (Nat.mul fromIdx sz)
                | .none => .none
              | .none =>
                match isHomogeneousUntypedFields elems with
                | true => .some (Nat.mul fromIdx (inferElemListByteStride elems))
                | false => .none
        match stepOffOpt with
        | .none => .none
        | .some stepOff =>
          let nextSubTyOpt : Option Ty :=
            match elemKindOpt with
            | .some ek =>
              .some { kind := .array ek (length subElems), layoutIdx := unresolvedLayoutIdx layouts }
            | .none => .none
          projectionChainByteOffset?
            layouts
            nextSubTyOpt
            (.some (.aggregate 0 subElems))
            .none
            (Nat.add accOff stepOff)
            localDecls
            rest
    | .some _ => .none
    | .none =>
      let arrStrideCountOpt : Option (Nat × Option Nat) :=
        match resolvedCurTyOpt with
        | .some curTy =>
          match LayoutTable.lookup layouts curTy.layoutIdx with
          | .some { fields := .array stride count, .. } =>
            .some (count, .some stride.bytes)
          | _ =>
            match curTy.kind with
            | .array ek arrLen =>
              let fbTy :=
                match elemTyOpt with
                | .some et => et
                | .none => { kind := ek, layoutIdx := unresolvedLayoutIdx layouts }
              .some (arrLen, tyByteSize localDecls layouts fbTy)
            | _ => .none
        | .none => .none
      match arrStrideCountOpt with
      | .none => .none
      | .some (arrLen, strideOpt) =>
        match Nat.ble toIdx arrLen with
        | false => .none
        | true =>
          let endIdx :=
            match fromEnd with
            | true => Nat.sub arrLen toIdx
            | false => toIdx
          match Nat.ble fromIdx endIdx with
          | false => .none
          | true =>
            let subLen := Nat.sub endIdx fromIdx
            let stepOffOpt : Option Nat :=
              match Nat.beq fromIdx 0 with
              | true => .some 0
              | false =>
                match strideOpt with
                | .some elemSz => .some (Nat.mul fromIdx elemSz)
                | .none => .none
            match stepOffOpt with
            | .none => .none
            | .some stepOff =>
              let nextSubTyOpt : Option Ty :=
                match elemKindOpt with
                | .some ek =>
                  .some { kind := .array ek subLen, layoutIdx := unresolvedLayoutIdx layouts }
                | .none => .none
              projectionChainByteOffset?
                layouts
                nextSubTyOpt
                .none
                .none
                (Nat.add accOff stepOff)
                localDecls
                rest
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
  | true, false =>
    let cleanRest := stripTransparentProjections restProj
    let staticSubOk : Bool :=
      match projHasSubslice cleanRest, pointeeTyOpt with
      | true, .some pt =>
        match resolveProjectedTyResolved localDecls layouts pt cleanRest with
        | .some _ => true
        | .none => false
      | _, _ => true
    match staticSubOk with
    | false => .none
    | true =>
      let candidateOpt : Option (List ProjectionElem) :=
        match startsWithArrayOrSliceProj cleanRest, pointeeTyOpt with
        | true, .some { kind := .array ptEk ptArrLen, .. } =>
          match readProjectedValue indexLocals targetRootVal normTargetProj with
          | .ok (.aggregate 0 backingElems) =>
            let containerElemIsPtEk : Bool :=
              match
                resolveSeqContainerElemTyOpt
                  localDecls
                  layouts
                  entry.targetLocal
                  normTargetProj
                  backingElems
                  (resolveSeqContainerElemByteStride
                    localDecls
                    layouts
                    entry.targetLocal
                    normTargetProj
                    backingElems)
              with
              | .some et => rigidTyEq et.kind ptEk
              | .none => true
            match containerElemIsPtEk with
            | false => .some rawFullProj
            | true =>
              match Nat.ble ptArrLen (length backingElems) with
              | false => .none
              | true =>
                match Nat.beq ptArrLen (length backingElems) with
                | true => .some rawFullProj
                | false =>
                  let winTail := ProjectionElem.subslice 0 ptArrLen false :: cleanRest
                  let combined :=
                    match normTargetProj with
                    | .nil => winTail
                    | ph :: pt => ph :: appendProjections pt winTail
                  .some (normalizeSubsliceProjections combined)
          | _ => .some rawFullProj
        | _, _ => .some rawFullProj
      match candidateOpt with
      | .none => .none
      | .some candProj =>
        match projHasSubslice candProj with
        | false => .some (candProj, 0)
        | true =>
          let cleanCand := stripTransparentProjections candProj
          match
            Bool.and
              (forwardSubslicesOrdered cleanCand)
              (subsliceChainValidOnVal
                indexLocals
                targetRootVal
                (normalizeSubsliceProjections cleanCand))
          with
          | true => .some (candProj, 0)
          | false => .none
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
            let spansMultipleElems : Bool :=
              match restProj, effReqBytesOpt with
              | .nil, .some reqB =>
                Bool.and (Nat.ble 1 elemSz) (Nat.ble (.succ elemSz) reqB)
              | _, _ => false
            match spansMultipleElems with
            | true => .none
            | false =>
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
                let cleanRest := stripTransparentProjections restProj
                let spanPointeeArr : Option Nat :=
                  match startsWithArrayOrSliceProj cleanRest, pointeeTyOpt, elemTyOpt with
                  | true, .some { kind := .array ptEk ptArrLen, .. }, .some et =>
                    match rigidTyEq et.kind ptEk with
                    | true => .some ptArrLen
                    | false => .none
                  | _, _, _ => .none
                match spanPointeeArr with
                | .some ptArrLen =>
                  let endIdx := Nat.add idx ptArrLen
                  let staticSubOk : Bool :=
                    match projHasSubslice cleanRest, pointeeTyOpt with
                    | true, .some pt =>
                      match resolveProjectedTyResolved localDecls layouts pt cleanRest with
                      | .some _ => true
                      | .none => false
                    | _, _ => true
                  match Bool.and staticSubOk (Nat.ble endIdx (length elems)) with
                  | false => .none
                  | true =>
                    let winProj := ProjectionElem.subslice idx endIdx false :: cleanRest
                    let combined :=
                      match initProj with
                      | .nil => winProj
                      | ph :: pt => ph :: appendProjections pt winProj
                    let normCombined := normalizeSubsliceProjections combined
                    match
                      Bool.and
                        (forwardSubslicesOrdered cleanRest)
                        (subsliceChainValidOnVal indexLocals targetRootVal normCombined)
                    with
                    | true => .some (normCombined, 0)
                    | false => .none
                | .none =>
                  let elemProj := ProjectionElem.constantIndex idx 0 false :: restProj
                  let combined :=
                    match initProj with
                    | .nil => elemProj
                    | ph :: pt => ph :: appendProjections pt elemProj
                  let normCombined := normalizeSubsliceProjections combined
                  match projHasSubslice restProj with
                  | false => .some (normCombined, 0)
                  | true =>
                    match
                      Bool.and
                        (forwardSubslicesOrdered cleanRest)
                        (subsliceChainValidOnVal indexLocals targetRootVal normCombined)
                    with
                    | true => .some (normCombined, 0)
                    | false => .none
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
                  let spansMultipleElems : Bool :=
                    match restProj, effReqBytesOpt with
                    | .nil, .some reqB =>
                      Bool.and (Nat.ble 1 elemSz) (Nat.ble (.succ elemSz) reqB)
                    | _, _ => false
                  match spansMultipleElems with
                  | true => .none
                  | false =>
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
                      let cleanRest := stripTransparentProjections restProj
                      let spanPointeeArr : Option Nat :=
                        match startsWithArrayOrSliceProj cleanRest, pointeeTyOpt, elemTyOpt with
                        | true, .some { kind := .array ptEk ptArrLen, .. }, .some et =>
                          match rigidTyEq et.kind ptEk with
                          | true => .some ptArrLen
                          | false => .none
                        | _, _, _ => .none
                      match spanPointeeArr with
                      | .some ptArrLen =>
                        let endIdx := Nat.add elemOffset ptArrLen
                        let staticSubOk : Bool :=
                          match projHasSubslice cleanRest, pointeeTyOpt with
                          | true, .some pt =>
                            match resolveProjectedTyResolved localDecls layouts pt cleanRest with
                            | .some _ => true
                            | .none => false
                          | _, _ => true
                        match Bool.and staticSubOk (Nat.ble endIdx (length elems)) with
                        | false => .none
                        | true =>
                          let winProj := ProjectionElem.subslice elemOffset endIdx false :: cleanRest
                          let combined :=
                            match normTargetProj with
                            | .nil => winProj
                            | ph :: pt => ph :: appendProjections pt winProj
                          let normCombined := normalizeSubsliceProjections combined
                          match
                            Bool.and
                              (forwardSubslicesOrdered cleanRest)
                              (subsliceChainValidOnVal indexLocals targetRootVal normCombined)
                          with
                          | true => .some (normCombined, 0)
                          | false => .none
                      | .none =>
                        match endsWithSubslice normTargetProj, cleanRest with
                        | false, .subslice relFrom relTo false :: tailProj =>
                          let absFrom := Nat.add elemOffset relFrom
                          let absTo := Nat.add elemOffset relTo
                          match
                            Bool.and
                              (Nat.ble relFrom relTo)
                              (Nat.ble absTo (length elems))
                          with
                          | false => .none
                          | true =>
                            let subTail := ProjectionElem.subslice absFrom absTo false :: tailProj
                            let combined :=
                              match normTargetProj with
                              | .nil => subTail
                              | ph :: pt => ph :: appendProjections pt subTail
                            let normCombined := normalizeSubsliceProjections combined
                            match
                              Bool.and
                                (forwardSubslicesOrdered tailProj)
                                (subsliceChainValidOnVal indexLocals targetRootVal normCombined)
                            with
                            | true => .some (normCombined, 0)
                            | false => .none
                        | _, _ =>
                          let elemProj := ProjectionElem.constantIndex elemOffset 0 false :: restProj
                          let combined :=
                            match normTargetProj with
                            | .nil => elemProj
                            | ph :: pt => ph :: appendProjections pt elemProj
                          let normCombined := normalizeSubsliceProjections combined
                          match projHasSubslice restProj with
                          | false => .some (normCombined, 0)
                          | true =>
                            match
                              Bool.and
                                (forwardSubslicesOrdered cleanRest)
                                (subsliceChainValidOnVal indexLocals targetRootVal normCombined)
                            with
                            | true => .some (normCombined, 0)
                            | false => .none
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
Fold exact tuple element alignments when every element kind has a statically
known alignment (`.none` if any element is an unlaid-out ADT/closure).
-/
@[reducible]
def foldTupleMaxExactAlign?
    (recKind : RigidTy → Option Nat)
    (acc : Nat) :
    List RigidTy → Option Nat
  | .nil => .some acc
  | fk :: rest =>
    match recKind fk with
    | .none => .none
    | .some fa =>
      let next :=
        match Nat.ble acc fa with
        | true => fa
        | false => acc
      foldTupleMaxExactAlign? recKind next rest

/--
Compute the exact guaranteed ABI byte alignment of `ty` when known from
`layouts`, `tyKindByteAlign`, or `localDecls` (returning `.none` for ADTs,
closures, dynamic trait objects, and foreign types that have no `TypeLayout`
entry, rather than conservatively defaulting their container alignment to `1`).
-/
@[reducible]
def tyExactByteAlignAux
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Option Nat
  | .zero, _ => .none
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
              Bool.and
                (Bool.not (isUnresolvedLayoutIdx layouts rTy.layoutIdx))
                (Nat.beq l.size.bytes sz)
            | _, _ => false
        match ok with
        | false => .none
        | true =>
          match Nat.ble 1 l.align.bytes with
          | true => .some l.align.bytes
          | false => .some 1
    match directLayoutAlignOpt with
    | .some a => .some a
    | .none =>
      match tyKindByteAlign layouts rTy.kind with
      | .some a =>
        match Nat.ble 1 a with
        | true => .some a
        | false => .some 1
      | .none =>
        match findArrayElemStrideAndAlign? layouts localDecls rTy.kind with
        | .some (_, a) =>
          match Nat.ble 1 a with
          | true => .some a
          | false => .some 1
        | .none =>
          match rTy.kind with
          | .array elem _ | .slice elem =>
            tyExactByteAlignAux
              localDecls
              layouts
              fuel
              { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
          | .tuple (k :: ks) =>
            foldTupleMaxExactAlign?
              (fun fk =>
                tyExactByteAlignAux
                  localDecls
                  layouts
                  fuel
                  { kind := fk, layoutIdx := unresolvedLayoutIdx layouts })
              1
              (k :: ks)
          | _ => .none

@[reducible]
def tyExactByteAlign?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option Nat :=
  tyExactByteAlignAux localDecls layouts 8 ty

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
Walk `remProj` from `(curTyOpt, curValOpt)` to verify that the address
`addr(entry.targetLocal, entry.targetProjection) + offsetBytes` is guaranteed
`reqAlign`-aligned in every execution:
- At any non-downcast container `curTy` with `tyExactByteAlign? = .some encAlign`:
  - if `reqAlign > encAlign`, returns `false` immediately (no fixed offset inside
    an `encAlign`-aligned allocation can be `reqAlign`-aligned across all valid
    stack placements);
  - otherwise, if `projectionChainByteOffset?` computes the exact byte offset
    `relOff` of `remProj` within `curTy`, checks `(relOff + offsetBytes) % reqAlign = 0`.
- When `curTy` has unknown alignment (e.g., an ADT local without a `TypeLayout`
  entry) or `projectionChainByteOffset?` cannot resolve an unlaid-out outer
  container (e.g., an unlaid-out heterogeneous `repr(Rust)` tuple), steps one
  projection into the inner place and re-checks from that sub-place.
-/
def checkTargetPlaceAlignWalk
    (targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (reqAlign : Nat)
    (offsetBytes : Nat)
    (curTyOpt : Option Ty)
    (curValOpt : Option Value)
    (activeVariant : Option VariantIdx) :
    List ProjectionElem → Bool
  | .nil =>
    match activeVariant, curTyOpt with
    | .none, .some curTy =>
      match tyExactByteAlign? targetDecls layouts curTy with
      | .none => true
      | .some encAlign =>
        match Nat.ble reqAlign encAlign with
        | false => false
        | true =>
          let (_, rem) := divModBytesAux offsetBytes offsetBytes reqAlign 0
          Nat.beq rem 0
    | _, _ => true
  | projElem :: rest =>
    let stepCheckOpt : Option Bool :=
      match activeVariant, curTyOpt with
      | .none, .some curTy =>
        match tyExactByteAlign? targetDecls layouts curTy with
        | .none => .none
        | .some encAlign =>
          match Nat.ble reqAlign encAlign with
          | false => .some false
          | true =>
            match
              projectionChainByteOffset?
                layouts
                (.some curTy)
                curValOpt
                .none
                0
                targetDecls
                (projElem :: rest)
            with
            | .some relOff =>
              let absOff := Nat.add relOff offsetBytes
              let (_, rem) := divModBytesAux absOff absOff reqAlign 0
              .some (Nat.beq rem 0)
            | .none => .none
      | _, _ => .none
    match stepCheckOpt with
    | .some res => res
    | .none =>
      match projElem with
      | .opaqueCast castTy =>
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          (.some (resolveTyWithLocalDecls targetDecls layouts castTy))
          curValOpt
          .none
          rest
      | .unwrapUnsafeBinder innerTy =>
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          (.some (resolveTyWithLocalDecls targetDecls layouts innerTy))
          curValOpt
          .none
          rest
      | .downcast _ varIdx =>
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          curTyOpt
          curValOpt
          (.some varIdx)
          rest
      | .field fieldIdx fieldTy =>
        let resolvedCurTyOpt : Option Ty :=
          match curTyOpt with
          | .some rawCurTy => .some (resolveTyWithLocalDecls targetDecls layouts rawCurTy)
          | .none => .none
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
        let nextFieldTy := resolveTyWithLocalDecls targetDecls layouts rawNextFieldTy
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          (.some nextFieldTy)
          nextValOpt
          .none
          rest
      | .constantIndex rawIdx _ fromEnd =>
        let resolvedCurTyOpt : Option Ty :=
          match curTyOpt with
          | .some rawCurTy => .some (resolveTyWithLocalDecls targetDecls layouts rawCurTy)
          | .none => .none
        let nextElemTyOpt : Option Ty :=
          match resolvedCurTyOpt with
          | .some curTy =>
            let ekOpt : Option RigidTy :=
              match curTy.kind with
              | .array ek _ => .some ek
              | .slice ek => .some ek
              | _ => .none
            match ekOpt with
            | .none => .none
            | .some ek =>
              match LayoutTable.lookup layouts curTy.layoutIdx with
              | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
                .some { kind := ek, layoutIdx := flIdx }
              | _ =>
                .some
                  (resolveTyWithLocalDecls
                    targetDecls
                    layouts
                    { kind := ek, layoutIdx := unresolvedLayoutIdx layouts })
          | .none => .none
        let nextValOpt : Option Value :=
          match curValOpt with
          | .some (.aggregate 0 elems) =>
            let arrLen := length elems
            let idxOpt : Option Nat :=
              match fromEnd with
              | false => .some rawIdx
              | true =>
                match Bool.and (Nat.ble 1 rawIdx) (Nat.ble rawIdx arrLen) with
                | true => .some (Nat.sub arrLen rawIdx)
                | false => .none
            match idxOpt with
            | .some idx => get? elems idx
            | .none => .none
          | _ => .none
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          nextElemTyOpt
          nextValOpt
          .none
          rest
      | .subslice fromIdx toIdx fromEnd =>
        let resolvedCurTyOpt : Option Ty :=
          match curTyOpt with
          | .some rawCurTy => .some (resolveTyWithLocalDecls targetDecls layouts rawCurTy)
          | .none => .none
        let elemKindOpt : Option RigidTy :=
          match resolvedCurTyOpt with
          | .some { kind := .array ek _, .. } => .some ek
          | .some { kind := .slice ek, .. } => .some ek
          | _ => .none
        let nextValOpt : Option Value :=
          match curValOpt with
          | .some (.aggregate 0 elems) =>
            match extractSubslice elems fromIdx toIdx fromEnd with
            | .some subElems => .some (.aggregate 0 subElems)
            | .none => .none
          | _ => .none
        let nextSubTyOpt : Option Ty :=
          match elemKindOpt, nextValOpt with
          | .some ek, .some (.aggregate 0 subElems) =>
            .some { kind := .array ek (length subElems), layoutIdx := unresolvedLayoutIdx layouts }
          | .some ek, _ =>
            .some { kind := .slice ek, layoutIdx := unresolvedLayoutIdx layouts }
          | .none, _ => .none
        checkTargetPlaceAlignWalk
          targetDecls
          layouts
          reqAlign
          offsetBytes
          nextSubTyOpt
          nextValOpt
          .none
          rest
      | _ => true

/--
Address-level alignment check for an access whose required alignment is that of
`tyOpt`, through a stack pointer `ptrVal` whose `BorrowEntry` `entry` targets the
place `(entry.targetLocal, entry.targetProjection)` described by `targetDecls`
(the active frame's `LocalDecl`s; `.nil` for caller-frame targets, whose
declarations are not in scope, skips the check).

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
      checkTargetPlaceAlignWalk
        targetDecls
        layouts
        reqAlign
        ptrVal.offsetBytes
        (.some decl.ty)
        targetRootValOpt
        .none
        entry.targetProjection
  | _, _ => true

/--
Address-level alignment check for an access of type `tyOpt` at byte offset
`offsetBytes` within a `CapturedAllocation` `alloc`: requires
`reqAlign ≤ alloc.align.bytes` (when `alloc.align.bytes ≥ 1`) and
`offsetBytes % reqAlign = 0`.
-/
@[reducible]
def checkGlobalAllocAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (tyOpt : Option Ty)
    (alloc : CapturedAllocation)
    (offsetBytes : Nat) :
    Bool :=
  match tyOpt with
  | .none => true
  | .some ty =>
    let reqAlign := tyByteAlign localDecls layouts ty
    match Nat.ble reqAlign 1 with
    | true => true
    | false =>
      let allocAlignOk :=
        match Nat.ble 1 alloc.align.bytes with
        | false => true
        | true => Nat.ble reqAlign alloc.align.bytes
      match allocAlignOk with
      | false => false
      | true =>
        match Nat.beq offsetBytes 0 with
        | true => true
        | false =>
          let (_, rem) := divModBytesAux offsetBytes offsetBytes reqAlign 0
          Nat.beq rem 0

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
Map IEEE float `RigidTy` kinds onto same-width unsigned integer kinds for
`encodeValueToBytes` / `decodeValueFromBytes` (floats have no invalid bit
patterns and identical little-endian byte order).
-/
@[reducible]
def byteCodecScalarKind : RigidTy → RigidTy
  | .float .f16 => .uint .u16
  | .float .f32 => .uint .u32
  | .float .f64 => .uint .u64
  | .float .f128 => .uint .u128
  | k => k

@[reducible]
def mapByteCodecScalarKinds : List RigidTy → List RigidTy
  | .nil => .nil
  | k :: ks => byteCodecScalarKind k :: mapByteCodecScalarKinds ks

@[reducible]
def normalizeCodecTy (ty : Ty) : Ty :=
  match ty.kind with
  | .float fk => { kind := byteCodecScalarKind (.float fk), layoutIdx := 0 }
  | .array (.float fk) n =>
    { kind := .array (byteCodecScalarKind (.float fk)) n, layoutIdx := ty.layoutIdx }
  | .tuple ks =>
    { kind := .tuple (mapByteCodecScalarKinds ks), layoutIdx := ty.layoutIdx }
  | _ => ty

/--
`true` when `kind` is a thin pointer (`*T`, `&T` for sized `T`, or `fn(...)`).
-/
@[reducible]
def isThinPtrKind : RigidTy → Bool
  | .fnPtr _ _ _ _ => true
  | .rawPtr _ pointee | .ref _ pointee =>
    match pointee with
    | .slice _ | .str | .dynamic _ => false
    | _ => true
  | _ => false

/--
`true` when `ty` is an `.adt` whose captured `TypeLayout` in `layouts` has
`fields = .union _`.
-/
@[reducible]
def isUnionLayout (layouts : LayoutTable) (ty : Ty) : Bool :=
  match ty.kind with
  | .adt _ _ =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some { fields := .union _, .. } => true
    | _ => false
  | _ => false

/--
Test whether deref-free projection chain `proj` starting from `baseTy` projects
into at least one union `.field` (`isUnionLayout`). Returns `false` when `proj`
stops at the union root itself (`proj = .nil`), since copying or moving a whole
union value with uninitialized bytes is defined behavior in Rust.
-/
@[reducible]
def tyProjTouchesUnion
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (baseTy : Ty) :
    List ProjectionElem → Bool
  | .nil => false
  | .deref :: _ => false
  | .field fieldIdx fieldTy :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match isUnionLayout layouts rBase with
    | true => true
    | false =>
      let nextTy : Ty :=
        match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
        | false => fieldTy
        | true =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some l =>
            match l.variants with
            | .single _ =>
              match get? l.fieldLayouts fieldIdx with
              | .some flIdx => { fieldTy with layoutIdx := flIdx }
              | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
            | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
      tyProjTouchesUnion localDecls layouts nextTy rest
  | .opaqueCast castTy :: rest =>
    tyProjTouchesUnion
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
  | .unwrapUnsafeBinder innerTy :: rest =>
    tyProjTouchesUnion
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
  | .index _ :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match elemTyOf rBase with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      tyProjTouchesUnion localDecls layouts elemTy rest
    | .none => false
  | .constantIndex _ _ _ :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match elemTyOf rBase with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      tyProjTouchesUnion localDecls layouts elemTy rest
    | .none => false
  | .subslice _ _ _ :: rest =>
    tyProjTouchesUnion localDecls layouts baseTy rest
  | .downcast _ _ :: rest =>
    tyProjTouchesUnion localDecls layouts baseTy rest

/--
Test whether `p` is a non-deref projection on a local in `localDecls` that
projects into a union field (`tyProjTouchesUnion`). Reduces immediately to
`false` when `localDecls = .nil` or `p.projection = .nil`.
-/
@[reducible]
def placeTouchesUnion
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place) :
    Bool :=
  match p.projection with
  | .nil => false
  | .deref :: _ => false
  | projHead :: projTail =>
    match localDecls with
    | .nil => false
    | _ :: _ =>
      match layouts.entries with
      | .nil => false
      | _ :: _ =>
        match get? localDecls p.local_ with
        | .some decl => tyProjTouchesUnion localDecls layouts decl.ty (projHead :: projTail)
        | .none => false

/--
Structural equality on `AbstractByte` provenance pairs `Option (Nat × Nat)`.
-/
@[reducible]
def abstractByteProvEq : Option (Nat × Nat) → Option (Nat × Nat) → Bool
  | .none, .none => true
  | .some (a₁, t₁), .some (a₂, t₂) =>
    Bool.and (Nat.beq a₁ a₂) (Nat.beq t₁ t₂)
  | _, _ => false

/--
Structural equality on `AbstractByte`.
-/
@[reducible]
def abstractByteEq : AbstractByte → AbstractByte → Bool
  | .uninit, .uninit => true
  | .init b₁ p₁, .init b₂ p₂ =>
    Bool.and
      (Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat)
      (abstractByteProvEq p₁ p₂)
  | _, _ => false

/--
Element-wise structural equality on `List AbstractByte`.
-/
def abstractByteListEq : List AbstractByte → List AbstractByte → Bool
  | .nil, .nil => true
  | b₁ :: r₁, b₂ :: r₂ =>
    Bool.and (abstractByteEq b₁ b₂) (abstractByteListEq r₁ r₂)
  | _, _ => false

/--
Encode a `List AbstractByte` image as per-byte `Value`s for the optional
trailing raw-byte overlay slot of a union aggregate (`.scalar ⟨0, 0⟩` for
`.uninit`, `.scalar ⟨b, 1⟩` for `.init b .none`, and `.ptr { allocId := a,
offsetBytes := b } 1` for `.init b (.some (a, _))`).
-/
def encodeRawAbstractByteVals : List AbstractByte → List Value
  | .nil => .nil
  | .uninit :: rest => .scalar ⟨0, 0⟩ :: encodeRawAbstractByteVals rest
  | .init b .none :: rest =>
    .scalar ⟨b.toBitVec.toNat, 1⟩ :: encodeRawAbstractByteVals rest
  | .init b (.some (a, _)) :: rest =>
    .ptr { allocId := a, offsetBytes := b.toBitVec.toNat } 1 ::
      encodeRawAbstractByteVals rest

/--
Overlay per-byte `Value`s encoded by `encodeRawAbstractByteVals` onto `buf`.
-/
def overlayRawAbstractByteVals :
    List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, buf => .some buf
  | _, .nil => .none
  | .scalar ⟨0, 0⟩ :: vRest, _ :: bRest =>
    match overlayRawAbstractByteVals vRest bRest with
    | .some tail => .some (.uninit :: tail)
    | .none => .none
  | .scalar ⟨bits, 1⟩ :: vRest, _ :: bRest =>
    match overlayRawAbstractByteVals vRest bRest with
    | .some tail => .some (.init (UInt8.ofNat bits) .none :: tail)
    | .none => .none
  | .ptr p 1 :: vRest, _ :: bRest =>
    match overlayRawAbstractByteVals vRest bRest with
    | .some tail =>
      .some (.init (UInt8.ofNat p.offsetBytes) (.some (p.allocId, p.tag)) :: tail)
    | .none => .none
  | _, _ => .none

/--
Construct a list of `n` copies of `b : Bool`.
-/
def replicateBool : Nat → Bool → List Bool
  | .zero, _ => .nil
  | .succ k, b => b :: replicateBool k b

/--
Overwrite `patch` into `buf` starting at byte offset `offset`.
-/
def writeBoolsAt :
    List Bool → Nat → List Bool → Option (List Bool)
  | buf, _, .nil => .some buf
  | .nil, _, _ :: _ => .none
  | _ :: bufRest, .zero, w :: wRest =>
    match writeBoolsAt bufRest .zero wRest with
    | .some tail' => .some (w :: tail')
    | .none => .none
  | b :: bufRest, .succ off, wList =>
    match writeBoolsAt bufRest off wList with
    | .some tail' => .some (b :: tail')
    | .none => .none

/--
Write field value masks at `offsets` into `buf` using `fieldLayouts`.
-/
def maskArbitrarySlotsIntoBufAux
    (maskSlot : Nat → List Bool) :
    List Size → List Nat → List Bool → List Bool
  | .nil, _, buf => buf
  | _, .nil, buf => buf
  | off :: offRest, flIdx :: flRest, buf =>
    let fMask := maskSlot flIdx
    let buf' :=
      match writeBoolsAt buf off.bytes fMask with
      | .some b => b
      | .none => buf
    maskArbitrarySlotsIntoBufAux maskSlot offRest flRest buf'

/--
Write array element value masks at `strideBytes` intervals starting at
`runningOff` into `buf`.
-/
def maskArraySlotsIntoBufAux
    (elemMask : List Bool)
    (strideBytes runningOff : Nat) :
    Nat → List Bool → List Bool
  | .zero, buf => buf
  | .succ rem, buf =>
    let buf' :=
      match writeBoolsAt buf runningOff elemMask with
      | .some b => b
      | .none => buf
    maskArraySlotsIntoBufAux elemMask strideBytes (Nat.add runningOff strideBytes) rem buf'

/--
Compute the per-byte non-padding mask of `TypeLayout` at `layoutIdx` in
`layouts`: `true` at bytes belonging to a field or primitive/union payload, and
`false` at inter-field or trailing struct/array padding bytes.
-/
def layoutValueMaskAux :
    Nat → LayoutTable → Nat → List Bool
  | .zero, _, _ => .nil
  | .succ fuel', layouts, layoutIdx =>
    let maskChild := fun (cIdx : Nat) =>
      layoutValueMaskAux fuel' layouts cIdx
    match LayoutTable.lookup layouts layoutIdx with
    | .none => .nil
    | .some l =>
      match l.isUninhabited with
      | true => .nil
      | false =>
        match l.fields with
        | .arbitrary offsets _ =>
          match l.variants with
          | .single _ =>
            match Nat.beq (length l.fieldLayouts) (length offsets) with
            | true =>
              maskArbitrarySlotsIntoBufAux
                maskChild
                offsets
                l.fieldLayouts
                (replicateBool l.size.bytes false)
            | false => replicateBool l.size.bytes true
          | _ => replicateBool l.size.bytes true
        | .array stride count =>
          match l.fieldLayouts with
          | elemFlIdx :: _ =>
            maskArraySlotsIntoBufAux
              (maskChild elemFlIdx)
              stride.bytes
              0
              count
              (replicateBool l.size.bytes false)
          | .nil => replicateBool l.size.bytes true
        | _ => replicateBool l.size.bytes true

mutual
/--
`true` when `v` contains a `.unit` or zero-width uninitialized scalar leaf.
-/
def valueContainsUnit : Value → Bool
  | .unit => true
  | .scalar ⟨_, 0⟩ => true
  | .aggregate _ fs => valueListContainsUnit fs
  | _ => false

def valueListContainsUnit : List Value → Bool
  | .nil => false
  | v :: rest =>
    match valueContainsUnit v with
    | true => true
    | false => valueListContainsUnit rest
end

/--
`true` when `sub` appears as an in-order subsequence of `full` under
`abstractByteEq`.
-/
def abstractByteSubseq : List AbstractByte → List AbstractByte → Bool
  | .nil, _ => true
  | _ :: _, .nil => false
  | a :: aRest, b :: bRest =>
    match abstractByteEq a b with
    | true => abstractByteSubseq aRest bRest
    | false => abstractByteSubseq (a :: aRest) bRest

/--
Merge union slot image `(slotBytes, slotMask)` (stored at offset `0`) into
`(accBytes, accMask)`, returning `.none` when some byte covered as a non-padding
value byte by both sources (`accMask = true` and `effSlotMask = true`) differs
under `abstractByteEq` (including `.uninit` vs `.init`).
-/
def mergeMaskedAbstractBytes :
    List AbstractByte → List Bool → List AbstractByte → List Bool →
      Option (List AbstractByte × List Bool)
  | accB, accM, .nil, _ => .some (accB, accM)
  | .nil, _, _ :: _, _ => .none
  | _, .nil, _ :: _, _ => .none
  | a :: aRest, am :: amRest, b :: bRest, bmList =>
    let (bm, bmRest) : Bool × List Bool :=
      match bmList with
      | m :: mRest => (m, mRest)
      | .nil => (true, .nil)
    let effBm : Bool :=
      match b with
      | .init _ _ => true
      | .uninit => bm
    match mergeMaskedAbstractBytes aRest amRest bRest bmRest with
    | .none => .none
    | .some (tailB, tailM) =>
      match effBm with
      | false => .some (a :: tailB, am :: tailM)
      | true =>
        match am with
        | false => .some (b :: tailB, true :: tailM)
        | true =>
          match abstractByteEq a b with
          | true => .some (a :: tailB, true :: tailM)
          | false => .none

/--
Split a union field list into its `count` typed slots and the optional trailing
raw-byte overlay values (`.none` when the list is malformed).
-/
def splitUnionTypedAndOverlay :
    Nat → List Value → Option (List Value × Option (List Value))
  | .zero, .nil => .some (.nil, .none)
  | .zero, .aggregate 0 rawVals :: .nil => .some (.nil, .some rawVals)
  | .zero, _ :: _ => .none
  | .succ _, .nil => .some (.nil, .none)
  | .succ k, v :: rest =>
    match splitUnionTypedAndOverlay k rest with
    | .some (typedVals, overlayOpt) => .some (v :: typedVals, overlayOpt)
    | .none => .none

/--
`true` when `entries` contains a non-zero-sized multi-variant enum layout whose
variant `0` has `0` fields (so `.aggregate 0 .nil` in a union with
`fieldLayouts = .nil` may represent a non-ZST enum variant `E::A` rather than a
zero-sized `()`/`ZST`).
-/
def layoutEntriesHaveNonZstFieldlessEnum0 : List TypeLayout → Bool
  | .nil => false
  | l :: rest =>
    let isNonZstEnum0 : Bool :=
      match Nat.ble 1 l.size.bytes, l.variants with
      | true, .multiple _ _ (.arbitrary .nil _ :: _) => true
      | _, _ => false
    match isNonZstEnum0 with
    | true => true
    | false => layoutEntriesHaveNonZstFieldlessEnum0 rest

/--
Count the typed union slots among the first `count` entries of a union field
list whose value occupies storage alongside a raw-byte overlay: `.unit`
placeholders are empty, and a field-less `.aggregate 0 .nil` is empty when its
field layout (from `fieldLayouts`) is zero-sized or absent (while
`layoutFreeAmbiguous` in `encodeUnionSlotsIntoBufAux` and the overlay check in
`mergeUnionTypedSlotsAux` validate `fieldLayouts = .nil` enum variants).
-/
def unionNonUnitNonZstTypedSlotCount (layouts : LayoutTable) :
    Nat → List Nat → List Value → Nat
  | .zero, _, _ => 0
  | _, _, .nil => 0
  | .succ k, flIdxs, v :: rest =>
    let (flIdxOpt, nextIdxs) : Option Nat × List Nat :=
      match flIdxs with
      | f :: fRest => (.some f, fRest)
      | .nil => (.none, .nil)
    let slotEmpty : Bool :=
      match v, flIdxOpt with
      | .unit, _ => true
      | .aggregate 0 .nil, .none => true
      | .aggregate 0 .nil, .some flIdx =>
        match LayoutTable.lookup layouts flIdx with
        | .some fl => Nat.beq fl.size.bytes 0
        | .none => true
      | _, _ => false
    match slotEmpty with
    | true => unionNonUnitNonZstTypedSlotCount layouts k nextIdxs rest
    | false => .succ (unionNonUnitNonZstTypedSlotCount layouts k nextIdxs rest)

/--
Merge the images of the non-`.unit` typed union slots `fieldVals` into
`(buf, bufMask)` (`mergeMaskedAbstractBytes`), using each slot's layout index
from `fieldLayouts`.
-/
def mergeUnionTypedSlotsAux
    (layouts : LayoutTable)
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat)
    (hasOverlay : Bool)
    (unionSize : Nat) :
    List Nat → List Value → List AbstractByte → List Bool → Option (List AbstractByte)
  | _, .nil, buf, _ => .some buf
  | flIdxs, fv :: vRest, buf, bufMask =>
    let (flIdxOpt, nextIdxs) : Option Nat × List Nat :=
      match flIdxs with
      | f :: fRest => (.some f, fRest)
      | .nil => (.none, .nil)
    match fv with
    | .unit =>
      mergeUnionTypedSlotsAux
        layouts
        encodeSlot
        fallbackLayoutIdx
        hasOverlay
        unionSize
        nextIdxs
        vRest
        buf
        bufMask
    | _ =>
      match flIdxOpt with
      | .some flIdx =>
        match encodeSlot flIdx fv with
        | .none => .none
        | .some fBytes =>
          let fMask := layoutValueMaskAux 8 layouts flIdx
          match mergeMaskedAbstractBytes buf bufMask fBytes fMask with
          | .none => .none
          | .some (buf', bufMask') =>
            mergeUnionTypedSlotsAux
              layouts
              encodeSlot
              fallbackLayoutIdx
              hasOverlay
              unionSize
              nextIdxs
              vRest
              buf'
              bufMask'
      | .none =>
        match fv, hasOverlay with
        | .aggregate varIdx .nil, true =>
          let isStaleEnumSlot : Bool :=
            match varIdx with
            | .zero => layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries
            | .succ _ => true
          match isStaleEnumSlot with
          | false =>
            mergeUnionTypedSlotsAux
              layouts
              encodeSlot
              fallbackLayoutIdx
              hasOverlay
              unionSize
              nextIdxs
              vRest
              buf
              bufMask
          | true => .none
        | .aggregate _ (_ :: _), true =>
          match encodeUntypedValueToBytes defaultCodecFuel fv with
          | .none => .none
          | .some .nil =>
            match valueContainsUnit fv with
            | false =>
              mergeUnionTypedSlotsAux
                layouts
                encodeSlot
                fallbackLayoutIdx
                hasOverlay
                unionSize
                nextIdxs
                vRest
                buf
                bufMask
            | true =>
              let uninitBytes := replicateUninitBytes unionSize
              let fullMask := replicateBool unionSize true
              match mergeMaskedAbstractBytes buf bufMask uninitBytes fullMask with
              | .none => .none
              | .some (buf', bufMask') =>
                mergeUnionTypedSlotsAux
                  layouts
                  encodeSlot
                  fallbackLayoutIdx
                  hasOverlay
                  unionSize
                  nextIdxs
                  vRest
                  buf'
                  bufMask'
          | .some (b :: bs) =>
            match abstractByteSubseq (b :: bs) buf with
            | false => .none
            | true =>
              mergeUnionTypedSlotsAux
                layouts
                encodeSlot
                fallbackLayoutIdx
                hasOverlay
                unionSize
                nextIdxs
                vRest
                buf
                bufMask
        | _, _ =>
          match encodeSlot fallbackLayoutIdx fv with
          | .none => .none
          | .some .nil =>
            match valueContainsUnit fv with
            | false =>
              mergeUnionTypedSlotsAux
                layouts
                encodeSlot
                fallbackLayoutIdx
                hasOverlay
                unionSize
                nextIdxs
                vRest
                buf
                bufMask
            | true =>
              let uninitBytes := replicateUninitBytes unionSize
              let fullMask := replicateBool unionSize true
              match mergeMaskedAbstractBytes buf bufMask uninitBytes fullMask with
              | .none => .none
              | .some (buf', bufMask') =>
                mergeUnionTypedSlotsAux
                  layouts
                  encodeSlot
                  fallbackLayoutIdx
                  hasOverlay
                  unionSize
                  nextIdxs
                  vRest
                  buf'
                  bufMask'
          | .some (b :: bs) =>
            let fBytes := b :: bs
            let fMask := replicateBool (length fBytes) true
            match mergeMaskedAbstractBytes buf bufMask fBytes fMask with
            | .none => .none
            | .some (buf', bufMask') =>
              mergeUnionTypedSlotsAux
                layouts
                encodeSlot
                fallbackLayoutIdx
                hasOverlay
                unionSize
                nextIdxs
                vRest
                buf'
                bufMask'

/--
Count the non-`.unit` values among the first `count` typed slots of a union
field list.
-/
def unionNonUnitTypedSlotCount : Nat → List Value → Nat
  | .zero, _ => 0
  | _, .nil => 0
  | .succ k, .unit :: rest => unionNonUnitTypedSlotCount k rest
  | .succ k, _ :: rest => .succ (unionNonUnitTypedSlotCount k rest)

/--
`true` when `vals` contains a field-less aggregate `.aggregate _ .nil`.
-/
def valueListHasEmptyAggregate : List Value → Bool
  | .nil => false
  | .aggregate _ .nil :: _ => true
  | _ :: rest => valueListHasEmptyAggregate rest

/--
`true` when union slot value `v` has no faithful layout-free byte image (used
when the union's `fieldLayouts` are absent): an aggregate with fields, a
field-less non-zero variant (an enum tag), or a field-less variant `0` while
`layouts` contains a non-zero-sized enum whose variant `0` is field-less (so `v`
may be that enum's tag rather than a zero-sized value).
-/
def unionSlotLacksLayoutFreeImage (layouts : LayoutTable) : Value → Bool
  | .aggregate 0 .nil => layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries
  | .aggregate _ .nil => true
  | .aggregate _ (_ :: _) => true
  | _ => false

/--
`true` when some value in `vals` satisfies `unionSlotLacksLayoutFreeImage`.
-/
def unionTypedSlotsLackLayoutFreeImage (layouts : LayoutTable) : List Value → Bool
  | .nil => false
  | v :: rest =>
    match unionSlotLacksLayoutFreeImage layouts v with
    | true => true
    | false => unionTypedSlotsLackLayoutFreeImage layouts rest

/--
Count the typed slots among the first `count` entries of a union field list
whose layout-free value may occupy storage: `.unit` placeholders are empty, and
a field-less `.aggregate 0 .nil` is empty unless `hasNonZstFieldlessEnum0`
(`layoutEntriesHaveNonZstFieldlessEnum0`), in which case it may be a
non-zero-sized enum's tag.
-/
def unionLayoutFreeOccupiedSlotCount (hasNonZstFieldlessEnum0 : Bool) :
    Nat → List Value → Nat
  | .zero, _ => 0
  | _, .nil => 0
  | .succ k, .unit :: rest =>
    unionLayoutFreeOccupiedSlotCount hasNonZstFieldlessEnum0 k rest
  | .succ k, .aggregate 0 .nil :: rest =>
    match hasNonZstFieldlessEnum0 with
    | true => .succ (unionLayoutFreeOccupiedSlotCount hasNonZstFieldlessEnum0 k rest)
    | false => unionLayoutFreeOccupiedSlotCount hasNonZstFieldlessEnum0 k rest
  | .succ k, _ :: rest =>
    .succ (unionLayoutFreeOccupiedSlotCount hasNonZstFieldlessEnum0 k rest)

/--
Encode a `count`-slot union field list `fieldVals` of byte size `unionSize`:
starts from the trailing raw-byte overlay image (if any, else all `.uninit`)
and merges every non-`.unit` typed slot image into it, failing (`.none`) when
two slots, or a slot and the overlay, disagree on a non-padding byte (including
when a stale union-unaware write stores an uninitialized value into a slot while
another slot or the overlay holds initialized bytes).
-/
def encodeUnionSlotsIntoBufAux
    (layouts : LayoutTable)
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat)
    (count : Nat)
    (fieldLayouts : List Nat)
    (fieldVals : List Value)
    (unionSize : Nat) :
    Option (List AbstractByte) :=
  match splitUnionTypedAndOverlay count fieldVals with
  | .none => .none
  | .some (typedVals, overlayOpt) =>
    -- Without `fieldLayouts`, a slot holding an aggregate (or a field-less
    -- variant that may be an enum tag) has no faithful layout-free image
    -- (`unionSlotLacksLayoutFreeImage`), so its agreement with a second
    -- storage-occupying slot cannot be checked: fail closed.
    let layoutFreeAmbiguous : Bool :=
      match fieldLayouts with
      | _ :: _ => false
      | .nil =>
        Bool.and
          (Nat.ble
            2
            (unionLayoutFreeOccupiedSlotCount
              (layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries)
              count
              typedVals))
          (unionTypedSlotsLackLayoutFreeImage layouts typedVals)
    match layoutFreeAmbiguous, overlayOpt with
    | true, _ => .none
    | false, .none =>
      mergeUnionTypedSlotsAux
        layouts
        encodeSlot
        fallbackLayoutIdx
        false
        unionSize
        fieldLayouts
        typedVals
        (replicateUninitBytes unionSize)
        (replicateBool unionSize false)
    | false, .some rawVals =>
      match Nat.ble (unionNonUnitNonZstTypedSlotCount layouts count fieldLayouts typedVals) 1 with
      | false => .none
      | true =>
        match overlayRawAbstractByteVals rawVals (replicateUninitBytes unionSize) with
        | .none => .none
        | .some rawImage =>
          mergeUnionTypedSlotsAux
            layouts
            encodeSlot
            fallbackLayoutIdx
            true
            unionSize
            fieldLayouts
            typedVals
            rawImage
            (replicateBool unionSize true)

/--
`true` when a `count`-slot union field list may hold mutually inconsistent
slots (a raw-byte overlay is present, or at least two typed slots are
non-`.unit`), so a direct slot read must first validate the union image.
-/
@[reducible]
def unionNeedsConsistencyCheck (count : Nat) (fields : List Value) : Bool :=
  Bool.or
    (Nat.blt count (length fields))
    (Nat.ble 2 (unionNonUnitTypedSlotCount count fields))

/--
Write struct/tuple field values in `fieldVals` at `offsets` into `buf` using
each field's layout index from `fieldLayouts`.
-/
def encodeArbitrarySlotsIntoBufAux
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat) :
    List Size → List Nat → List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, _, .nil, buf => .some buf
  | .nil, _, _ :: _, _ => .none
  | _ :: _, _, .nil, _ => .none
  | off :: offRest, flIdxs, fv :: vRest, buf =>
    let (flIdx, nextIdxs) :=
      match flIdxs with
      | f :: fRest => (f, fRest)
      | .nil => (fallbackLayoutIdx, .nil)
    match encodeSlot flIdx fv with
    | .none => .none
    | .some fBytes =>
      match writeAbstractBytesAt buf off.bytes fBytes with
      | .none => .none
      | .some buf' =>
        encodeArbitrarySlotsIntoBufAux
          encodeSlot
          fallbackLayoutIdx
          offRest
          nextIdxs
          vRest
          buf'

/--
Write array element values in `elems` at `strideBytes` intervals starting at
`runningOff` into `buf` using element layout index `elemFlIdx`.
-/
def encodeArraySlotsIntoBufAux
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (elemFlIdx strideBytes runningOff : Nat) :
    List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, buf => .some buf
  | ev :: eRest, buf =>
    match encodeSlot elemFlIdx ev with
    | .none => .none
    | .some eBytes =>
      match writeAbstractBytesAt buf runningOff eBytes with
      | .none => .none
      | .some buf' =>
        encodeArraySlotsIntoBufAux
          encodeSlot
          elemFlIdx
          strideBytes
          (Nat.add runningOff strideBytes)
          eRest
          buf'

/--
Fuel-bounded layout-driven byte encoder using `LayoutTable` index `layoutIdx`,
preserving `.uninit` padding bytes inside structs and `.uninit` uninitialized
slots inside `.unit`-padded unions.
-/
def encodeByLayoutIdxAux :
    Nat → LayoutTable → Nat → Value → Option (List AbstractByte)
  | .zero, _, _, _ => .none
  | .succ _, _, _, .unit => .some .nil
  | .succ _, layouts, layoutIdx, .scalar sv =>
    let validOk : Bool :=
      match LayoutTable.lookup layouts layoutIdx with
      | .some { isUninhabited := true, .. } => false
      | .some l =>
        let sizeOk : Bool :=
          match Nat.ble 1 l.size.bytes with
          | true => Nat.beq sv.sizeBytes l.size.bytes
          | false => false
        match sizeOk with
        | false => false
        | true =>
          match l.backendRepr with
          | .scalar (.initialized _ vr) =>
            match wrappingRangeContains vr sv.bits with
            | false => false
            | true =>
              match
                Bool.and
                  (Nat.beq sv.sizeBytes 4)
                  (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF))
              with
              | true => isValidCharCode sv.bits
              | false => true
          | _ => true
      | .none => true
    match validOk with
    | true => encodeScalarBytes sv .none
    | false => .none
  | .succ _, layouts, layoutIdx, .ptr p sz =>
    let ptrOk : Bool :=
      match LayoutTable.lookup layouts layoutIdx with
      | .some { isUninhabited := true, .. } => false
      | .some l =>
        match Nat.ble 1 l.size.bytes with
        | true => Nat.beq sz l.size.bytes
        | false => false
      | .none => true
    match ptrOk with
    | true => encodeScalarBytes ⟨p.offsetBytes, sz⟩ (.some (p.allocId, p.tag))
    | false => .none
  | .succ fuel', layouts, layoutIdx, .aggregate varIdx fieldVals =>
    let fallbackIdx := unresolvedLayoutIdx layouts
    let encodeChild := fun (cIdx : Nat) (cv : Value) =>
      encodeByLayoutIdxAux fuel' layouts cIdx cv
    match LayoutTable.lookup layouts layoutIdx with
    | .none => encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx fieldVals)
    | .some l =>
      match l.isUninhabited with
      | true => .none
      | false =>
        match l.fields with
        | .union count =>
          match Nat.beq varIdx 0 with
          | false => .none
          | true =>
            encodeUnionSlotsIntoBufAux
              layouts
              encodeChild
              fallbackIdx
              count
              l.fieldLayouts
              fieldVals
              l.size.bytes
        | .arbitrary offsets _ =>
          match l.variants with
          | .single expectedVar =>
            match
              Bool.and
                (Nat.beq varIdx expectedVar)
                (Nat.beq (length offsets) (length fieldVals))
            with
            | false => .none
            | true =>
              encodeArbitrarySlotsIntoBufAux
                encodeChild
                fallbackIdx
                offsets
                l.fieldLayouts
                fieldVals
                (replicateUninitBytes l.size.bytes)
          | _ =>
            encodeValueToBytes
              defaultCodecFuel
              layouts
              { kind := .adt "" .nil, layoutIdx := layoutIdx }
              (.aggregate varIdx fieldVals)
        | .array stride count =>
          match
            Bool.and
              (Nat.beq varIdx 0)
              (Nat.beq (length fieldVals) count)
          with
          | false => .none
          | true =>
            let elemFlIdx :=
              match l.fieldLayouts with
              | flIdx :: _ => flIdx
              | .nil => fallbackIdx
            encodeArraySlotsIntoBufAux
              encodeChild
              elemFlIdx
              stride.bytes
              0
              fieldVals
              (replicateUninitBytes l.size.bytes)
        | _ =>
          match encodeUntypedValueToBytes defaultCodecFuel (.aggregate varIdx fieldVals) with
          | .some bs =>
            match Nat.beq (length bs) l.size.bytes with
            | true => .some bs
            | false => .none
          | .none => .none

/--
Force the spine of a `List Value` before wrapping it in `.some` / `.ok` so
multi-step kernel `rfl` reductions never retain unreduced list-producing thunks
inside a stored union `Value.aggregate 0 ...`.
-/
def forceValueListOpt : List Value → Option (List Value)
  | .nil => .some .nil
  | v :: vs =>
    match forceValueListOpt vs with
    | .some vs' => .some (v :: vs')
    | .none => .none

/--
Finalize a `count`-slot union field list `typedFields` against target byte image
`targetBytes`: retains `typedFields` directly when `encodeByLayoutIdxAux`
reproduces `targetBytes` exactly, and appends the raw-byte overlay slot at index
`count` otherwise so partially initialized or non-field-aligned byte images are
preserved losslessly. Returns `.some finalFields` with its list spine forced.
-/
def finalizeUnionFieldsWithRawOverlayOpt
    (layouts : LayoutTable)
    (unionLayoutIdx : Nat)
    (typedFields : List Value)
    (targetBytes : List AbstractByte) :
    Option (List Value) :=
  match encodeByLayoutIdxAux 8 layouts unionLayoutIdx (.aggregate 0 typedFields) with
  | .some reBytes =>
    match abstractByteListEq reBytes targetBytes with
    | true => forceValueListOpt typedFields
    | false =>
      match forceValueListOpt (encodeRawAbstractByteVals targetBytes) with
      | .some rawVals =>
        forceValueListOpt
          (appendValueList typedFields (.aggregate 0 rawVals :: .nil))
      | .none => .none
  | .none =>
    match forceValueListOpt (encodeRawAbstractByteVals targetBytes) with
    | .some rawVals =>
      forceValueListOpt
        (appendValueList typedFields (.aggregate 0 rawVals :: .nil))
    | .none => .none

/--
Decode a `count`-field union byte image `bytes` at `layoutIdx` into a `.unit`-padded
`Value.aggregate 0 ...` (attaching a raw-byte overlay when `bytes` contains
initialized bytes), forcing the field-list spine before constructing `.some`.
-/
def decodeUnionBytesWithCountOpt
    (layouts : LayoutTable)
    (layoutIdx count : Nat)
    (bytes : List AbstractByte) :
    Option Value :=
  let typedSlots := replicateValue count .unit
  match finalizeUnionFieldsWithRawOverlayOpt layouts layoutIdx typedSlots bytes with
  | .some fs => .some (.aggregate 0 fs)
  | .none => .none

/--
Decode `bytes` into a union `Value` when `ty` has a valid inhabited
`FieldsShape.union` layout of size `length bytes`.
-/
def decodeUnionByLayout?
    (layouts : LayoutTable)
    (ty : Ty)
    (bytes : List AbstractByte) :
    Option Value :=
  match LayoutTable.lookup layouts ty.layoutIdx with
  | .none => .none
  | .some l =>
    match
      l.isUninhabited,
      Nat.beq (length bytes) l.size.bytes,
      l.variants,
      l.fields
    with
    | false, true, .single 0, .union count =>
      decodeUnionBytesWithCountOpt layouts ty.layoutIdx count bytes
    | _, _, _, _ => .none

/--
Decode aggregate fields at `offsets` pairing each field's `RigidTy` with its
`TypeLayout` index from `fieldLayouts`.
-/
def decodeTypedKindsAndLayoutsAtOffsets
    (decodeChild : Ty → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List RigidTy → List Nat → Option (List Value)
  | .nil, .nil, .nil => .some .nil
  | off :: offRest, k :: kRest, fIdx :: fRest =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .none
    | .some fl =>
      match sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | .none => .none
      | .some fSlice =>
        match decodeChild { kind := k, layoutIdx := fIdx } fSlice with
        | .none => .none
        | .some v =>
          match
            decodeTypedKindsAndLayoutsAtOffsets
              decodeChild
              layouts
              bytes
              offRest
              kRest
              fRest
          with
          | .some vs => .some (v :: vs)
          | .none => .none
  | _, _, _ => .none

/--
`true` when some byte of `bytes` is initialized with pointer provenance
(`AbstractByte.init _ (.some _)`).
-/
@[reducible]
def abstractBytesHaveProv : List AbstractByte → Bool
  | .nil => false
  | .init _ (.some _) :: _ => true
  | _ :: rest => abstractBytesHaveProv rest

/--
`true` when every byte of `bytes` is initialized with exactly the provenance pair
`(allocId, tag)`.
-/
def abstractBytesAllProvAux (allocId tag : Nat) : List AbstractByte → Bool
  | .nil => true
  | .init _ (.some (a, t)) :: rest =>
    Bool.and
      (Bool.and (Nat.beq a allocId) (Nat.beq t tag))
      (abstractBytesAllProvAux allocId tag rest)
  | _ :: _ => false

/--
`true` when `bytes` is non-empty and every byte carries the same pointer
provenance as its first byte, i.e. `bytes` is an intact (non-spliced) pointer
image. Pointer bytes with no provenance, or with mixed provenance, yield a
provenance-less address.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."
-/
@[reducible]
def abstractBytesUniformProv : List AbstractByte → Bool
  | .init _ (.some (a, t)) :: rest => abstractBytesAllProvAux a t rest
  | _ => false

/--
Decode a raw pointer or reference image `bytes` of pointee `pointee` at pointer
width `ptrBytes`, without fabricating provenance:
- an intact pointer image (`abstractBytesUniformProv`) decodes to
  `Value.ptr { allocId, offsetBytes := bits } ptrBytes`;
- a provenance-less (or spliced) raw pointer image decodes to the provenance-less
  address `Value.scalar ⟨bits, ptrBytes⟩`;
- a provenance-less (or spliced) reference image is invalid (`.none`);
- wide pointers decode their data half as above and their metadata half as
  `Value.scalar ⟨meta, ptrBytes⟩` (slice/`str` lengths must not carry provenance;
  `dyn` vtable pointers keep intact provenance).
-/
def decodePtrBytesNoForge
    (isRef : Bool)
    (pointee : RigidTy)
    (ptrBytes : Nat)
    (bytes : List AbstractByte) :
    Option Value :=
  let dataOf (dataBytes : List AbstractByte) : Option Value :=
    match Nat.beq (length dataBytes) ptrBytes, decodeScalarBytes dataBytes false with
    | true, .some (sv, prov) =>
      match abstractBytesUniformProv dataBytes, prov with
      | true, .some (allocId, _) =>
        .some (.ptr { allocId := allocId, offsetBytes := sv.bits } ptrBytes)
      | _, _ =>
        match isRef with
        | true => .none
        | false => .some (.scalar ⟨sv.bits, ptrBytes⟩)
    | _, _ => .none
  let wideMetaIsDyn : Option Bool :=
    match pointee with
    | .slice _ => .some false
    | .str => .some false
    | .dynamic _ => .some true
    | _ => .none
  match wideMetaIsDyn with
  | .none => dataOf bytes
  | .some isDyn =>
    match Nat.beq (length bytes) (Nat.add ptrBytes ptrBytes) with
    | false => .none
    | true =>
      let metaBytes := dropAbstractBytes ptrBytes bytes
      let metaOpt : Option Value :=
        match decodeScalarBytes metaBytes false with
        | .none => .none
        | .some (metaSv, metaProv) =>
          match isDyn, abstractBytesUniformProv metaBytes, metaProv with
          | true, true, .some (vtAllocId, _) =>
            .some (.ptr { allocId := vtAllocId, offsetBytes := metaSv.bits } ptrBytes)
          | true, _, _ => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
          | false, _, _ =>
            match abstractBytesHaveProv metaBytes with
            | true => .none
            | false => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
      match dataOf (takeAbstractBytes ptrBytes bytes), metaOpt with
      | .some dataVal, .some metaVal => .some (.aggregate 0 (dataVal :: metaVal :: .nil))
      | _, _ => .none

/--
Decode `bytes` according to `ScalarLayout` `sl` without fabricating pointer
provenance from provenance-less bytes and without permitting pointer-provenance
bytes to decode into non-pointer scalar layouts.
-/
def decodeScalarLayoutBytesNoForge
    (sl : ScalarLayout)
    (bytes : List AbstractByte) :
    Option Value :=
  match scalarLayoutByteWidth sl with
  | .none => .none
  | .some sz =>
    match Nat.beq (length bytes) sz with
    | false => .none
    | true =>
      match sl with
      | .initialized (.pointer _) vr =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some (sv, prov) =>
          match abstractBytesUniformProv bytes, prov with
          | true, .some (allocId, _) =>
            .some (.ptr { allocId := allocId, offsetBytes := sv.bits } sz)
          | _, _ =>
            match wrappingRangeContains vr sv.bits with
            | true => .some (.scalar sv)
            | false => .none
      | .initialized _ vr =>
        match abstractBytesHaveProv bytes with
        | true => .none
        | false =>
          match decodeScalarBytes bytes false with
          | .none => .none
          | .some (sv, _) =>
            match wrappingRangeContains vr sv.bits with
            | false => .none
            | true =>
              match
                Bool.and
                  (Nat.beq sv.sizeBytes 4)
                  (Bool.and (Nat.beq vr.start 0) (Nat.beq vr.end_ 0x10FFFF))
              with
              | true =>
                match isValidCharCode sv.bits with
                | true => .some (.scalar sv)
                | false => .none
              | false => .some (.scalar sv)
      | .union (.pointer _) =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some (sv, prov) =>
          match abstractBytesUniformProv bytes, prov with
          | true, .some (allocId, _) =>
            .some (.ptr { allocId := allocId, offsetBytes := sv.bits } sz)
          | _, _ => .some (.scalar sv)
      | .union _ =>
        match abstractBytesHaveProv bytes with
        | true => .none
        | false =>
          match decodeScalarBytes bytes false with
          | .some (sv, _) => .some (.scalar sv)
          | .none => .none

/--
Fuel-bounded layout- and type-aware byte decoder extending `decodeValueFromBytes`
with union raw-byte preservation (`decodeUnionBytesWithCount`), per-element
`fieldLayouts` propagation on arrays/tuples/structs, `char` UTF-16 surrogate
rejection on layout-only `.primitive` fields, and provenance-faithful scalar
decoding:
- integer, `bool`, and `char` images carrying pointer provenance are rejected
  (the abstract address of a pointer is not recoverable from its byte image);
- raw pointer images without intact provenance decode to provenance-less
  addresses (`Value.scalar`), and reference / `fnPtr` images without intact
  provenance are rejected, so transmutes and union reads never fabricate
  provenance;
- ADT fields are decoded by their `fieldLayouts` (generic arguments are not
  field types).
-/
def decodeTypedValueFromBytes :
    Nat → LayoutTable → Ty → List AbstractByte → Option Value
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, ty, bytes =>
    let rTy := normalizeCodecTy ty
    let decodeChild := fun (cTy : Ty) (bs : List AbstractByte) =>
      decodeTypedValueFromBytes fuel' layouts cTy bs
    match rTy.kind with
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true =>
        match bytes with
        | .nil => .some (.aggregate 0 .nil)
        | _ :: _ => .none
      | false =>
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some { fields := .array stride _, fieldLayouts := elemFlIdx :: _, .. } =>
          match Nat.beq (length bytes) (Nat.mul stride.bytes n) with
          | false => .none
          | true =>
            match
              decodeArrayChunksWith
                (decodeChild { kind := elemKind, layoutIdx := elemFlIdx })
                stride.bytes
                n
                bytes
            with
            | .some elems => .some (.aggregate 0 elems)
            | .none => .none
        | _ =>
          let elemSzOpt : Option Nat :=
            match rigidTyKindByteSize elemKind with
            | .some sz => .some sz
            | .none =>
              match LayoutTable.lookup layouts rTy.layoutIdx with
              | .some { fields := .array stride _, .. } => .some stride.bytes
              | _ =>
                match elemKind with
                | .tuple ks => tupleFieldsByteSize ks
                | _ => .none
          match elemSzOpt with
          | .none => .none
          | .some elemSz =>
            match Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => .none
            | true =>
              match
                decodeArrayChunksWith
                  (decodeChild { kind := elemKind, layoutIdx := 0 })
                  elemSz
                  n
                  bytes
              with
              | .some elems => .some (.aggregate 0 elems)
              | .none => .none
    | .tuple (kHead :: kTail) =>
      let ks := kHead :: kTail
      let decodeTypedKind := fun (k : RigidTy) (bs : List AbstractByte) =>
        decodeChild { kind := k, layoutIdx := 0 } bs
      let sizeOfKind := fun (k : RigidTy) =>
        rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .some l =>
        match Nat.beq (length bytes) l.size.bytes, l.fields with
        | true, .arbitrary offsets _ =>
          match
            Bool.and
              (Nat.beq (length ks) (length offsets))
              (Nat.beq (length l.fieldLayouts) (length offsets))
          with
          | true =>
            match
              decodeTypedKindsAndLayoutsAtOffsets
                decodeChild
                layouts
                bytes
                offsets
                ks
                l.fieldLayouts
            with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
          | false =>
            match
              decodeFieldsAtOffsetsWith
                decodeTypedKind
                sizeOfKind
                bytes
                offsets
                ks
            with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
        | true, _ =>
          match decodeSeqFieldsWith decodeTypedKind sizeOfKind ks bytes with
          | .some vals => .some (.aggregate 0 vals)
          | .none => .none
        | false, _ => .none
      | .none =>
        match decodeSeqFieldsWith decodeTypedKind sizeOfKind ks bytes with
        | .some vals => .some (.aggregate 0 vals)
        | .none => .none
    | .adt _ _ =>
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .none => decodeValueFromBytes (.succ fuel') layouts rTy bytes
      | .some l =>
        match
          Bool.or
            l.isUninhabited
            (Bool.not (Nat.beq (length bytes) l.size.bytes))
        with
        | true => .none
        | false =>
          match l.variants, l.fields with
          | .single 0, .union count =>
            decodeUnionBytesWithCountOpt layouts rTy.layoutIdx count bytes
          | .single variantIdx, .arbitrary .nil _ =>
            .some (.aggregate variantIdx .nil)
          | .single variantIdx, .arbitrary offsets _ =>
            match Nat.beq (length l.fieldLayouts) (length offsets) with
            | true =>
              match
                decodeFieldsByLayoutIdxs
                  (fun fIdx fSlice =>
                    decodeChild { kind := .adt "" .nil, layoutIdx := fIdx } fSlice)
                  layouts
                  bytes
                  offsets
                  l.fieldLayouts
              with
              | .some vals => .some (.aggregate variantIdx vals)
              | .none => .none
            | false =>
              match offsets, l.backendRepr with
              | off0 :: .nil, .scalar s0 =>
                match scalarLayoutByteWidth s0 with
                | .none => .none
                | .some sz0 =>
                  match sliceAbstractBytes bytes off0.bytes sz0 with
                  | .none => .none
                  | .some slice0 =>
                    match decodeScalarLayoutBytesNoForge s0 slice0 with
                    | .some v0 => .some (.aggregate variantIdx (v0 :: .nil))
                    | .none => .none
              | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
                | .some sz0, .some sz1 =>
                  match
                    sliceAbstractBytes bytes off0.bytes sz0,
                    sliceAbstractBytes bytes off1.bytes sz1
                  with
                  | .some slice0, .some slice1 =>
                    match
                      decodeScalarLayoutBytesNoForge s0 slice0,
                      decodeScalarLayoutBytesNoForge s1 slice1
                    with
                    | .some v0, .some v1 =>
                      .some (.aggregate variantIdx (v0 :: v1 :: .nil))
                    | _, _ => .none
                  | _, _ => .none
                | _, _ => .none
              | _, _ =>
                match abstractBytesHaveProv bytes with
                | true => .none
                | false =>
                  match decodeFieldsBySpan bytes l.size.bytes offsets with
                  | .some vals => .some (.aggregate variantIdx vals)
                  | .none => .none
          | .single variantIdx, .array stride count =>
            match Nat.beq count 0 with
            | true =>
              match bytes with
              | .nil => .some (.aggregate variantIdx .nil)
              | _ :: _ => .none
            | false =>
              match l.fieldLayouts with
              | elemFlIdx :: _ =>
                match
                  decodeArrayChunksWith
                    (decodeChild { kind := .adt "" .nil, layoutIdx := elemFlIdx })
                    stride.bytes
                    count
                    bytes
                with
                | .some vals => .some (.aggregate variantIdx vals)
                | .none => .none
              | .nil =>
                match abstractBytesHaveProv bytes with
                | true => .none
                | false => decodeValueFromBytes (.succ fuel') layouts rTy bytes
          | .single _, .primitive =>
            match Nat.beq l.size.bytes 0 with
            | true => .some .unit
            | false =>
              match l.backendRepr with
              | .scalar s0 => decodeScalarLayoutBytesNoForge s0 bytes
              | _ =>
                match abstractBytesHaveProv bytes with
                | true => .none
                | false =>
                  match decodeScalarBytes bytes false with
                  | .some (sv, _) => .some (.scalar sv)
                  | .none => .none
          | _, _ => decodeValueFromBytes (.succ fuel') layouts rTy bytes
    | .bool | .char | .int _ | .uint _ =>
      match abstractBytesHaveProv bytes with
      | true => .none
      | false => decodeValueFromBytes (.succ fuel') layouts rTy bytes
    | .fnPtr _ _ _ _ =>
      decodePtrBytesNoForge true (.tuple .nil) (layoutPointerBytes layouts) bytes
    | .rawPtr _ pointee =>
      decodePtrBytesNoForge false pointee (layoutPointerBytes layouts) bytes
    | .ref _ pointee =>
      decodePtrBytesNoForge true pointee (layoutPointerBytes layouts) bytes
    | _ => decodeValueFromBytes (.succ fuel') layouts rTy bytes

/--
Encode `v` of type `ty` using `encodeByLayoutIdxAux` when `ty` is a union or
layout-backed aggregate, falling back to `encodeValueToBytes`.
-/
def encodeTypedValueToBytes
    (layouts : LayoutTable)
    (ty : Ty)
    (v : Value) :
    Option (List AbstractByte) :=
  let rTy := normalizeCodecTy ty
  match isUnionLayout layouts rTy with
  | true => encodeByLayoutIdxAux 8 layouts rTy.layoutIdx v
  | false =>
    match encodeValueToBytes defaultCodecFuel layouts rTy v with
    | .some bs => .some bs
    | .none =>
      match rTy.kind with
      | .adt _ _ | .tuple (_ :: _) | .array _ _ =>
        match LayoutTable.lookup layouts rTy.layoutIdx with
        | .some _ => encodeByLayoutIdxAux 8 layouts rTy.layoutIdx v
        | .none => .none
      | _ => .none

/--
Resolve dynamic `.index idxLocal` projections in `proj` into `.constantIndex
idxVal 0 false` using `locals` (failing on `.deref` or non-scalar index locals).
-/
def resolveUnionSubProjIndices
    (locals : List LocalSlot) :
    List ProjectionElem → Option (List ProjectionElem)
  | .nil => .some .nil
  | .deref :: _ => .none
  | .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar idxSc)) =>
      match resolveUnionSubProjIndices locals rest with
      | .some rest' => .some (.constantIndex idxSc.bits 0 false :: rest')
      | .none => .none
    | _ => .none
  | elem :: rest =>
    match resolveUnionSubProjIndices locals rest with
    | .some rest' => .some (elem :: rest')
    | .none => .none

/--
Verify that a normalized sub-projection chain `proj` on `curTy` accesses a
statically bounded fixed-offset sub-place without enum `.downcast` checks, so a
partial read/write through a union field can address `[subOff .. subOff + leafSz)`
directly without requiring unrelated sibling bytes of `curTy` to be initialized.
-/
def checkStaticSubProjBounds
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Ty → List ProjectionElem → Bool
  | _, .nil => true
  | _, .opaqueCast castTy :: rest =>
    checkStaticSubProjBounds
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
  | _, .unwrapUnsafeBinder innerTy :: rest =>
    checkStaticSubProjBounds
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
  | _, .downcast _ _ :: _ => false
  | curTy, .field idx fieldTy :: rest =>
    let rCur := resolveTyWithLocalDecls localDecls layouts curTy
    let nextTy : Ty :=
      match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
      | false => fieldTy
      | true =>
        match LayoutTable.lookup layouts rCur.layoutIdx with
        | .some { variants := .single _, fieldLayouts := fls, .. } =>
          match get? fls idx with
          | .some flIdx => { fieldTy with layoutIdx := flIdx }
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
        | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
    let fieldInBounds : Bool :=
      match rCur.kind with
      | .tuple ks => Nat.blt idx (length ks)
      | .adt _ _ =>
        match LayoutTable.lookup layouts rCur.layoutIdx with
        | .some { isUninhabited := false, variants := .single _, fields := .arbitrary offsets _, .. } =>
          Nat.blt idx (length offsets)
        | .some { isUninhabited := false, variants := .single 0, fields := .union count, .. } =>
          Nat.blt idx count
        | _ => false
      | _ => false
    match fieldInBounds with
    | true => checkStaticSubProjBounds localDecls layouts nextTy rest
    | false => false
  | curTy, .constantIndex offset minLen fromEnd :: rest =>
    let rCur := resolveTyWithLocalDecls localDecls layouts curTy
    match rCur.kind with
    | .array ek arrLen =>
      let fromEndOk :=
        match fromEnd with
        | false => true
        | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset arrLen)
      let idx :=
        match fromEnd with
        | true => Nat.sub arrLen offset
        | false => offset
      match
        Bool.and
          (Nat.ble minLen arrLen)
          (Bool.and fromEndOk (Nat.blt idx arrLen))
      with
      | false => false
      | true =>
        let elemTy : Ty :=
          match LayoutTable.lookup layouts rCur.layoutIdx with
          | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
            { kind := ek, layoutIdx := flIdx }
          | _ =>
            resolveTyWithLocalDecls
              localDecls
              layouts
              { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
        checkStaticSubProjBounds localDecls layouts elemTy rest
    | _ => false
  | curTy, .subslice fromIdx toIdx fromEnd :: rest =>
    let rCur := resolveTyWithLocalDecls localDecls layouts curTy
    match rCur.kind with
    | .array ek arrLen =>
      match Nat.ble toIdx arrLen with
      | false => false
      | true =>
        let endIdx :=
          match fromEnd with
          | true => Nat.sub arrLen toIdx
          | false => toIdx
        match Bool.and (Nat.ble fromIdx endIdx) (Nat.ble endIdx arrLen) with
        | false => false
        | true =>
          let subTy : Ty :=
            { kind := .array ek (Nat.sub endIdx fromIdx)
              layoutIdx := unresolvedLayoutIdx layouts }
          checkStaticSubProjBounds localDecls layouts subTy rest
    | _ => false
  | _, _ => false

/--
Construct a full-width wrapper `Value` when writing `leafVal` along a chain of
0-offset single-field wrappers (such as `ManuallyDrop<T>` inside `MaybeUninit<T>`,
i.e., `_0.value.value = x`) into an uninitialized union field.
-/
def wrapFullWidthInitChain?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Ty → List ProjectionElem → Value → Option Value
  | _, .nil, leafVal => .some leafVal
  | _, .opaqueCast castTy :: rest, leafVal =>
    wrapFullWidthInitChain?
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
      leafVal
  | _, .unwrapUnsafeBinder innerTy :: rest, leafVal =>
    wrapFullWidthInitChain?
      localDecls
      layouts
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
      leafVal
  | curTy, .field 0 fieldTy :: rest, leafVal =>
    let rCur := resolveTyWithLocalDecls localDecls layouts curTy
    let rField : Ty :=
      match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
      | false => fieldTy
      | true =>
        match LayoutTable.lookup layouts rCur.layoutIdx with
        | .some { variants := .single _, fieldLayouts := flIdx :: _, .. } =>
          { fieldTy with layoutIdx := flIdx }
        | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
    let singleFieldSameSizeOk : Bool :=
      match rCur.kind with
      | .tuple (_ :: .nil) => true
      | .adt _ _ =>
        match LayoutTable.lookup layouts rCur.layoutIdx with
        | .some l =>
          match l.isUninhabited, l.variants, l.fields with
          | false, .single 0, .arbitrary (off0 :: .nil) _ =>
            match Nat.beq off0.bytes 0, tyByteSize localDecls layouts rField with
            | true, .some fSz => Nat.beq fSz l.size.bytes
            | _, _ => false
          | false, .single 0, .union count =>
            match Nat.ble 1 count, tyByteSize localDecls layouts rField with
            | true, .some fSz => Nat.beq fSz l.size.bytes
            | _, _ => false
          | _, _, _ => false
        | .none => false
      | _ => false
    match singleFieldSameSizeOk with
    | false => .none
    | true =>
      match wrapFullWidthInitChain? localDecls layouts rField rest leafVal with
      | .none => .none
      | .some innerVal =>
        match rCur.kind with
        | .adt _ _ =>
          match LayoutTable.lookup layouts rCur.layoutIdx with
          | .some { fields := .union count, .. } =>
            .some (.aggregate 0 (innerVal :: replicateValue (Nat.sub count 1) .unit))
          | _ => .some (.aggregate 0 (innerVal :: .nil))
        | _ => .some (.aggregate 0 (innerVal :: .nil))
  | _, _, _ => .none

/--
Read a deref-free projection chain `proj` on `v` of static type `baseTy` with
union byte-reinterpretation semantics:
- Reading a union `.field idx fieldTy` whose runtime slot holds a non-`.unit`
  value returns/projects that value directly.
- Reading a union `.field idx fieldTy` whose runtime slot is `.unit` (or beyond
  `length fields` while `< unionFieldCount`) encodes the union's initialized
  storage bytes via `encodeByLayoutIdxAux`, slices `[subOff .. subOff + sizeof)`
  for direct sub-projections (or `[0 .. sizeof(fieldTy))` at the field root),
  and decodes via `decodeTypedValueFromBytes` (faulting with `.ub` on `.uninit`
  or bit-invalid bytes).

Reference (The Rust Reference, "Union types"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html#reading-and-writing-union-fields>

> "Unions have no notion of an \"active field\". Instead, every union access
> just interprets the storage as the type of the field used for the access.
> Reading a union field reads the bits of the union at the field's type."
-/
def readProjectedValueUnionAware
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Value → Ty → List ProjectionElem → ProjReadResult
  | v, _, .nil => .ok v
  | v, _, .opaqueCast castTy :: rest =>
    readProjectedValueUnionAware
      locals
      localDecls
      layouts
      v
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
  | v, _, .unwrapUnsafeBinder innerTy :: rest =>
    readProjectedValueUnionAware
      locals
      localDecls
      layouts
      v
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
  | .aggregate varIdx fields, baseTy, .downcast _ targetVar :: rest =>
    match Nat.beq varIdx targetVar with
    | true =>
      readProjectedValueUnionAware
        locals
        localDecls
        layouts
        (.aggregate varIdx fields)
        baseTy
        rest
    | false => .ub
  | _, _, .downcast _ _ :: _ => .ub
  | v, baseTy, .field idx fieldTy :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    let unionCountAndLayoutOpt : Option (Nat × TypeLayout) :=
      match rBase.kind with
      | .adt _ _ =>
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some l =>
          match l.fields with
          | .union count => .some (count, l)
          | _ => .none
        | .none => .none
      | _ => .none
    match unionCountAndLayoutOpt with
    | .some (count, l) =>
      match v, Nat.ble (.succ idx) count with
      | .aggregate 0 fields, true =>
        let rFieldTy : Ty :=
          match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
          | false => fieldTy
          | true =>
            match get? l.fieldLayouts idx with
            | .some flIdx => { fieldTy with layoutIdx := flIdx }
            | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
        let directFvOpt : Option Value :=
          match get? fields idx with
          | .some .unit =>
            match rFieldTy.kind with
            | .tuple .nil => .some .unit
            | .fnDef _ _ => .some .unit
            | _ => .none
          | .some fv => .some fv
          | .none => .none
        -- A union value whose slots (or raw-byte overlay) disagree on some
        -- initialized byte does not determine a storage image (e.g. after a
        -- union-unaware projected write updated one slot without resetting its
        -- siblings), so no slot may be trusted: fail closed.
        let unionImageOk : Bool :=
          match unionNeedsConsistencyCheck count fields with
          | false => true
          | true =>
            match encodeByLayoutIdxAux 8 layouts rBase.layoutIdx (.aggregate 0 fields) with
            | .none => false
            | .some unionBytes =>
              match l.fieldLayouts, get? fields idx with
              | .nil, .some (.aggregate varIdx aggFs) =>
                match encodeTypedValueToBytes layouts rFieldTy (.aggregate varIdx aggFs) with
                | .none => false
                | .some fBytes =>
                  let fMask := layoutValueMaskAux 8 layouts rFieldTy.layoutIdx
                  match
                    mergeMaskedAbstractBytes
                      unionBytes
                      (replicateBool (length unionBytes) true)
                      fBytes
                      fMask
                  with
                  | .some _ => true
                  | .none => false
              | _, _ => true
        match unionImageOk, directFvOpt with
        | false, _ => .unsupported
        | true, .some fv =>
          readProjectedValueUnionAware locals localDecls layouts fv rFieldTy rest
        | true, .none =>
          let directSubReadOpt : Option ProjReadResult :=
            match rest with
            | .nil => .none
            | _ :: _ =>
              match resolveUnionSubProjIndices locals rest with
              | .none => .some .ub
              | .some idxResolved =>
                let normRest :=
                  normalizeSubsliceProjections (stripTransparentProjections idxResolved)
                match checkStaticSubProjBounds localDecls layouts rFieldTy normRest with
                | false => .none
                | true =>
                  match
                    projectionChainByteOffset?
                      layouts
                      (.some rFieldTy)
                      .none
                      .none
                      0
                      localDecls
                      normRest,
                    resolveProjectedTyResolved localDecls layouts rFieldTy normRest
                  with
                  | .some subOff, .some leafTy =>
                    match tyByteSize localDecls layouts leafTy with
                    | .none => .none
                    | .some 0 =>
                      let zv :=
                        match decodeTypedValueFromBytes defaultCodecFuel layouts leafTy .nil with
                        | .some v0 => v0
                        | .none => .unit
                      .some (.ok zv)
                    | .some (.succ leafPred) =>
                      let leafSz := .succ leafPred
                      match
                        encodeByLayoutIdxAux 8 layouts rBase.layoutIdx (.aggregate 0 fields)
                      with
                      | .none => .some .ub
                      | .some unionBytes =>
                        match sliceAbstractBytes unionBytes subOff leafSz with
                        | .none => .some .ub
                        | .some leafSlice =>
                          match
                            decodeTypedValueFromBytes defaultCodecFuel layouts leafTy leafSlice
                          with
                          | .some leafVal => .some (.ok leafVal)
                          | .none => .some .ub
                  | _, _ => .none
          match directSubReadOpt with
          | .some res => res
          | .none =>
            match tyByteSize localDecls layouts rFieldTy with
            | .none => .unsupported
            | .some 0 =>
              let zstVal : Value :=
                match decodeTypedValueFromBytes defaultCodecFuel layouts rFieldTy .nil with
                | .some zv => zv
                | .none => .unit
              readProjectedValueUnionAware locals localDecls layouts zstVal rFieldTy rest
            | .some (.succ szPred) =>
              let fieldSz := .succ szPred
              match
                encodeByLayoutIdxAux 8 layouts rBase.layoutIdx (.aggregate 0 fields)
              with
              | .none => .ub
              | .some unionBytes =>
                match sliceAbstractBytes unionBytes 0 fieldSz with
                | .none => .ub
                | .some fieldSlice =>
                  match
                    decodeTypedValueFromBytes defaultCodecFuel layouts rFieldTy fieldSlice
                  with
                  | .some decodedFv =>
                    readProjectedValueUnionAware
                      locals
                      localDecls
                      layouts
                      decodedFv
                      rFieldTy
                      rest
                  | .none => .ub
      | _, _ => .ub
    | .none =>
      let nextTy : Ty :=
        match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
        | false => fieldTy
        | true =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some l =>
            match l.variants with
            | .single _ =>
              match get? l.fieldLayouts idx with
              | .some flIdx => { fieldTy with layoutIdx := flIdx }
              | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
            | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
      match v with
      | .aggregate _ fields =>
        match get? fields idx with
        | .some fv =>
          readProjectedValueUnionAware locals localDecls layouts fv nextTy rest
        | .none => .ub
      | .scalar sc =>
        match idx with
        | .zero =>
          readProjectedValueUnionAware locals localDecls layouts (.scalar sc) nextTy rest
        | .succ _ => .ub
      | .ptr p sz =>
        match idx with
        | .zero =>
          readProjectedValueUnionAware locals localDecls layouts (.ptr p sz) nextTy rest
        | .succ _ => .ub
      | .unit => .ub
  | .aggregate 0 elems, baseTy, .index idxLocal :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    let elemTy : Ty :=
      match elemTyOf rBase with
      | .some { kind := ek, .. } =>
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      | .none => rBase
    match get? locals idxLocal with
    | .some (.init (.scalar idxSc)) =>
      match get? elems idxSc.bits with
      | .some ev =>
        readProjectedValueUnionAware locals localDecls layouts ev elemTy rest
      | .none => .ub
    | _ => .ub
  | _, _, .index _ :: _ => .ub
  | .aggregate 0 elems, baseTy, .constantIndex offset minLen fromEnd :: rest =>
    let len := length elems
    let fromEndOk :=
      match fromEnd with
      | false => true
      | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset len)
    match Bool.and (Nat.ble minLen len) fromEndOk with
    | false => .ub
    | true =>
      let idx :=
        match fromEnd with
        | true => Nat.sub len offset
        | false => offset
      let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
      let elemTy : Ty :=
        match elemTyOf rBase with
        | .some { kind := ek, .. } =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
            { kind := ek, layoutIdx := flIdx }
          | _ =>
            resolveTyWithLocalDecls
              localDecls
              layouts
              { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
        | .none => rBase
      match get? elems idx with
      | .some ev =>
        readProjectedValueUnionAware locals localDecls layouts ev elemTy rest
      | .none => .ub
  | _, _, .constantIndex _ _ _ :: _ => .ub
  | .aggregate 0 elems, baseTy, .subslice fromIdx toIdx fromEnd :: rest =>
    match extractSubslice elems fromIdx toIdx fromEnd with
    | .none => .ub
    | .some subElems =>
      let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
      let subTy : Ty :=
        match rBase.kind with
        | .array ek _ =>
          { kind := .array ek (length subElems), layoutIdx := rBase.layoutIdx }
        | _ => rBase
      readProjectedValueUnionAware
        locals
        localDecls
        layouts
        (.aggregate 0 subElems)
        subTy
        rest
  | _, _, .subslice _ _ _ :: _ => .ub
  | _, _, .deref :: _ => .unsupported

/--
Rebuild the `count` typed union slots when field `activeIdx` is updated to
`newFieldVal` (or `.unit` for a partial sub-field write):
- Slot `activeIdx` receives `newFieldVal`.
- Zero-sized sibling slots that already held `.aggregate 0 .nil` (`()`) retain
  `.aggregate 0 .nil`; all other sibling slots become `.unit` so subsequent
  reads reinterpret the union's updated byte image at the accessed field's `Ty`.
-/
def rebuildUnionFieldsAfterWriteOpt
    (layouts : LayoutTable)
    (activeIdx curIdx : Nat)
    (newFieldVal : Value) :
    Nat → List Nat → List Value → Option (List Value)
  | .zero, _, _ => .some .nil
  | .succ rem, flIdxs, oldFields =>
    let (flIdxOpt, nextFlIdxs) : Option Nat × List Nat :=
      match flIdxs with
      | f :: fRest => (.some f, fRest)
      | .nil => (.none, .nil)
    let (oldFvOpt, nextOldFields) : Option Value × List Value :=
      match oldFields with
      | fv :: fvRest => (.some fv, fvRest)
      | .nil => (.none, .nil)
    match
      rebuildUnionFieldsAfterWriteOpt
        layouts
        activeIdx
        (.succ curIdx)
        newFieldVal
        rem
        nextFlIdxs
        nextOldFields
    with
    | .none => .none
    | .some tail =>
      match Nat.beq curIdx activeIdx with
      | true => .some (newFieldVal :: tail)
      | false =>
        match flIdxOpt, oldFvOpt with
        | .none, .some (.aggregate 0 .nil) =>
          match layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries with
          | true => .some (.unit :: tail)
          | false => .some (.aggregate 0 .nil :: tail)
        | .some sibFlIdx, .some (.aggregate 0 .nil) =>
          match LayoutTable.lookup layouts sibFlIdx with
          | .some sibL =>
            match Nat.beq sibL.size.bytes 0 with
            | true => .some (.aggregate 0 .nil :: tail)
            | false => .some (.unit :: tail)
          | .none => .some (.unit :: tail)
        | _, _ => .some (.unit :: tail)

/--
`true` when the active value `v` of a union field must be stored as the `.unit`
placeholder in `typedFields`:
- `v` has no faithful layout-free image (`unionSlotLacksLayoutFreeImage`) and its
  field/operand type is statically zero-sized; or
- the union has no `fieldLayouts` (`unionFieldLayouts = .nil`) and `v` is a
  field-less aggregate `.aggregate _ .nil` whose typed byte image (`opTyOpt`) is
  non-empty, so `v`'s exact tag/padding bytes are carried by the raw-byte overlay
  and any non-ZST `.aggregate _ .nil` later found in `typedFields` alongside an
  overlay can only come from a stale union-unaware `writeProjectedValue`.
-/
def unionActiveSlotIsZstPlaceholder
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (opTyOpt : Option Ty)
    (v : Value)
    (unionFieldLayouts : List Nat := .nil) :
    Bool :=
  match unionSlotLacksLayoutFreeImage layouts v, opTyOpt with
  | true, .some opTy =>
    let rOpTy := resolveTyWithLocalDecls localDecls layouts opTy
    match tyByteSize localDecls layouts rOpTy with
    | .some 0 => true
    | _ =>
      match unionFieldLayouts, v with
      | .nil, .aggregate _ .nil =>
        match encodeTypedValueToBytes layouts rOpTy v with
        | .some (_ :: _) => true
        | _ => false
      | _, _ => false
  | _, _ => false

/--
True when `v` is an unpopulated intermediate shell `.aggregate 0 fields`
materialized by `ensureNestedFieldShells` (every slot is `.unit` or recursively
an unpopulated shell).
-/
def isUnpopulatedFieldShell : Value → Bool
  | .unit => true
  | .aggregate 0 .nil => true
  | .aggregate 0 (f :: fs) =>
    Bool.and (isUnpopulatedFieldShell f) (isUnpopulatedFieldShell (.aggregate 0 fs))
  | _ => false

/--
True when every element of `vs` is `.unit`.
-/
def allValueUnits : List Value → Bool
  | .nil => true
  | .unit :: rest => allValueUnits rest
  | _ :: _ => false

/--
If `fields[idx]` is a synthetic unpopulated shell `.aggregate 0 innerFs`
materialized by `ensureNestedFieldShells` (not a valid typed value of `rFieldTy`),
restore that slot to `.unit` (or collapse an all-`.unit` shell list back to `.nil`).
-/
def stripUnpopulatedUnionShellAtIdx
    (layouts : LayoutTable)
    (rFieldTy : Ty)
    (idx : Nat) :
    List Value → List Value
  | .nil => .nil
  | f₀ :: fRest =>
    let fields := f₀ :: fRest
    match get? fields idx with
    | .some (.aggregate 0 innerFs) =>
      match isUnpopulatedFieldShell (.aggregate 0 innerFs) with
      | false => fields
      | true =>
        match encodeTypedValueToBytes layouts rFieldTy (.aggregate 0 innerFs) with
        | .some _ => fields
        | .none =>
          match set? fields idx .unit with
          | .some cleared =>
            match allValueUnits cleared with
            | true => .nil
            | false => cleared
          | .none => fields
    | _ => fields

/--
Write `newVal` along deref-free projection chain `proj` into `v` of static type
`baseTy` with union sibling-field synchronization and partial sub-field byte
overlay support.
-/
def writeProjectedValueUnionAware
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Value → Ty → List ProjectionElem → Value → ProjWriteResult
  | _, _, .nil, newVal => .ok newVal
  | v, _, .opaqueCast castTy :: rest, newVal =>
    writeProjectedValueUnionAware
      locals
      localDecls
      layouts
      v
      (resolveTyWithLocalDecls localDecls layouts castTy)
      rest
      newVal
  | v, _, .unwrapUnsafeBinder innerTy :: rest, newVal =>
    writeProjectedValueUnionAware
      locals
      localDecls
      layouts
      v
      (resolveTyWithLocalDecls localDecls layouts innerTy)
      rest
      newVal
  | .aggregate varIdx fields, baseTy, .downcast _ targetVar :: rest, newVal =>
    match Nat.beq varIdx targetVar with
    | true =>
      writeProjectedValueUnionAware
        locals
        localDecls
        layouts
        (.aggregate varIdx fields)
        baseTy
        rest
        newVal
    | false => .ub
  | _, _, .downcast _ _ :: _, _ => .ub
  | v, baseTy, .field idx fieldTy :: rest, newVal =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    let unionCountAndLayoutOpt : Option (Nat × TypeLayout) :=
      match rBase.kind with
      | .adt _ _ =>
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some l =>
          match l.fields with
          | .union count => .some (count, l)
          | _ => .none
        | .none => .none
      | _ => .none
    match unionCountAndLayoutOpt with
    | .some (count, l) =>
      match v, Nat.ble (.succ idx) count with
      | .aggregate 0 rawFields, true =>
        let rFieldTy : Ty :=
          match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
          | false => fieldTy
          | true =>
            match get? l.fieldLayouts idx with
            | .some flIdx => { fieldTy with layoutIdx := flIdx }
            | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
        let fields : List Value :=
          match rest with
          | .nil => rawFields
          | _ :: _ => stripUnpopulatedUnionShellAtIdx layouts rFieldTy idx rawFields
        let baseBytesOpt :=
          encodeByLayoutIdxAux 8 layouts rBase.layoutIdx (.aggregate 0 fields)
        let baseConsistent : Bool :=
          match baseBytesOpt with
          | .some unionBytes =>
            match unionNeedsConsistencyCheck count fields, l.fieldLayouts, get? fields idx with
            | true, .nil, .some (.aggregate varIdx aggFs) =>
              match encodeTypedValueToBytes layouts rFieldTy (.aggregate varIdx aggFs) with
              | .none => false
              | .some fBytes =>
                let fMask := layoutValueMaskAux 8 layouts rFieldTy.layoutIdx
                match
                  mergeMaskedAbstractBytes
                    unionBytes
                    (replicateBool (length unionBytes) true)
                    fBytes
                    fMask
                with
                | .some _ => true
                | .none => false
            | _, _, _ => true
          | .none => Bool.not (unionNeedsConsistencyCheck count fields)
        let baseBytes :=
          match baseBytesOpt with
          | .some bs => bs
          | .none => replicateUninitBytes l.size.bytes
        let commitFullFieldUpdate (updatedFv : Value) : ProjWriteResult :=
          let patchBytesOpt := encodeTypedValueToBytes layouts rFieldTy updatedFv
          let fullWidthOverwrite : Bool :=
            match patchBytesOpt with
            | .some pbs => Nat.beq (length pbs) l.size.bytes
            | .none => false
          match Bool.or baseConsistent fullWidthOverwrite with
          | false => .unsupported
          | true =>
            let mergedBytes :=
              match patchBytesOpt with
              | .some pbs =>
                match writeAbstractBytesAt baseBytes 0 pbs with
                | .some mbs => mbs
                | .none => baseBytes
              | .none => baseBytes
            -- The `.unit` placeholder choice is a `match` taken before `.ok` is
            -- built (continuation `finish`), so the stored union value carries
            -- no unreduced application of the check (see
            -- `evalAggregateAdtUnionValue?`).
            let finish : Value → ProjWriteResult := fun slotFv =>
              match
                rebuildUnionFieldsAfterWriteOpt
                  layouts
                  idx
                  0
                  slotFv
                  count
                  l.fieldLayouts
                  fields
              with
              | .none => .ub
              | .some typedFields =>
                match patchBytesOpt with
                | .some _ =>
                  match
                    finalizeUnionFieldsWithRawOverlayOpt
                      layouts
                      rBase.layoutIdx
                      typedFields
                      mergedBytes
                  with
                  | .some finalFields => .ok (.aggregate 0 finalFields)
                  | .none => .ub
                | .none => .ok (.aggregate 0 typedFields)
            match
              unionActiveSlotIsZstPlaceholder
                localDecls
                layouts
                (.some rFieldTy)
                updatedFv
                l.fieldLayouts
            with
            | true => finish .unit
            | false => finish updatedFv
        let isLeafFieldWrite : Bool :=
          match rest with
          | .nil => true
          | _ :: _ => false
        match isLeafFieldWrite with
        | true => commitFullFieldUpdate newVal
        | false =>
          let uninitNonFieldSubProj : Bool :=
            match fields, stripTransparentProjections rest with
            | .nil, .field _ _ :: _ => false
            | .nil, _ => true
            | _ :: _, _ => false
          match uninitNonFieldSubProj with
          | true => .ub
          | false =>
            match baseConsistent with
            | false => .unsupported
            | true =>
              -- A write to a statically addressed sub-place `u.f.<rest>` stores
              -- exactly `size_of(leaf)` bytes at the sub-place offset: sibling bytes
              -- of the union (including padding bytes of `f` itself) keep their
              -- current contents, so it is applied as a byte patch on the union
              -- image rather than as a read-modify-write of the whole field `f`
              -- (which would re-encode `f`'s padding as uninitialized).
              let staticLeafPatchOpt : Option (List AbstractByte) :=
                match resolveUnionSubProjIndices locals rest with
                | .none => .none
                | .some idxResolved =>
                  let normRest :=
                    normalizeSubsliceProjections (stripTransparentProjections idxResolved)
                  match checkStaticSubProjBounds localDecls layouts rFieldTy normRest with
                  | false => .none
                  | true =>
                    match
                      projectionChainByteOffset?
                        layouts
                        (.some rFieldTy)
                        .none
                        .none
                        0
                        localDecls
                        normRest,
                      resolveProjectedTyResolved localDecls layouts rFieldTy normRest
                    with
                    | .some subOff, .some leafTy =>
                      match encodeTypedValueToBytes layouts leafTy newVal with
                      | .none => .none
                      | .some patchBytes => writeAbstractBytesAt baseBytes subOff patchBytes
                    | _, _ => .none
              match staticLeafPatchOpt with
              | .some mergedBytes =>
                let fullFvOpt : Option Value :=
                  match tyByteSize localDecls layouts rFieldTy with
                  | .some fSz =>
                    match sliceAbstractBytes mergedBytes 0 fSz with
                    | .some fSlice =>
                      decodeTypedValueFromBytes defaultCodecFuel layouts rFieldTy fSlice
                    | .none => .none
                  | .none => .none
                let slotFv : Value :=
                  match fullFvOpt with
                  | .some fv => fv
                  | .none => .unit
                match
                  rebuildUnionFieldsAfterWriteOpt
                    layouts
                    idx
                    0
                    slotFv
                    count
                    l.fieldLayouts
                    fields
                with
                | .none => .ub
                | .some typedFields =>
                  match
                    finalizeUnionFieldsWithRawOverlayOpt
                      layouts
                      rBase.layoutIdx
                      typedFields
                      mergedBytes
                  with
                  | .some finalFields => .ok (.aggregate 0 finalFields)
                  | .none => .ub
              | .none =>
                match
                  readProjectedValueUnionAware
                    locals
                    localDecls
                    layouts
                    (.aggregate 0 fields)
                    rBase
                    (.field idx rFieldTy :: .nil)
                with
                | .ok curFv =>
                  match
                    writeProjectedValueUnionAware
                      locals
                      localDecls
                      layouts
                      curFv
                      rFieldTy
                      rest
                      newVal
                  with
                  | .ok updatedFv => commitFullFieldUpdate updatedFv
                  | .ub => .ub
                  | .unsupported => .unsupported
                | .unsupported => .unsupported
                | .ub =>
                  match wrapFullWidthInitChain? localDecls layouts rFieldTy rest newVal with
                  | .some wrappedFv => commitFullFieldUpdate wrappedFv
                  | .none =>
                    match get? rawFields idx with
                    | .some (.aggregate 0 innerFs) =>
                      match
                        writeProjectedValueUnionAware
                          locals
                          localDecls
                          layouts
                          (.aggregate 0 innerFs)
                          rFieldTy
                          rest
                          newVal
                      with
                      | .ok updatedFv => commitFullFieldUpdate updatedFv
                      | .ub => .ub
                      | .unsupported => .unsupported
                    | _ => .ub
      | _, _ => .ub
    | .none =>
      let nextTy : Ty :=
        match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
        | false => fieldTy
        | true =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some l =>
            match l.variants with
            | .single _ =>
              match get? l.fieldLayouts idx with
              | .some flIdx => { fieldTy with layoutIdx := flIdx }
              | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
            | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
      match v with
      | .aggregate varIdx fields =>
        match get? fields idx with
        | .some oldFv =>
          match writeProjectedValueUnionAware locals localDecls layouts oldFv nextTy rest newVal with
          | .ok updatedFv =>
            match set? fields idx updatedFv with
            | .some fields' => .ok (.aggregate varIdx fields')
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | .none =>
          match rest with
          | .nil => .ok (.aggregate varIdx (setOrExtendFields fields idx newVal))
          | _ :: _ => .ub
      | .scalar sc =>
        match idx with
        | .zero =>
          writeProjectedValueUnionAware locals localDecls layouts (.scalar sc) nextTy rest newVal
        | .succ _ => .ub
      | .ptr p sz =>
        match idx with
        | .zero =>
          writeProjectedValueUnionAware locals localDecls layouts (.ptr p sz) nextTy rest newVal
        | .succ _ => .ub
      | .unit => .ub
  | .aggregate 0 elems, baseTy, .index idxLocal :: rest, newVal =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    let elemTy : Ty :=
      match elemTyOf rBase with
      | .some { kind := ek, .. } =>
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      | .none => rBase
    match get? locals idxLocal with
    | .some (.init (.scalar idxSc)) =>
      match get? elems idxSc.bits with
      | .some oldEv =>
        match writeProjectedValueUnionAware locals localDecls layouts oldEv elemTy rest newVal with
        | .ok updatedEv =>
          match set? elems idxSc.bits updatedEv with
          | .some elems' => .ok (.aggregate 0 elems')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | _ => .ub
  | _, _, .index _ :: _, _ => .ub
  | .aggregate 0 elems, baseTy, .constantIndex offset minLen fromEnd :: rest, newVal =>
    let len := length elems
    let fromEndOk :=
      match fromEnd with
      | false => true
      | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset len)
    match Bool.and (Nat.ble minLen len) fromEndOk with
    | false => .ub
    | true =>
      let idx :=
        match fromEnd with
        | true => Nat.sub len offset
        | false => offset
      let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
      let elemTy : Ty :=
        match elemTyOf rBase with
        | .some { kind := ek, .. } =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
            { kind := ek, layoutIdx := flIdx }
          | _ =>
            resolveTyWithLocalDecls
              localDecls
              layouts
              { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
        | .none => rBase
      match get? elems idx with
      | .some oldEv =>
        match writeProjectedValueUnionAware locals localDecls layouts oldEv elemTy rest newVal with
        | .ok updatedEv =>
          match set? elems idx updatedEv with
          | .some elems' => .ok (.aggregate 0 elems')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
  | _, _, .constantIndex _ _ _ :: _, _ => .ub
  | .aggregate 0 elems, baseTy, .subslice fromIdx toIdx fromEnd :: rest, newVal =>
    match extractSubslice elems fromIdx toIdx fromEnd with
    | .none => .ub
    | .some subElems =>
      let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
      let subTy : Ty :=
        match rBase.kind with
        | .array ek _ =>
          { kind := .array ek (length subElems), layoutIdx := rBase.layoutIdx }
        | _ => rBase
      match
        writeProjectedValueUnionAware
          locals
          localDecls
          layouts
          (.aggregate 0 subElems)
          subTy
          rest
          newVal
      with
      | .ok (.aggregate 0 updatedSubElems) =>
        match replaceSubslice elems fromIdx toIdx fromEnd updatedSubElems with
        | .some elems' => .ok (.aggregate 0 elems')
        | .none => .ub
      | .ok _ => .ub
      | .ub => .ub
      | .unsupported => .unsupported
  | _, _, .subslice _ _ _ :: _, _ => .ub
  | _, _, .deref :: _, _ => .unsupported

/--
Read `proj` on `rootVal` at `loc` using `readProjectedValueUnionAware` when the
place touches a union in `localDecls` / `layouts`, and `readProjectedValue`
otherwise.
-/
@[reducible]
def readProjectedForLocal
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (rootVal : Value)
    (proj : List ProjectionElem) :
    ProjReadResult :=
  match placeTouchesUnion localDecls layouts { local_ := loc, projection := proj } with
  | false => readProjectedValue locals rootVal proj
  | true =>
    match get? localDecls loc with
    | .some decl =>
      readProjectedValueUnionAware locals localDecls layouts rootVal decl.ty proj
    | .none => readProjectedValue locals rootVal proj

/--
Write `newVal` to `proj` on `rootVal` at `loc` using
`writeProjectedValueUnionAware` when the place touches a union in `localDecls` /
`layouts`, and `writeProjectedValue` otherwise.
-/
@[reducible]
def writeProjectedForLocal
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (rootVal : Value)
    (proj : List ProjectionElem)
    (newVal : Value) :
    ProjWriteResult :=
  match placeTouchesUnion localDecls layouts { local_ := loc, projection := proj } with
  | false => writeProjectedValue locals rootVal proj newVal
  | true =>
    match get? localDecls loc with
    | .some decl =>
      writeProjectedValueUnionAware locals localDecls layouts rootVal decl.ty proj newVal
    | .none => writeProjectedValue locals rootVal proj newVal

/-- Alias for `writeProjectedForLocal`. -/
abbrev writeProjectedValueForLocal := writeProjectedForLocal


/--
Resolve a layout-faithful `Ty` for an aggregate `baseTy` with runtime variant
`varIdx` and field list `fields`:
- For arrays/slices of a primitive scalar kind (`varIdx = 0`), synthesizes the
  exact-length array `{ kind := .array (byteCodecScalarKind elemKind) (length fields), ... }`
  so both `[T; N]` and `.subslice` / `[T]` views encode faithfully.
- For layout-free tuples (`()`, `(T,)`, or homogeneous primitive scalar tuples),
  allows encoding even without a `LayoutTable` entry.
- Otherwise, resolves `baseTy` via `resolveTyWithLocalDecls localDecls layouts`,
  requires a captured `TypeLayout` entry matching `(varIdx, length fields)`, and
  requires all field values to be flat scalars (`allFlatScalarValues fields`).
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
  | .array elemKind _ | .slice elemKind =>
    match Bool.and (Nat.beq varIdx 0) (isPrimitiveScalarKind elemKind) with
    | true =>
      .some
        { kind := .array (byteCodecScalarKind elemKind) (length fields)
          layoutIdx := unresolvedLayoutIdx layouts }
    | false =>
      let resolvedTy := resolveTyWithLocalDecls localDecls layouts baseTy
      match allFlatScalarValues fields, LayoutTable.lookup layouts resolvedTy.layoutIdx with
      | true, .some l =>
        match l.fields with
        | .array _ count =>
          match Bool.and (Nat.beq varIdx 0) (Nat.beq count (length fields)) with
          | true => .some resolvedTy
          | false => .none
        | _ => .none
      | _, _ => .none
  | .tuple ks =>
    match allFlatScalarValues fields with
    | false => .none
    | true =>
      let resolvedTy := resolveTyWithLocalDecls localDecls layouts baseTy
      match LayoutTable.lookup layouts resolvedTy.layoutIdx with
      | .some l =>
        match layoutMatchesAggregateVariant l varIdx (length fields) with
        | true => .some (normalizeCodecTy resolvedTy)
        | false => .none
      | .none =>
        match
          Bool.and
            (Nat.beq varIdx 0)
            (Bool.and
              (Nat.beq (length fields) (length ks))
              (isLayoutFreeTupleKinds ks))
        with
        | true =>
          .some
            { kind := .tuple (mapByteCodecScalarKinds ks)
              layoutIdx := unresolvedLayoutIdx layouts }
        | false => .none
  | _ =>
    let resolvedTy := resolveTyWithLocalDecls localDecls layouts baseTy
    match LayoutTable.lookup layouts resolvedTy.layoutIdx with
    | .some l =>
      match l.isUninhabited, l.fields with
      | false, .union count =>
        match Bool.and (Nat.beq varIdx 0) (Nat.ble (length fields) (.succ count)) with
        | true => .some resolvedTy
        | false => .none
      | _, _ =>
        match
          Bool.and
            (Bool.or
              (allFlatScalarValues fields)
              (Nat.beq (length l.fieldLayouts) (length fields)))
            (layoutMatchesAggregateVariant l varIdx (length fields))
        with
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
      | .unit, _ => .some .nil
      | .scalar _, _ => encodeUntypedValueToBytes defaultCodecFuel baseVal
      | .ptr _ _, _ => encodeUntypedValueToBytes defaultCodecFuel baseVal
      | .aggregate varIdx fields, .some baseTy =>
        match resolveFaithfulAggregateTy? localDecls layouts baseTy varIdx fields with
        | .some resolvedTy => encodeTypedValueToBytes layouts resolvedTy baseVal
        | .none => .none
      | _, _ => .none
    match encodedOpt with
    | .none => .none
    | .some encodedBytes =>
      match sliceAbstractBytes encodedBytes offsetBytes reqBytes with
      | .none => .none
      | .some sliceBytes =>
        decodeTypedValueFromBytes defaultCodecFuel layouts rAccTy sliceBytes

/--
Byte-offset decoding fallback for a typed thin-pointer dereference read:
- For `restProj = []`, decodes `accessedTyOpt` at `ptrVal.offsetBytes` within
  the borrow target value (`entry.targetProjection` of `targetRootVal`).
- For `restProj = _ :: _` with known `pointeeTyOpt`, decodes `pointeeTyOpt` at
  `ptrVal.offsetBytes` and applies `readProjectedValue locals · restProj`.
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
    (localDecls : List LocalDecl := .nil)
    (pointeeTyOpt : Option Ty := .none) :
    Option Value :=
  match restProj with
  | .nil =>
    match accessedTyOpt with
    | .some accTy =>
      match
        readProjectedForLocal
          locals
          localDecls
          layouts
          entry.targetLocal
          targetRootVal
          entry.targetProjection
      with
      | .ok baseVal =>
        decodeSubValueAtByteOffset? layouts targetTyOpt baseVal ptrVal.offsetBytes accTy localDecls
      | _ => .none
    | .none => .none
  | pHead :: pTail =>
    match pointeeTyOpt with
    | .some pt =>
      match
        readProjectedForLocal
          locals
          localDecls
          layouts
          entry.targetLocal
          targetRootVal
          entry.targetProjection
      with
      | .ok baseVal =>
        match
          decodeSubValueAtByteOffset? layouts targetTyOpt baseVal ptrVal.offsetBytes pt localDecls
        with
        | .some decodedPt =>
          match
            readProjectedValueUnionAware
              locals
              localDecls
              layouts
              decodedPt
              pt
              (pHead :: pTail)
          with
          | .ok projVal => .some projVal
          | _ => .none
        | .none => .none
      | _ => .none
    | .none => .none

/--
Set or extend `decls` at `loc` with `newDecl`, appending any replaced declaration
to the tail so ADT type-layout lookups across `decls` remain complete.
-/
def setOrExtendLocalDecls
    (placeholderTy : Ty) :
    List LocalDecl → Nat → LocalDecl → List LocalDecl
  | .nil, .zero, newDecl => newDecl :: .nil
  | .nil, .succ k, newDecl =>
    { mutability := .mut, ty := placeholderTy, debugName := .none } ::
      setOrExtendLocalDecls placeholderTy .nil k newDecl
  | oldDecl :: rest, .zero, newDecl =>
    newDecl :: appendLocalDecls rest (oldDecl :: .nil)
  | d :: rest, .succ k, newDecl =>
    d :: setOrExtendLocalDecls placeholderTy rest k newDecl
where
  appendLocalDecls : List LocalDecl → List LocalDecl → List LocalDecl
    | .nil, ys => ys
    | x :: xs, ys => x :: appendLocalDecls xs ys

/--
Infer a synthetic `List LocalDecl` for a caller-frame borrow target
(`targetDecls = .nil`, so the caller's declarations are not in scope) from
statically known types only:
- when the borrow covers the whole target local (`entry.targetProjection = .nil`)
  and the access starts at offset `0`, a union pointee type `effPointeeTyOpt` is
  the type at which the target's storage is accessed, so it is used as the
  target root type;
- otherwise, when the `.field` type annotations along `rawFullProj` project
  through a union field (`tyProjTouchesUnion` from a placeholder root), the root
  is given a placeholder non-union type so union-aware projection applies from
  the first annotated union onward.
The target root type is never guessed from the runtime shape of the target value
(a struct value can coincide with a union layout's slot shape).
-/
def inferCallerTargetDecls
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (entry : BorrowEntry)
    (rawFullProj : List ProjectionElem)
    (ptrOffsetBytes : Nat)
    (effPointeeTyOpt : Option Ty) :
    List LocalDecl :=
  let placeholderTy : Ty :=
    { kind := .adt "" .nil, layoutIdx := unresolvedLayoutIdx layouts }
  let projEndsAtUnion : List ProjectionElem → Bool
    | .nil => false
    | pHead :: pTail =>
      match resolveProjectedTyResolved localDecls layouts placeholderTy (pHead :: pTail) with
      | .some leafTy => isUnionLayout layouts leafTy
      | .none => false
  let annotatedRootOpt : Option Ty :=
    match
      Bool.or
        (tyProjTouchesUnion localDecls layouts placeholderTy rawFullProj)
        (Bool.or
          (projEndsAtUnion rawFullProj)
          (projEndsAtUnion entry.targetProjection))
    with
    | true => .some placeholderTy
    | false => .none
  let rootTyOpt : Option Ty :=
    match entry.targetProjection, Nat.beq ptrOffsetBytes 0, effPointeeTyOpt with
    | .nil, true, .some pt =>
      match isUnionLayout layouts pt with
      | true => .some pt
      | false => annotatedRootOpt
    | _, _, _ => annotatedRootOpt
  match rootTyOpt with
  | .none => .nil
  | .some rootTy =>
    setOrExtendLocalDecls
      placeholderTy
      localDecls
      entry.targetLocal
      { mutability := .mut, ty := rootTy, debugName := .none }

/--
Dereference and project a stack-backed thin pointer `ptrVal` (`BorrowEntry`
`entry`, referent root `targetRootVal`) with alignment, scalar width slicing,
out-of-bounds offset detection, and bit-validity checks.

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
    let effTargetDecls : List LocalDecl :=
      match targetDecls with
      | _ :: _ => targetDecls
      | .nil =>
        inferCallerTargetDecls
          localDecls
          layouts
          entry
          rawFullProj
          ptrVal.offsetBytes
          effPointeeTyOpt
    let codecDecls : List LocalDecl :=
      match effTargetDecls with
      | .nil => localDecls
      | _ :: _ => effTargetDecls
    let effTargetTyOpt : Option Ty :=
      match targetTyOpt with
      | .some tTy => .some tTy
      | .none =>
        placeTyResolved
          effTargetDecls
          layouts
          { local_ := entry.targetLocal, projection := entry.targetProjection }
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
            match
              readProjectedForLocal
                locals
                effTargetDecls
                layouts
                entry.targetLocal
                targetRootVal
                rawFullProj
            with
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
        let fallbackDecode : Option Value :=
          decodeAtBorrowTargetOffset?
            locals
            targetRootVal
            entry
            ptrVal
            restProj
            layouts
            resolvedAccTyOpt
            effTargetTyOpt
            codecDecls
            effPointeeTyOpt
        match
          resolveStackThinPtrTargetProjWithResidual?
            locals
            targetRootVal
            entry
            ptrVal
            restProj
            effTargetDecls
            layouts
            effPointeeTyOpt
            reqBytesOpt
        with
        | .none =>
          match fallbackDecode with
          | .some decodedVal =>
            match validateValueForTy? layouts resolvedAccTyOpt decodedVal with
            | true => .ok decodedVal locals
            | false => .ub
          | .none => .ub
        | .some (fullProj, residualBytes) =>
          match
            readProjectedForLocal
              locals
              effTargetDecls
              layouts
              entry.targetLocal
              targetRootVal
              fullProj
          with
          | .ok fieldVal =>
            let subTyOpt : Option Ty :=
              placeTyResolved
                effTargetDecls
                layouts
                { local_ := entry.targetLocal, projection := fullProj }
            let decodeFromResolvedOrTarget : Ty → Option Value := fun accTy =>
              match
                decodeSubValueAtByteOffset?
                  layouts
                  subTyOpt
                  fieldVal
                  residualBytes
                  accTy
                  codecDecls
              with
              | .some v => .some v
              | .none => fallbackDecode
            let finalValOpt : Option Value :=
              match resolvedAccTyOpt with
              | .none =>
                match Nat.beq residualBytes 0 with
                | true => .some fieldVal
                | false => .none
              | .some accTy =>
                match accTy.kind with
                | .never => .none
                | .tuple .nil | .fnDef _ _ =>
                  match Nat.beq residualBytes 0 with
                  | true =>
                    match fieldVal with
                    | .aggregate 0 .nil => .some (.aggregate 0 .nil)
                    | _ => .some .unit
                  | false => decodeFromResolvedOrTarget accTy
                | _ =>
                  match tyScalarBytes accTy with
                  | .some reqBytes =>
                    match fieldVal with
                    | .scalar fSc =>
                      match
                        Bool.and
                          (Nat.beq residualBytes 0)
                          (Nat.beq reqBytes fSc.sizeBytes)
                      with
                      | true => .some (.scalar fSc)
                      | false =>
                        match extractScalarSlice? fSc residualBytes reqBytes with
                        | .some slicedSc => .some (.scalar slicedSc)
                        | .none => decodeFromResolvedOrTarget accTy
                    | .unit => decodeFromResolvedOrTarget accTy
                    | _ => decodeFromResolvedOrTarget accTy
                  | .none =>
                    match isThinPtrKind accTy.kind with
                    | true =>
                      match fieldVal with
                      | .ptr p pSz =>
                        match
                          Bool.and
                            (Nat.beq residualBytes 0)
                            (Nat.beq pSz (layoutPointerBytes layouts))
                        with
                        | true => .some (.ptr p pSz)
                        | false => .none
                      | .unit => decodeFromResolvedOrTarget accTy
                      | _ => decodeFromResolvedOrTarget accTy
                    | false =>
                      match Nat.beq residualBytes 0 with
                      | false => decodeFromResolvedOrTarget accTy
                      | true =>
                        match subTyOpt with
                        | .some subTy =>
                          let unitOkForNonZst : Bool :=
                            match fieldVal with
                            | .unit =>
                              match tyByteSize codecDecls layouts accTy with
                              | .some (.succ _) => false
                              | _ => true
                            | _ => true
                          match
                            Bool.and
                              unitOkForNonZst
                              (Bool.and
                                (Bool.not (endsWithSubslice fullProj))
                                (rigidTyEq accTy.kind subTy.kind))
                          with
                          | true => .some fieldVal
                          | false =>
                            let sameElemArrayMatchOpt : Option (Option Value) :=
                              match accTy.kind, subTy.kind with
                              | .array accEk accLen, .array subEk _ =>
                                match rigidTyEq accEk subEk with
                                | true =>
                                  match fieldVal with
                                  | .aggregate 0 elems =>
                                    match Nat.beq (length elems) accLen with
                                    | true => .some (.some fieldVal)
                                    | false => .some .none
                                  | _ => .some .none
                                | false => .none
                              | .array accEk accLen, .slice subEk =>
                                match rigidTyEq accEk subEk with
                                | true =>
                                  match fieldVal with
                                  | .aggregate 0 elems =>
                                    match Nat.beq (length elems) accLen with
                                    | true => .some (.some fieldVal)
                                    | false => .some .none
                                  | _ => .some .none
                                | false => .none
                              | _, _ => .none
                            match sameElemArrayMatchOpt with
                            | .some res => res
                            | .none => decodeFromResolvedOrTarget accTy
                        | .none =>
                          match fieldVal with
                          | .unit =>
                            match tyByteSize localDecls layouts accTy with
                            | .some 0 => .some .unit
                            | .some _ => .none
                            | .none => .some .unit
                          | .scalar _ | .ptr _ _ =>
                            match tyByteSize localDecls layouts accTy with
                            | .some _ =>
                              decodeSubValueAtByteOffset?
                                layouts
                                .none
                                fieldVal
                                0
                                accTy
                                localDecls
                            | .none => .some fieldVal
                          | .aggregate _ _ => .some fieldVal
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
  let alignTyOpt : Option Ty :=
    match pointeeTyOpt, restProj with
    | .some pt, _ => .some pt
    | .none, .nil => accessedTyOpt
    | .none, _ :: _ => .none
  match
    Bool.and
      (Nat.beq ptrSz ptrBytes)
      (Bool.and
        (Nat.beq lenSc.sizeBytes ptrBytes)
        (checkDerefAlign localDecls layouts alignTyOpt ptrVal.offsetBytes))
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
        let targetRootAndDeclsOpt : Option (Value × List LocalDecl) :=
          match get? locals entry.targetLocal with
          | .some (.init v) => .some (v, localDecls)
          | .some _ => .none
          | .none =>
            match get? callerLocals entry.targetLocal with
            | .some (.init v) => .some (v, .nil)
            | _ => .none
        match targetRootAndDeclsOpt with
        | .some (targetRootVal, targetDecls) =>
          match
            checkTargetPlaceAlign
              targetDecls
              layouts
              alignTyOpt
              entry
              ptrVal
              (.some targetRootVal)
          with
          | false => .ub
          | true =>
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
        match checkGlobalAllocAlign localDecls layouts alignTyOpt alloc ptrVal.offsetBytes with
        | false => .ub
        | true =>
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
    let globalAlignTyOpt : Option Ty :=
      match pointeeTyOpt, restProj with
      | .some pt, _ => .some pt
      | .none, .nil => accessedTyOpt
      | .none, _ :: _ => .none
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
        match checkDerefAlign localDecls layouts globalAlignTyOpt ptrVal.offsetBytes with
        | false => .ub
        | true =>
          match lookupGlobalAlloc globals ptrVal.allocId with
          | .some alloc =>
            match
              checkGlobalAllocAlign localDecls layouts globalAlignTyOpt alloc ptrVal.offsetBytes
            with
            | false => .ub
            | true =>
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
  | .nil =>
    match get? locals p.local_ with
    | .some (.init rootVal) =>
      match validateValueForTy? layouts (placeTy localDecls layouts p) rootVal with
      | true => .ok rootVal locals
      | false => .ub
    | .some .uninit => .ub
    | .some .dead => .ub
    | .none => .ub
  | proj :: rest =>
    match get? locals p.local_ with
    | .some (.init rootVal) =>
      match readProjectedForLocal locals localDecls layouts p.local_ rootVal (proj :: rest) with
      | .ok fieldVal =>
        match validateValueForTy? layouts (placeTyResolved localDecls layouts p) fieldVal with
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
            let globalAlignTyOpt : Option Ty :=
              match pointeeTyOpt, restProj with
              | .some pt, _ => .some pt
              | .none, .nil => accessedTyOpt
              | .none, _ :: _ => .none
            match checkDerefAlign localDecls layouts globalAlignTyOpt ptrVal.offsetBytes with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  checkGlobalAllocAlign
                    localDecls
                    layouts
                    globalAlignTyOpt
                    alloc
                    ptrVal.offsetBytes
                with
                | false => .ub
                | true =>
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
    | .nil =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue locals rootVal .nil with
        | .ok fieldVal => .ok fieldVal locals
        | .ub => .ub
        | .unsupported => .unsupported
      | .some .uninit => .ub
      | .some .dead => .ub
      | .none => .ub
    | proj :: rest =>
      match get? locals p.local_ with
      | .some (.init rootVal) =>
        match placeTouchesUnion localDecls layouts p with
        | false =>
          match readProjectedValue locals rootVal (proj :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | true =>
          match readProjectedForLocal locals localDecls layouts p.local_ rootVal (proj :: rest) with
          | .ok fieldVal =>
            match validateValueForTy? layouts (placeTyResolved localDecls layouts p) fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
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
            let globalAlignTyOpt : Option Ty :=
              match pointeeTyOpt, restProj with
              | .some pt, _ => .some pt
              | .none, .nil => accessedTyOpt
              | .none, _ :: _ => .none
            match checkDerefAlign localDecls layouts globalAlignTyOpt ptrVal.offsetBytes with
            | false => .ub
            | true =>
              match lookupGlobalAlloc globals ptrVal.allocId with
              | .some alloc =>
                match
                  checkGlobalAllocAlign
                    localDecls
                    layouts
                    globalAlignTyOpt
                    alloc
                    ptrVal.offsetBytes
                with
                | false => .ub
                | true =>
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
        match placeTouchesUnion localDecls layouts p with
        | false =>
          match readProjectedValue locals rootVal (proj :: rest) with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
        | true =>
          match readProjectedForLocal locals localDecls layouts p.local_ rootVal (proj :: rest) with
          | .ok fieldVal =>
            match validateValueForTy? layouts (placeTyResolved localDecls layouts p) fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
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
Splice a value `newVal` (of static type `accTyOpt`) at byte offset `offsetBytes`
into `oldSubVal` (of static type `subTyOpt`) by encoding both to
`List AbstractByte`, writing the patch slice via `writeAbstractBytesAt`, and
decoding back to `oldSubVal`'s representation. Returns `.none` on out-of-bounds
width/offset or when either aggregate lacks a layout-faithful byte codec.
-/
def spliceSubValueAtByteOffset?
    (localDecls targetDecls : List LocalDecl)
    (layouts : LayoutTable)
    (subTyOpt : Option Ty)
    (oldSubVal : Value)
    (offsetBytes : Nat)
    (accTyOpt : Option Ty)
    (newVal : Value) :
    Option Value :=
  let patchBytesOpt : Option (List AbstractByte) :=
    match newVal with
    | .unit =>
      match accTyOpt with
      | .some accTy =>
        match tyByteSize localDecls layouts accTy with
        | .some 0 => .some .nil
        | _ => .none
      | .none => .some .nil
    | .scalar wSc => encodeUntypedValueToBytes defaultCodecFuel (.scalar wSc)
    | .ptr p pSz => encodeUntypedValueToBytes defaultCodecFuel (.ptr p pSz)
    | .aggregate varIdx fields =>
      match accTyOpt with
      | .some accTy =>
        match resolveFaithfulAggregateTy? localDecls layouts accTy varIdx fields with
        | .some resolvedAccTy =>
          encodeTypedValueToBytes layouts resolvedAccTy newVal
        | .none => .none
      | .none => .none
  match patchBytesOpt with
  | .none => .none
  | .some patchBytes =>
    match oldSubVal with
    | .unit =>
      match Bool.and (Nat.beq offsetBytes 0) (Nat.beq (length patchBytes) 0) with
      | true => .some .unit
      | false => .none
    | .scalar oldSc =>
      let oldBytes := encodeLittleEndianBytes oldSc.bits oldSc.sizeBytes .none
      match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
      | .none => .none
      | .some mergedBytes =>
        match decodeLittleEndianBytes mergedBytes with
        | .some (mergedBits, _) => .some (.scalar ⟨mergedBits, oldSc.sizeBytes⟩)
        | .none => .none
    | .ptr _ pSz =>
      match Nat.beq pSz (layoutPointerBytes layouts) with
      | false => .none
      | true =>
        match encodeUntypedValueToBytes defaultCodecFuel oldSubVal with
        | .none => .none
        | .some oldBytes =>
          match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
          | .none => .none
          | .some mergedBytes =>
            decodeValueFromBytes
              defaultCodecFuel
              layouts
              { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
              mergedBytes
    | .aggregate oldVar oldFields =>
      match subTyOpt with
      | .none => .none
      | .some subTy =>
        match resolveFaithfulAggregateTy? targetDecls layouts subTy oldVar oldFields with
        | .none => .none
        | .some resolvedSubTy =>
          match encodeTypedValueToBytes layouts resolvedSubTy oldSubVal with
          | .none => .none
          | .some oldBytes =>
            match writeAbstractBytesAt oldBytes offsetBytes patchBytes with
            | .none => .none
            | .some mergedBytes =>
              decodeTypedValueFromBytes defaultCodecFuel layouts resolvedSubTy mergedBytes

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
    let effTargetDecls : List LocalDecl :=
      match targetDecls with
      | _ :: _ => targetDecls
      | .nil =>
        inferCallerTargetDecls
          localDecls
          layouts
          entry
          rawFullProj
          ptrVal.offsetBytes
          effPointeeTyOpt
    let inScalarSpliceOpt : Option PlaceWriteResult :=
      match restProj, val, get? targetLocals entry.targetLocal with
      | .nil, .scalar wSc, .some (.init targetRootVal) =>
        match
          readProjectedForLocal
            indexLocals
            effTargetDecls
            layouts
            entry.targetLocal
            targetRootVal
            rawFullProj
        with
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
                writeProjectedForLocal
                  indexLocals
                  effTargetDecls
                  layouts
                  entry.targetLocal
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
        let commitAtProj : List ProjectionElem → Value → PlaceWriteResult :=
          fun proj storeVal =>
            match proj with
            | .nil =>
              match set? targetLocals entry.targetLocal (.init storeVal) with
              | .some targetLocals' => .ok targetLocals'
              | .none => .ub
            | pHead :: pTail =>
              match
                writeProjectedForLocal
                  indexLocals
                  effTargetDecls
                  layouts
                  entry.targetLocal
                  targetRootVal
                  (pHead :: pTail)
                  storeVal
              with
              | .ok targetRootVal' =>
                match set? targetLocals entry.targetLocal (.init targetRootVal') with
                | .some targetLocals' => .ok targetLocals'
                | .none => .ub
              | .ub => .ub
              | .unsupported => .unsupported
        let spliceIntoRootViaEntryOffset : PlaceWriteResult :=
          match restProj, get? effTargetDecls entry.targetLocal with
          | .nil, .some rootDecl =>
            let normEntryProj :=
              normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
            match
              projectionChainByteOffset?
                layouts
                (.some rootDecl.ty)
                (.some targetRootVal)
                .none
                0
                effTargetDecls
                normEntryProj
            with
            | .none => .ub
            | .some baseOff =>
              match
                spliceSubValueAtByteOffset?
                  localDecls
                  effTargetDecls
                  layouts
                  (.some (resolveTyWithLocalDecls effTargetDecls layouts rootDecl.ty))
                  targetRootVal
                  (Nat.add baseOff ptrVal.offsetBytes)
                  resolvedAccTyOpt
                  val
              with
              | .some splicedRoot => commitAtProj .nil splicedRoot
              | .none => .ub
          | _, _ => .ub
        let reqBytesOpt : Option Nat :=
          match restProj, val with
          | .nil, .scalar wSc => .some wSc.sizeBytes
          | .nil, _ =>
            match resolvedAccTyOpt with
            | .some accTy => tyByteSize localDecls layouts accTy
            | .none => .none
          | _ :: _, _ => .none
        match isSyntheticFieldOnScalarPointee, entry.targetProjection with
        | true, .nil => commitAtProj rawFullProj val
        | _, _ =>
          let resolvedProjOpt : Option (List ProjectionElem × Nat) :=
            resolveStackThinPtrTargetProjWithResidual?
              indexLocals
              targetRootVal
              entry
              ptrVal
              restProj
              effTargetDecls
              layouts
              effPointeeTyOpt
              reqBytesOpt
          match resolvedProjOpt with
        | .none =>
          match restProj with
          | _ :: _ => .ub
          | .nil =>
            match
              readProjectedForLocal
                indexLocals
                effTargetDecls
                layouts
                entry.targetLocal
                targetRootVal
                entry.targetProjection
            with
            | .ok oldBaseVal =>
              let baseSubTyOpt :=
                placeTyResolved
                  effTargetDecls
                  layouts
                  { local_ := entry.targetLocal, projection := entry.targetProjection }
              match
                spliceSubValueAtByteOffset?
                  localDecls
                  effTargetDecls
                  layouts
                  baseSubTyOpt
                  oldBaseVal
                  ptrVal.offsetBytes
                  resolvedAccTyOpt
                  val
              with
              | .some splicedBase => commitAtProj entry.targetProjection splicedBase
              | .none => .ub
            | .ub =>
              match
                placeTouchesUnion
                  effTargetDecls
                  layouts
                  { local_ := entry.targetLocal, projection := entry.targetProjection }
              with
              | true => spliceIntoRootViaEntryOffset
              | false => .ub
            | .unsupported => .unsupported
        | .some (fullProj, residualBytes) =>
          match
            readProjectedForLocal
              indexLocals
              effTargetDecls
              layouts
              entry.targetLocal
              targetRootVal
              fullProj
          with
          | .ub =>
            match
              placeTouchesUnion
                effTargetDecls
                layouts
                { local_ := entry.targetLocal, projection := fullProj }
            with
            | false => .ub
            | true =>
              let subTyOpt : Option Ty :=
                placeTyResolved
                  effTargetDecls
                  layouts
                  { local_ := entry.targetLocal, projection := fullProj }
              let directUnionInitOk : Bool :=
                match Nat.beq residualBytes 0, resolvedAccTyOpt, subTyOpt with
                | true, .some { kind := .never, .. }, _ => false
                | true, .some accTy, .some subTy =>
                  Bool.and
                    (Bool.not (endsWithSubslice fullProj))
                    (rigidTyEq accTy.kind subTy.kind)
                | true, .none, _ => Bool.not (endsWithSubslice fullProj)
                | _, _, _ => false
              match directUnionInitOk with
              | true => commitAtProj fullProj val
              | false => spliceIntoRootViaEntryOffset
          | .unsupported => .unsupported
          | .ok oldVal =>
            let subTyOpt : Option Ty :=
              placeTyResolved
                effTargetDecls
                layouts
                { local_ := entry.targetLocal, projection := fullProj }
            let storeValOpt : Option Value :=
              match resolvedAccTyOpt with
              | .some { kind := .never, .. } => .none
              | _ =>
                match val with
                | .scalar wSc =>
                  match oldVal with
                  | .scalar oldSc =>
                    match spliceScalarSlice? oldSc residualBytes wSc with
                    | .some mergedSc => .some (.scalar mergedSc)
                    | .none => .none
                  | _ =>
                    spliceSubValueAtByteOffset?
                      localDecls
                      effTargetDecls
                      layouts
                      subTyOpt
                      oldVal
                      residualBytes
                      resolvedAccTyOpt
                      val
                | _ =>
                  match Nat.beq residualBytes 0 with
                  | false =>
                    spliceSubValueAtByteOffset?
                      localDecls
                      effTargetDecls
                      layouts
                      subTyOpt
                      oldVal
                      residualBytes
                      resolvedAccTyOpt
                      val
                  | true =>
                    let directStoreOpt : Option (Option Value) :=
                      match resolvedAccTyOpt, subTyOpt with
                      | .some accTy, .some subTy =>
                        match
                          Bool.and
                            (Bool.not (endsWithSubslice fullProj))
                            (rigidTyEq accTy.kind subTy.kind)
                        with
                        | true => .some (.some val)
                        | false =>
                          match accTy.kind, subTy.kind with
                          | .array accEk accLen, .array subEk _ =>
                            match rigidTyEq accEk subEk with
                            | true =>
                              match val, oldVal with
                              | .aggregate 0 newElems, .aggregate 0 oldElems =>
                                match
                                  Bool.and
                                    (Nat.beq (length newElems) accLen)
                                    (Nat.beq (length oldElems) accLen)
                                with
                                | true => .some (.some val)
                                | false => .some .none
                              | _, _ => .some .none
                            | false => .none
                          | .array accEk accLen, .slice subEk =>
                            match rigidTyEq accEk subEk with
                            | true =>
                              match val, oldVal with
                              | .aggregate 0 newElems, .aggregate 0 oldElems =>
                                match
                                  Bool.and
                                    (Nat.beq (length newElems) accLen)
                                    (Nat.beq (length oldElems) accLen)
                                with
                                | true => .some (.some val)
                                | false => .some .none
                              | _, _ => .some .none
                            | false => .none
                          | _, _ => .none
                      | .some accTy, .none =>
                        match oldVal with
                        | .unit =>
                          match tyByteSize localDecls layouts accTy with
                          | .some 0 => .some (.some .unit)
                          | .some _ => .some .none
                          | .none => .some (.some val)
                        | .scalar _ => .none
                        | .ptr _ pSz =>
                          match isThinPtrKind accTy.kind with
                          | true =>
                            match Nat.beq pSz (layoutPointerBytes layouts) with
                            | true => .some (.some val)
                            | false => .some .none
                          | false => .none
                        | .aggregate _ _ => .some (.some val)
                      | .none, _ =>
                        match oldVal, val with
                        | .unit, .unit => .some (.some .unit)
                        | .unit, _ => .some .none
                        | _, _ => .some (.some val)
                    match directStoreOpt with
                    | .some res => res
                    | .none =>
                      spliceSubValueAtByteOffset?
                        localDecls
                        effTargetDecls
                        layouts
                        subTyOpt
                        oldVal
                        0
                        resolvedAccTyOpt
                        val
            match storeValOpt with
            | .none => .ub
            | .some storeVal => commitAtProj fullProj storeVal
      | .some .uninit =>
        match rawFullProj, Nat.beq ptrVal.offsetBytes 0 with
        | .nil, true =>
          let initValOpt : Option Value :=
            match resolvedAccTyOpt, get? effTargetDecls entry.targetLocal with
            | .some { kind := .never, .. }, _ => .none
            | .some accTy, .some decl =>
              let declTy := resolveTyWithLocalDecls effTargetDecls layouts decl.ty
              match rigidTyEq accTy.kind declTy.kind with
              | true => .some val
              | false =>
                match tyByteSize localDecls layouts accTy, tyByteSize effTargetDecls layouts declTy with
                | .some wB, .some dB =>
                  match Nat.beq wB dB with
                  | false => .none
                  | true =>
                    match isPrimitiveScalarKind accTy.kind, isPrimitiveScalarKind declTy.kind with
                    | true, true => .some val
                    | _, _ =>
                      let codecDecls :=
                        match effTargetDecls with
                        | .nil => localDecls
                        | _ :: _ => effTargetDecls
                      decodeSubValueAtByteOffset? layouts (.some accTy) val 0 declTy codecDecls
                | _, _ => .none
            | .none, .some decl =>
              let declTy := resolveTyWithLocalDecls effTargetDecls layouts decl.ty
              match val, tyByteSize effTargetDecls layouts declTy with
              | .scalar wSc, .some dB =>
                match Nat.beq wSc.sizeBytes dB with
                | true => .some val
                | false => .none
              | .unit, .some dB =>
                match Nat.beq dB 0 with
                | true => .some val
                | false => .none
              | _, _ => .some val
            | _, .none => .some val
          match initValOpt with
          | .none => .ub
          | .some initVal =>
            match set? targetLocals entry.targetLocal (.init initVal) with
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
      let sliceAlignTyOpt : Option Ty :=
        match pointeeTyOpt, restProj with
        | .some pt, _ => .some pt
        | .none, .nil => accessedTyOpt
        | .none, _ :: _ => .none
      match
        Bool.and
          (checkDerefAlign localDecls layouts sliceAlignTyOpt ptrVal.offsetBytes)
          (validateValueForTy? layouts accessedTyOpt val)
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
                checkTargetPlaceAlign
                  localDecls
                  layouts
                  sliceAlignTyOpt
                  entry
                  ptrVal
                  (.some targetRootVal)
              with
              | false => .ub
              | true =>
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
        match
          writeProjectedForLocal
            locals
            localDecls
            layouts
            dst.local_
            rootVal
            (proj :: rest)
            val
        with
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
      let sliceAlignTyOpt : Option Ty :=
        match pointeeTyOpt, restProj with
        | .some pt, _ => .some pt
        | .none, .nil => accessedTyOpt
        | .none, _ :: _ => .none
      match
        Bool.and
          (checkDerefAlign localDecls layouts sliceAlignTyOpt ptrVal.offsetBytes)
          (validateValueForTy? layouts accessedTyOpt val)
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
Encode the source value `v` of a byte cast at static type `srcTy`: uses
`encodeTypedValueToBytes`, falling back to the layout-free encoding only for
non-union types (a union value without a determined storage image, e.g. one
with mutually inconsistent slots, has no byte representation).
-/
def encodeByteCastSourceBytes
    (layouts : LayoutTable)
    (srcTy : Ty)
    (v : Value) :
    Option (List AbstractByte) :=
  match encodeTypedValueToBytes layouts srcTy v with
  | .some bs => .some bs
  | .none =>
    match isUnionLayout layouts (normalizeCodecTy srcTy) with
    | true => .none
    | false => encodeUntypedValueToBytes defaultCodecFuel v

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
    let rTargetTy := resolveTyWithLocalDecls localDecls layouts targetTy
    match tyByteSize localDecls layouts rTargetTy with
    | .none => .unsupported
    | .some dstSize =>
      match operandTy localDecls layouts op with
      | .some srcTy =>
        let rSrcTy := resolveTyWithLocalDecls localDecls layouts srcTy
        match tyByteSize localDecls layouts rSrcTy with
        | .none => .unsupported
        | .some srcSize =>
          match Nat.beq srcSize dstSize with
          | false => .unsupported
          | true =>
            let encodedOpt : Option (List AbstractByte) :=
              encodeByteCastSourceBytes layouts rSrcTy v
            match encodedOpt with
            | .none => .ub
            | .some bs =>
              match Nat.beq (length bs) dstSize with
              | false => .ub
              | true =>
                match
                  decodeTypedValueFromBytes defaultCodecFuel layouts rTargetTy bs
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
            match decodeTypedValueFromBytes defaultCodecFuel layouts rTargetTy bs with
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
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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

def rawPtrUnsizeArrayToSliceLen?
    (srcOpt : Option Ty)
    (targetTy : Ty)
    (ptrBytes : Nat) :
    Option Nat :=
  match srcOpt, targetTy.kind with
  | .some { kind := .rawPtr srcMut (.array srcElem n), .. }, .rawPtr dstMut (.slice dstElem) =>
    match
      Bool.and
        (unsizeMutabilityCompatible srcMut dstMut)
        (Bool.and (rigidTyEq srcElem dstElem) (Nat.blt n (scalarModulus ptrBytes)))
    with
    | true => .some n
    | false => .none
  | _, _ => .none

/--
Evaluate `CastKind.pointerCoercion "Unsize"`, coercing an array reference or
raw pointer (`Value.ptr p sz` of type `&[T; N]`, `&mut [T; N]`, `*const [T; N]`,
or `*mut [T; N]`, or provenance-less `Value.scalar sc` of type `*const [T; N]` /
`*mut [T; N]`) to a slice fat pointer.

Faults with `.ub` if `op` does not evaluate to a pointer of width `ptrBytes`,
if `targetTy` is a reference whose borrow tag is `.disabled` (or provenance-less
scalar), or if source and target types are incompatible for slice unsizing.
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
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
  | .ok (.scalar sc) locals' =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | false => .ub
    | true =>
      match rawPtrUnsizeArrayToSliceLen? (operandTy localDecls layouts op) targetTy ptrBytes with
      | .some n =>
        .ok
          (.aggregate 0
            (.scalar ⟨wrapScalarBits sc.bits (scalarModulus ptrBytes), ptrBytes⟩ ::
              .scalar ⟨n, ptrBytes⟩ :: .nil))
          locals'
          mem
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
@[reducible]
def projLastFieldArrayCap? : List ProjectionElem → Option Nat
  | .nil => .none
  | .field _ fTy :: .nil =>
    match fTy.kind with
    | .array _ cap => .some cap
    | _ => .none
  | .field _ fTy :: .subslice fromIdx toIdx false :: .nil =>
    match fTy.kind with
    | .array _ cap =>
      match Bool.and (Nat.ble fromIdx toIdx) (Nat.ble toIdx cap) with
      | true => .some (Nat.sub toIdx fromIdx)
      | false => .none
    | _ => .none
  | _ :: rest => projLastFieldArrayCap? rest

def deriveStackElemThinPtr
    (locals : List LocalSlot)
    (mem : Memory)
    (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry)
    (elemCountOpt : Option Nat)
    (ptrBytes : Nat := 8) :
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
            | true => .ok (.ptr ptrVal ptrBytes) locals mem
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
              .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes) locals mem'
      | .none =>
        match readProjectedValue locals targetRootVal normProj with
        | .ok .unit =>
          let fieldCapOpt := projLastFieldArrayCap? normProj
          let isUninitUnionFieldArray : Bool :=
            match normProj, fieldCapOpt with
            | .field _ _ :: _, .some cap => Nat.ble 1 cap
            | _, _ => false
          match isUninitUnionFieldArray with
          | true =>
            let capOk : Bool :=
              match elemCountOpt, fieldCapOpt with
              | .some n, .some cap => Nat.ble n cap
              | .none, .some _ => true
              | _, _ => false
            match Bool.and (Nat.beq ptrVal.offsetBytes 0) capOk with
            | true => .ok (.ptr ptrVal ptrBytes) locals mem
            | false => .ub
          | false =>
            let isZeroSlice :=
              match elemCountOpt with
              | .some n => Nat.beq n 0
              | .none => true
            match Bool.and (Nat.beq ptrVal.offsetBytes 0) isZeroSlice with
            | false =>
              match normProj, fieldCapOpt, Nat.beq ptrVal.offsetBytes 0 with
              | .field _ _ :: _, .none, true => .ok (.ptr ptrVal ptrBytes) locals mem
              | _, _, _ => .ub
            | true =>
              match endsWithSubslice normProj with
              | true => .ok (.ptr ptrVal ptrBytes) locals mem
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
                .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes) locals mem'
        | .ub =>
          match normProj, Nat.beq ptrVal.offsetBytes 0 with
          | .field _ _ :: _, true => .ok (.ptr ptrVal ptrBytes) locals mem
          | _, _ => .ub
        | _ => .ub

def arrayToPointerElemLen?
    (srcOpt : Option Ty)
    (targetTy : Ty) :
    Option (Option Nat) :=
  match targetTy.kind with
  | .rawPtr dstMut dstElem =>
    match isWideRawPtrTy targetTy with
    | true => .none
    | false =>
      match srcOpt with
      | .none => .some .none
      | .some { kind := .rawPtr srcMut (.array srcElem arrLen), .. } =>
        match Bool.and (unsizeMutabilityCompatible srcMut dstMut) (rigidTyEq srcElem dstElem) with
        | true => .some (.some arrLen)
        | false => .none
      | .some _ => .none
  | _ => .none

def mutToConstTargetShape?
    (srcOpt : Option Ty)
    (targetTy : Ty) :
    Option (Option Bool) :=
  match targetTy.kind with
  | .rawPtr .not dstPointee =>
    let srcOk : Bool :=
      match srcOpt with
      | .none => true
      | .some { kind := .rawPtr .mut srcPointee, .. } => rigidTyEq srcPointee dstPointee
      | .some _ => false
    match srcOk with
    | false => .none
    | true =>
      match isWideRawPtrTy targetTy with
      | false => .some .none
      | true =>
        match dstPointee with
        | .dynamic _ => .some (.some true)
        | _ => .some (.some false)
  | _ => .none

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
        let ptrBytes := layoutPointerBytes layouts
        match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
        | .ok (.ptr ptrVal sz) locals' =>
          match Nat.beq sz ptrBytes, arrayToPointerElemLen? (operandTy localDecls layouts op) targetTy with
          | true, .some elemLenOpt =>
            match lookupBorrow mem.borrows ptrVal.tag with
            | .some parentEntry =>
              deriveStackElemThinPtr locals' mem ptrVal parentEntry elemLenOpt ptrBytes
            | .none => .ok (.ptr ptrVal ptrBytes) locals' mem
          | _, _ => .ub
        | .ok (.scalar sc) locals' =>
          match Nat.beq sc.sizeBytes ptrBytes, arrayToPointerElemLen? (operandTy localDecls layouts op) targetTy with
          | true, .some _ =>
            .ok (.scalar ⟨wrapScalarBits sc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
          | _, _ => .ub
        | .ok _ _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | false =>
        match stringEq coercionKind "MutToConstPointer" with
        | false => .unsupported
        | true =>
          let ptrBytes := layoutPointerBytes layouts
          let shapeOpt := mutToConstTargetShape? (operandTy localDecls layouts op) targetTy
          match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
          | .ok (.ptr ptrVal sz) locals' =>
            match Nat.beq sz ptrBytes, shapeOpt with
            | true, .some .none => .ok (.ptr ptrVal ptrBytes) locals' mem
            | _, _ => .ub
          | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
            match Bool.and (Nat.beq sz ptrBytes) (Nat.beq metaSc.sizeBytes ptrBytes), shapeOpt with
            | true, .some (.some _) =>
              .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .scalar metaSc :: .nil)) locals' mem
            | _, _ => .ub
          | .ok (.aggregate 0 (.ptr ptrVal sz :: .ptr vtPtr vtSz :: .nil)) locals' =>
            match Bool.and (Nat.beq sz ptrBytes) (Nat.beq vtSz ptrBytes), shapeOpt with
            | true, .some (.some true) =>
              .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .ptr vtPtr ptrBytes :: .nil)) locals' mem
            | _, _ => .ub
          | .ok (.scalar sc) locals' =>
            match Nat.beq sc.sizeBytes ptrBytes, shapeOpt with
            | true, .some .none =>
              .ok (.scalar ⟨wrapScalarBits sc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
            | _, _ => .ub
          | .ok (.aggregate 0 (.scalar addrSc :: .scalar metaSc :: .nil)) locals' =>
            match
              Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq metaSc.sizeBytes ptrBytes),
              shapeOpt
            with
            | true, .some (.some _) =>
              let modPtr := scalarModulus ptrBytes
              .ok
                (.aggregate 0
                  (.scalar ⟨wrapScalarBits addrSc.bits modPtr, ptrBytes⟩ ::
                    .scalar ⟨wrapScalarBits metaSc.bits modPtr, ptrBytes⟩ :: .nil))
                locals' mem
            | _, _ => .ub
          | .ok (.aggregate 0 (.scalar addrSc :: .ptr vtPtr vtSz :: .nil)) locals' =>
            match
              Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq vtSz ptrBytes),
              shapeOpt
            with
            | true, .some (.some true) =>
              let modPtr := scalarModulus ptrBytes
              .ok
                (.aggregate 0
                  (.scalar ⟨wrapScalarBits addrSc.bits modPtr, ptrBytes⟩ ::
                    .ptr vtPtr ptrBytes :: .nil))
                locals' mem
            | _, _ => .ub
          | .ok _ _ => .ub
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
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
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
        (stringEq defPath "core::marker::PhantomData")
        (stringEq defPath "std::marker::PhantomData")
    with
    | true => true
    | false =>
      match
        Bool.or
          (Bool.or
            (stringEq defPath "core::cell::UnsafeCell")
            (stringEq defPath "std::cell::UnsafeCell"))
          (Bool.or
            (Bool.or
              (stringEq defPath "core::cell::SyncUnsafeCell")
              (stringEq defPath "std::cell::SyncUnsafeCell"))
            (Bool.or
              (Bool.or
                (stringEq defPath "core::cell::Cell")
                (stringEq defPath "std::cell::Cell"))
              (Bool.or
                (stringEq defPath "core::cell::RefCell")
                (stringEq defPath "std::cell::RefCell"))))
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
Determine whether `place`'s resolved type in `localDecls` and `layouts` is
`Freeze` (`tyIsFreeze`), defaulting to `true` when `localDecls` is omitted or
does not determine a type for `place`.

Reference (The Rust Reference, "Interior mutability"):
<https://doc.rust-lang.org/1.98.0/reference/interior-mutability.html>

> "All interior mutability in Rust is enabled by the UnsafeCell<T> type, which
> is defined in the standard library."
-/
@[reducible]
def placeIsFreeze
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place) :
    Bool :=
  match placeTy localDecls layouts place with
  | .some ty => tyIsFreeze ty
  | .none => true

/--
Determine whether a structural `RigidTy` is statically known to have zero byte
size in `Runtime(PostCleanup)` MIR on a 64-bit target (`rustc
1.98.0-nightly (14210df0e 2026-05-31)`), using bounded recursion with `fuel`.

Reference (The Rust Reference, "Type Layout", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
@[reducible]
def rigidTyIsZeroSized : Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ _, .never => true
  | .succ _, .tuple .nil => true
  | .succ fuel, .tuple (k :: ks) =>
    Bool.and (rigidTyIsZeroSized fuel k) (rigidTyIsZeroSized fuel (.tuple ks))
  | .succ _, .array _ .zero => true
  | .succ fuel, .array elem _ => rigidTyIsZeroSized fuel elem
  | .succ _, .fnDef _ _ => true
  | .succ _, .closure _ .nil => true
  | .succ fuel, .closure _ (u :: us) =>
    Bool.and (rigidTyIsZeroSized fuel u) (rigidTyIsZeroSized fuel (.tuple us))
  | .succ fuel, .adt defPath args =>
    match
      Bool.or
        (stringEq defPath "core::marker::PhantomData")
        (stringEq defPath "std::marker::PhantomData")
    with
    | true => true
    | false =>
      match
        Bool.or
          (Bool.or
            (stringEq defPath "core::cell::UnsafeCell")
            (stringEq defPath "std::cell::UnsafeCell"))
          (Bool.or
            (Bool.or
              (stringEq defPath "core::cell::SyncUnsafeCell")
              (stringEq defPath "std::cell::SyncUnsafeCell"))
            (Bool.or
              (Bool.or
                (stringEq defPath "core::cell::Cell")
                (stringEq defPath "std::cell::Cell"))
              (Bool.or
                (Bool.or
                  (stringEq defPath "core::mem::ManuallyDrop")
                  (stringEq defPath "std::mem::ManuallyDrop"))
                (Bool.or
                  (stringEq defPath "core::mem::MaybeUninit")
                  (stringEq defPath "std::mem::MaybeUninit"))))),
        args
      with
      | true, inner :: .nil => rigidTyIsZeroSized fuel inner
      | _, _ => false
  | .succ _, k =>
    match rigidTyKindByteSize k with
    | .some .zero => true
    | _ => false

/--
Determine whether a `Ty` is statically zero-sized by inspecting `ty.kind` with
fuel `16` (`rigidTyIsZeroSized 16 ty.kind`).
-/
@[reducible]
def tyIsZeroSized (ty : Ty) : Bool :=
  rigidTyIsZeroSized 16 ty.kind

/--
Determine whether `place`'s resolved type in `localDecls` and `layouts` is
statically zero-sized (`tyIsZeroSized`), defaulting to `false` when `localDecls`
is omitted or does not determine a type for `place`.
-/
@[reducible]
def placeIsZeroSized
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place) :
    Bool :=
  match placeTy localDecls layouts place with
  | .some ty => tyIsZeroSized ty
  | .none => false

/--
Determine whether a structural `RigidTy` is statically known to be uninhabited
in `Runtime(PostCleanup)` MIR (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`),
using bounded recursion with `fuel`.
-/
@[reducible]
def rigidTyIsUninhabited : Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ _, .never => true
  | .succ _, .tuple .nil => false
  | .succ fuel, .tuple (k :: ks) =>
    Bool.or
      (rigidTyIsUninhabited fuel k)
      (rigidTyIsUninhabited fuel (.tuple ks))
  | .succ _, .array _ .zero => false
  | .succ fuel, .array elem (.succ _) => rigidTyIsUninhabited fuel elem
  | .succ _, .closure _ .nil => false
  | .succ fuel, .closure defPath (u :: us) =>
    Bool.or
      (rigidTyIsUninhabited fuel u)
      (rigidTyIsUninhabited fuel (.closure defPath us))
  | .succ fuel, .adt defPath args =>
    match
      Bool.or
        (stringEq defPath "core::convert::Infallible")
        (stringEq defPath "std::convert::Infallible")
    with
    | true => true
    | false =>
      match
        Bool.or
          (Bool.or
            (stringEq defPath "core::cell::UnsafeCell")
            (stringEq defPath "std::cell::UnsafeCell"))
          (Bool.or
            (Bool.or
              (stringEq defPath "core::cell::SyncUnsafeCell")
              (stringEq defPath "std::cell::SyncUnsafeCell"))
            (Bool.or
              (Bool.or
                (stringEq defPath "core::cell::Cell")
                (stringEq defPath "std::cell::Cell"))
              (Bool.or
                (Bool.or
                  (stringEq defPath "core::cell::RefCell")
                  (stringEq defPath "std::cell::RefCell"))
                (Bool.or
                  (stringEq defPath "core::mem::ManuallyDrop")
                  (stringEq defPath "std::mem::ManuallyDrop"))))),
        args
      with
      | true, inner :: .nil => rigidTyIsUninhabited fuel inner
      | _, _ => false
  | .succ _, _ => false

/--
Determine whether a `Ty` is uninhabited either structurally
(`rigidTyIsUninhabited 16 ty.kind`) or via its compiler-captured
`TypeLayout.isUninhabited` flag in `layouts`.
-/
@[reducible]
def tyIsUninhabited (layouts : LayoutTable) (ty : Ty) : Bool :=
  match rigidTyIsUninhabited 16 ty.kind with
  | true => true
  | false =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some l => l.isUninhabited
    | .none => false

/--
Determine whether `place`'s resolved type in `localDecls` and `layouts` is
uninhabited (`tyIsUninhabited`), defaulting to `false` when `localDecls` is
omitted or does not determine a type for `place`.
-/
@[reducible]
def placeIsUninhabited
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place) :
    Bool :=
  match placeTy localDecls layouts place with
  | .some ty => tyIsUninhabited layouts ty
  | .none => false

/--
Determine the initial Tree Borrows permission for a shared borrow (`&place`)
based on whether `place`'s resolved type in `localDecls` and `layouts` is
`Freeze`.

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
    | false => TreeBorrowPerm.cell
  | .none => TreeBorrowPerm.frozen

/--
Determine the initial Tree Borrows permission for an unprotected mutable borrow
(`&mut place`, including two-phase borrows) based on whether `place`'s resolved
type is `Freeze`: `TreeBorrowPerm.reservedFrz false` for `Freeze` places and
`TreeBorrowPerm.reservedIM` for `!Freeze` places.
-/
@[reducible]
def mutableBorrowPerm
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place) :
    TreeBorrowPerm :=
  match placeTy localDecls layouts place with
  | .some ty =>
    match tyIsFreeze ty with
    | true => TreeBorrowPerm.reservedFrz false
    | false => TreeBorrowPerm.reservedIM
  | .none => TreeBorrowPerm.reservedFrz false

/--
Determine the initial Tree Borrows permission of the protected tag created by a
function-entry retag (`RetagKind::FnEntry`) of a reference with mutability
`mutability` to a pointee of kind `pointee`.
-/
@[reducible]
def fnEntryRetagPerm
    (mutability : Mutability)
    (pointee : RigidTy) :
    TreeBorrowPerm :=
  match mutability with
  | .not =>
    match rigidTyIsFreeze 16 pointee with
    | true => TreeBorrowPerm.frozen
    | false => TreeBorrowPerm.cell
  | .mut => TreeBorrowPerm.reservedFrz false

/--
Determine the initial Tree Borrows permission of the tag created by a MIR
`StatementKind.retag` of `retagKind` on a reference with mutability
`mutability` to a pointee of kind `pointee`.
-/
@[reducible]
def retagPerm
    (retagKind : RetagKind)
    (mutability : Mutability)
    (pointee : RigidTy) :
    TreeBorrowPerm :=
  match retagKind with
  | .fnEntry => fnEntryRetagPerm mutability pointee
  | .default | .twoPhase | .raw =>
    match mutability with
    | .not =>
      match rigidTyIsFreeze 16 pointee with
      | true => TreeBorrowPerm.frozen
      | false => TreeBorrowPerm.cell
    | .mut =>
      match rigidTyIsFreeze 16 pointee with
      | true => TreeBorrowPerm.reservedFrz false
      | false => TreeBorrowPerm.reservedIM

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
          | .none =>
            match LayoutTable.lookup layouts ptrTy.layoutIdx with
            | .some { size := pSz, fields := .primitive, fieldLayouts := flIdx :: .nil, .. } =>
              match
                Bool.and
                  (Nat.beq pSz.bytes (layoutPointerBytes layouts))
                  (Nat.ble (.succ flIdx) (length layouts.entries))
              with
              | true => { kind := inner, layoutIdx := flIdx }
              | false => { kind := inner, layoutIdx := unresolvedLayoutIdx layouts }
            | _ => { kind := inner, layoutIdx := unresolvedLayoutIdx layouts }
        tyByteSize localDecls layouts resolvedPointeeTy
    | .none => .none

/--
Test whether `op` is a relational `BinOp` (`.eq`, `.ne`, `.lt`, `.le`, `.gt`,
`.ge`, or three-way `.cmp`), which compares pointers by their machine address
ignoring provenance (`MiniRust` `spec/lang/step/operators.md` `compare_ptr`).
-/
@[reducible]
def isRelationalBinOp : BinOp → Bool
  | .eq => true
  | .ne => true
  | .lt => true
  | .le => true
  | .gt => true
  | .ge => true
  | .cmp => true
  | _ => false

/--
Test whether `op` has pointer/reference/fn-pointer type (`.rawPtr`, `.ref`,
`.fnPtr`) or no declared type in `localDecls` (`.none`, e.g., untyped synthetic
probes). Used to guard mixed `(.ptr, .scalar)` and `(.scalar, .ptr)` relational
comparisons so ill-typed `Value.ptr` values in integer/boolean/char locals never
masquerade as scalar integers.
-/
@[reducible]
def isPtrOrUntypedOperand
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Bool :=
  match operandTy localDecls layouts op with
  | .none => true
  | .some ty =>
    match ty.kind with
    | .rawPtr _ _ => true
    | .ref _ _ => true
    | .fnPtr .. => true
    | _ => false

/--
Test whether `op` is a relational `BinOp` whose operands have pointer (or
untyped) `Operand` types in `localDecls`.
-/
@[reducible]
def isPtrRelationalBinOp
    (op : BinOp)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp rhsOp : Operand) :
    Bool :=
  match isRelationalBinOp op with
  | false => false
  | true =>
    match isPtrOrUntypedOperand localDecls layouts lhsOp with
    | false => false
    | true => isPtrOrUntypedOperand localDecls layouts rhsOp

/--
Convert an unbacked `ProvenancePtr` `p` of byte width `sz` to its raw
page-based unsigned address `ScalarInt`
`((p.allocId * 65536 + p.offsetBytes) mod 2^(8*sz))`.
-/
@[reducible]
def ptrToAddrScalar (p : ProvenancePtr) (sz : Nat) : ScalarInt :=
  { bits :=
      wrapScalarBits
        (Nat.add (Nat.mul p.allocId 65536) p.offsetBytes)
        (scalarModulus sz)
    sizeBytes := sz }

/--
Base 64-KiB page index for stack local `0` in canonical pointer addresses:
- On 64-bit targets (`8 <= ptrBytes`): `1048576` (`0x10_0000`, i.e., byte base
  `0x10_0000_0000`), disjoint from `0` (`null`), `1..65535` (globals / synthetic
  `allocId`s), and `65536..1048575` (`fnPtrAllocBase` function pointers).
- On 32-bit targets (`ptrBytes < 8`): `32768` (`0x8000`, i.e., byte base
  `0x8000_0000`).
-/
@[reducible]
def stackLocalAddrPageBase (ptrBytes : Nat) : Nat :=
  match Nat.ble 8 ptrBytes with
  | true => 1048576
  | false => 32768

/--
Resolve the byte offset of `entry.targetProjection` within stack local
`entry.targetLocal` (`0` when `targetProjection` strips to `.nil`, or resolved
via `projectionChainByteOffset?` from `localDecls`/`layouts` and/or runtime
`locals`/`callerLocals`). Returns `.none` if a non-empty projection's byte
offset cannot be determined.
-/
def borrowPlaceByteOffset?
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (entry : BorrowEntry) :
    Option Nat :=
  let normProj :=
    normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
  match normProj with
  | .nil => .some 0
  | _ :: _ =>
    let (rootValOpt, targetDecls, rootTyOpt) :
        Option Value × List LocalDecl × Option Ty :=
      match get? locals entry.targetLocal with
      | .some slot =>
        let vOpt :=
          match slot with
          | .init v => .some v
          | _ => .none
        let tyOpt :=
          match get? localDecls entry.targetLocal with
          | .some decl => .some (resolveTyWithLocalDecls localDecls layouts decl.ty)
          | .none => .none
        (vOpt, localDecls, tyOpt)
      | .none =>
        let vOpt :=
          match get? callerLocals entry.targetLocal with
          | .some (.init v) => .some v
          | _ => .none
        (vOpt, .nil, .none)
    projectionChainByteOffset?
      layouts
      rootTyOpt
      rootValOpt
      .none
      0
      targetDecls
      normProj

/--
Compute the canonical base byte address of a stack `BorrowEntry` `entry`:
`(stackLocalAddrPageBase ptrBytes + entry.targetLocal) * 65536 + placeOff`.
Two distinct Tree Borrows tags borrowing the same stack local (or the same field
via sub-place projection vs byte offset) therefore map to the exact same
canonical address.
-/
def borrowBaseAddress?
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat)
    (entry : BorrowEntry) :
    Option Nat :=
  match borrowPlaceByteOffset? locals callerLocals localDecls layouts entry with
  | .some placeOff =>
    let localPage := Nat.add (stackLocalAddrPageBase ptrBytes) entry.targetLocal
    .some (Nat.add (Nat.mul localPage 65536) placeOff)
  | .none => .none

/--
Compute the canonical unsigned byte address of `p : ProvenancePtr`:
- If `p.tag` resolves to a stack `BorrowEntry` in `borrows`, returns
  `borrowBaseAddress? ... entry + p.offsetBytes` (so distinct borrow tags for
  the same stack place have equal addresses).
- Otherwise (global allocation, function pointer, or synthetic unbacked
  `allocId`), returns `.some (p.allocId * 65536 + p.offsetBytes)`.
-/
def ptrAddress?
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat)
    (p : ProvenancePtr) :
    Option Nat :=
  match lookupBorrow borrows p.tag with
  | .none => .some (Nat.add (Nat.mul p.allocId 65536) p.offsetBytes)
  | .some entry =>
    match borrowBaseAddress? locals callerLocals localDecls layouts ptrBytes entry with
    | .some baseAddr => .some (Nat.add baseAddr p.offsetBytes)
    | .none => .none

/--
Convert a tracked `ProvenancePtr` `p` of byte width `sz` to its canonical
unsigned address `ScalarInt` modulo `2^(8*sz)` for relational pointer
comparisons. Returns `.none` only if `p` is a sub-place stack borrow whose
projection offset cannot be resolved without layout metadata.
-/
def ptrAddressScalar?
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat)
    (p : ProvenancePtr)
    (sz : Nat) :
    Option ScalarInt :=
  match ptrAddress? locals borrows callerLocals localDecls layouts ptrBytes p with
  | .some addr =>
    .some { bits := wrapScalarBits addr (scalarModulus sz), sizeBytes := sz }
  | .none => .none

def resolveWideWordScalar?
    (word : Value)
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat) :
    Option ScalarInt :=
  match word with
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | true =>
      ptrAddressScalar?
        locals
        borrows
        callerLocals
        localDecls
        layouts
        ptrBytes
        p
        ptrBytes
    | false => .none
  | .scalar sc =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | true => .some { bits := wrapScalarBits sc.bits (scalarModulus ptrBytes), sizeBytes := ptrBytes }
    | false => .none
  | _ => .none

def isExplicitWidePtrTy (tyOpt : Option Ty) : Bool :=
  match tyOpt with
  | .some { kind := .rawPtr _ (.slice _), .. } => true
  | .some { kind := .rawPtr _ .str, .. } => true
  | .some { kind := .rawPtr _ (.dynamic _), .. } => true
  | .some { kind := .ref _ (.slice _), .. } => true
  | .some { kind := .ref _ .str, .. } => true
  | .some { kind := .ref _ (.dynamic _), .. } => true
  | _ => false

/--
Evaluate a relational `BinOp` (`isRelationalBinOp op = true`) on two 2-word
wide pointers `(lhsThin, lhsMeta)` and `(rhsThin, rhsMeta)`, comparing first the
thin data-pointer canonical address and then the metadata word lexicographically
(`MiniRust` `spec/lang/step/operators.md` `compare_ptr`).
-/
@[reducible]
def evalWidePtrRelBinOp
    (op : BinOp)
    (lhsThin : Value)
    (lhsMeta : Value)
    (rhsThin : Value)
    (rhsMeta : Value)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat) :
    RvalueEvalResult :=
  match
    resolveWideWordScalar? lhsThin locals₂ mem.borrows mem.callerLocals localDecls layouts ptrBytes,
    resolveWideWordScalar? rhsThin locals₂ mem.borrows mem.callerLocals localDecls layouts ptrBytes,
    resolveWideWordScalar? lhsMeta locals₂ mem.borrows mem.callerLocals localDecls layouts ptrBytes,
    resolveWideWordScalar? rhsMeta locals₂ mem.borrows mem.callerLocals localDecls layouts ptrBytes
  with
  | .some lhsAddr, .some rhsAddr, .some lhsMetaNorm, .some rhsMetaNorm =>
    match Nat.beq lhsAddr.bits rhsAddr.bits with
    | false => evalScalarBinOp op lhsAddr rhsAddr locals₂ mem false
    | true => evalScalarBinOp op lhsMetaNorm rhsMetaNorm locals₂ mem false
  | _, _, _, _ => .unsupported

/--
Wrapper for wide raw-pointer / wide reference aggregate relational comparisons
(`.aggregate 0 [thin, meta]`) that accepts flat `.aggregate` constructor
fields so downstream equation-compiler proofs avoid nested pattern splitting.
-/
@[reducible]
def evalWidePtrAggregateRelBinOp
    (op : BinOp)
    (lhsOp : Operand)
    (lhsVar : Nat)
    (lhsFields : List Value)
    (rhsVar : Nat)
    (rhsFields : List Value)
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  match Nat.beq lhsVar 0, Nat.beq rhsVar 0, lhsFields, rhsFields with
  | true, true, lhsThin :: lhsMeta :: .nil, rhsThin :: rhsMeta :: .nil =>
    let hasPtrOrWidePtrTy : Bool :=
      match isPtrOrUntypedOperand localDecls layouts lhsOp with
      | false => false
      | true =>
        match isWidePtrMetadata lhsMeta, isWidePtrMetadata rhsMeta with
        | true, true =>
          match isExplicitWidePtrTy (operandTy localDecls layouts lhsOp) with
          | true => true
          | false =>
            match lhsThin, rhsThin with
            | .ptr _ _, _ => true
            | _, .ptr _ _ => true
            | _, _ => false
        | _, _ => false
    match Bool.and (isRelationalBinOp op) hasPtrOrWidePtrTy with
    | true =>
      evalWidePtrRelBinOp
        op
        lhsThin
        lhsMeta
        rhsThin
        rhsMeta
        locals₂
        mem
        localDecls
        layouts
        (layoutPointerBytes layouts)
    | false => .unsupported
  | _, _, _, _ => .unsupported

/--
Evaluate `BinOp.offset` when the pointer operand `lhsOp` evaluates to a
provenance-less `Value.scalar lhs` (`null`, `ptr::without_provenance`, or an
unexposed `usize as *const T` cast) and the count operand evaluates to
`Value.scalar rhs`.

Per Miri (`ptr_offset_inbounds`) and MiniRust (`spec/lang/step/operators.md`
`ptr_offset_inbounds` + `spec/mem/basic.md` `check_ptr`), in-bounds pointer
arithmetic on a pointer without provenance succeeds if and only if the total
byte offset `count * size_of::<T>()` is `0` (either `count == 0` or ZST
`size_of::<T>() == 0`), preserving `lhs`, and faults with `.ub` for any
non-zero byte offset.
-/
@[reducible]
def evalScalarPtrOffsetBinOp
    (locals₂ : List LocalSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (lhsOp : Operand)
    (lhs : ScalarInt)
    (rhs : ScalarInt) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  let lhsKindClass : Nat :=
    match operandTy localDecls layouts lhsOp with
    | .none => 1
    | .some ty =>
      match isThinRawPtrTy ty with
      | true => 1
      | false =>
        match isWideRawPtrTy ty with
        | true => 2
        | false =>
          match ty.kind with
          | .ref _ _ => 2
          | _ => 0
  match lhsKindClass with
  | 0 => .unsupported
  | 2 => .ub
  | _ =>
    match Bool.and (Nat.beq lhs.sizeBytes ptrBytes) (Nat.beq rhs.sizeBytes ptrBytes) with
    | false => .ub
    | true =>
      match pointeeElemByteStride localDecls layouts lhsOp with
      | .none => .ub
      | .some elemStride =>
        let modPtr := scalarModulus ptrBytes
        let lhsBits := wrapScalarBits lhs.bits modPtr
        let rhsBits := wrapScalarBits rhs.bits modPtr
        match Bool.or (Nat.beq rhsBits 0) (Nat.beq elemStride 0) with
        | true => .ok (.scalar ⟨lhsBits, ptrBytes⟩) locals₂ mem
        | false => .ub

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
      let targetLive : Bool :=
        match get? locals entry.targetLocal with
        | .some (.init _) => true
        | .some .uninit => true
        | .some .dead => false
        | .none =>
          match get? mem.callerLocals entry.targetLocal with
          | .some (.init _) => true
          | .some .uninit => true
          | _ => false
      match targetLive, Nat.beq entry.rangeLen 0 with
      | false, _ => .some 0
      | true, false => .some (Nat.add entry.rangeOffset entry.rangeLen)
      | true, true =>
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
    (allocBoundOpt : Option Nat := .none)
    (expectedPtrBytes : Nat := 8) :
    Option ProvenancePtr :=
  match
    Bool.and
      (Nat.beq ptrSizeBytes expectedPtrBytes)
      (Nat.beq offsetSc.sizeBytes expectedPtrBytes)
  with
  | false => .none
  | true =>
    let modulus := scalarModulus expectedPtrBytes
    let halfMod := signedHalfModulus expectedPtrBytes
    let offsetBits := wrapScalarBits offsetSc.bits modulus
    let newOffsetOpt : Option Nat :=
      match isSignedNegative offsetBits expectedPtrBytes with
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
          (layoutPointerBytes layouts)
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
   a thin pointer `.ptr { allocId := mem.nextTag, offsetBytes := 0 } ptrBytes`.
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
    (layouts : LayoutTable := emptyLayoutTable)
    (checkPerm : Bool := true)
    (localDecls : List LocalDecl := .nil)
    (accessedTyOpt : Option Ty := .none)
    (checkResultRefAlign : Bool := false) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    Bool.and
      (Nat.beq ptrSz ptrBytes)
      (Nat.beq lenSc.sizeBytes ptrBytes)
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
          match checkPerm with
          | false => true
          | true =>
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
                        (.ptr { allocId := tag, offsetBytes := newOffsetBytes } ptrBytes ::
                          .scalar ⟨lenSc.bits, ptrBytes⟩ ::
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
                            (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes ::
                              .scalar ⟨subLen, ptrBytes⟩ ::
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
                        let tailValid : Bool :=
                          Bool.and
                            (forwardSubslicesOrdered tailProj)
                            (subsliceChainValidOnVal locals targetRootVal fullProj)
                        let resAlignOk : Bool :=
                          match checkResultRefAlign with
                          | false => true
                          | true =>
                            checkTargetPlaceAlign
                              localDecls
                              layouts
                              accessedTyOpt
                              entry
                              { allocId := tag, offsetBytes := 0 }
                              (.some targetRootVal)
                        match Bool.and tailValid resAlignOk with
                        | false => .ub
                        | true =>
                          let mem' := {
                            mem with
                            borrows := entry :: mem.borrows
                            nextTag := Nat.add tag 1
                          }
                          .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes) locals mem'
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
                        (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes ::
                          .scalar ⟨0, ptrBytes⟩ ::
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
                  (.ptr parentPtr ptrBytes :: .scalar ⟨lenSc.bits, ptrBytes⟩ :: .nil))
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
                      (.ptr { parentPtr with offsetBytes := newOffset } ptrBytes ::
                        .scalar ⟨subLen, ptrBytes⟩ ::
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
                    (.ptr { parentPtr with offsetBytes := newOffset } ptrBytes)
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
                (.ptr parentPtr ptrBytes :: .scalar ⟨0, ptrBytes⟩ :: .nil))
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
    (layouts : LayoutTable := emptyLayoutTable)
    (localDecls : List LocalDecl := .nil)
    (rawPtrMode : Bool := false)
    (accessedTyOpt : Option Ty := .none) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  let alignTargetOk (off : Nat) : Bool :=
    match rawPtrMode with
    | true => true
    | false =>
      Bool.and
        (checkDerefAlign localDecls layouts accessedTyOpt off)
        (checkGlobalAllocAlign localDecls layouts accessedTyOpt alloc off)
  let mutOk :=
    match isMut, alloc.mutability with
    | true, .not => false
    | _, _ => true
  match
    Bool.and
      (Nat.beq ptrSz ptrBytes)
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
            match tyByteSize localDecls layouts { kind := elemKind, layoutIdx := elemIdx } with
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
          match rawPtrMode with
          | true => 0
          | false =>
            match pointeeTyOpt with
            | .some pointeeTy =>
              match tyByteSize localDecls layouts pointeeTy with
              | .some n => n
              | .none => 0
            | .none => 0
        match
          Bool.and
            (Nat.ble reqBytes remBytes)
            (alignTargetOk parentPtr.offsetBytes)
        with
        | true => .ok (.ptr parentPtr ptrBytes) locals mem
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
        let neededBytes :=
          match rawPtrMode with
          | true => Nat.mul idx elemSz
          | false => Nat.mul (.succ idx) elemSz
        let newOff := Nat.add parentPtr.offsetBytes (Nat.mul idx elemSz)
        match
          Bool.and
            (Nat.ble minLen maxElems)
            (Bool.and
              fromEndBoundsOk
              (Bool.and
                (Nat.ble (.succ idx) maxElems)
                (Bool.and
                  (Nat.ble neededBytes remBytes)
                  (alignTargetOk newOff))))
        with
        | true =>
          .ok (.ptr { parentPtr with offsetBytes := newOff } ptrBytes) locals mem
        | false => .ub
      | .subslice fromIdx toIdx fromEnd :: .nil =>
        match Nat.ble toIdx maxElems with
        | false => .ub
        | true =>
          let endIdx :=
            match fromEnd with
            | true => Nat.sub maxElems toIdx
            | false => toIdx
          let neededBytes :=
            match rawPtrMode with
            | true => Nat.mul endIdx elemSz
            | false => Nat.mul endIdx elemSz
          let newOff := Nat.add parentPtr.offsetBytes (Nat.mul fromIdx elemSz)
          match
            Bool.and
              (Nat.ble fromIdx endIdx)
              (Bool.and
                (Nat.ble endIdx maxElems)
                (Bool.and
                  (Nat.ble neededBytes remBytes)
                  (alignTargetOk newOff)))
          with
          | true =>
            .ok (.ptr { parentPtr with offsetBytes := newOff } ptrBytes) locals mem
          | false => .ub
      | _ =>
        match forwardSubslicesOrdered resolvedRest with
        | false => .ub
        | true =>
          match
            projectionChainByteOffset?
              layouts
              pointeeTyOpt
              .none
              .none
              0
              localDecls
              resolvedRest
          with
          | .none => .ub
          | .some fieldOff =>
            let reqTailBytesOpt : Option Nat :=
              match rawPtrMode with
              | true =>
                match projHasSubslice resolvedRest, pointeeTyOpt with
                | false, _ => .some 0
                | true, .none =>
                  match projHasFromEndSubslice resolvedRest with
                  | true => .none
                  | false => .some 0
                | true, .some pointeeTy =>
                  match resolveProjectedTyResolved localDecls layouts pointeeTy resolvedRest with
                  | .none => .none
                  | .some subTy =>
                    match tyByteSize localDecls layouts subTy with
                    | .some sz => .some sz
                    | .none => .some 0
              | false =>
                match pointeeTyOpt with
                | .none => .none
                | .some pointeeTy =>
                  match resolveProjectedTyResolved localDecls layouts pointeeTy resolvedRest with
                  | .none => .none
                  | .some subTy => tyByteSize localDecls layouts subTy
            match reqTailBytesOpt with
            | .none => .ub
            | .some reqTailBytes =>
              let newOff := Nat.add parentPtr.offsetBytes fieldOff
              match
                Bool.and
                  (Nat.ble (Nat.add fieldOff reqTailBytes) remBytes)
                  (alignTargetOk newOff)
              with
              | true =>
                .ok (.ptr { parentPtr with offsetBytes := newOff } ptrBytes) locals mem
              | false => .ub

/--
Evaluate `Rvalue.rawPtr` through a dereferenced provenance-less slice fat pointer
`Value.aggregate 0 [Value.scalar addrSc, Value.scalar lenSc]` with non-empty
post-deref projection `restProj`.

Per Miri and MiniRust (`spec/lang/step/expressions.md` `PlaceExpr::Index` /
`PlaceExpr::Field` + `spec/mem/basic.md` `check_ptr`), array/slice index bounds
are checked against `lenSc.bits`, and the resulting `ptr_offset_inbounds` on the
provenance-less data scalar succeeds if and only if the total byte offset is `0`.
-/
def evalScalarSliceFatPtrDerefRaw
    (locals : List LocalSlot)
    (mem : Memory)
    (addrSc : ScalarInt)
    (lenSc : ScalarInt)
    (restProj : List ProjectionElem)
    (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    Bool.and
      (Nat.beq addrSc.sizeBytes ptrBytes)
      (Nat.beq lenSc.sizeBytes ptrBytes)
  with
  | false => .ub
  | true =>
    let modPtr := scalarModulus ptrBytes
    let baseBits := wrapScalarBits addrSc.bits modPtr
    let lenBits := wrapScalarBits lenSc.bits modPtr
    match
      resolveBorrowProjectionElems
        locals
        (stripTransparentProjections restProj)
    with
    | .none => .ub
    | .some rawResolvedRest =>
      let resolvedRest := normalizeSubsliceProjections rawResolvedRest
      let elemTyOpt : Option Ty :=
        match pointeeTyOpt with
        | .some { kind := .slice elemKind, layoutIdx := pIdx } =>
          let elemIdx :=
            match LayoutTable.lookup layouts pIdx with
            | .some { fieldLayouts := flIdx :: _, .. } => flIdx
            | _ => synthKindLayoutIdx layouts elemKind
          .some (resolveTyWithLocalDecls localDecls layouts { kind := elemKind, layoutIdx := elemIdx })
        | .some { kind := .str, .. } =>
          .some { kind := .uint .u8, layoutIdx := synthKindLayoutIdx layouts (.uint .u8) }
        | _ => .none
      let elemSzOpt : Option Nat :=
        match elemTyOpt with
        | .some elemTy => tyByteSize localDecls layouts elemTy
        | .none => .none
      match resolvedRest with
      | .nil =>
        .ok
          (.aggregate 0
            (.scalar ⟨baseBits, ptrBytes⟩ :: .scalar ⟨lenBits, ptrBytes⟩ :: .nil))
          locals
          mem
      | .subslice fromIdx toIdx fromEnd :: .nil =>
        match Nat.ble toIdx lenBits with
        | false => .ub
        | true =>
          let endIdx :=
            match fromEnd with
            | true => Nat.sub lenBits toIdx
            | false => toIdx
          match Nat.ble fromIdx endIdx with
          | false => .ub
          | true =>
            let subLen := Nat.sub endIdx fromIdx
            let offZero : Bool :=
              match Nat.beq fromIdx 0 with
              | true => true
              | false =>
                match elemSzOpt with
                | .some 0 => true
                | _ => false
            match offZero with
            | true =>
              .ok
                (.aggregate 0
                  (.scalar ⟨baseBits, ptrBytes⟩ :: .scalar ⟨subLen, ptrBytes⟩ :: .nil))
                locals
                mem
            | false => .ub
      | .constantIndex offset minLen fromEnd :: tailProj =>
        let fromEndBoundsOk :=
          match fromEnd with
          | false => true
          | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset lenBits)
        match Bool.and (Nat.ble minLen lenBits) fromEndBoundsOk with
        | false => .ub
        | true =>
          let idx :=
            match fromEnd with
            | true => Nat.sub lenBits offset
            | false => offset
          match Nat.ble (.succ idx) lenBits with
          | false => .ub
          | true =>
            let headZeroOpt : Option Bool :=
              match Nat.beq idx 0 with
              | true => .some true
              | false =>
                match elemSzOpt with
                | .some sz => .some (Nat.beq sz 0)
                | .none => .none
            let tailZeroOpt : Option Bool :=
              match tailProj with
              | .nil => .some true
              | _ :: _ =>
                match
                  projectionChainByteOffset?
                    layouts
                    elemTyOpt
                    .none
                    .none
                    0
                    localDecls
                    tailProj
                with
                | .some tailOff => .some (Nat.beq tailOff 0)
                | .none => .none
            match headZeroOpt, tailZeroOpt with
            | .some true, .some true =>
              .ok (.scalar ⟨baseBits, ptrBytes⟩) locals mem
            | _, _ => .ub
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
Validate that a loaded operand value complies with the type's `ScalarLayout.validRange`.
Typed loads (`Operand.copy` and `Operand.move`) of scalar types with a restricted range
(e.g., `bool` [0, 1]) must evaluate to UB if the underlying value is outside the valid range.
-/
@[simp, reducible]
def validateLoadedValue
    (layouts : LayoutTable)
    (localDecls : List LocalDecl)
    (op : Operand)
    (v : Value) : Bool :=
  match op with
  | .constant _ => true
  | .copy _ | .move _ =>
    match operandTy localDecls layouts op with
    | .some ty =>
      match ty.kind with
      | .bool =>
        match v with
        | .scalar sc => Bool.or (Nat.beq sc.bits 0) (Nat.beq sc.bits 1)
        | _ => false
      | _ => true
    | .none => true

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
    (isSyntheticFieldOnScalarPointee : Bool := false)
    (localDecls : List LocalDecl := targetDecls) :
    Option (Option (List ProjectionElem × Nat)) :=
  let rawFull :=
    match parentEntry.targetProjection with
    | .nil => resolvedRest
    | ph :: pt => ph :: appendProjections pt resolvedRest
  let effTargetDecls : List LocalDecl :=
    match targetDecls with
    | _ :: _ => targetDecls
    | .nil =>
      inferCallerTargetDecls
        localDecls
        layouts
        parentEntry
        rawFull
        parentPtr.offsetBytes
        effPointeeTyOpt
  let codecDecls : List LocalDecl :=
    match effTargetDecls with
    | .nil => localDecls
    | _ :: _ => effTargetDecls
  let resolvedAccTyOpt : Option Ty :=
    match accessedTyOpt with
    | .some accTy => .some (resolveTyWithLocalDecls codecDecls layouts accTy)
    | .none => .none
  let accBytesOpt : Option Nat :=
    match resolvedAccTyOpt with
    | .some accTy =>
      match tyByteSize codecDecls layouts accTy with
      | .some sz => .some sz
      | .none =>
        match tyByteSize localDecls layouts accTy with
        | .some sz => .some sz
        | .none => tyByteSize .nil layouts accTy
    | .none => .none
  let reqBytesOpt : Option Nat :=
    match resolvedRest with
    | .nil => accBytesOpt
    | _ :: _ => .none
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
          effTargetDecls
          layouts
          effPointeeTyOpt
          reqBytesOpt
      with
      | .some (fp, resOff) => .some (fp, resOff)
      | .none =>
        match resolvedRest, resolvedAccTyOpt, accBytesOpt with
        | .nil, .some accTy, .some reqBytes =>
          match
            readProjectedForLocal
              locals
              codecDecls
              layouts
              parentEntry.targetLocal
              targetRootVal
              rawFull
          with
          | .ok (.scalar sc) =>
            let ok : Bool :=
              match Nat.beq reqBytes 0 with
              | true => Nat.ble parentPtr.offsetBytes sc.sizeBytes
              | false => Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) sc.sizeBytes
            match ok with
            | true => .some (rawFull, parentPtr.offsetBytes)
            | false => .none
          | .ok (.aggregate aggVar aggFields) =>
            let rawSubTyOpt :=
              placeTyResolved
                effTargetDecls
                layouts
                { local_ := parentEntry.targetLocal, projection := rawFull }
            match
              decodeSubValueAtByteOffset?
                layouts
                rawSubTyOpt
                (.aggregate aggVar aggFields)
                parentPtr.offsetBytes
                accTy
                codecDecls
            with
            | .some _ =>
              .some (normalizeSubsliceProjections rawFull, parentPtr.offsetBytes)
            | .none => .none
          | _ => .none
        | _, _, _ => .none
  match resolvedFullProjOpt with
  | .none => .none
  | .some (fullProj, residualOffset) =>
    match
      readProjectedForLocal
        locals
        codecDecls
        layouts
        parentEntry.targetLocal
        targetRootVal
        fullProj
    with
    | .ub => .none
    | .unsupported => .some .none
    | .ok targetSubVal =>
      let subTyOpt : Option Ty :=
        placeTyResolved
          effTargetDecls
          layouts
          { local_ := parentEntry.targetLocal, projection := fullProj }
      let widthOk : Bool :=
        match resolvedAccTyOpt with
        | .none => Nat.beq residualOffset 0
        | .some accTy =>
          match accTy.kind with
          | .never => false
          | _ =>
            let exactNonScalarSubTyMatch : Bool :=
              match subTyOpt, tyScalarBytes accTy with
              | .some subTy, .none =>
                Bool.and
                  (Nat.beq residualOffset 0)
                  (Bool.and
                    (Bool.not (endsWithSubslice fullProj))
                    (rigidTyEq accTy.kind subTy.kind))
              | _, _ => false
            match exactNonScalarSubTyMatch with
            | true => true
            | false =>
              match targetSubVal with
              | .scalar sc =>
                match accBytesOpt with
                | .some reqBytes =>
                  Nat.ble (Nat.add residualOffset reqBytes) sc.sizeBytes
                | .none => false
              | .unit =>
                match accBytesOpt with
                | .some reqBytes =>
                  Bool.and (Nat.beq residualOffset 0) (Nat.beq reqBytes 0)
                | .none => Nat.beq residualOffset 0
              | .ptr _ pSz =>
                match accBytesOpt with
                | .some reqBytes =>
                  Nat.ble (Nat.add residualOffset reqBytes) pSz
                | .none => Nat.beq residualOffset 0
              | .aggregate aggVar subElems =>
                match subTyOpt with
                | .some subTy =>
                  match
                    Bool.and
                      (Bool.not (endsWithSubslice fullProj))
                      (rigidTyEq accTy.kind subTy.kind)
                  with
                  | true => Nat.beq residualOffset 0
                  | false =>
                    match endsWithSubslice fullProj with
                    | true =>
                      let subElemKindOpt : Option RigidTy :=
                        match subTy.kind with
                        | .array subEk _ => .some subEk
                        | .slice subEk => .some subEk
                        | _ => .none
                      match subElemKindOpt with
                      | .none => false
                      | .some subEk =>
                        let subElemTy :=
                          resolveTyWithLocalDecls
                            codecDecls
                            layouts
                            { kind := subEk, layoutIdx := unresolvedLayoutIdx layouts }
                        match tyByteSize codecDecls layouts subElemTy, accBytesOpt with
                        | .some elemSz, .some reqBytes =>
                          Nat.ble
                            (Nat.add residualOffset reqBytes)
                            (Nat.mul (length subElems) elemSz)
                        | _, .none =>
                          Bool.and
                            (Nat.beq residualOffset 0)
                            (match accTy.kind with
                             | .slice accEk => rigidTyEq accEk subEk
                             | .array accEk accLen =>
                               Bool.and
                                 (rigidTyEq accEk subEk)
                                 (Nat.ble accLen (length subElems))
                             | _ => false)
                        | .none, .some _ => false
                    | false =>
                      match tyByteSize codecDecls layouts subTy, accBytesOpt with
                      | .some subBytes, .some reqBytes =>
                        Nat.ble (Nat.add residualOffset reqBytes) subBytes
                      | .none, .some reqBytes =>
                        Bool.and (Nat.beq residualOffset 0) (Nat.beq reqBytes 0)
                      | _, .none => Nat.beq residualOffset 0
                | .none =>
                  match
                    decodeSubValueAtByteOffset?
                      layouts
                      .none
                      (.aggregate aggVar subElems)
                      residualOffset
                      accTy
                      codecDecls
                  with
                  | .some _ => true
                  | .none =>
                    match tyScalarBytes accTy with
                    | .some _ => false
                    | .none =>
                      match
                        Bool.and
                          (Nat.beq aggVar 0)
                          (isHomogeneousUntypedFields subElems),
                        inferValueCReprBytes (.aggregate aggVar subElems),
                        accBytesOpt
                      with
                      | true, .some subBytes, .some reqBytes =>
                        Nat.ble (Nat.add residualOffset reqBytes) subBytes
                      | _, _, _ =>
                        match aggVar, subElems, accBytesOpt with
                        | 0, .nil, .some reqBytes =>
                          Bool.and (Nat.beq residualOffset 0) (Nat.beq reqBytes 0)
                        | _, _, _ => Nat.beq residualOffset 0
      match widthOk with
      | false => .none
      | true => .some (.some (fullProj, residualOffset))

/--
Reference-reborrow target resolution (`Rvalue.ref _ (*ptr ...)`) with the
address-level alignment check `checkTargetPlaceAlign`:
- first checks that `*ptr` itself is aligned at `(parentEntry.targetProjection,
  parentPtr.offsetBytes)` for `alignTyOpt`;
- then resolves `(fullProj, residualOffset)` via `resolveRefDerefTargetCore?`
  and verifies that the resulting reference `&T` (`accessedTyOpt`) is aligned at
  `(fullProj, residualOffset)` (preventing safe references to misaligned fields
  inside `#[repr(packed)]` structs while permitting aligned fields inside
  `#[repr(packed(N))]` structs even when `parentPtr.offsetBytes` is only
  `N`-aligned).
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
    (isSyntheticFieldOnScalarPointee : Bool := false)
    (localDecls : List LocalDecl := targetDecls) :
    Option (Option (List ProjectionElem × Nat)) :=
  let rawFull :=
    match parentEntry.targetProjection with
    | .nil => resolvedRest
    | ph :: pt => ph :: appendProjections pt resolvedRest
  let effTargetDecls : List LocalDecl :=
    match targetDecls with
    | _ :: _ => targetDecls
    | .nil =>
      inferCallerTargetDecls
        localDecls
        layouts
        parentEntry
        rawFull
        parentPtr.offsetBytes
        effPointeeTyOpt
  let alignTyOpt : Option Ty :=
    match effPointeeTyOpt, resolvedRest with
    | .some pt, _ => .some pt
    | .none, .nil => accessedTyOpt
    | .none, _ :: _ => .none
  match
    checkTargetPlaceAlign
      effTargetDecls
      layouts
      alignTyOpt
      parentEntry
      parentPtr
      (.some targetRootVal)
  with
  | false => .none
  | true =>
    match
      resolveRefDerefTargetCore?
        locals
        targetRootVal
        parentEntry
        parentPtr
        resolvedRest
        effTargetDecls
        layouts
        effPointeeTyOpt
        accessedTyOpt
        isSyntheticFieldOnScalarPointee
        localDecls
    with
    | .none => .none
    | .some .none => .some .none
    | .some (.some (fullProj, residualOffset)) =>
      let refTargetAlignOk : Bool :=
        match isSyntheticFieldOnScalarPointee with
        | true => true
        | false =>
          Bool.and
            (checkDerefAlign localDecls layouts accessedTyOpt residualOffset)
            (checkTargetPlaceAlign
              effTargetDecls
              layouts
              accessedTyOpt
              { parentEntry with targetProjection := fullProj }
              { parentPtr with offsetBytes := residualOffset }
              (.some targetRootVal))
      match refTargetAlignOk with
      | false => .none
      | true => .some (.some (fullProj, residualOffset))

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
    (isSyntheticFieldOnScalarPointee : Bool)
    (localDecls : List LocalDecl := targetDecls) :
    Option (List ProjectionElem × Nat) :=
  let rawFull :=
    match parentEntry.targetProjection with
    | .nil => resolvedRest
    | ph :: pt => ph :: appendProjections pt resolvedRest
  let effTargetDecls : List LocalDecl :=
    match targetDecls with
    | _ :: _ => targetDecls
    | .nil =>
      inferCallerTargetDecls
        localDecls
        layouts
        parentEntry
        rawFull
        parentPtr.offsetBytes
        effPointeeTyOpt
  let codecDecls : List LocalDecl :=
    match effTargetDecls with
    | .nil => localDecls
    | _ :: _ => effTargetDecls
  let reqBytesOpt : Option Nat :=
    match resolvedRest, accessedTyOpt with
    | .nil, .some accTy =>
      match tyByteSize codecDecls layouts accTy with
      | .some sz => .some sz
      | .none =>
        match tyByteSize localDecls layouts accTy with
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
        effTargetDecls
        layouts
        effPointeeTyOpt
        reqBytesOpt
    with
    | .some (fp, resOff) => .some (fp, resOff)
    | .none =>
      match
        accessedTyOpt,
        readProjectedForLocal
          locals
          codecDecls
          layouts
          parentEntry.targetLocal
          targetRootVal
          rawFull
      with
      | .some accTy, .ok (.scalar sc) =>
        match reqBytesOpt with
        | .some reqBytes =>
          let ok : Bool :=
            match Nat.beq reqBytes 0 with
            | true => Nat.ble parentPtr.offsetBytes sc.sizeBytes
            | false => Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) sc.sizeBytes
          match ok with
          | true => .some (rawFull, parentPtr.offsetBytes)
          | false => .none
        | .none =>
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
      | .some accTy, .ok (.aggregate aggVar aggFields) =>
        let rawSubTyOpt :=
          placeTyResolved
            effTargetDecls
            layouts
            { local_ := parentEntry.targetLocal, projection := rawFull }
        let resolvedAccTy := resolveTyWithLocalDecls codecDecls layouts accTy
        match
          resolvedRest,
          decodeSubValueAtByteOffset?
            layouts
            rawSubTyOpt
            (.aggregate aggVar aggFields)
            parentPtr.offsetBytes
            resolvedAccTy
            codecDecls
        with
        | .nil, .some _ =>
          .some (normalizeSubsliceProjections rawFull, parentPtr.offsetBytes)
        | _, _ =>
          match
            needsThinPtrElemResolution
              parentEntry.targetProjection
              parentPtr.offsetBytes,
            resolvedRest,
            Nat.beq parentPtr.offsetBytes 0
          with
          | false, .nil, _ => .some (rawFull, parentPtr.offsetBytes)
          | false, _ :: _, true =>
            match projHasSubslice resolvedRest with
            | true => .none
            | false => .some (rawFull, 0)
          | _, _, _ => .none
      | _, _ =>
        match
          needsThinPtrElemResolution
            parentEntry.targetProjection
            parentPtr.offsetBytes,
          resolvedRest,
          Nat.beq parentPtr.offsetBytes 0
        with
        | false, .nil, _ => .some (rawFull, parentPtr.offsetBytes)
        | false, _ :: _, true =>
          match projHasSubslice resolvedRest with
          | true => .none
          | false => .some (rawFull, 0)
        | _, _, _ => .none

/--
Rank a Tree Borrows permission for angelic `int2ptr`
(`CastKind.pointerWithExposedProvenance`) provenance selection (`MiniRust`
`spec/mem/intptrcast.md` `predict`):
`.active` (3) > `.reserved` / `.reservedIM` / `.reservedConflicted` (2) >
`.frozen` (1) > `.disabled` (0).
-/
def exposedPermScore : TreeBorrowPerm → Nat
  | .active => 3
  | .frozen => 1
  | .disabled => 0
  | _ => 2

/--
Scan `borrows` for live exposed stack borrow tags whose allocation span covers
`addrBits`, returning `(bestCandOpt, sawAmbiguousExposedStackAddr)` where:
- `bestCandOpt = .some (tag, offBytes, permScore, interiorBit, remSpan)` picks
  the highest-ranked exposed stack borrow tag (`permScore`, then strictly
  interior `candOff < bound` over one-past-the-end `candOff == bound`, then
  largest remaining byte span `bound - candOff`),
- `sawAmbiguousExposedStackAddr = true` records if an exposed live stack borrow
  lies on the same local page as `addrBits` with either an unresolvable
  projection offset or `addrBits < tagBase`, so the caller fails closed rather
  than falsely stripping provenance.
-/
def findBestExposedStackBorrow
    (locals : List LocalSlot)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot)
    (exposedAllocIds : List AllocId)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat)
    (addrBits : Nat) :
    List BorrowEntry → Option (Nat × Nat × Nat × Nat × Nat) × Bool
  | .nil => (.none, false)
  | entry :: rest =>
    let (restBest, restAmbig) :=
      findBestExposedStackBorrow
        locals globals callerLocals exposedAllocIds localDecls layouts ptrBytes addrBits rest
    match isExposedAllocId exposedAllocIds entry.tag with
    | false => (restBest, restAmbig)
    | true =>
      let targetLive : Bool :=
        match get? locals entry.targetLocal with
        | .some (.init _) => true
        | .some .uninit => true
        | .some .dead => false
        | .none =>
          match get? callerLocals entry.targetLocal with
          | .some (.init _) => true
          | .some .uninit => true
          | _ => false
      match targetLive with
      | false => (restBest, restAmbig)
      | true =>
        let localPage := Nat.add (stackLocalAddrPageBase ptrBytes) entry.targetLocal
        let localPageBase := Nat.mul localPage 65536
        match borrowPlaceByteOffset? locals callerLocals localDecls layouts entry with
        | .none =>
          let onLocalPage :=
            Bool.and
              (Nat.ble localPageBase addrBits)
              (Nat.blt addrBits (Nat.add localPageBase 65536))
          (restBest, Bool.or restAmbig onLocalPage)
        | .some placeOff =>
          let tagBase := Nat.add localPageBase placeOff
          match Nat.ble tagBase addrBits with
          | false =>
            let beforeSubPlace := Nat.ble localPageBase addrBits
            (restBest, Bool.or restAmbig beforeSubPlace)
          | true =>
            let candOff := Nat.sub addrBits tagBase
            let boundMem : Memory :=
              { emptyMemory with
                globals := globals
                borrows := { entry with perm := .active } :: .nil
                callerLocals := callerLocals }
            let rawBoundOpt :=
              ptrAllocByteBound?
                locals
                boundMem
                localDecls
                layouts
                { allocId := entry.tag, offsetBytes := 0 }
            let bound : Nat :=
              match rawBoundOpt with
              | .some b => b
              | .none => Nat.sub 65536 (Nat.min placeOff 65536)
            match Nat.ble candOff bound with
            | false => (restBest, restAmbig)
            | true =>
              let pScore := exposedPermScore entry.perm
              let interiorBit :=
                match Nat.blt candOff bound with
                | true => 1
                | false => 0
              let remSpan := Nat.sub bound candOff
              let cand := (entry.tag, candOff, pScore, interiorBit, remSpan)
              let pickCand : Bool :=
                match restBest with
                | .none => true
                | .some (_, _, bestPerm, bestInt, bestRem) =>
                  match Nat.blt bestPerm pScore with
                  | true => true
                  | false =>
                    match Nat.beq bestPerm pScore with
                    | false => false
                    | true =>
                      match Nat.blt bestInt interiorBit with
                      | true => true
                      | false =>
                        match Nat.beq bestInt interiorBit with
                        | false => false
                        | true => Nat.blt bestRem remSpan
              match pickCand with
              | true => (.some cand, restAmbig)
              | false => (restBest, restAmbig)

/--
Recover a thin pointer `Value` from integer address `addrBits` for
`CastKind.pointerWithExposedProvenance` (`MiniRust` `spec/mem/intptrcast.md`
`int2ptr`):
1. Searches `borrows` for the highest-ranked live exposed stack borrow whose
   canonical span `[tagBase, tagBase + bound]` covers `addrBits`.
2. Returns `.none` (causing `evalRvalue` to emit `.unsupported`) if an exposed
   live stack borrow on the same local page could not be resolved cleanly.
3. Otherwise checks page-addressed globals (`pageOff <= alloc.bytes.length`) or
   exposed non-stack `allocId`s (`lookupBorrow borrows pageAllocId = .none`),
   falling back to a provenance-less `.scalar ⟨addrBits, ptrBytes⟩`.
-/
def recoverExposedPtrValue?
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot)
    (exposedAllocIds : List AllocId)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptrBytes : Nat)
    (addrBits : Nat) :
    Option Value :=
  let (bestStackOpt, sawAmbig) :=
    findBestExposedStackBorrow
      locals globals callerLocals exposedAllocIds localDecls layouts ptrBytes addrBits borrows
  match bestStackOpt with
  | .some (bestTag, bestOff, _, _, _) =>
    .some (.ptr { allocId := bestTag, offsetBytes := bestOff } ptrBytes)
  | .none =>
    match sawAmbig with
    | true => .none
    | false =>
      let pageAllocId := Nat.div addrBits 65536
      let pageOff := Nat.mod addrBits 65536
      let pageExposedOrGlobal : Bool :=
        match lookupGlobalAlloc globals pageAllocId with
        | .some alloc =>
          Bool.and
            (Bool.not (Nat.beq pageAllocId 0))
            (Nat.ble pageOff (length alloc.bytes))
        | .none =>
          match Nat.beq pageAllocId 0 with
          | true => false
          | false =>
            match lookupBorrow borrows pageAllocId with
            | .some _ => false
            | .none => isExposedAllocId exposedAllocIds pageAllocId
      match pageExposedOrGlobal with
      | true =>
        .some (.ptr { allocId := pageAllocId, offsetBytes := pageOff } ptrBytes)
      | false =>
        .some (.scalar ⟨addrBits, ptrBytes⟩)

/--
Validate `PlaceExpr::Deref` on a safe reference local (`&T` / `&mut T`) inside
`Rvalue.rawPtr` (`&raw const *r`, `&raw mut (*r).field`, etc.), checking
alignment and pointee-size dereferenceability (`MiniRust`
`spec/lang/step/expressions.md` `PlaceExpr::Deref` `safe_pointee`).
-/
def checkSafeRefDerefOk
    (locals : List LocalSlot)
    (parentPtr : ProvenancePtr)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointeeTyOpt : Option Ty) :
    Bool :=
  match checkDerefAlign localDecls layouts pointeeTyOpt parentPtr.offsetBytes with
  | false => false
  | true =>
    let reqBytes : Nat :=
      match pointeeTyOpt with
      | .some pTy =>
        match tyByteSize localDecls layouts pTy with
        | .some sz => sz
        | .none => 0
      | .none => 0
    match lookupBorrow borrows parentPtr.tag with
    | .some parentEntry =>
      let permOk : Bool :=
        match parentEntry.perm with
        | .disabled => false
        | _ => true
      let liveOk : Bool :=
        match get? locals parentEntry.targetLocal with
        | .some (.init _) => true
        | .some .uninit => true
        | .some .dead => false
        | .none =>
          match get? callerLocals parentEntry.targetLocal with
          | .some (.init _) => true
          | .some .uninit => true
          | _ => false
      match Bool.and permOk liveOk with
      | false => false
      | true =>
        let boundMem : Memory :=
          { emptyMemory with
            globals := globals
            borrows := { parentEntry with perm := .active } :: .nil
            callerLocals := callerLocals }
        match
          ptrAllocByteBound?
            locals
            boundMem
            localDecls
            layouts
            { allocId := parentPtr.allocId, offsetBytes := 0 }
        with
        | .some bound => Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) bound
        | .none => true
    | .none =>
      match lookupGlobalAlloc globals parentPtr.allocId with
      | .some alloc =>
        Nat.ble (Nat.add parentPtr.offsetBytes reqBytes) (length alloc.bytes)
      | .none =>
        let isZstPointee : Bool :=
          match pointeeTyOpt with
          | .some pTy =>
            match tyByteSize localDecls layouts pTy with
            | .some 0 => Bool.not (Nat.beq parentPtr.offsetBytes 0)
            | _ => false
          | .none => false
        Bool.and (Nat.beq parentPtr.allocId 0) isZstPointee

/--
Evaluate a dereferenced safe borrow (`Rvalue.ref borrowKind place` when
`place.projection = .deref :: restProj`), validating pointer width, alignment,
and Tree Borrows permissions before creating a child reborrow tag or delegating
to global / slice-fat-pointer borrow helpers.

Reference (The Rust Reference, "Borrow operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#borrow-operators>

> "The & (shared borrow) and &mut (mutable borrow) operators are unary prefix
> operators. When applied to a place expression, this expressions produces a
> reference (pointer) to the location that the value refers to."
-/
def evalRvalueRefDeref
    (locals : List LocalSlot)
    (borrowKind : BorrowKind)
    (place : Place)
    (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
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
        (Nat.beq ptrSz ptrBytes)
        (checkDerefAlign localDecls layouts alignTyOpt parentPtr.offsetBytes)
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
                  localDecls
              with
              | .none => .ub
              | .some .none => .unsupported
              | .some (.some (fullProj, residualOffset)) =>
                let tag := mem.nextTag
                let skipInitRead :=
                  match perm with
                  | .cell => true
                  | _ => placeIsZeroSized localDecls layouts place
                let readUB :=
                  match mem.borrows with
                  | _ :: _ :: _ =>
                    match skipInitRead with
                    | true => false
                    | false =>
                      hasTreeReadUB
                        mem.borrows
                        mem.borrows
                        mem.activeProtectors
                        parentEntry.targetLocal
                        (.some parentPtr.tag)
                        fullProj
                        parentEntry.rangeOffset
                        parentEntry.rangeLen
                  | _ => false
                match readUB with
                | true => .ub
                | false =>
                  let borrowsAfterRead :=
                    match skipInitRead with
                    | true => mem.borrows
                    | false =>
                      freezeTreeBorrowsOnReadAtProj
                        mem.borrows
                        mem.borrows
                        parentEntry.targetLocal
                        (.some parentPtr.tag)
                        fullProj
                        parentEntry.rangeOffset
                        parentEntry.rangeLen
                        mem.activeProtectors
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
                    borrows := entry :: borrowsAfterRead
                    nextTag := Nat.add tag 1
                  }
                  .ok (.ptr { allocId := tag, offsetBytes := residualOffset } ptrBytes) locals mem'
      | .none =>
        match lookupGlobalAlloc mem.globals parentPtr.allocId with
        | .some alloc =>
          let globalRefOk : Bool :=
            let baseAlignOk :=
              checkGlobalAllocAlign
                localDecls
                layouts
                alignTyOpt
                alloc
                parentPtr.offsetBytes
            let accCheckOk :=
              match stripTransparentProjections restProj with
              | .nil =>
                let wOk :=
                  match accessedTyOpt with
                  | .some accTy =>
                    match tyByteSize localDecls layouts accTy with
                    | .some reqB =>
                      Nat.ble
                        (Nat.add parentPtr.offsetBytes reqB)
                        (length alloc.bytes)
                    | .none => true
                  | .none => true
                Bool.and
                  wOk
                  (checkGlobalAllocAlign
                    localDecls
                    layouts
                    accessedTyOpt
                    alloc
                    parentPtr.offsetBytes)
              | _ => true
            Bool.and baseAlignOk accCheckOk
          match globalRefOk with
          | false => .ub
          | true =>
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
              localDecls
              false
              accessedTyOpt
        | .none => .ub
  | .some (.init (.aggregate 0 (.ptr parentPtr ptrSz :: .scalar lenSc :: .nil))) =>
    let sliceAlignTyOpt : Option Ty :=
      match pointeeTyOpt, restProj with
      | .some pt, _ => .some pt
      | .none, .nil => accessedTyOpt
      | .none, _ :: _ => .none
    let sliceTargetAlignOk : Bool :=
      match lookupBorrow mem.borrows parentPtr.tag with
      | .some parentEntry =>
        match get? locals parentEntry.targetLocal with
        | .some (.init rootVal) =>
          checkTargetPlaceAlign
            localDecls
            layouts
            sliceAlignTyOpt
            parentEntry
            parentPtr
            (.some rootVal)
        | _ => true
      | .none =>
        match lookupGlobalAlloc mem.globals parentPtr.allocId with
        | .some alloc =>
          checkGlobalAllocAlign
            localDecls
            layouts
            sliceAlignTyOpt
            alloc
            parentPtr.offsetBytes
        | .none => true
    match
      Bool.and
        (checkDerefAlign localDecls layouts sliceAlignTyOpt parentPtr.offsetBytes)
        sliceTargetAlignOk
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
        true
        localDecls
        accessedTyOpt
        true
  | _ => .ub

/--
Validate `.subslice` projections on a non-dereferenced stack local `loc` holding
`slot`: returns `true` immediately when `resolvedProj` has no `.subslice`;
otherwise enforces forward subslice ordering (`from ≤ to`), static array/slice
bounds when `loc` is in `localDecls` (or rejects `fromEnd = true` on untyped
uninitialized locals), and runtime `subsliceChainValidOnVal` when `slot = .init rootVal`.
-/
@[reducible]
def validateNonDerefSubslices
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (slot : LocalSlot)
    (resolvedProj : List ProjectionElem) :
    Bool :=
  match projHasSubslice resolvedProj with
  | false => true
  | true =>
    match forwardSubslicesOrdered resolvedProj with
    | false => false
    | true =>
      let staticOk : Bool :=
        match get? localDecls loc with
        | .some decl =>
          match resolveProjectedTyResolved localDecls layouts decl.ty resolvedProj with
          | .some _ => true
          | .none => false
        | .none =>
          match slot with
          | .init _ => true
          | _ => Bool.not (projHasFromEndSubslice resolvedProj)
      match staticOk with
      | false => false
      | true =>
        match slot with
        | .init rootVal => subsliceChainValidOnVal locals rootVal resolvedProj
        | _ => true

/--
Evaluate raw address-of (`Rvalue.rawPtr mutability place`), supporting both
root stack places (`&raw const x`, `&raw mut x`) and dereferenced projections
(`&raw const (*p)...`, `&raw mut (*p)...`) without creating intermediate safe
references or triggering Tree Borrows reborrows (`ReborrowSettings::new`
returns `None` for `PtrType::Raw`).

Reference (The Rust Reference, "Raw borrow operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#raw-borrow-operators>

> "Evaluating the operand of a raw borrow expression does not cause its value to
> be moved or read, and does not create any temporary references."
-/
def evalRvalueRawPtr
    (locals : List LocalSlot)
    (mutability : Mutability)
    (place : Place)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let perm :=
    match mutability with
    | .not => sharedBorrowPerm localDecls layouts place
    | .mut => TreeBorrowPerm.active
  let ptrBytes := layoutPointerBytes layouts
  match place.projection with
  | .deref :: restProj =>
    let cleanRest := stripTransparentProjections restProj
    let pointeeTyOpt :=
      placeTyResolved localDecls layouts { local_ := place.local_, projection := .deref :: .nil }
    let accessedTyOpt := placeTyResolved localDecls layouts place
    let isRefLocal : Bool :=
      match get? localDecls place.local_ with
      | .some { ty := { kind := .ref _ _, .. }, .. } => true
      | _ => false
    let isRawPtrLocal : Bool :=
      match get? localDecls place.local_ with
      | .some { ty := { kind := .rawPtr _ _, .. }, .. } => true
      | _ => false
    match get? locals place.local_ with
    | .some (.init (.ptr parentPtr ptrSz)) =>
      let safeRefOk : Bool :=
        match isRefLocal with
        | false => true
        | true =>
          checkSafeRefDerefOk
            locals
            parentPtr
            mem.borrows
            mem.globals
            mem.callerLocals
            localDecls
            layouts
            pointeeTyOpt
      match Bool.and (Nat.beq ptrSz ptrBytes) safeRefOk with
      | false => .ub
      | true =>
        match cleanRest with
        | .nil => .ok (.ptr parentPtr ptrSz) locals mem
        | _ :: _ =>
          let isSyntheticFieldOnScalarPointee : Bool :=
            match cleanRest, pointeeTyOpt with
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
          match resolveBorrowProjectionElems locals restProj with
          | .none => .ub
          | .some resolvedRest =>
            let normRest := normalizeSubsliceProjections (stripTransparentProjections resolvedRest)
            match lookupBorrow mem.borrows parentPtr.tag with
            | .some parentEntry =>
                let rawPerm := parentEntry.perm
                let targetSlotAndDeclsOpt : Option (LocalSlot × List LocalDecl) :=
                  match get? locals parentEntry.targetLocal with
                  | .some slot => .some (slot, localDecls)
                  | .none =>
                    match get? mem.callerLocals parentEntry.targetLocal with
                    | .some slot => .some (slot, .nil)
                    | .none => .none
                let fallbackByByteOffset (checkDead : Bool) (rejectSubslice : Bool) :
                    RvalueEvalResult :=
                  match
                    Bool.or
                      (Bool.and isRefLocal checkDead)
                      (Bool.and rejectSubslice (projHasSubslice normRest))
                  with
                  | true => .ub
                  | false =>
                    match forwardSubslicesOrdered normRest with
                    | false => .ub
                    | true =>
                      match
                        projectionChainByteOffset?
                          layouts
                          effPointeeTyOpt
                          .none
                          .none
                          0
                          localDecls
                          normRest
                      with
                      | .none => .ub
                      | .some fieldOff =>
                        match checkDead with
                        | true =>
                          match
                            Bool.and
                              (Nat.beq fieldOff 0)
                              (Bool.not (projHasSubslice normRest))
                          with
                          | true => .ok (.ptr parentPtr ptrSz) locals mem
                          | false => .ub
                        | false =>
                          let subEndSpanOpt : Option Nat :=
                            match projHasSubslice normRest with
                            | false => .some 0
                            | true =>
                              match effPointeeTyOpt with
                              | .none => .none
                              | .some pTy =>
                                match resolveProjectedTyResolved localDecls layouts pTy normRest with
                                | .none => .none
                                | .some subTy => tyByteSize localDecls layouts subTy
                          match subEndSpanOpt with
                          | .none => .ub
                          | .some subEndSpan =>
                            let boundMem : Memory :=
                              { emptyMemory with
                                globals := mem.globals
                                borrows := { parentEntry with perm := .active } :: .nil
                                callerLocals := mem.callerLocals }
                            let boundOpt :=
                              ptrAllocByteBound? locals boundMem localDecls layouts parentPtr
                            let endSpanInBounds : Bool :=
                              match Nat.beq subEndSpan 0, boundOpt with
                              | true, _ => true
                              | false, .none => true
                              | false, .some allocBound =>
                                Nat.ble
                                  (Nat.add parentPtr.offsetBytes (Nat.add fieldOff subEndSpan))
                                  allocBound
                            match endSpanInBounds with
                            | false => .ub
                            | true =>
                              match evalBinOpOffset parentPtr ptrSz ⟨fieldOff, ptrSz⟩ 1 boundOpt ptrSz with
                              | .none => .ub
                              | .some newPtr =>
                                match parentEntry.targetProjection with
                                | .nil => .ok (.ptr { parentPtr with offsetBytes := newPtr.offsetBytes } ptrSz) locals mem
                                | _ :: _ =>
                                  let tag := mem.nextTag
                                  let entry : BorrowEntry := {
                                    tag := tag
                                    targetLocal := parentEntry.targetLocal
                                    targetProjection := parentEntry.targetProjection
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
                                  .ok (.ptr { allocId := tag, offsetBytes := newPtr.offsetBytes } ptrSz) locals mem'
                match targetSlotAndDeclsOpt with
                | .none => fallbackByByteOffset true true
                | .some (.dead, _) => fallbackByByteOffset true true
                | .some (.uninit, targetDecls) =>
                  match
                    needsThinPtrElemResolution
                      parentEntry.targetProjection
                      parentPtr.offsetBytes,
                    Nat.beq parentPtr.offsetBytes 0
                  with
                  | false, true =>
                    let inBoundsUninit : Bool :=
                      match forwardSubslicesOrdered normRest with
                      | false => false
                      | true =>
                        match
                          projectionChainByteOffset?
                            layouts
                            effPointeeTyOpt
                            .none
                            .none
                            0
                            localDecls
                            normRest
                        with
                        | .none =>
                          match effPointeeTyOpt with
                          | .none =>
                            Bool.and
                              (Bool.not (startsWithArrayOrSliceProj normRest))
                              (Bool.not (projHasFromEndSubslice normRest))
                          | .some _ => false
                        | .some fieldOff =>
                          let subSpanOpt : Option Nat :=
                            match projHasSubslice normRest, effPointeeTyOpt with
                            | false, _ => .some 0
                            | true, .none =>
                              match projHasFromEndSubslice normRest with
                              | true => .none
                              | false => .some 0
                            | true, .some pTy =>
                              match resolveProjectedTyResolved localDecls layouts pTy normRest with
                              | .none => .none
                              | .some subTy =>
                                match tyByteSize localDecls layouts subTy with
                                | .some sz => .some sz
                                | .none => .some 0
                          match subSpanOpt with
                          | .none => false
                          | .some subSpan =>
                            match get? targetDecls parentEntry.targetLocal with
                            | .some decl =>
                              match tyByteSize targetDecls layouts decl.ty with
                              | .some allocSz =>
                                Nat.ble (Nat.add fieldOff subSpan) allocSz
                              | .none => true
                            | .none => true
                    match inBoundsUninit with
                    | false => .ub
                    | true =>
                      let tag := mem.nextTag
                      let fullProj :=
                        match parentEntry.targetProjection with
                        | .nil => resolvedRest
                        | ph :: pt => ph :: appendProjections pt resolvedRest
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
                      .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrSz) locals mem'
                  | _, _ => fallbackByByteOffset false false
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
                      localDecls
                  with
                  | .some (fullProj, residualOffset) =>
                    let tag := mem.nextTag
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
                    .ok (.ptr { allocId := tag, offsetBytes := residualOffset } ptrSz) locals mem'
                  | .none => fallbackByByteOffset false true
            | .none =>
              match lookupGlobalAlloc mem.globals parentPtr.allocId with
              | .some alloc =>
                let isMut :=
                  match isRefLocal, mutability with
                  | true, .mut => true
                  | _, _ => false
                evalGlobalThinPtrDerefBorrow
                  locals
                  mem
                  alloc
                  parentPtr
                  ptrSz
                  restProj
                  isMut
                  effPointeeTyOpt
                  layouts
                  localDecls
                  (Bool.not isRefLocal)
              | .none =>
                match isRefLocal with
                | true => .ub
                | false =>
                  match
                    projectionChainByteOffset?
                      layouts
                      effPointeeTyOpt
                      .none
                      .none
                      0
                      localDecls
                      normRest
                  with
                  | .some 0 => .ok (.ptr parentPtr ptrSz) locals mem
                  | _ => .ub
    | .some (.init (.scalar sc)) =>
      match Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Bool.not isRefLocal) with
      | false => .ub
      | true =>
        let baseBits := wrapScalarBits sc.bits (scalarModulus ptrBytes)
        match cleanRest with
        | .nil => .ok (.scalar ⟨baseBits, ptrBytes⟩) locals mem
        | _ :: _ =>
          let isSyntheticFieldOnScalarPointee : Bool :=
            match cleanRest, pointeeTyOpt with
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
          match resolveBorrowProjectionElems locals cleanRest with
          | .none => .ub
          | .some rawResolvedRest =>
            let resolvedRest := normalizeSubsliceProjections rawResolvedRest
            match
              projectionChainByteOffset?
                layouts
                effPointeeTyOpt
                .none
                .none
                0
                localDecls
                resolvedRest
            with
            | .some 0 => .ok (.scalar ⟨baseBits, ptrBytes⟩) locals mem
            | _ => .ub
    | .some (.init (.aggregate 0 (.ptr parentPtr ptrSz :: .scalar lenSc :: .nil))) =>
      match
        Bool.and
          (Nat.beq ptrSz ptrBytes)
          (Nat.beq lenSc.sizeBytes ptrBytes)
      with
      | false => .ub
      | true =>
        match cleanRest, isRawPtrLocal with
        | .nil, true =>
          let lenBits := wrapScalarBits lenSc.bits (scalarModulus ptrBytes)
          .ok
            (.aggregate 0
              (.ptr parentPtr ptrSz :: .scalar ⟨lenBits, ptrBytes⟩ :: .nil))
            locals
            mem
        | _, true =>
          let rawPerm :=
            match lookupBorrow mem.borrows parentPtr.tag with
            | .some pe => pe.perm
            | .none => perm
          evalSliceFatPtrDerefBorrow
            locals
            mem
            parentPtr
            ptrSz
            lenSc
            restProj
            rawPerm
            false
            pointeeTyOpt
            layouts
            false
        | _, false =>
          let sliceAlignTyOpt : Option Ty :=
            match pointeeTyOpt, restProj with
            | .some pt, _ => .some pt
            | .none, .nil => accessedTyOpt
            | .none, _ :: _ => .none
          let sliceTargetAlignOk : Bool :=
            match lookupBorrow mem.borrows parentPtr.tag with
            | .some parentEntry =>
              match get? locals parentEntry.targetLocal with
              | .some (.init rootVal) =>
                checkTargetPlaceAlign
                  localDecls
                  layouts
                  sliceAlignTyOpt
                  parentEntry
                  parentPtr
                  (.some rootVal)
              | _ => true
            | .none =>
              match lookupGlobalAlloc mem.globals parentPtr.allocId with
              | .some alloc =>
                checkGlobalAllocAlign
                  localDecls
                  layouts
                  sliceAlignTyOpt
                  alloc
                  parentPtr.offsetBytes
              | .none => true
          let safeRefSliceAlignOk : Bool :=
            match isRefLocal with
            | false => true
            | true =>
              Bool.and
                (checkDerefAlign localDecls layouts sliceAlignTyOpt parentPtr.offsetBytes)
                sliceTargetAlignOk
          match safeRefSliceAlignOk with
          | false => .ub
          | true =>
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
              true
              localDecls
    | .some (.init (.aggregate 0 (.scalar addrSc :: .scalar lenSc :: .nil))) =>
      match isRefLocal with
      | true => .ub
      | false =>
        match cleanRest with
        | .nil =>
          match
            Bool.and
              (Nat.beq addrSc.sizeBytes ptrBytes)
              (Nat.beq lenSc.sizeBytes ptrBytes)
          with
          | true =>
            let modPtr := scalarModulus ptrBytes
            .ok
              (.aggregate 0
                (.scalar ⟨wrapScalarBits addrSc.bits modPtr, ptrBytes⟩ ::
                  .scalar ⟨wrapScalarBits lenSc.bits modPtr, ptrBytes⟩ :: .nil))
              locals
              mem
          | false => .ub
        | _ :: _ =>
          evalScalarSliceFatPtrDerefRaw
            locals
            mem
            addrSc
            lenSc
            restProj
            pointeeTyOpt
            localDecls
            layouts
    | _ => .ub
  | _ =>
    match get? locals place.local_ with
    | .none => .ub
    | .some .dead => .ub
    | .some slot =>
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
        match projHasSubslice resolvedProj with
        | false => .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes) locals mem'
        | true =>
          match
            validateNonDerefSubslices
              locals
              localDecls
              layouts
              place.local_
              slot
              resolvedProj
          with
          | true => .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes) locals mem'
          | false => .ub

@[reducible]
def thinRawPtrPointee? (ty : Ty) : Option RigidTy :=
  match ty.kind with
  | .rawPtr _ (.slice _) => .none
  | .rawPtr _ .str => .none
  | .rawPtr _ (.dynamic _) => .none
  | .rawPtr _ dstElem => .some dstElem
  | _ => .none

@[reducible]
def wideRawPtrIsDyn? (ty : Ty) : Option Bool :=
  match ty.kind with
  | .rawPtr _ (.slice _) => .some false
  | .rawPtr _ .str => .some false
  | .rawPtr _ (.dynamic _) => .some true
  | _ => .none

@[reducible]
def isSliceOrStrPtrOrRefTy (tyOpt : Option Ty) : Bool :=
  match tyOpt with
  | .some { kind := .rawPtr _ (.slice _), .. } => true
  | .some { kind := .rawPtr _ .str, .. } => true
  | .some { kind := .ref _ (.slice _), .. } => true
  | .some { kind := .ref _ .str, .. } => true
  | _ => false

@[reducible]
def arrayPtrOrRefElemLen? (tyOpt : Option Ty) (dstElem : RigidTy) : Option Nat :=
  match tyOpt with
  | .some { kind := .rawPtr _ (.array srcElem arrLen), .. } =>
    match rigidTyEq srcElem dstElem with
    | true => .some arrLen
    | false => .none
  | .some { kind := .ref _ (.array srcElem arrLen), .. } =>
    match rigidTyEq srcElem dstElem with
    | true => .some arrLen
    | false => .none
  | _ => .none

@[reducible]
def isUnsizedRawPtrPointee (ty : Ty) : Bool :=
  match ty.kind with
  | .slice _ => true
  | .str => true
  | .dynamic _ => true
  | _ => false

@[reducible]
def wideAggregatePointeeIsDyn? (ty : Ty) : Option Bool :=
  match ty.kind with
  | .dynamic _ => .some true
  | .bool | .char | .int _ | .uint _ | .float _ | .array _ _
  | .rawPtr _ _ | .ref _ _ | .fnPtr .. | .fnDef _ _ | .never
  | .closure _ _ | .foreign _ => .none
  | _ => .some false

/--
Evaluate `CastKind.ptrToPtr` between raw pointers (`*const T` / `*mut T` to
`*const U` / `*mut U`), validating pointer/metadata byte widths against
`layoutPointerBytes layouts` and rejecting non-`rawPtr` target types or
incompatible thin/wide pointer shapes with `.ub`.

Reference (The Rust Reference, "Pointer-to-pointer cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast>

> "`*const T` / `*mut T` can be cast to `*const U` / `*mut U` with the
> following behavior:
> - If `T` and `U` are both sized, the pointer is returned unchanged.
> - If `T` is unsized and `U` is sized, the cast discards all metadata that
>   completes the wide pointer `T` and produces a thin pointer `U` consisting
>   of the data part of the unsized pointer."
-/
def evalCastPtrToPtr
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
  | .ok (.ptr ptrVal sz) locals' =>
    match Nat.beq sz ptrBytes with
    | false => .ub
    | true =>
      match thinRawPtrPointee? targetTy with
      | .none => .ub
      | .some dstElem =>
        match arrayPtrOrRefElemLen? (operandTy localDecls layouts op) dstElem, lookupBorrow mem.borrows ptrVal.tag with
        | .some arrLen, .some parentEntry =>
          deriveStackElemThinPtr locals' mem ptrVal parentEntry (.some arrLen) ptrBytes
        | _, _ => .ok (.ptr ptrVal ptrBytes) locals' mem
  | .ok (.aggregate 0 (.ptr ptrVal sz :: .scalar metaSc :: .nil)) locals' =>
    match
      Bool.and
        (Nat.beq sz ptrBytes)
        (Nat.beq metaSc.sizeBytes ptrBytes)
    with
    | false => .ub
    | true =>
      match isThinRawPtrTy targetTy with
      | true =>
        match lookupBorrow mem.borrows ptrVal.tag with
        | .some parentEntry =>
          deriveStackElemThinPtr locals' mem ptrVal parentEntry (.some metaSc.bits) ptrBytes
        | .none => .ok (.ptr ptrVal ptrBytes) locals' mem
      | false =>
        match wideRawPtrIsDyn? targetTy with
        | .some false =>
          .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .scalar metaSc :: .nil)) locals' mem
        | .some true =>
          match isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) with
          | true => .ub
          | false => .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .scalar metaSc :: .nil)) locals' mem
        | .none => .ub
  | .ok (.aggregate 0 (.ptr ptrVal sz :: .ptr vtPtr vtSz :: .nil)) locals' =>
    match Bool.and (Nat.beq sz ptrBytes) (Nat.beq vtSz ptrBytes) with
    | false => .ub
    | true =>
      match isThinRawPtrTy targetTy with
      | true => .ok (.ptr ptrVal ptrBytes) locals' mem
      | false =>
        match wideRawPtrIsDyn? targetTy, isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) with
        | .some true, false =>
          .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .ptr vtPtr ptrBytes :: .nil)) locals' mem
        | _, _ => .ub
  | .ok (.scalar sc) locals' =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | false => .ub
    | true =>
      match isThinRawPtrTy targetTy with
      | true =>
        .ok (.scalar ⟨wrapScalarBits sc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
      | false => .ub
  | .ok (.aggregate 0 (.scalar addrSc :: .scalar metaSc :: .nil)) locals' =>
    match
      Bool.and
        (Nat.beq addrSc.sizeBytes ptrBytes)
        (Nat.beq metaSc.sizeBytes ptrBytes)
    with
    | false => .ub
    | true =>
      let modPtr := scalarModulus ptrBytes
      let addrBits := wrapScalarBits addrSc.bits modPtr
      let metaBits := wrapScalarBits metaSc.bits modPtr
      match isThinRawPtrTy targetTy with
      | true => .ok (.scalar ⟨addrBits, ptrBytes⟩) locals' mem
      | false =>
        match wideRawPtrIsDyn? targetTy with
        | .some false =>
          .ok (.aggregate 0 (.scalar ⟨addrBits, ptrBytes⟩ :: .scalar ⟨metaBits, ptrBytes⟩ :: .nil)) locals' mem
        | .some true =>
          match isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) with
          | true => .ub
          | false =>
            .ok (.aggregate 0 (.scalar ⟨addrBits, ptrBytes⟩ :: .scalar ⟨metaBits, ptrBytes⟩ :: .nil)) locals' mem
        | .none => .ub
  | .ok (.aggregate 0 (.scalar addrSc :: .ptr vtPtr vtSz :: .nil)) locals' =>
    match Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq vtSz ptrBytes) with
    | false => .ub
    | true =>
      let addrBits := wrapScalarBits addrSc.bits (scalarModulus ptrBytes)
      match isThinRawPtrTy targetTy with
      | true => .ok (.scalar ⟨addrBits, ptrBytes⟩) locals' mem
      | false =>
        match wideRawPtrIsDyn? targetTy, isSliceOrStrPtrOrRefTy (operandTy localDecls layouts op) with
        | .some true, false =>
          .ok (.aggregate 0 (.scalar ⟨addrBits, ptrBytes⟩ :: .ptr vtPtr ptrBytes :: .nil)) locals' mem
        | _, _ => .ub
  | .ok _ _ => .unsupported
  | .ub => .ub
  | .unsupported => .unsupported

/--
Evaluate `CastKind.pointerExposeProvenance` (`ptr as usize` / `ptr.expose_provenance()`),
converting a thin pointer to its deterministic virtual address and recording its
`allocId` in `mem.exposedAllocIds`.

Reference (The Rust Reference, "Pointer-to-address cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#pointer-to-address-cast>

> "Casting a pointer to an integer produces the address of the referenced
> memory, and exposes the pointer's provenance."
-/
@[reducible]
def exposeTargetBytes? (ptrBytes : Nat) (ty : Ty) : Option Nat :=
  match ty.kind with
  | .uint .usize => .some ptrBytes
  | .int .isize => .some ptrBytes
  | k => intCastTargetBytes k

/--
Test whether a dereferenced write to `dst` through the pointer stored in
`dst.local_` is undefined behavior at a strict ancestor of the writer's tag in
the Tree Borrows hierarchy `borrows` (`treeBorrowAncestorsChildAccessUB
.write`): a write through a reborrow is a child write for every ancestor, so a
`.frozen` or `.disabled` ancestor makes it undefined behavior even when the
writer's own permission allows the write.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L184-L199>

> "/// A child node was write-accessed: `Reserved` must become `Unique` to obtain
> /// write permissions, `Frozen` and `Disabled` cannot obtain such permissions and produce UB."
-/
@[reducible]
def derefWriteTreeUB
    (locals₁ : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place) :
    Bool :=
  match borrows with
  | .nil => false
  | _ :: .nil => false
  | b₁ :: b₂ :: restBorrows =>
    let allBorrows := b₁ :: b₂ :: restBorrows
    match get? locals₁ dst.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow allBorrows ptrVal.tag with
      | .some entry =>
        treeBorrowAncestorsChildAccessUB .write allBorrows entry.parentTag
      | .none => false
    | _ => false

def isExposePtrSourceTy (srcOpt : Option Ty) : Bool :=
  match srcOpt with
  | .none => true
  | .some ty =>
    match isThinRawPtrTy ty with
    | true => true
    | false =>
      match ty.kind with
      | .fnPtr _ _ _ abi => Bool.not (callConvEq abi .rustIntrinsic)
      | _ => false

def isExposeIntSourceTy (ptrBytes : Nat) (srcOpt : Option Ty) : Bool :=
  match srcOpt with
  | .none => true
  | .some ty =>
    match exposeTargetBytes? ptrBytes ty with
    | .some _ => true
    | .none => false

def evalPointerExposeProvenance
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match exposeTargetBytes? ptrBytes targetTy, isExposePtrSourceTy (operandTy localDecls layouts op) with
  | .some outBytes, true =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok (.ptr ptrVal ptrSz) locals' =>
      match Nat.beq ptrSz ptrBytes with
      | false => .ub
      | true =>
        match
          ptrAddress?
            locals'
            mem.borrows
            mem.callerLocals
            localDecls
            layouts
            ptrBytes
            ptrVal
        with
        | .some fullAddr =>
          let rawAddr := wrapScalarBits fullAddr (scalarModulus ptrBytes)
          let addr := wrapScalarBits rawAddr (scalarModulus outBytes)
          let mem' :=
            { mem with exposedAllocIds := recordExposedAllocId mem.exposedAllocIds ptrVal.allocId }
          .ok (.scalar ⟨addr, outBytes⟩) locals' mem'
        | .none => .unsupported
    | .ok (.scalar sc) locals' =>
      match Nat.beq sc.sizeBytes ptrBytes with
      | false => .ub
      | true =>
        let rawAddr := wrapScalarBits sc.bits (scalarModulus ptrBytes)
        let addr := wrapScalarBits rawAddr (scalarModulus outBytes)
        .ok (.scalar ⟨addr, outBytes⟩) locals' mem
    | .ok _ _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | _, _ => .ub

@[reducible]
def isBadWithExposedTargetTy (ty : Ty) : Bool :=
  Bool.not (isThinRawPtrTy ty)

/--
Evaluate `CastKind.pointerWithExposedProvenance` (`addr as *const T` /
`ptr::with_exposed_provenance`), recovering exposed provenance when `addr`
falls within a previously exposed allocation or returning a provenance-less
address scalar (`Value.scalar ⟨addrBits, ptrBytes⟩`).

Reference (The Rust Reference, "Address-to-pointer cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#address-to-pointer-cast>

> "Casting an integer to a pointer produces a pointer with the given address and
> exposed provenance."
-/
def evalPointerWithExposedProvenance
    (locals : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match
    isBadWithExposedTargetTy targetTy,
    isExposeIntSourceTy ptrBytes (operandTy localDecls layouts op)
  with
  | false, true =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok (.scalar sc) locals' =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let modPtr := scalarModulus ptrBytes
        let addrBits :=
          match operandIsSigned localDecls op layouts with
          | false => wrapScalarBits sc.bits modPtr
          | true =>
            match Nat.ble ptrBytes sc.sizeBytes with
            | true => wrapScalarBits sc.bits modPtr
            | false => signExtendBits sc.bits sc.sizeBytes ptrBytes
        match
          recoverExposedPtrValue?
            locals'
            mem.borrows
            mem.globals
            mem.callerLocals
            mem.exposedAllocIds
            localDecls
            layouts
            ptrBytes
            addrBits
        with
        | .some recoveredVal => .ok recoveredVal locals' mem
        | .none => .unsupported
    | .ok _ _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | _, _ => .ub

/--
Evaluate `AggregateKind.rawPtr pointeeTy mutability ops` (`ptr::from_raw_parts`
and `ptr::from_raw_parts_mut`), validating data-pointer and metadata widths
against `layoutPointerBytes layouts` and checking pointee metadata compatibility
(faulting with `.ub` on thin/wide metadata mismatch and returning `.unsupported`
on `dyn Trait` vtable metadata construction).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1308-L1314>

> "/// Create a raw pointer from the data pointer and metadata.
> /// The `Mutability` indicates whether it's `*const` or `*mut`,
> /// and the `Ty` is the pointee type.
> RawPtr(Ty<'tcx>, Mutability),"
-/
def evalAggregateRawPtr
    (locals : List LocalSlot)
    (pointeeTy : Ty)
    (ops : List Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
  | .ok (.ptr ptrVal ptrSz :: .unit :: .nil) locals' =>
    match isUnsizedRawPtrPointee pointeeTy, Nat.beq ptrSz ptrBytes with
    | false, true => .ok (.ptr ptrVal ptrBytes) locals' mem
    | _, _ => .ub
  | .ok (.ptr ptrVal ptrSz :: .aggregate 0 .nil :: .nil) locals' =>
    match isUnsizedRawPtrPointee pointeeTy, Nat.beq ptrSz ptrBytes with
    | false, true => .ok (.ptr ptrVal ptrBytes) locals' mem
    | _, _ => .ub
  | .ok (.scalar addrSc :: .unit :: .nil) locals' =>
    match isUnsizedRawPtrPointee pointeeTy, Nat.beq addrSc.sizeBytes ptrBytes with
    | false, true => .ok (.scalar ⟨wrapScalarBits addrSc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
    | _, _ => .ub
  | .ok (.scalar addrSc :: .aggregate 0 .nil :: .nil) locals' =>
    match isUnsizedRawPtrPointee pointeeTy, Nat.beq addrSc.sizeBytes ptrBytes with
    | false, true => .ok (.scalar ⟨wrapScalarBits addrSc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
    | _, _ => .ub
  | .ok (.ptr ptrVal ptrSz :: .scalar metaSc :: .nil) locals' =>
    match wideAggregatePointeeIsDyn? pointeeTy with
    | .some true => .unsupported
    | .none => .ub
    | .some false =>
      match Bool.and (Nat.beq ptrSz ptrBytes) (Nat.beq metaSc.sizeBytes ptrBytes) with
      | true =>
        .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .scalar ⟨metaSc.bits, ptrBytes⟩ :: .nil))
          locals' mem
      | false => .ub
  | .ok (.scalar addrSc :: .scalar metaSc :: .nil) locals' =>
    match wideAggregatePointeeIsDyn? pointeeTy with
    | .some true => .unsupported
    | .none => .ub
    | .some false =>
      match Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq metaSc.sizeBytes ptrBytes) with
      | true =>
        let modPtr := scalarModulus ptrBytes
        .ok
          (.aggregate 0
            (.scalar ⟨wrapScalarBits addrSc.bits modPtr, ptrBytes⟩ ::
              .scalar ⟨wrapScalarBits metaSc.bits modPtr, ptrBytes⟩ :: .nil))
          locals' mem
      | false => .ub
  | .ok (.ptr ptrVal ptrSz :: .ptr vtPtr vtSz :: .nil) locals' =>
    match wideAggregatePointeeIsDyn? pointeeTy with
    | .some true =>
      match Bool.and (Nat.beq ptrSz ptrBytes) (Nat.beq vtSz ptrBytes) with
      | true =>
        .ok (.aggregate 0 (.ptr ptrVal ptrBytes :: .ptr vtPtr ptrBytes :: .nil)) locals' mem
      | false => .ub
    | _ => .ub
  | .ok (.scalar addrSc :: .ptr vtPtr vtSz :: .nil) locals' =>
    match wideAggregatePointeeIsDyn? pointeeTy with
    | .some true =>
      match Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq vtSz ptrBytes) with
      | true =>
        let modPtr := scalarModulus ptrBytes
        .ok
          (.aggregate 0
            (.scalar ⟨wrapScalarBits addrSc.bits modPtr, ptrBytes⟩ ::
              .ptr vtPtr ptrBytes :: .nil))
          locals' mem
      | false => .ub
    | _ => .ub
  | .ok _ _ => .unsupported
  | .ub => .ub
  | .unsupported => .unsupported

def isNonWidePtrAggregateTy (tyOpt : Option Ty) : Bool :=
  match tyOpt with
  | .none => false
  | .some ty => Bool.not (isExplicitWidePtrTy (.some ty))

def isThinPtrMetadataOperandTy (tyOpt : Option Ty) : Bool :=
  match tyOpt with
  | .none => true
  | .some ty =>
    match isThinRawPtrTy ty with
    | true => true
    | false =>
      match ty.kind with
      | .ref _ (.slice _) => false
      | .ref _ .str => false
      | .ref _ (.dynamic _) => false
      | .ref _ _ => true
      | .fnPtr .. => true
      | _ => false

def evalUnaryPtrMetadata
    (locals : List LocalSlot)
    (op : Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  let srcTyOpt := operandTy localDecls layouts op
  match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls with
  | .ok (.aggregate 0 (.ptr _ ptrSz :: .scalar metaSc :: .nil)) locals' =>
    match
      Bool.and
        (Nat.beq ptrSz ptrBytes)
        (Nat.beq metaSc.sizeBytes ptrBytes)
    with
    | true => .ok (.scalar ⟨metaSc.bits, metaSc.sizeBytes⟩) locals' mem
    | false => .ub
  | .ok (.aggregate 0 (.ptr _ ptrSz :: .ptr vtPtr vtSz :: .nil)) locals' =>
    match isNonWidePtrAggregateTy srcTyOpt with
    | true => .ok (.scalar ⟨2, ptrBytes⟩) locals' mem
    | false =>
      match
        Bool.and
          (Bool.not (isSliceOrStrPtrOrRefTy srcTyOpt))
          (Bool.and (Nat.beq ptrSz ptrBytes) (Nat.beq vtSz ptrBytes))
      with
      | true => .ok (.ptr vtPtr ptrBytes) locals' mem
      | false => .ub
  | .ok (.aggregate 0 (.scalar addrSc :: .scalar metaSc :: .nil)) locals' =>
    match isNonWidePtrAggregateTy srcTyOpt with
    | true => .ok (.scalar ⟨2, ptrBytes⟩) locals' mem
    | false =>
      match
        Bool.and
          (Nat.beq addrSc.sizeBytes ptrBytes)
          (Nat.beq metaSc.sizeBytes ptrBytes)
      with
      | true =>
        .ok (.scalar ⟨wrapScalarBits metaSc.bits (scalarModulus ptrBytes), ptrBytes⟩) locals' mem
      | false => .ub
  | .ok (.aggregate 0 (.scalar addrSc :: .ptr vtPtr vtSz :: .nil)) locals' =>
    match isNonWidePtrAggregateTy srcTyOpt with
    | true => .ok (.scalar ⟨2, ptrBytes⟩) locals' mem
    | false =>
      match
        Bool.and
          (Bool.not (isSliceOrStrPtrOrRefTy srcTyOpt))
          (Bool.and (Nat.beq addrSc.sizeBytes ptrBytes) (Nat.beq vtSz ptrBytes))
      with
      | true => .ok (.ptr vtPtr ptrBytes) locals' mem
      | false => .ub
  | .ok (.aggregate 0 elems) locals' =>
    match isExplicitWidePtrTy srcTyOpt with
    | true => .ub
    | false => .ok (.scalar ⟨length elems, ptrBytes⟩) locals' mem
  | .ok (.ptr _ ptrSz) locals' =>
    match Nat.beq ptrSz ptrBytes with
    | true => .ok .unit locals' mem
    | false => .ub
  | .ok (.scalar sc) locals' =>
    match Bool.and (Nat.beq sc.sizeBytes ptrBytes) (isThinPtrMetadataOperandTy srcTyOpt) with
    | true => .ok .unit locals' mem
    | false => .ub
  | .ok _ _ => .unsupported
  | .ub => .ub
  | .unsupported => .unsupported

def collectAdtLayoutsInTupleAux
    (collectElem : RigidTy → Nat → List TypeLayout → List TypeLayout) :
    List RigidTy → List Nat → List TypeLayout → List TypeLayout
  | .nil, _, acc => acc
  | ek :: ekRest, flIdxs, acc =>
    let (flIdx, flRest) :=
      match flIdxs with
      | f :: fs => (f, fs)
      | .nil => (0, .nil)
    let acc' := collectElem ek flIdx acc
    collectAdtLayoutsInTupleAux collectElem ekRest flRest acc'

/--
Collect `TypeLayout` entries in `layouts` for every occurrence of `.adt defPath _`
inside `ty` (descending through `.tuple`, `.array`, and `.slice` `fieldLayouts`).
-/
def collectAdtLayoutsInTyAux :
    Nat → LayoutTable → DefPath → Ty → List TypeLayout → List TypeLayout
  | .zero, _, _, _, acc => acc
  | .succ fuel', layouts, defPath, ty, acc =>
    let collectChild := fun (ek : RigidTy) (flIdx : Nat) (a : List TypeLayout) =>
      collectAdtLayoutsInTyAux fuel' layouts defPath { kind := ek, layoutIdx := flIdx } a
    match ty.kind with
    | .adt dp _ =>
      match stringEq dp defPath with
      | false => acc
      | true =>
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l => l :: acc
        | .none => acc
    | .tuple elemKinds =>
      let flIdxs : List Nat :=
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l => l.fieldLayouts
        | .none => .nil
      collectAdtLayoutsInTupleAux collectChild elemKinds flIdxs acc
    | .array ek _ =>
      match LayoutTable.lookup layouts ty.layoutIdx with
      | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
        collectChild ek flIdx acc
      | _ => acc
    | .slice ek =>
      match LayoutTable.lookup layouts ty.layoutIdx with
      | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
        collectChild ek flIdx acc
      | _ => acc
    | _ => acc

/--
Collect `TypeLayout` entries for `defPath` across all declarations in `localDecls`.
-/
def collectAdtLayoutsInDecls
    (layouts : LayoutTable)
    (defPath : DefPath) :
    List LocalDecl → List TypeLayout
  | .nil => .nil
  | decl :: rest =>
    collectAdtLayoutsInTyAux
      6
      layouts
      defPath
      decl.ty
      (collectAdtLayoutsInDecls layouts defPath rest)

/--
Check whether `l` is a single-variant `.union _` `TypeLayout`.
-/
@[reducible]
def layoutIsSingleVariantUnion (l : TypeLayout) : Option Nat :=
  match l.variants, l.fields with
  | .single 0, .union count => .some count
  | _, _ => .none

/--
Return `true` when every `TypeLayout` in `ls` has `layoutIsSingleVariantUnion l = .some _`.
-/
def allLayoutsAreUnions : List TypeLayout → Bool
  | .nil => true
  | l :: rest =>
    match layoutIsSingleVariantUnion l with
    | .some _ => allLayoutsAreUnions rest
    | .none => false

/--
Check whether union `TypeLayout` `l` (`fields = .union count`) is inhabited,
has `fIdx < count`, and accepts `valOpt` at active field `fIdx`.
-/
def unionLayoutAcceptsActiveField
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (l : TypeLayout)
    (fIdx : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty := .none) :
    Option (Nat × TypeLayout) :=
  match l.isUninhabited, layoutIsSingleVariantUnion l with
  | true, _ => .none
  | false, .none => .none
  | false, .some count =>
    match Nat.blt fIdx count with
    | false => .none
    | true =>
      let opTyValidOk : Bool :=
        match opTyOpt, valOpt with
        | .some rawOpTy, .some v =>
          let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
          match validateValueForTy? layouts (.some opTy) v with
          | false => false
          | true =>
            match encodeTypedValueToBytes layouts opTy v with
            | .some _ => true
            | .none => false
        | _, _ => true
      match opTyValidOk with
      | false => .none
      | true =>
        match get? l.fieldLayouts fIdx with
        | .some flIdx =>
          match LayoutTable.lookup layouts flIdx with
          | .none => .some (count, l)
          | .some fl =>
            match fl.isUninhabited with
            | true => .none
            | false =>
              let opSizeMatchesFl : Bool :=
                match opTyOpt with
                | .some rawOpTy =>
                  let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
                  match tyByteSize localDecls layouts opTy with
                  | .some opSz => Nat.beq opSz fl.size.bytes
                  | .none => true
                | .none => true
              match opSizeMatchesFl with
              | false => .none
              | true =>
                match valOpt with
                | .none => .some (count, l)
                | .some v =>
                  let unitOk : Bool :=
                    match v with
                    | .unit => Nat.beq fl.size.bytes 0
                    | _ => true
                  match unitOk with
                  | false => .none
                  | true =>
                    match encodeByLayoutIdxAux defaultCodecFuel layouts flIdx v with
                    | .some _ => .some (count, l)
                    | .none => .none
        | .none =>
          match opTyOpt with
          | .none => .some (count, l)
          | .some rawOpTy =>
            let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
            match LayoutTable.lookup layouts opTy.layoutIdx with
            | .some opFl =>
              match
                Bool.or
                  opFl.isUninhabited
                  (Bool.not (Nat.ble opFl.size.bytes l.size.bytes))
              with
              | true => .none
              | false =>
                match valOpt with
                | .none => .some (count, l)
                | .some v =>
                  let unitOk : Bool :=
                    match v with
                    | .unit => Nat.beq opFl.size.bytes 0
                    | _ => true
                  match unitOk with
                  | false => .none
                  | true =>
                    match encodeTypedValueToBytes layouts opTy v with
                    | .some _ => .some (count, l)
                    | .none => .none
            | .none =>
              match tyByteSize localDecls layouts opTy with
              | .some opSz =>
                match Nat.ble opSz l.size.bytes with
                | true => .some (count, l)
                | false => .none
              | .none => .some (count, l)

/--
Find a union `TypeLayout` in `ls` that accepts `(fIdx, valOpt)` whose active
field layout index at `fIdx` equals `targetFlIdx`.
-/
def findExactFieldLayoutUnionInList
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fIdx targetFlIdx : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty) :
    List TypeLayout → Option (Nat × TypeLayout)
  | .nil => .none
  | l :: rest =>
    let flMatch : Bool :=
      match get? l.fieldLayouts fIdx with
      | .some flIdx => Nat.beq flIdx targetFlIdx
      | .none => false
    match flMatch with
    | false =>
      findExactFieldLayoutUnionInList localDecls layouts fIdx targetFlIdx valOpt opTyOpt rest
    | true =>
      match unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt with
      | .some info => .some info
      | .none =>
        findExactFieldLayoutUnionInList localDecls layouts fIdx targetFlIdx valOpt opTyOpt rest

/--
Find a union `TypeLayout` in `ls` that accepts `(fIdx, valOpt)` whose total byte
size equals `targetSz`.
-/
def findExactSizeUnionInList
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fIdx targetSz : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty) :
    List TypeLayout → Option (Nat × TypeLayout)
  | .nil => .none
  | l :: rest =>
    match Nat.beq l.size.bytes targetSz with
    | false =>
      findExactSizeUnionInList localDecls layouts fIdx targetSz valOpt opTyOpt rest
    | true =>
      match unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt with
      | .some info => .some info
      | .none =>
        findExactSizeUnionInList localDecls layouts fIdx targetSz valOpt opTyOpt rest

/--
Find the first union `TypeLayout` in `ls` that accepts `(fIdx, valOpt)`,
preferring layouts whose `fieldLayouts[fIdx]` matches `opTy.layoutIdx`, then
layouts whose byte size matches `opTy`, and finally any accepting union layout.
-/
def findMatchingUnionCountInList
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fIdx : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty)
    (ls : List TypeLayout) :
    Option (Nat × TypeLayout) :=
  let rec findAny : List TypeLayout → Option (Nat × TypeLayout)
    | .nil => .none
    | l :: rest =>
      match unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt with
      | .some info => .some info
      | .none => findAny rest
  let byExactFl : Option (Nat × TypeLayout) :=
    match opTyOpt with
    | .some rawOpTy =>
      let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
      match isUnresolvedLayoutIdx layouts opTy.layoutIdx with
      | true => .none
      | false =>
        findExactFieldLayoutUnionInList
          localDecls
          layouts
          fIdx
          opTy.layoutIdx
          valOpt
          opTyOpt
          ls
    | .none => .none
  match byExactFl with
  | .some info => .some info
  | .none =>
    let byExactSz : Option (Nat × TypeLayout) :=
      match opTyOpt with
      | .some rawOpTy =>
        let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
        match tyByteSize localDecls layouts opTy with
        | .some opSz =>
          findExactSizeUnionInList localDecls layouts fIdx opSz valOpt opTyOpt ls
        | .none => .none
      | .none => .none
    match byExactSz with
    | .some info => .some info
    | .none => findAny ls

/--
Scan `layouts.entries` (when `defPath` had no layout-bearing entry in `localDecls`):
returns `(sawAnyUnion, uniqueAllUnionCount?, conflict, firstMatchingInfo?)`.
-/
def scanTableUnionEntries
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fIdx : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty) :
    List TypeLayout → Bool × Option Nat × Bool × Option (Nat × TypeLayout)
  | .nil => (false, .none, false, .none)
  | l :: rest =>
    let (sawRest, countRest, conflictRest, matchRest) :=
      scanTableUnionEntries localDecls layouts fIdx valOpt opTyOpt rest
    match layoutIsSingleVariantUnion l with
    | .none => (sawRest, countRest, conflictRest, matchRest)
    | .some c =>
      let (newCountOpt, newConflict) : Option Nat × Bool :=
        match sawRest, countRest with
        | false, _ => (.some c, false)
        | true, .some prevC =>
          match Nat.beq c prevC with
          | true => (.some c, conflictRest)
          | false => (.none, true)
        | true, .none => (.none, true)
      let newMatch : Option (Nat × TypeLayout) :=
        match matchRest with
        | .some m => .some m
        | .none => unionLayoutAcceptsActiveField localDecls layouts l fIdx valOpt opTyOpt
      (true, newCountOpt, newConflict, newMatch)

/--
Resolve union field count and layout metadata for `AggregateKind.adt defPath _ (.some fIdx)`:
- `.some (.some (count, l))`: `defPath` is an inhabited union of `count` fields with
  `fIdx < count` and valid active-field value `valOpt`.
- `.some .none`: `defPath` is a non-union ADT (struct/enum), uninhabited,
  out-of-range (`fIdx ≥ count`), or `valOpt` violates the active field's layout.
- `.none`: untyped fallback (no union `TypeLayout` for `defPath` in scope).
-/
def findAdtUnionInfo
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (defPath : DefPath)
    (fIdx : Nat)
    (valOpt : Option Value)
    (opTyOpt : Option Ty := .none) :
    Option (Option (Nat × TypeLayout)) :=
  let declLayouts := collectAdtLayoutsInDecls layouts defPath localDecls
  match declLayouts with
  | l₀ :: lRest =>
    match allLayoutsAreUnions (l₀ :: lRest) with
    | false => .some .none
    | true =>
      match findMatchingUnionCountInList localDecls layouts fIdx valOpt opTyOpt (l₀ :: lRest) with
      | .some info => .some (.some info)
      | .none => .some .none
  | .nil =>
    match localDecls with
    | _ :: _ => .none
    | .nil =>
      let (sawUnion, _, conflict, matchOpt) :=
        scanTableUnionEntries localDecls layouts fIdx valOpt opTyOpt layouts.entries
      match sawUnion, conflict with
      | false, _ => .none
      | true, true => .none
      | true, false =>
        match matchOpt with
        | .some info => .some (.some info)
        | .none => .some .none

/--
Attach a trailing raw-byte overlay to `typedFields` when `unionLayout.fieldLayouts`
is empty (`rustc` default on `FieldsShape.union`) and the active field's typed byte
encoding differs from `encodeUntypedValueToBytes` (e.g., a struct field with padding
bytes), so subsequent cross-variant reads observe exact `.uninit` padding bytes.
Forces the resulting `List Value` spine before returning `.some` so kernel `rfl`
executions never retain unreduced closures inside `Value.aggregate 0 ...`.
-/
def attachUnionActiveFieldOverlayOpt
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (unionLayout : TypeLayout)
    (typedFields : List Value)
    (activeVal : Value)
    (opTyOpt : Option Ty) :
    Option (List Value) :=
  match unionLayout.fieldLayouts, opTyOpt with
  | .nil, .some rawOpTy =>
    let opTy := resolveTyWithLocalDecls localDecls layouts rawOpTy
    match encodeTypedValueToBytes layouts opTy activeVal with
    | .none => forceValueListOpt typedFields
    | .some activeBytes =>
      let sameAsUntyped : Bool :=
        match encodeUntypedValueToBytes defaultCodecFuel activeVal with
        | .some untypedBytes => abstractByteListEq activeBytes untypedBytes
        | .none => false
      match sameAsUntyped with
      | true => forceValueListOpt typedFields
      | false =>
        match writeAbstractBytesAt (replicateUninitBytes unionLayout.size.bytes) 0 activeBytes with
        | .some mergedBytes =>
          match forceValueListOpt (encodeRawAbstractByteVals mergedBytes) with
          | .some rawVals =>
            forceValueListOpt
              (appendValueList typedFields (.aggregate 0 rawVals :: .nil))
          | .none => .none
        | .none => forceValueListOpt typedFields
  | _, _ => forceValueListOpt typedFields

/--
Construct the union `Value` for `evalAggregateAdt` when `activeField = .some fIdx`
(returning `.none` on UB: non-zero `variantIdx`, empty or out-of-bounds operand
list, invalid active-field operand, or invalid union field index). The active
slot holds `.unit` instead of the operand value when
`unionActiveSlotIsZstPlaceholder` holds. That choice is made by a `match` before
the result is built (each branch applies the continuation `mk`), so a
constructed union is the same closed term as without the check: kernel `rfl`
re-checks of multi-step machine runs exhaust memory when the stored value keeps
an unreduced application (even of an identity wrapper) over the operand
context.
-/
def evalAggregateAdtUnionValue?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (defPath : DefPath)
    (variantIdx : VariantIdx)
    (fIdx : FieldIdx)
    (ops : List Operand)
    (vals : List Value) :
    Option Value :=
  match Nat.beq variantIdx 0 with
  | false => .none
  | true =>
    match vals with
    | .nil => .none
    | v :: .nil =>
      let opTyOpt : Option Ty :=
        match ops with
        | op :: .nil => operandTy localDecls layouts op
        | _ => .none
      match validateValueForTy? layouts opTyOpt v with
      | false => .none
      | true =>
        match findAdtUnionInfo localDecls layouts defPath fIdx (.some v) opTyOpt with
        | .some .none => .none
        | .some (.some (count, unionLayout)) =>
          let prefixUnits := replicateValue fIdx .unit
          let suffixUnits := replicateValue (Nat.sub count (.succ fIdx)) .unit
          let mk : Value → Option Value := fun activeSlot =>
            let typedFields := appendValueList prefixUnits (activeSlot :: suffixUnits)
            match
              attachUnionActiveFieldOverlayOpt
                localDecls
                layouts
                unionLayout
                typedFields
                v
                opTyOpt
            with
            | .some fields => .some (.aggregate 0 fields)
            | .none => .none
          match
            unionActiveSlotIsZstPlaceholder
              localDecls
              layouts
              opTyOpt
              v
              unionLayout.fieldLayouts
          with
          | true => mk .unit
          | false => mk v
        | .none =>
          let mk : Value → Option Value := fun activeSlot =>
            match forceValueListOpt (appendValueList (replicateValue fIdx .unit) (activeSlot :: .nil)) with
            | .some fields => .some (.aggregate 0 fields)
            | .none => .none
          match unionActiveSlotIsZstPlaceholder localDecls layouts opTyOpt v with
          | true => mk .unit
          | false => mk v
    | v₀ :: v₁ :: vRest =>
      let fullVals := v₀ :: v₁ :: vRest
      let nVals := length fullVals
      match get? fullVals fIdx with
      | .none => .none
      | .some activeVal =>
        let activeOpTyOpt : Option Ty :=
          match get? ops fIdx with
          | .some activeOp => operandTy localDecls layouts activeOp
          | .none => .none
        match validateValueForTy? layouts activeOpTyOpt activeVal with
        | false => .none
        | true =>
          match findAdtUnionInfo localDecls layouts defPath fIdx (.some activeVal) activeOpTyOpt with
          | .some .none => .none
          | .some (.some (count, unionLayout)) =>
            match Nat.ble nVals count with
            | false => .none
            | true =>
              let prefixUnits := replicateValue fIdx .unit
              let suffixUnits := replicateValue (Nat.sub count (.succ fIdx)) .unit
              let mk : Value → Option Value := fun activeSlot =>
                let typedFields := appendValueList prefixUnits (activeSlot :: suffixUnits)
                match
                  attachUnionActiveFieldOverlayOpt
                    localDecls
                    layouts
                    unionLayout
                    typedFields
                    activeVal
                    activeOpTyOpt
                with
                | .some fields => .some (.aggregate 0 fields)
                | .none => .none
              match
                unionActiveSlotIsZstPlaceholder
                  localDecls
                  layouts
                  activeOpTyOpt
                  activeVal
                  unionLayout.fieldLayouts
              with
              | true => mk .unit
              | false => mk activeVal
          | .none =>
            let prefixUnits := replicateValue fIdx .unit
            let suffixUnits := replicateValue (Nat.sub nVals (.succ fIdx)) .unit
            let mk : Value → Option Value := fun activeSlot =>
              match forceValueListOpt (appendValueList prefixUnits (activeSlot :: suffixUnits)) with
              | .some fields => .some (.aggregate 0 fields)
              | .none => .none
            match unionActiveSlotIsZstPlaceholder localDecls layouts activeOpTyOpt activeVal with
            | true => mk .unit
            | false => mk activeVal

@[reducible]
def evalAggregateAdt
    (locals : List LocalSlot)
    (defPath : DefPath)
    (variantIdx : VariantIdx)
    (activeField : Option FieldIdx)
    (ops : List Operand)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueEvalResult :=
  match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok vals locals' =>
    match activeField with
    | .none => .ok (.aggregate variantIdx vals) locals' mem
    | .some fIdx =>
      match evalAggregateAdtUnionValue? localDecls layouts defPath variantIdx fIdx ops vals with
      | .some v => .ok v locals' mem
      | .none => .ub

/--
Evaluate an `Rvalue` in `locals` and `mem`, using `localDecls` and `layouts` to
resolve operand types, signedness, and byte layouts for `Rvalue.binaryOp`,
`Rvalue.unaryOp`, `Rvalue.cast`, and `Rvalue.aggregate`.

Tree Borrows modeling in `Rvalue.use`, `Rvalue.copyForDeref`, `Rvalue.ref`, and
`Rvalue.rawPtr`:
- Dereference reads (`.use (.copy/.move (.deref :: _))` and `.copyForDeref
  (.deref :: _)`) with two or more borrow entries first reject reads that are
  undefined behavior anywhere in the hierarchy (`derefReadTreeUB`: a
  `.disabled` reader or ancestor, or a foreign read that would disable a
  protected `.unique` entry), then apply the foreign-read transition with
  protector status (`freezeDerefReadBorrowsAt`). With a single entry the
  reader has no ancestor or foreign entry, and `evalOperand` already rejects a
  `.disabled` reader. Dereference reads that occur inside other rvalue operands
  are checked only against the reader's own permission by `evalOperand`.
- Dereference reborrows (`.ref borrowKind (.deref :: restProj)`) link the new
  tag to `parentTag := .some parentPtr.tag`, perform the initial child read
  through the parent unless `perm` is `.cell` or `place` is zero-sized
  (`placeIsZeroSized localDecls layouts place`, rejecting the read with
  `hasTreeReadUB` when two or more entries exist, then applying
  `freezeTreeBorrowsOnReadAtProj` with protector status, matching Miri's
  `Permission::associated_access` and MiniRust's
  `PermissionUnprot::init_access` over the pointee's byte range), and
  initialize the new tag with Miri's unprotected `NewPermission::new` choice:
  `sharedBorrowPerm` (`.frozen` or `.cell`) for shared reborrows and
  `mutableBorrowPerm` (`.reservedFrz false` or `.reservedIM`) for mutable and
  two-phase reborrows.
  A mutable reborrow through a `.frozen` parent is rejected eagerly; Miri
  instead rejects the first write through the new tag (a child write of the
  `.frozen` ancestor), so Anneal's choice reports undefined behavior no later
  than Miri does.
- Root borrows of a stack local (`.ref borrowKind local` with
  `parentTag := .none`) use the same `NewPermission::new` choice:
  `sharedBorrowPerm` for shared borrows and `mutableBorrowPerm` for mutable and
  two-phase borrows (Miri retags `RetagKind::TwoPhase` like a default retag).
  Direct accesses to the local carry `writerTag = .none` and are foreign to
  every tag.
- Raw pointer creation (`.rawPtr mutability place`) assigns `sharedBorrowPerm
  localDecls layouts place` when `mutability = .not` and `.unique` when
  `mutability = .mut`, inheriting a `.reservedFrz`, `.reservedIM`, or `.cell`
  parent permission for `*const` pointers on `.deref :: restProj`. Miri gives
  raw pointers their parent's tag instead of a new one (`tb_retag_ptr_value`:
  "We don't give new tags to raw pointers."); Anneal's separate raw-pointer tag
  receives the same child and foreign transitions as its parent for accesses
  through itself and through tags outside its subtree, so it can only add
  undefined behavior relative to Miri, never remove it.

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
      match validateLoadedValue layouts localDecls op v with
      | false => .ub
      | true =>
        match op, mem.borrows with
        | .copy { local_ := ptrLoc, projection := .deref :: restProj },
          b₁ :: b₂ :: restBorrows =>
          match
            derefReadTreeUB
              locals
              ptrLoc
              restProj
              (b₁ :: b₂ :: restBorrows)
              mem.activeProtectors
          with
          | true => .ub
          | false =>
            .ok
              v
              locals'
              { mem with
                borrows :=
                  freezeDerefReadBorrowsAt
                    locals
                    ptrLoc
                    restProj
                    (b₁ :: b₂ :: restBorrows)
                    mem.activeProtectors }
        | .move { local_ := ptrLoc, projection := .deref :: restProj },
          b₁ :: b₂ :: restBorrows =>
          match
            derefReadTreeUB
              locals
              ptrLoc
              restProj
              (b₁ :: b₂ :: restBorrows)
              mem.activeProtectors
          with
          | true => .ub
          | false =>
            .ok
              v
              locals'
              { mem with
                borrows :=
                  freezeDerefReadBorrowsAt
                    locals
                    ptrLoc
                    restProj
                    (b₁ :: b₂ :: restBorrows)
                    mem.activeProtectors }
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
          match op with
          | .offset =>
            evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs
          | _ =>
            let isSigned := operandIsSigned localDecls lhsOp layouts
            evalScalarBinOp op lhs rhs locals₂ mem isSigned
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset =>
            evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz offsetSc
          | _ =>
            match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | true =>
              match
                ptrAddressScalar?
                  locals₂
                  mem.borrows
                  mem.callerLocals
                  localDecls
                  layouts
                  (layoutPointerBytes layouts)
                  ptrVal
                  sz
              with
              | .some lhsAddrSc =>
                evalScalarBinOp op lhsAddrSc offsetSc locals₂ mem false
              | .none => .unsupported
            | false => .unsupported
        | .scalar lhsSc, .ptr ptrVal sz =>
          match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
          | true =>
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                (layoutPointerBytes layouts)
                ptrVal
                sz
            with
            | .some rhsAddrSc =>
              evalScalarBinOp op lhsSc rhsAddrSc locals₂ mem false
            | .none => .unsupported
          | false => .unsupported
        | .ptr lhsPtr lhsSz, .ptr rhsPtr rhsSz =>
          match isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
          | true =>
            let ptrBytes := layoutPointerBytes layouts
            match
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                ptrBytes
                lhsPtr
                lhsSz,
              ptrAddressScalar?
                locals₂
                mem.borrows
                mem.callerLocals
                localDecls
                layouts
                ptrBytes
                rhsPtr
                rhsSz
            with
            | .some lhsAddrSc, .some rhsAddrSc =>
              evalScalarBinOp op lhsAddrSc rhsAddrSc locals₂ mem false
            | _, _ => .unsupported
          | false => .unsupported
        | .aggregate lhsVar lhsFields, .aggregate rhsVar rhsFields =>
          evalWidePtrAggregateRelBinOp
            op
            lhsOp
            lhsVar
            lhsFields
            rhsVar
            rhsFields
            locals₂
            mem
            localDecls
            layouts
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
        match
          derefReadTreeUB
            locals
            place.local_
            restProj
            (b₁ :: b₂ :: restBorrows)
            mem.activeProtectors
        with
        | true => .ub
        | false =>
          .ok
            v
            locals'
            { mem with
              borrows :=
                freezeDerefReadBorrowsAt
                  locals
                  place.local_
                  restProj
                  (b₁ :: b₂ :: restBorrows)
                  mem.activeProtectors }
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
      | .mut _ => mutableBorrowPerm localDecls layouts place
    match place.projection with
    | .deref :: restProj =>
      evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts
    | _ =>
      match get? locals place.local_ with
      | .none => .ub
      | .some .dead => .ub
      | .some slot =>
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
          match projHasSubslice resolvedProj with
          | false => .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
          | true =>
            let rootValOpt : Option Value :=
              match slot with
              | .init rv => .some rv
              | _ => .none
            let subOk : Bool :=
              Bool.and
                (validateNonDerefSubslices
                  locals
                  localDecls
                  layouts
                  place.local_
                  slot
                  resolvedProj)
                (checkTargetPlaceAlign
                  localDecls
                  layouts
                  (placeTyResolved localDecls layouts place)
                  entry
                  { allocId := tag, offsetBytes := 0 }
                  rootValOpt)
            match subOk with
            | true => .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
            | false => .ub
  | .rawPtr mutability place =>
    evalRvalueRawPtr locals mutability place mem localDecls layouts
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
    evalCastPtrToPtr locals op targetTy mem localDecls layouts
  | .cast (.pointerCoercion coercionKind) op targetTy =>
    evalReifyFnPointer locals op targetTy mem localDecls layouts coercionKind
  | .cast .fnPtrToPtr op targetTy =>
    evalFnPtrToPtr locals op targetTy mem localDecls layouts
  | .cast .pointerExposeProvenance op targetTy =>
    evalPointerExposeProvenance locals op targetTy mem localDecls layouts
  | .cast .pointerWithExposedProvenance op targetTy =>
    evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts
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
    evalUnaryPtrMetadata locals op mem localDecls layouts
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
  | .aggregate (.adt defPath variantIdx activeField) ops =>
    evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts
  | .aggregate (.closure _) ops =>
    match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls with
    | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.rawPtr pointeeTy _) ops =>
    evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts
  | _ => .unsupported

/--
Alias for `evalRvalue` with explicit `Memory` threading.
-/
abbrev evalRvalueWithMemory := evalRvalue

end Trusted.Rustc.V2026_06_01.MirSemantics
