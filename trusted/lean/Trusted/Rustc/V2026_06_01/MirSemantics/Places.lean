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
  | .transition (.reservedFrz conflicted) => .transition (.reservedFrz conflicted)
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
Test whether a dereferenced write to `dst` through the pointer stored in
`dst.local_` is undefined behavior at a strict ancestor of the writer's tag in
the Tree Borrows hierarchy `borrows` (`treeBorrowAncestorsChildAccessUB
.write`): a write through a reborrow is a child write for every ancestor, so a
`.frozen` or `.disabled` ancestor makes it undefined behavior even when the
writer's own permission allows the write.

The writer's own permission is checked by `writePlaceValue` and protector
conflicts by `evalPlaceWrite`. With fewer than two borrow entries the writer
has no ancestor in `borrows`, so the test is `false`, mirroring the borrow-list
cases of `invalidateDerefWriteBorrows`.

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
Resolve dynamic `.index idxLocal` projection elements against the current
`locals` state at borrow creation time, converting each `.index idxLocal`
whose index local holds an initialized `.scalar sc` into
`.constantIndex sc.bits 0 false` so subsequent dereferences do not depend on
whether the temporary index local remains live.

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
Determine whether a monomorphized `RigidTy` is `Freeze` (contains no
`UnsafeCell` interior mutability or raw pointer), using structural recursion
with `fuel`.

Returns `true` (`Freeze`) unconditionally for `core::marker::PhantomData` /
`std::marker::PhantomData` (`unsafe impl<T: ?Sized> Freeze for PhantomData<T>`);
returns `false` (`!Freeze`) for `.rawPtr`, for standard interior-mutable cells
(`core::cell::UnsafeCell`, `std::cell::UnsafeCell`,
`core::cell::SyncUnsafeCell`, `std::cell::SyncUnsafeCell`, `core::cell::Cell`,
`std::cell::Cell`, `core::cell::RefCell`, `std::cell::RefCell`), and for any
other `.adt`, `.tuple`, `.array`, or `.slice` whose type arguments or element
types contain a `!Freeze` component; returns `true` (`Freeze`) otherwise.
Modeling choice: Because `RigidTy.adt` carries generic `args` rather than full
field declarations, `rigidTyIsFreeze` explicitly recognizes `PhantomData` as
`Freeze` and `UnsafeCell` / `SyncUnsafeCell` / `Cell` / `RefCell` as `!Freeze`,
recurses structurally on `args` for other ADTs, and classifies `.rawPtr` as
`!Freeze` so custom interior-mutable wrappers conservatively receive `.cell`
(shared) or `.reservedIM` (mutable).

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
size (`!`, `()`, nested zero-sized tuples, zero-length arrays `[T; 0]`, arrays
of zero-sized elements, `fn` item types, non-capturing or zero-sized-capturing
closures, `core::marker::PhantomData` / `std::marker::PhantomData`, or standard
single-field transparent/same-size wrappers `UnsafeCell<T>`,
`SyncUnsafeCell<T>`, `Cell<T>`, `ManuallyDrop<T>`, and `MaybeUninit<T>` around a
zero-sized `T`) in `Runtime(PostCleanup)` MIR on a 64-bit target (`rustc
1.98.0-nightly (14210df0e 2026-05-31)`), using bounded recursion with `fuel`.

Modeling choice vs. stable Rust Reference: For general user-defined
`RigidTy.adt` types, byte size is stored in `LayoutTable` (`Ty.layoutIdx`)
rather than on `RigidTy` itself, so `rigidTyIsZeroSized` recognizes
`PhantomData<T>` and standard transparent/same-size wrappers (`UnsafeCell<T>`,
`SyncUnsafeCell<T>`, `Cell<T>`, `ManuallyDrop<T>`, `MaybeUninit<T>`) directly
and conservatively returns `false` on other `RigidTy.adt` constructors. During
reference reborrows (`evalRvalue` `.ref`) and retagging (`evalFnEntryRetag`,
`evalNonFnEntryRetag`, and `evalStmt` `.retag`), a zero-sized pointee covers an
empty `[offset, offset + 0)` byte range, so Miri and MiniRust perform zero
initial read accesses and accept non-null provenance-free dangling references
without allocating a tag.

Reference (The Rust Reference, "Type Layout", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."

Reference (MiniRust `spec/mem/tree_borrows/memory.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/memory.md#L81-L86>
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/memory.md#L116-L123>

> "let Some((alloc_id, parent_path)) = ptr.provenance else {
>     assert!(pointee_size.is_zero());
>     // Pointers without provenance cannot access any memory, so giving them a new
>     // tag makes no sense.
>     return ret(ptr);
> };"
>
> "// Perform a read access on all bytes inside the pointee whose permission requires such an access.
> for (idx, perm) in settings.inside.iter().enumerate() {
>     let idx = Int::from(idx); // FIXME: we need a version of `enumerate` that yields `Int`s.
>     let idx = Size::from_bytes(idx).unwrap();
>     if let Some(access) = perm.init_access() {
>         allocation.extra.root.access(Some(child_path), access, offset+idx, Offset::from_bytes_const(1))?
>     }
> }"
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

Reference (The Rust Reference, "Type Layout", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
@[reducible]
def tyIsZeroSized (ty : Ty) : Bool :=
  rigidTyIsZeroSized 16 ty.kind

/--
Determine whether `place`'s resolved type in `localDecls` and `layouts` is
statically zero-sized (`tyIsZeroSized`), defaulting to `false` when `localDecls`
is omitted or does not determine a type for `place`.

Reference (The Rust Reference, "Type Layout", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
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
(`!`, tuples containing an uninhabited element, non-empty arrays `[T; n + 1]`
of an uninhabited element, closures capturing an uninhabited upvar,
`core::convert::Infallible` / `std::convert::Infallible`, or `#[repr(transparent)]`
single-field wrappers `UnsafeCell<T>`, `SyncUnsafeCell<T>`, `Cell<T>`, and
`ManuallyDrop<T>` around an uninhabited `T`) in `Runtime(PostCleanup)` MIR
(`rustc 1.98.0-nightly (14210df0e 2026-05-31)`), using bounded recursion with
`fuel`.

Zero-length arrays `[T; 0]`, `core::marker::PhantomData<T>` /
`std::marker::PhantomData<T>`, and `core::mem::MaybeUninit<T>` /
`std::mem::MaybeUninit<T>` are inhabited (`[]`, `PhantomData`, and
`MaybeUninit::uninit()`) even when `T` is uninhabited (`[!; 0]`,
`PhantomData<!>`, `MaybeUninit<!>`).

Modeling choice vs. stable Rust Reference: For general user-defined
`RigidTy.adt` types, uninhabitedness (`TypeLayout.isUninhabited` /
`VariantsShape.empty`) is stored in `LayoutTable` (`Ty.layoutIdx`) rather than
on `RigidTy` itself, so `rigidTyIsUninhabited` recognizes
`core::convert::Infallible` / `std::convert::Infallible` and transparent
wrappers (`UnsafeCell<T>`, `SyncUnsafeCell<T>`, `Cell<T>`, `ManuallyDrop<T>`)
directly and conservatively returns `false` on other `RigidTy.adt` constructors
(`tyIsUninhabited` additionally consults `LayoutTable.lookup`). During MIR
reference retagging (`evalFnEntryRetag`, `evalNonFnEntryRetag`, and `evalStmt`
`.retag`), producing or retagging a reference `&T` or `&mut T` whose pointee
`T` is uninhabited (`rigidTyIsUninhabited 16 pointee = true`) is immediate
undefined behavior even when `T` has zero byte size (`&!`, `&[!; 1]`,
`&(!, ())`, `&UnsafeCell<!>`).

Reference (The Rust Reference, "Never type", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of
> computations that never complete."

Reference (The Rust Reference, "Behavior considered undefined", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."
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
                (stringEq defPath "core::mem::ManuallyDrop")
                (stringEq defPath "std::mem::ManuallyDrop")))),
        args
      with
      | true, inner :: .nil => rigidTyIsUninhabited fuel inner
      | _, _ => false
  | .succ _, _ => false

/--
Determine whether a `Ty` is uninhabited either structurally
(`rigidTyIsUninhabited 16 ty.kind`) or via its compiler-captured
`TypeLayout.isUninhabited` flag in `layouts`.

Reference (The Rust Reference, "Never type", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of
> computations that never complete."
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

Reference (The Rust Reference, "Never type", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The never type ! is a type with no values, representing the result of
> computations that never complete."
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

When `placeTy localDecls layouts place` resolves to a `!Freeze` type (such as
`core::cell::UnsafeCell<T>`), a shared borrow starts in `TreeBorrowPerm.cell`
instead of `TreeBorrowPerm.frozen` so interior mutation through
`&UnsafeCell<T>` is permitted; when `place` is `Freeze` (or when `localDecls`
is omitted / does not declare a type for `place`), the shared borrow defaults
to `TreeBorrowPerm.frozen`. This is Miri's `NewPermission::new` choice for
shared references at the granularity of the whole place; Miri additionally
distinguishes `UnsafeCell` bytes from frozen bytes within one type, which
Anneal approximates by the place's overall `Freeze`-ness.

Reference (The Rust Reference, "Interior mutability"):
<https://doc.rust-lang.org/1.98.0/reference/interior-mutability.html>

> "Shared references in Rust disallow mutation by default, and &mut is called an
> exclusive reference. However, there are situations where it would be helpful
> to mutate data behind a shared reference. This is known as interior mutability
> in Rust, in contrast with exterior mutability, which happens through &mut or
> directly on a value."

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L172-L179>

> "match ref_mutability {
>     // Shared references
>     Some(Mutability::Not) =>
>         if frozen {
>             Permission::new_frozen()
>         } else {
>             Permission::new_cell()
>         },"
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

Miri retags two-phase borrows (`RetagKind::TwoPhase`) with the same permission
as ordinary references; only function-entry retags are protected, and those
always receive `ReservedFrz` (see `fnEntryRetagPerm`).

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L180-L192>

> "// Mutable references
> Some(Mutability::Mut) => {
>     if implicit_writes_enabled && !matches!(part, Outside) {
>         // We cannot use `Unique` for the outside part.
>         Permission::new_unique()
>     } else if is_protected || frozen {
>         // We also use this for protected `&mut UnsafeCell` as otherwise adding
>         // `noalias` would not be sound.
>         Permission::new_reserved_frz()
>     } else {
>         Permission::new_reserved_im()
>     }
> }"
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
`mutability` to a pointee of kind `pointee`: shared references receive
`.frozen` (for `Freeze` pointees) or `.cell`, and mutable references always
receive `.reservedFrz false`, independently of interior mutability, so that no
protected `.reservedIM` is ever created.

Modeling choice: Anneal does not model Miri's optional
`-Zmiri-tree-borrows-implicit-writes` flag (off by default), under which
protected mutable references would start as `Unique`.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L139-L192>

> "let is_protected = mode == RetagMode::FnEntry;"
> ...
> "} else if is_protected || frozen {
>     // We also use this for protected `&mut UnsafeCell` as otherwise adding
>     // `noalias` would not be sound.
>     Permission::new_reserved_frz()"

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L279>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,"
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
`mutability` to a pointee of kind `pointee`:
- `.fnEntry` delegates to `fnEntryRetagPerm` (protected mutable references
  always receive `.reservedFrz false` so no protected `.reservedIM` exists);
- `.default`, `.twoPhase`, and `.raw` select `.frozen` / `.cell` on shared
  references and `.reservedFrz false` / `.reservedIM` on mutable references
  according to `rigidTyIsFreeze 16 pointee`, matching Miri's unprotected
  `NewPermission::new` selection.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L139-L192>

> "let is_protected = mode == RetagMode::FnEntry;"
> ...
> "} else if is_protected || frozen {
>     // We also use this for protected `&mut UnsafeCell` as otherwise adding
>     // `noalias` would not be sound.
>     Permission::new_reserved_frz()
> } else {
>     Permission::new_reserved_im()
> }"
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
  | .use op =>
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
    | .ok v locals' =>
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
  | .copyForDeref place =>
    match evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals with
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
    match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
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
      match get? locals place.local_ with
      | .some (.init (.ptr parentPtr _)) =>
        match lookupBorrow mem.borrows parentPtr.tag with
        | .some parentEntry =>
          match parentEntry.perm, borrowKind with
          | .disabled, _ => .ub
          | .frozen, .mut _ => .ub
          | _, _ =>
            match resolveBorrowProjectionElems locals restProj with
            | .none => .ub
            | .some resolvedRest =>
              let tag := mem.nextTag
              let fullProj :=
                match parentEntry.targetProjection with
                | .nil => resolvedRest
                | ph :: pt => ph :: appendProjections pt resolvedRest
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
                .ok (.ptr { allocId := tag, offsetBytes := 0 } 8) locals mem'
        | .none => .ub
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
      | .mut => TreeBorrowPerm.unique
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
            match resolveBorrowProjectionElems locals restProj with
            | .none => .ub
            | .some resolvedRest =>
              let tag := mem.nextTag
              let fullProj :=
                match parentEntry.targetProjection with
                | .nil => resolvedRest
                | ph :: pt => ph :: appendProjections pt resolvedRest
              let rawPerm :=
                match mutability, parentEntry.perm with
                | .not, .reservedFrz conflicted =>
                  TreeBorrowPerm.reservedFrz conflicted
                | .not, .reservedIM => TreeBorrowPerm.reservedIM
                | .not, .cell => TreeBorrowPerm.cell
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
        | .none => .ub
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
