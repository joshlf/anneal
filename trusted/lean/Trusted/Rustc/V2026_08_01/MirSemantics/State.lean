import Trusted.Refinement
import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Trusted.Rustc.V2026_08_01.MirAst.Statements
import Trusted.Rustc.V2026_08_01.MirAst.Terminators
import Trusted.Rustc.V2026_08_01.MirAst.Body

namespace Trusted.Rustc.V2026_08_01.MirSemantics

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst

/-!
Operational state, runtime values, stack frames, Tree Borrows permissions, open
MIR interaction-tree effect signatures (`MirEffect`), and evaluation result
types for `Runtime(PostCleanup)` MIR at
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#88`, `#99`, `#100`, `#102`).

Every syntactically valid `CapturedMir` construct exists in `MirAst`. Any
construct whose operational transition is not yet modeled emits a fault node
`MirStepNode.unsupported` (`.vis (.inl .unsupported) PEmpty.elim`). Because
`FaultEffect.isFault` holds on `MirFailE`, `TreeSafe` is provably `False` along
any execution path that reaches an unmodeled construct (`R-RESULT-01`).

External or unresolved `TerminatorKind.call` and `TerminatorKind.tailCall`
targets (those without an inline `CapturedMir` body in `Memory.callees`) emit
an interaction request in `MirCallE` carrying `(defPath, args, memory)` and
receiving a `MirCallAns` carrying both the return outcome and the post-call
`Memory`. Consequently, unresolved external calls are impure, potentially
nondeterministic across identical invocations, and memory-effecting by default.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/

/--
Observable event emitted by a single MIR transition step.
-/
inductive MirObs : Type where
  /-- Internal step with no external I/O or leakage observation. -/
  | silent : MirObs
  /-- Branch or memory-address event carrying cost or leakage tag `tag`. -/
  | event (tag : Nat) : MirObs

/--
Runtime value held in a MIR local variable or returned from a function.
-/
inductive Value : Type where
  /-- Zero-sized value (`()`, `FnDef`, etc.). -/
  | unit : Value
  /-- Concrete integer, boolean, or character bit pattern (`ScalarInt`). -/
  | scalar (val : ScalarInt) : Value
  /-- Pointer with allocation provenance (`ProvenancePtr`). -/
  | ptr (ptr : ProvenancePtr) (sizeBytes : Nat) : Value
  /-- Composite value (tuple, struct, array, or enum variant `variantIdx`). -/
  | aggregate (variantIdx : VariantIdx) (fields : List Value) : Value

/--
Storage state of a single MIR local variable (`_0`..`_{n-1}`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "At any point during the execution of a function, each local is either
> allocated or unallocated. Except as noted below, all locals except function
> parameters are initially unallocated. `StorageLive` statements cause memory
> to be allocated for the local while `StorageDead` statements cause the memory
> to be freed. ... Using a local in any way (not only reading/writing from it)
> while it is unallocated is UB."
-/
inductive LocalSlot : Type where
  /-- Storage for this local is currently dead (`StorageDead`). -/
  | dead : LocalSlot
  /-- Storage is live (`StorageLive`) and uninitialized (`Deinit`). -/
  | uninit : LocalSlot
  /-- Storage is live and holds initialized value `val`. -/
  | init (val : Value) : LocalSlot

/--
Execution frame for the active `CapturedMir` body.
-/
structure StackFrame : Type where
  /-- Index of the active basic block (`bb0` is `0`). -/
  blockIdx : BasicBlockIdx
  /-- 0-based index of the next statement to execute within `blockIdx`; when
      `stmtIdx == statements.length`, the block's `terminator` executes next. -/
  stmtIdx : Nat
  /-- Storage slots for all locals (`_0`..`_{n-1}`). -/
  locals : List LocalSlot

/--
Tree Borrows permission state for a reference or raw-pointer provenance tag.

The six constructors are exactly the six activation states of Miri's Tree
Borrows `PermissionPriv` (and MiniRust's `PermissionUnprot`), so a tag's state
here is in one-to-one correspondence with Miri's per-location permission:
- `.cell` (`Cell`) is a shared reference to interior-mutable data
  (`&UnsafeCell<T>`). It is isolated: every child or foreign read or write
  leaves it `.cell`, and no access through it is undefined behavior.
- `.reservedFrz conflicted` (`ReservedFrz { conflicted }`) is a mutable
  reference that has not been written through yet, created for `Freeze`
  pointees and for every function-entry-protected mutable reference. A
  foreign read while protected sets `conflicted := true`; a child write while
  protected and conflicted is undefined behavior; any other child write
  activates it to `.unique`; a foreign write disables it.
- `.reservedIM` (`ReservedIM`) is a mutable reference that has not been
  written through yet, created for unprotected `!Freeze` pointees. Unlike
  `.reservedFrz`, it tolerates foreign writes; a child write activates it to
  `.unique`. Miri never creates it under a protector.
- `.unique` (`Unique`, formerly called `Active`) is an activated mutable
  reference. A foreign read freezes it (or disables it while protected, which
  is undefined behavior); a foreign write disables it.
- `.frozen` (`Frozen`) permits reads and rejects child writes as undefined
  behavior; a foreign write disables it.
- `.disabled` (`Disabled`) rejects every child access as undefined behavior.

`.cell` and `.reservedIM` are distinct states even though both tolerate
foreign writes: `.reservedIM` becomes `.unique` on its first child write and
then follows `.unique → .frozen → .disabled`, whereas `.cell` never changes.
Encoding `.cell` as `.frozen` plus an interior-mutability flag would conflate
these behaviors.

Modeling choice vs. stable Rust Reference: The stable Rust Reference specifies
that breaking pointer aliasing rules or mutating immutable bytes is undefined
behavior, but does not mandate a single operational aliasing automaton. Anneal
models pointer aliasing operationally using Tree Borrows (Villani et al., PLDI
2025), matching Miri's `-Zmiri-tree-borrows` implementation (`perms.rs`,
`tree.rs`) and MiniRust's `spec/mem/tree_borrows/` state machine. The transition
function over these states is `treeBorrowPermTransition` in `Places.lean`.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L10-L53>

> "enum PermissionPriv {
>     /// represents: a shared reference to interior mutable data.
>     /// allows: all foreign and child accesses;
>     /// rejects: nothing
>     Cell,
>     /// represents: a local mutable reference that has not yet been written to;
>     /// allows: child reads, foreign reads;
>     /// affected by: child writes (becomes Unique),
>     /// rejects: foreign writes (Disabled).
>     ///
>     /// `ReservedFrz` is mostly for types that are `Freeze` (no interior mutability).
>     /// If the type has interior mutability, see `ReservedIM` instead.
>     /// (Note: since the discovery of `tests/fail/tree_borrows/reservedim_spurious_write.rs`,
>     /// we also use `ReservedFreeze` for mutable references that were retagged with a protector
>     /// independently of interior mutability)
>     ///
>     /// special case: behaves differently when protected, which is where `conflicted`
>     /// is relevant
>     /// - `conflicted` is set on foreign reads,
>     /// - `conflicted` must not be set on child writes (there is UB otherwise).
>     ...
>     ReservedFrz { conflicted: bool },
>     /// Alternative version of `ReservedFrz` made for types with interior mutability.
>     /// allows: child reads, foreign reads, foreign writes (extra);
>     /// affected by: child writes (becomes Unique);
>     /// rejects: nothing.
>     ReservedIM,
>     /// represents: a unique pointer;
>     /// allows: child reads, child writes;
>     /// rejects: foreign reads (Frozen), foreign writes (Disabled).
>     Unique,
>     /// represents: a shared pointer;
>     /// allows: all read accesses;
>     /// rejects child writes (UB), foreign writes (Disabled).
>     Frozen,
>     /// represents: a dead pointer;
>     /// allows: all foreign accesses;
>     /// rejects: all child accesses (UB).
>     Disabled,
> }"

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
>
> "- Mutating immutable bytes."

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value. When a
> shared reference to a value is created, it prevents direct mutation of the
> value."
>
> "Mutable references point to memory which is owned by some other value."

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/state_machine_unprotected.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/state_machine_unprotected.md#L5-L19>

> "enum PermissionUnprot {
>     /// Represents a shared reference to interior mutable data.
>     Cell,
>     /// Represents a two-phase borrow during its reservation phase
>     Reserved,
>     /// Represents a interior mutable two-phase borrow during its reservation phase
>     ReservedIm,
>     /// Represents an activated (written to) mutable reference, i.e. it must actually be unique right now
>     Unique,
>     /// Represents a shared (immutable) reference
>     Frozen,
>     /// Represents a dead reference
>     Disabled,
> }"

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
inductive TreeBorrowPerm : Type where
  /-- Shared reference to interior-mutable data; isolated (`Cell`). -/
  | cell : TreeBorrowPerm
  /-- Unwritten mutable reference for `Freeze` or protected pointees, with the
      protector-conflict latch `conflicted` (`ReservedFrz { conflicted }`). -/
  | reservedFrz (conflicted : Bool) : TreeBorrowPerm
  /-- Unwritten, unprotected mutable reference to `!Freeze` data
      (`ReservedIM`). -/
  | reservedIM : TreeBorrowPerm
  /-- Activated (written-through) mutable reference (`Unique`). -/
  | unique : TreeBorrowPerm
  /-- Shared or immutable borrow with read-only permission (`Frozen`). -/
  | frozen : TreeBorrowPerm
  /-- Invalidated borrow tag; any child access is undefined behavior
      (`Disabled`). -/
  | disabled : TreeBorrowPerm

/--
Legacy name for `TreeBorrowPerm.unique`, retained so that earlier proofs and
specifications that mention an activated borrow as `.active` keep their
meaning. It is a pattern-matchable abbreviation, not a seventh state.
-/
@[match_pattern, reducible]
def TreeBorrowPerm.active : TreeBorrowPerm := .unique

/--
Legacy name for the unconflicted `Freeze` reservation
`TreeBorrowPerm.reservedFrz false`, retained so that earlier proofs and
specifications that mention a fresh mutable reborrow as `.reserved` keep their
meaning. It is a pattern-matchable abbreviation, not a seventh state.
-/
@[match_pattern, reducible]
def TreeBorrowPerm.reserved : TreeBorrowPerm := .reservedFrz false

/--
Compute the initial `TreeBorrowPerm` for a function-entry protected reborrow
(`RetagKind.fnEntry`).

When `isMutable == true`, the protected reborrow starts in `.active` permission
when implicit function-entry writes are enabled (`implicitWrites == true`,
activating the mutable reference at function entry and performing an initial
child write against foreign aliases) and in `.reserved` permission when
`implicitWrites == false` (two-phase or deferred-write mode). When
`isMutable == false`, a shared borrow of a `Freeze` type (`isFreeze == true`)
starts `.frozen`, whereas a shared borrow of a non-`Freeze` (`UnsafeCell`-bearing)
type (`isFreeze == false`) starts `.reserved` so interior-mutable accesses remain
permitted.

Reference (The Rust Reference, "Mutable references (`&mut T`)"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html#mutable-references-mut>

> "Mutable references point to memory which is owned by some other value. A
> mutable reference type is written &mut type or &'a mut type."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
>
> "- Mutating immutable bytes."
-/
def initProtectedReborrowPerm
    (isMutable : Bool)
    (isFreeze : Bool)
    (implicitWrites : Bool := true) :
    TreeBorrowPerm :=
  match isMutable with
  | true =>
    match implicitWrites with
    | true => .active
    | false => .reserved
  | false =>
    match isFreeze with
    | true => .frozen
    | false => .reserved

/--
Return `true` when an initial `TreeBorrowPerm` assigned to a function-entry
protected reborrow performs an immediate implicit child write upon creation
(`.active` permission), and `false` otherwise (`.reserved`, `.frozen`, or
`.disabled`).

Reference (The Rust Reference, "Mutable references (`&mut T`)"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html#mutable-references-mut>

> "Mutable references point to memory which is owned by some other value. A
> mutable reference type is written &mut type or &'a mut type."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
>
> "- Mutating immutable bytes."
-/
def protectedReborrowHasInitWrite : TreeBorrowPerm → Bool
  | .active => true
  | _ => false

/--
0-based local variable index alias for borrow-table target references.
-/
abbrev LocalIdx : Type := Local

/--
Borrow-table entry associating a pointer provenance `tag` with its target stack
local, sub-place projection path, optional explicit byte sub-range
`[rangeOffset, rangeOffset + rangeLen)`, `TreeBorrowPerm` permission, optional
function-entry lifetime protector identifier (`RetagKind.fnEntry`), and
optional parent provenance tag (`parentTag`) in the Tree Borrows reborrow
hierarchy.

When `rangeLen == 0`, overlap with writes is governed structurally by
`targetProjection`; when `rangeLen > 0`, overlap with byte-ranged writes is
governed by the half-open interval `[rangeOffset, rangeOffset + rangeLen)`.
When `parentTag == .some pTag`, `tag` was created by reborrowing through a
dereference of `pTag`, so accesses through `tag` (or its descendants) are child
(`NodeRelation::Local`) accesses relative to `pTag` and its ancestors, whereas
accesses through any tag outside `pTag`'s subtree are `NodeRelation::Foreign`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1166-L1171>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L287>

> "A `Deref` projection begins by loading a value from the parent place, as if
> by [`Operand::Copy`]. It then dereferences the resulting pointer, creating a
> place of the pointee's type. The resulting address is the address that was
> stored in the pointer."
>
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

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and MiniRust
`spec/mem/tree_borrows/tree.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs>
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/tree.md#L3-L55>

> "The core data structure of Tree Borrows is a *tree*, with a state machine in
> each node. We use a tree to track reborrows in each allocation; each reborrow
> adds a new node to the tree."
>
> "When a node is accessed, each node in the tree can be divided into two
> disjoint sets: *local nodes* and *foreign nodes*, based on its relative
> position to the accessed node. The *local* set includes the node itself and
> all its descendants, while the *foreign* set contains all other nodes."

Reference (Neven Villani, Johannes Hostert, Ralf Jung, and Derek Dreyer,
"Tree Borrows", Proc. ACM Program. Lang. 9, PLDI, Article 182, June 2025):
<https://doi.org/10.1145/3729338>
-/
structure BorrowEntry : Type where
  /-- Unique provenance tag allocated by `Rvalue.ref` or `Rvalue.rawPtr`. -/
  tag : Nat
  /-- Root local variable in the stack frame referenced by this borrow. -/
  targetLocal : LocalIdx
  /-- Projection path within `targetLocal` at which the borrow was taken. -/
  targetProjection : List ProjectionElem
  /-- Current Tree Borrows access permission for `tag`. -/
  perm : TreeBorrowPerm
  /-- Starting byte offset within `targetLocal` when `rangeLen > 0`. -/
  rangeOffset : Nat := 0
  /-- Byte length of the borrowed sub-range (`0` means governed by
      `targetProjection`; `> 0` means `[rangeOffset, rangeOffset + rangeLen)`). -/
  rangeLen : Nat := 0
  /-- Optional function-entry lifetime protector identifier (`RetagKind.fnEntry`). -/
  protector : Option Nat := .none
  /-- Optional parent provenance tag in the Tree Borrows hierarchy (`some pTag`
      when reborrowed from a dereferenced pointer with provenance `pTag`; `none`
      for root borrows of a stack local). -/
  parentTag : Option Nat := .none
  /-- Depth of the stack frame owning `targetLocal`: `0` is the root frame and
      `length Memory.callStack` is the active frame, so the pair
      `(targetFrameDepth, targetLocal)` identifies the borrowed local uniquely
      across every inline call frame (a callee's `_1` and its caller's `_1` are
      distinct allocations). Root borrows (`Rvalue.ref` / `Rvalue.rawPtr` of a
      local) record the active frame's depth; reborrows and retags inherit their
      parent's depth.

      Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
      `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
      <https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

      > "At any point during the execution of a function, each local is either
      > allocated or unallocated." -/
  targetFrameDepth : Nat := 0
  /-- `true` once the allocation backing `targetLocal` has been deallocated
      (`StorageDead`, the implicit free of a repeated `StorageLive`, or the
      returning frame's teardown at `TerminatorKind.return_`). Distinguishes a
      dangling tag of a freed allocation from a tag whose Tree Borrows `perm`
      was `.disabled` by a foreign write while its allocation stays live: only
      the former loses the allocation's byte bounds for `BinOp.Offset`.

      Reference (MiniRust `spec/lang/step/statements.md` at commit
      `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
      <https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/statements.md#L166-L169>

      > "fn storage_live(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
      >     // First remove the old storage, if any.
      >     // This means the same address may be re-used for the new stoage.
      >     self.storage_dead(mem, local)?;" -/
  allocDead : Bool := false

/--
Saved caller activation record pushed onto `Memory.callStack` when executing a
`TerminatorKind.call` and popped by `TerminatorKind.return_` or stack unwinding
(`applyUnwindAction` on `.continue_` / `TerminatorKind.unwindResume`).

Snapshots the caller's active lifetime protectors so that protectors activated
via `RetagKind.fnEntry` during the callee frame are deactivated upon
`TerminatorKind.return_` or unwind, records `returnUnwind : UnwindAction` to
dispatch when the callee unwinds into this caller frame, and records
`isDiverging : Bool` (`true` when `target = .none`) so returning normally from a
diverging call faults with `MirStepNode.fail .ub`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L853>

> "/// Returns from the function.
> ///
> /// Like function calls, the exact semantics of returns in Rust are unclear.
> /// Returning very likely at least assigns the value currently in the return
> /// place (`_0`) to the place specified in the associated `Call` terminator
> /// in the calling function, as if assigned via `dest = move _0`.
> Return,
> ...
> Call {
>     func: Operand<'tcx>,
>     args: Box<[Spanned<Operand<'tcx>>]>,
>     destination: Place<'tcx>,
>     target: Option<BasicBlock>,
>     unwind: UnwindAction,
>     call_source: CallSource,
>     fn_span: Span,
> },"
-/
structure SavedCallerFrame : Type where
  /-- Caller `CapturedMir` body to restore on `TerminatorKind.return_` or unwind. -/
  callerBody : CapturedMir
  /-- Caller `StackFrame` after evaluating the call's argument operands. -/
  frame : StackFrame
  /-- Caller destination `Place` receiving the callee's `_0` return value. -/
  destination : Place
  /-- Caller basic block index jumped to after writing `destination` when
      `isDiverging == false`. -/
  returnTarget : BasicBlockIdx := 0
  /-- Optional caller lifetime protector identifier preserved across the call. -/
  callerProtector : Option Nat := .none
  /-- Snapshot of active lifetime protectors prior to entering the callee frame,
      restored on `TerminatorKind.return_` or unwind. -/
  calleeProtectors : List Nat := .nil
  /-- Unwind action to apply in the caller frame when the callee unwinds. -/
  returnUnwind : UnwindAction := .continue_
  /-- True when pushed by a diverging call (`target = .none`), where returning
      normally via `TerminatorKind.return_` is undefined behavior. -/
  isDiverging : Bool := false

/--
Reified function-pointer table entry in `Memory.fnPtrs`, modeling
`rustc_middle::mir::interpret::GlobalAlloc::Function` for a function item
coerced to a function pointer via `CastKind.pointerCoercion "ReifyFnPointer"`.

Records the synthetic allocation identifier `allocId` (`ProvenancePtr.allocId`
at byte offset `0`), the target function's canonical `defPath` and monomorphized
`typeArgs` (`RigidTy.fnDef defPath typeArgs`), and the optional reified function
pointer signature `fnSig` (`RigidTy.fnPtr inputs output safety abi`).

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "pub enum GlobalAlloc<'tcx> {
>     /// The alloc ID is used as a function pointer.
>     Function {
>         instance: ty::Instance<'tcx>,
>     },"

Reference (The Rust Reference, "Function pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-pointer.html>

> "Function pointer types, written using the `fn` keyword, refer to a function
> whose identity is not necessarily known at compile-time. They can be created
> via a coercion from both function items and non-capturing closures."
-/
structure FnPtrEntry : Type where
  /-- Synthetic allocation identifier (`ProvenancePtr.allocId`) for this function pointer. -/
  allocId : AllocId
  /-- Canonical `DefPath` of the target function item (`RigidTy.fnDef`). -/
  defPath : DefPath
  /-- Monomorphized generic type arguments of the function item (`RigidTy.fnDef`). -/
  typeArgs : List RigidTy := .nil
  /-- Optional function-pointer signature (`RigidTy.fnPtr inputs output safety abi`). -/
  fnSig : Option RigidTy := .none

/--
Abstract heap, global allocation, Tree Borrows tag table, active function-entry
lifetime protectors, interprocedural call stack, and reified function-pointer
table store.
-/
structure Memory : Type where
  /-- Next fresh allocation identifier. -/
  nextAllocId : AllocId := 0
  /-- Captured global allocations. -/
  globals : List CapturedAllocation := .nil
  /-- Active Tree Borrows entries for references and raw pointers. -/
  borrows : List BorrowEntry := .nil
  /-- Next fresh provenance tag for reference or raw-pointer creation. -/
  nextTag : Nat := 1
  /-- Captured callee MIR bodies available for inline `TerminatorKind.call`
      resolution; calls to targets absent from `callees` emit `MirCallE`
      interactions. -/
  callees : List CapturedMir := .nil
  /-- Registered trait implementations for polymorphic method resolution. -/
  traitImpls : List TraitImplEntry := .nil
  /-- Stack of suspended caller frames awaiting `TerminatorKind.return_`. -/
  callStack : List SavedCallerFrame := .nil
  /-- Active callee MIR body, or `.none` when executing the root body. -/
  activeCallee : Option CapturedMir := .none
  /-- Active function-entry lifetime protector identifiers (`RetagKind.fnEntry`). -/
  activeProtectors : List Nat := .nil
  /-- Next fresh function-entry lifetime protector identifier. -/
  nextProtector : Nat := 1
  /-- Caller-owned referent slots backing incoming reference (`&T`, `&mut T`) and
      raw-pointer (`*const T`, `*mut T`) arguments to a root function frame when
      `callStack` is empty (addressed at `targetLocal >= locals.length`).

      Reference (The Rust Reference, "Pointer types"):
      <https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

      > "Shared references point to memory which is owned by some other value."
      > "Mutable references point to memory which is owned by some other value." -/
  callerLocals : List LocalSlot := .nil
  /-- Reified function-pointer allocation table (`GlobalAlloc::Function`),
      mapping synthetic `AllocId`s (`>= fnPtrAllocBase`) to target function
      identities and signatures (`FnPtrEntry`).

      Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
      `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
      <https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

      > "/// The alloc ID is used as a function pointer.
      > Function {
      >     instance: ty::Instance<'tcx>,
      > }," -/
  fnPtrs : List FnPtrEntry := .nil
  /-- Allocation IDs whose provenance has been exposed via
      `CastKind.pointerExposeProvenance` (`ptr.expose_provenance()` / `ptr as usize`),
      allowing `CastKind.pointerWithExposedProvenance` (`ptr::with_exposed_provenance`
      / `usize as *const T`) to recover tracked provenance (`Value.ptr`).

      Reference (MiniRust `spec/mem/intptrcast.md`):
      `IntPtrCast::expose` inserts `provenance` into `exposed`, and `IntPtrCast::int2ptr`
      predicts exposed provenance when available or `None` otherwise. -/
  exposedAllocIds : List Nat := .nil
  /-- Root unwind ceiling (`DIV-LM-TAILCALL-NOUNWIND-UNWIND` at the modular root).

      Modeled property and scope (`Runtime` MIR at `rustc` commit
      `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `-C panic=unwind`): whether an
      unwind that escapes the root activation (`callStack = .nil`) may propagate
      into the unmodeled caller of the root function. `true` (the default, and
      the value in every initial state) keeps the modular-root convention
      `MirReturn.panic`; `enterTailCalleeFrame` clears it when the root
      activation is replaced, via `TerminatorKind.tailCall`, by a callee whose ABI
      cannot unwind (`CapturedMir.fnAbi.canUnwind = false`), after which
      `unwindFromCallStack .nil` faults with `.faulted .ub`. No transition sets
      it back to `true`, and the external-call continuations
      (`resumeExternalCall`, `resumeExternalDivergingCall`,
      `resumeExternalTailCallWithAbi`) restore the pre-call value because the
      answer memory of an external callee is not constrained on this field.

      Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
      <https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

      > "Calling a function with the wrong call ABI, or unwinding past a stack
      > frame that does not allow unwinding (e.g. by calling a "C-unwind"
      > function imported or transmuted as a "C" function or function pointer)."

      Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
      `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
      <https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L826-L835>

      > "/// Semantically tail calls consists of two actions:
      > /// - pop of the current stack frame
      > /// - a call to the `func`, with the return address of the **current** caller
      > ///   - so that a `return` inside `func` returns to the caller of the caller
      > ///     of the function that is currently being executed
      > ///
      > /// Note that in difference with [`Call`] this is missing
      > /// - `destination` (because it's always the return place)
      > /// - `target` (because it's always taken from the current stack frame)
      > /// - `unwind` (because it's always taken from the current stack frame)"

      Reference (`compiler/rustc_const_eval/src/interpret/call.rs` at commit
      `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
      <https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_const_eval/src/interpret/call.rs#L391-L399>

      > "if !callee_fn_abi.can_unwind {
      >     // The callee cannot unwind, so force the `Unreachable` unwind handling.
      >     match &mut cont {
      >         ReturnContinuation::Stop { .. } => {}
      >         ReturnContinuation::Goto { unwind, .. } => {
      >             *unwind = mir::UnwindAction::Unreachable;
      >         }
      >     }
      > }"

      Justification: a tail call re-uses the unwind action "taken from the
      current stack frame", and the interpreter replaces that action by
      `Unreachable` whenever the callee's ABI cannot unwind. For the root
      activation that action belongs to the unmodeled caller, so the only
      information the model has is whether some tail callee that replaced the
      root activation could not unwind: in that case every calling context makes
      an escaping unwind "unwinding past a stack frame that does not allow
      unwinding", which the Reference lists as undefined behavior. The
      implication is one-directional: `false` implies that an unwind escaping the
      root is undefined behavior; `true` does not assert that the root's caller
      tolerates unwinding.

      Modeling assumptions and unsupported behavior: the root's caller frame and
      its `UnwindAction` are not represented (modular-root convention); the quoted
      interpreter passage is supplied compiler behavior, not a stable-documentation
      guarantee; an external (out-of-table) tail callee narrows the ceiling only
      through `resumeExternalTailCallWithAbi`. -/
  rootUnwindCeiling : Bool := true

/--
Check whether `allocId` has been recorded in `exposed` via
`CastKind.pointerExposeProvenance`.
-/
@[reducible]
def isExposedAllocId : List Nat → Nat → Bool
  | .nil, _ => false
  | h :: t, allocId =>
    match Nat.beq h allocId with
    | true => true
    | false => isExposedAllocId t allocId

/--
Record `allocId` in `exposed` (deduplicating and ignoring `allocId = 0`, which
represents synthetic provenance-less addresses rather than a real allocation).
-/
@[reducible]
def recordExposedAllocId (exposed : List Nat) (allocId : Nat) : List Nat :=
  match Nat.beq allocId 0 with
  | true => exposed
  | false =>
    match isExposedAllocId exposed allocId with
    | true => exposed
    | false => allocId :: exposed

/--
Default empty `Memory` state used when evaluating pure `Rvalue` expressions
without an explicit `Memory` argument.
-/
def emptyMemory : Memory where
  nextAllocId := 0
  globals := .nil
  borrows := .nil
  nextTag := 1
  callees := .nil
  traitImpls := .nil
  callStack := .nil
  activeCallee := .none
  activeProtectors := .nil
  nextProtector := 1
  callerLocals := .nil
  fnPtrs := .nil
  exposedAllocIds := .nil
  rootUnwindCeiling := true

/--
Small-step machine configuration for `CapturedMir` execution.
-/
structure MachineState : Type where
  /-- Active stack frame. -/
  frame : StackFrame
  /-- Heap, borrow-tag, and call-stack memory state. -/
  memory : Memory

/--
Depth of the active stack frame of `s`: `0` for the root frame, and in general
`length s.memory.callStack`, because every inline `TerminatorKind.call` pushes
exactly one `SavedCallerFrame` and every `TerminatorKind.return_` pops one.
`BorrowEntry.targetFrameDepth` uses the same numbering.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "At any point during the execution of a function, each local is either
> allocated or unallocated."
-/
def currentFrameDepth (s : MachineState) : Nat := length s.memory.callStack

/--
`Memory.callStack` index of the saved frame at depth `d` when the active frame
has depth `depth` (`d < depth`): the most recent caller (depth `depth - 1`) is
at index `0` and the root frame (depth `0`) at index `depth - 1`.
-/
@[reducible]
def frameIndexOfDepth (depth d : Nat) : Nat := Nat.sub (Nat.sub depth 1) d

/--
Saved caller frame at depth `d` on `callStack` (`.none` unless
`d < length callStack`, i.e. unless the frame at depth `d` is a suspended
caller of the active frame).
-/
def savedFrameAtDepth? (callStack : List SavedCallerFrame) (d : Nat) :
    Option SavedCallerFrame :=
  match Nat.blt d (length callStack) with
  | true => get? callStack (frameIndexOfDepth (length callStack) d)
  | false => .none

/--
Frame-qualified lookup of borrow target `(d, loc)` in the **active** frame
(`DIV-MR-CALL-TARGET-LOCAL`): the active frame's slot `get? locals loc` when the
target frame is the active frame, and `.none` when it is a suspended caller
frame (or a frame that already returned).

With an empty `callStack` (the root frame is active) the lookup is exactly
`get? locals loc`, as for the single-frame borrow table: every live borrow then
targets depth `0`, and every tag minted in a frame that has since returned was
disabled by that frame's `TerminatorKind.return_` (`disableFrameBorrows`), so
every access through it faults before the slot is consulted.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "At any point during the execution of a function, each local is either
> allocated or unallocated."
-/
def activeFrameSlot?
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (d loc : Nat) :
    Option LocalSlot :=
  match callStack with
  | .nil => get? locals loc
  | _ :: _ =>
    match Nat.beq d (length callStack) with
    | true => get? locals loc
    | false => .none

/--
Frame-qualified lookup of borrow target `(d, loc)` **outside** the active
frame (`DIV-MR-CALL-TARGET-LOCAL`): the slot of local `loc` in the suspended
caller frame at depth `d`, falling back to the root frame's caller-owned
referent slots `callerLocals` (addressed at `loc ≥ length` of the root locals)
only for the root frame (`d = 0`).

With an empty `callStack` this is exactly `get? callerLocals loc`, the
caller-owned referent fallback of the single-frame borrow table.

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value."
> "Mutable references point to memory which is owned by some other value."
-/
def foreignFrameSlot?
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option LocalSlot :=
  match callStack with
  | .nil => get? callerLocals loc
  | _ :: _ =>
    match savedFrameAtDepth? callStack d with
    | .some sf =>
      match get? sf.frame.locals loc with
      | .some slot => .some slot
      | .none =>
        match d with
        | .zero => get? callerLocals loc
        | .succ _ => .none
    | .none => .none

/--
Frame-qualified local slot of borrow target `(d, loc)` in any live frame:
`activeFrameSlot?`, then `foreignFrameSlot?`.

With an empty `callStack` this is `get? locals loc` with the caller-owned
referent fallback `get? callerLocals loc`.
-/
def readFrameLocalSlot
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option LocalSlot :=
  match activeFrameSlot? locals callStack d loc with
  | .some slot => .some slot
  | .none => foreignFrameSlot? callStack callerLocals d loc

/--
With an empty `callStack`, `activeFrameSlot?` is the single-frame lookup
`get? locals loc`.
-/
@[simp]
theorem activeFrameSlot?_nil (locals : List LocalSlot) (d loc : Nat) :
    activeFrameSlot? locals .nil d loc = get? locals loc := rfl

/--
With an empty `callStack`, `foreignFrameSlot?` is the caller-owned referent
lookup `get? callerLocals loc`.
-/
@[simp]
theorem foreignFrameSlot?_nil (callerLocals : List LocalSlot) (d loc : Nat) :
    foreignFrameSlot? .nil callerLocals d loc = get? callerLocals loc := rfl

/--
Location of the slot list owning a foreign (non-active-frame) borrow target, as
resolved by `foreignFrameTarget?`.
-/
inductive ForeignFrameTarget : Type where
  /-- The target local lives in `callStack[idx].frame.locals`. -/
  | savedFrame (idx : Nat) (locals : List LocalSlot) : ForeignFrameTarget
  /-- The target local is a caller-owned referent slot of the root frame
      (`Memory.callerLocals`). -/
  | callerReferent (locals : List LocalSlot) : ForeignFrameTarget

/--
Slot list of the foreign (non-active-frame) borrow target `(d, loc)`, mirroring
`foreignFrameSlot?`: the suspended caller frame at depth `d` when it has a slot
`loc`, the root frame's caller-owned referent slots `callerLocals` when `d = 0`
otherwise (or whenever `callStack` is empty), and `.none` for a frame that is
not a suspended caller of the active frame.
-/
def foreignFrameTarget?
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option ForeignFrameTarget :=
  match callStack with
  | .nil => .some (.callerReferent callerLocals)
  | _ :: _ =>
    match savedFrameAtDepth? callStack d with
    | .some sf =>
      match get? sf.frame.locals loc with
      | .some _ =>
        .some (.savedFrame (frameIndexOfDepth (length callStack) d) sf.frame.locals)
      | .none =>
        match d with
        | .zero => .some (.callerReferent callerLocals)
        | .succ _ => .none
    | .none => .none

/-- Slot list of a `ForeignFrameTarget`. -/
def ForeignFrameTarget.locals : ForeignFrameTarget → List LocalSlot
  | .savedFrame _ locals => locals
  | .callerReferent locals => locals

/--
Commit the updated slot list `locals'` of a foreign borrow target back into
`mem`: the saved frame at `callStack[idx]`, or `mem.callerLocals`.
-/
def commitForeignFrameLocals
    (mem : Memory)
    (target : ForeignFrameTarget)
    (locals' : List LocalSlot) :
    Option Memory :=
  match target with
  | .callerReferent _ => .some { mem with callerLocals := locals' }
  | .savedFrame idx _ =>
    match get? mem.callStack idx with
    | .some sf =>
      match set? mem.callStack idx { sf with frame := { sf.frame with locals := locals' } } with
      | .some callStack' => .some { mem with callStack := callStack' }
      | .none => .none
    | .none => .none

/--
Frame-qualified update of the slot of borrow target `(d, loc)` to `slot`,
returning the updated active-frame `locals`, `callStack`, and `callerLocals`
(`.none` when no live frame owns `(d, loc)`). The slot written is exactly the
one read by `readFrameLocalSlot`.
-/
def writeFrameLocalSlot
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat)
    (slot : LocalSlot) :
    Option (List LocalSlot × List SavedCallerFrame × List LocalSlot) :=
  match activeFrameSlot? locals callStack d loc with
  | .some _ =>
    match set? locals loc slot with
    | .some locals' => .some (locals', callStack, callerLocals)
    | .none => .none
  | .none =>
    match foreignFrameTarget? callStack callerLocals d loc with
    | .some (.savedFrame idx frameLocals) =>
      match set? frameLocals loc slot, get? callStack idx with
      | .some frameLocals', .some sf =>
        match set? callStack idx { sf with frame := { sf.frame with locals := frameLocals' } } with
        | .some callStack' => .some (locals, callStack', callerLocals)
        | .none => .none
      | _, _ => .none
    | .some (.callerReferent referents) =>
      match set? referents loc slot with
      | .some referents' => .some (locals, callStack, referents')
      | .none => .none
    | .none => .none

/--
`localDecls` and `layouts` of the body executing in the frame at depth `d`:
`activeBody` for the active frame (`d = length callStack`) and the saved
`callerBody` for a suspended caller frame. `.none` for a frame that already
returned. With an empty `callStack`, depth `0` is the active frame.
-/
def frameLocalDeclsAndLayoutsAtDepth
    (callStack : List SavedCallerFrame)
    (activeDecls : List LocalDecl)
    (activeLayouts : LayoutTable)
    (d : Nat) :
    Option (List LocalDecl × LayoutTable) :=
  match Nat.beq d (length callStack) with
  | true => .some (activeDecls, activeLayouts)
  | false =>
    match savedFrameAtDepth? callStack d with
    | .some sf => .some (sf.callerBody.localDecls, sf.callerBody.layouts)
    | .none => .none

/--
`localDecls` and `layouts` of the foreign (non-active-frame) borrow target
`(d, loc)` resolved by `foreignFrameSlot?`: `(sf.callerBody.localDecls, sf.callerBody.layouts)`
when `loc` is a local of the suspended caller frame `sf` at depth `d`, and
`(.nil, defaultLayouts)` when `callStack` is empty or `(d, loc)` falls back to
the root frame's caller-owned referent slots `callerLocals`.
-/
def foreignFrameDeclsAndLayouts
    (callStack : List SavedCallerFrame)
    (defaultLayouts : LayoutTable)
    (d loc : Nat) :
    List LocalDecl × LayoutTable :=
  match callStack with
  | .nil => (.nil, defaultLayouts)
  | _ :: _ =>
    match savedFrameAtDepth? callStack d with
    | .some sf =>
      match get? sf.frame.locals loc with
      | .some _ => (sf.callerBody.localDecls, sf.callerBody.layouts)
      | .none => (.nil, sf.callerBody.layouts)
    | .none => (.nil, defaultLayouts)

/--
External or unresolved procedure-call interaction request emitted by
`TerminatorKind.call` and `TerminatorKind.tailCall` when no transparent
`CapturedMir` body is registered in `Memory.callees`.

Carrying `memory : Memory` alongside `defPath` and `args` reflects the fact
that Rust and FFI callees may read and mutate caller-visible memory and borrow
permissions.

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "A call expression calls a function. It consists of an expression with a
> function type or a type that implements one of the Fn, FnMut, or FnOnce
> traits, followed by a parenthesized comma-separated list of argument
> expressions. If the function eventually returns, then the expression
> completes."

Reference (The Rust Reference, "External blocks - ABI"):
<https://doc.rust-lang.org/1.98.0/reference/items/external-blocks.html#abi>

> "By default external blocks assume that the library they are calling uses
> the standard C ABI on the specific platform. Other ABIs may be specified
> using an abi string, as shown here:"
-/
structure MirCallReq : Type where
  /-- Canonical `DefId` path of the external or unlinked callee. -/
  defPath : DefPath
  /-- Monomorphized generic type arguments of the target function. -/
  typeArgs : List RigidTy := .nil
  /-- Evaluated argument values passed to the callee. -/
  args : List Value
  /-- Memory and borrow state at the call point. -/
  memory : Memory

/--
Response supplied by the environment or handler to an external `MirCallReq`.

Modeling `MirCallAns` as an effect response rather than a deterministic function
of `args` allows consecutive calls with identical arguments (such as FFI random
sources, I/O reads, or stateful counters) to yield distinct values, mutate
`Memory`, unwind (`panicked`), or abort (`aborted`).

Reference (The Rust Reference, "Call expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/call-expr.html>

> "If the function eventually returns, then the expression completes."
-/
inductive MirCallAns : Type where
  /-- Callee returned normally with `retVal` and updated `memory`. -/
  | returned (retVal : Value) (memory : Memory) : MirCallAns
  /-- Callee unwound (panicked) with updated `memory`. -/
  | panicked (memory : Memory) : MirCallAns
  /-- Callee terminated the process without unwinding. -/
  | aborted : MirCallAns

/--
Operational fault effect component of `MirEffect`.
-/
abbrev MirFailE : Effect.{0} := FailE FailureKind

/--
Observable leakage / branch-tag effect component of `MirEffect`.
-/
abbrev MirObsE : Effect.{0} := ObsE MirObs

/--
Impure external / unlinked procedure-call effect component of `MirEffect`.
-/
abbrev MirCallE : Effect.{0} := CallE MirCallReq (fun _ => MirCallAns)

/--
Open effect signature of MIR interaction trees: faults (`MirFailE`), visible
observations (`MirObsE`), and external calls (`MirCallE`) composed via `SumE`.
-/
abbrev MirEffect : Effect.{0} := SumE MirFailE (SumE MirObsE MirCallE)

/--
Normal return payload of a root MIR execution, pairing the returned `Value`
with the final `Memory`.
-/
abbrev MirReturn : Type := Prod Value Memory

/--
Terminal outcome of a root MIR execution (`normal (val, mem)`, `panic`, or
`abort`).
-/
abbrev MirOutcome : Type := Outcome MirReturn

/--
Extended coalgebra state for `ITree.cofix` unfolding of MIR execution, allowing
multi-phase transitions (such as receiving an external `MirCallAns` and either
resuming execution, halting on unwind/abort, or faulting on an invalid
destination place write) to be expressed without nested monadic binds inside
the single-step coalgebra.
-/
inductive MirExecState : Type where
  /-- Active MIR execution at `state`. -/
  | running (state : MachineState) : MirExecState
  /-- Execution has reached defined halting outcome `outcome`. -/
  | halted (outcome : MirOutcome) : MirExecState
  /-- Execution has triggered fault `kind`. -/
  | faulted (kind : FailureKind) : MirExecState

/--
One-step `ITreeF` transition result produced by `evalStmt`, `evalTerminator`,
and `stepMirFn`.
-/
abbrev MirStepNode : Type :=
  ITreeF MirEffect MirOutcome MirExecState

/--
Silent internal MIR transition advancing to `nextState`.
-/
def MirStepNode.step (nextState : MachineState) : MirStepNode :=
  .tau (.running nextState)

/--
MIR transition emitting `obs` (silent `.tau` on `.silent`, visible `MirObsE`
event on `.event tag`) and advancing to `nextState`.
-/
def MirStepNode.emitStep (obs : MirObs) (nextState : MachineState) :
    MirStepNode :=
  match obs with
  | .silent => .tau (.running nextState)
  | .event tag =>
    .vis (.inr (.inl (.emit (.event tag)))) (fun _ => .running nextState)

/--
Normal root-frame return node yielding `(retVal, mem)`.
-/
def MirStepNode.retNormal (retVal : Value) (mem : Memory) : MirStepNode :=
  .ret (.normal (retVal, mem))

/--
Terminal root-frame halting node yielding `out`.
-/
def MirStepNode.retOutcome (out : MirOutcome) : MirStepNode :=
  .ret out

/--
Operational fault node emitting `kind : FailureKind` on `MirFailE`.
-/
def MirStepNode.fail (kind : FailureKind) : MirStepNode :=
  .vis (.inl (.fail kind)) PEmpty.elim

/--
Fail-closed `.unsupported` transition node (`MirStepNode.fail .unsupported`).

Because `FaultEffect.isFault (.inl .unsupported)` holds, any reachable
`MirStepNode.unsupported` node falsifies `TreeSafe`.
-/
def MirStepNode.unsupported : MirStepNode :=
  MirStepNode.fail .unsupported

/--
External call interaction node emitting `req : MirCallReq` on `MirCallE` and
continuing at `k ans`.
-/
def MirStepNode.extCall
    (req : MirCallReq) (k : MirCallAns → MirExecState) : MirStepNode :=
  .vis (.inr (.inr (.call req))) k

/--
Result of traversing a `Place.projection` path on an initialized `Value`.
-/
inductive ProjReadResult : Type where
  /-- Traversal succeeded with projected value `val`. -/
  | ok (val : Value) : ProjReadResult
  /-- Index/field out of bounds, variant mismatch, or non-aggregate value. -/
  | ub : ProjReadResult
  /-- Projection element is not a modeled step. -/
  | unsupported : ProjReadResult

/--
Result of updating a nested field or element along a `Place.projection` path
inside an initialized `Value`.
-/
inductive ProjWriteResult : Type where
  /-- Update succeeded, producing replacement root value `val'`. -/
  | ok (val' : Value) : ProjWriteResult
  /-- Index/field out of bounds, variant mismatch, or non-aggregate value. -/
  | ub : ProjWriteResult
  /-- Projection element is not a modeled step. -/
  | unsupported : ProjWriteResult

/--
Result of reading a `Place` or evaluating an `Operand` in `locals`.
-/
inductive PlaceReadResult : Type where
  /-- Read succeeded with `val` and updated `locals'`. -/
  | ok (val : Value) (locals' : List LocalSlot) : PlaceReadResult
  /-- Reading an uninitialized, dead, disabled-borrow, or out-of-bounds place is
      undefined behavior. -/
  | ub : PlaceReadResult
  /-- Projection path or constant form is not yet modeled. -/
  | unsupported : PlaceReadResult

/--
Alias for `PlaceReadResult` when reading an `Operand`.
-/
abbrev OperandEvalResult : Type := PlaceReadResult

/--
Alias for `PlaceReadResult` when looking up a `Place`.
-/
abbrev LookupResult : Type := PlaceReadResult

/--
Result of evaluating a list of `Operand`s left-to-right.
-/
inductive OperandsEvalResult : Type where
  /-- Left-to-right evaluation succeeded with `vals` and updated `locals'`. -/
  | ok (vals : List Value) (locals' : List LocalSlot) : OperandsEvalResult
  /-- Evaluation of an operand triggered undefined behavior. -/
  | ub : OperandsEvalResult
  /-- An operand used an unmodeled construct. -/
  | unsupported : OperandsEvalResult

/--
Result of evaluating an `Rvalue`.
-/
inductive RvalueEvalResult : Type where
  /-- Evaluation succeeded with `val`, updated `locals'`, and updated
      `memory'`. -/
  | ok (val : Value) (locals' : List LocalSlot) (memory' : Memory) :
      RvalueEvalResult
  /-- Evaluation triggered undefined behavior. -/
  | ub : RvalueEvalResult
  /-- Rvalue form is not yet modeled. -/
  | unsupported : RvalueEvalResult

/--
Result of writing a runtime `Value` into a `Place` in `locals`.
-/
inductive PlaceWriteResult : Type where
  /-- Write succeeded, producing updated `locals'`. -/
  | ok (locals' : List LocalSlot) : PlaceWriteResult
  /-- Writing to a dead, uninitialized-aggregate, frozen/disabled borrow, or
      out-of-bounds place is undefined behavior. -/
  | ub : PlaceWriteResult
  /-- Projection element is not yet modeled. -/
  | unsupported : PlaceWriteResult

/--
Concatenate two `ProjectionElem` lists in `Init.Core`.
-/
def appendProjections :
    List ProjectionElem → List ProjectionElem → List ProjectionElem
  | .nil, ys => ys
  | x :: xs, ys => x :: appendProjections xs ys

/--
Construct a list of `count` copies of runtime value `v` for `Rvalue.repeat`.

Reference (The Rust Reference, "Array and array index expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/array-expr.html>

> "It is written by an expression for the value to be repeated, called the
> repeat operand, then a semicolon, then a constant expression for the number
> of times to repeat the value, called the length operand."
-/
def replicateValue : Nat → Value → List Value
  | .zero, _ => .nil
  | .succ k, v => v :: replicateValue k v

/--
Compare two `List UInt8` byte sequences for equality using only `Init.Core`
`Nat.beq`.
-/
@[reducible]
def listByteEq : List UInt8 → List UInt8 → Bool
  | .nil, .nil => true
  | b₁ :: bs₁, b₂ :: bs₂ =>
    match Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | true => listByteEq bs₁ bs₂
    | false => false
  | _, _ => false

/--
Compare two `String` values for UTF-8 byte equality in `Init.Core`.
-/
@[reducible]
def stringEq (a b : String) : Bool :=
  listByteEq a.toByteArray.data.toList b.toByteArray.data.toList

/--
Construct the initial `LocalSlot` list for a `CapturedMir` body given incoming
argument values `argVals` (`_0` is `.uninit`, `1..=argCount` are initialized
from `argVals`, and remaining temporaries start `.dead`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L368>

> "At any point during the execution of a function, each local is either
> allocated or unallocated. Except as noted below, all locals except function
> parameters are initially unallocated."
-/
def initLocalsAux : Nat → List LocalDecl → List Value → List LocalSlot
  | _, .nil, _ => .nil
  | .zero, _ :: decls, args => .uninit :: initLocalsAux 1 decls args
  | .succ idx, _ :: decls, arg :: restArgs =>
    .init arg :: initLocalsAux (Nat.add idx 1) decls restArgs
  | .succ idx, _ :: decls, .nil =>
    .dead :: initLocalsAux (Nat.add idx 1) decls .nil

/--
Initialize the local variable slots for `body` with argument values `args`.
-/
def initLocals (body : CapturedMir) (args : List Value) : List LocalSlot :=
  initLocalsAux 0 body.localDecls args

/--
Base allocation identifier offset (`65536`) for synthetic function-pointer
allocations (`GlobalAlloc::Function`), keeping reified function pointer
`AllocId`s non-zero and disjoint from default stack borrow tags (`1, 2, ...`).

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "pub enum GlobalAlloc<'tcx> {
>     /// The alloc ID is used as a function pointer.
>     Function {
>         instance: ty::Instance<'tcx>,
>     },"
-/
@[reducible]
def fnPtrAllocBase : AllocId := 65536

/--
Test whether `allocId` lies in the synthetic function-pointer `AllocId` range
(`allocId >= fnPtrAllocBase`).

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "/// The alloc ID is used as a function pointer.
> Function {
>     instance: ty::Instance<'tcx>,
> },"
-/
@[reducible]
def isFnPtrAllocId (allocId : AllocId) : Bool :=
  Nat.ble fnPtrAllocBase allocId

/--
Look up the `FnPtrEntry` with allocation identifier `allocId` in `fnPtrs`.

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "/// The alloc ID is used as a function pointer.
> Function {
>     instance: ty::Instance<'tcx>,
> },"
-/
@[reducible]
def lookupFnPtr : List FnPtrEntry → AllocId → Option FnPtrEntry
  | .nil, _ => .none
  | entry :: rest, allocId =>
    match Nat.beq entry.allocId allocId with
    | true => .some entry
    | false => lookupFnPtr rest allocId

/--
Compare two `UintTy` unsigned integer width tags for equality in `Init.Core`.
-/
@[reducible]
def uintTyEq : UintTy → UintTy → Bool
  | .u8, .u8 => true
  | .u16, .u16 => true
  | .u32, .u32 => true
  | .u64, .u64 => true
  | .u128, .u128 => true
  | .usize, .usize => true
  | _, _ => false

/--
Compare two `IntTy` signed integer width tags for equality in `Init.Core`.
-/
@[reducible]
def intTyEq : IntTy → IntTy → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | .isize, .isize => true
  | _, _ => false

/--
Compare two `FloatTy` floating-point width tags for equality in `Init.Core`.
-/
@[reducible]
def floatTyEq : FloatTy → FloatTy → Bool
  | .f16, .f16 => true
  | .f32, .f32 => true
  | .f64, .f64 => true
  | .f128, .f128 => true
  | _, _ => false

/--
Compare two `Mutability` qualifiers for equality in `Init.Core`.
-/
@[reducible]
def mutabilityEq : Mutability → Mutability → Bool
  | .not, .not => true
  | .mut, .mut => true
  | _, _ => false

/--
Compare two `Safety` qualifiers for equality in `Init.Core`.
-/
@[reducible]
def safetyEq : Safety → Safety → Bool
  | .safe, .safe => true
  | .unsafe_, .unsafe_ => true
  | _, _ => false

/--
Compare two `CallConv` calling-convention tags for equality in `Init.Core`.

Reference (The Rust Reference, "Function pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-pointer.html>

> "Two function pointer types are compatible if they have the same ABI, safety,
> parameter types, and return type."
-/
@[reducible]
def callConvEq : CallConv → CallConv → Bool
  | .rust, .rust => true
  | .c, .c => true
  | .rustIntrinsic, .rustIntrinsic => true
  | .other a, .other b => stringEq a b
  | _, _ => false

/--
Default recursion budget for fuel-bounded structural `RigidTy` equality.
-/
@[reducible]
def defaultTyEqFuel : Nat := 16

mutual

/--
Fuel-bounded structural equality on `RigidTy` in `Init.Core`.

Reference (The Rust Reference, "Function pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/function-pointer.html>

> "Function pointer types, written using the `fn` keyword, refer to a function
> whose identity is not necessarily known at compile-time."
-/
@[reducible]
def rigidTyEqAux : Nat → RigidTy → RigidTy → Bool
  | .zero, _, _ => false
  | .succ fuel, a, b =>
    match a, b with
    | .bool, .bool => true
    | .char, .char => true
    | .int w₁, .int w₂ => intTyEq w₁ w₂
    | .uint w₁, .uint w₂ => uintTyEq w₁ w₂
    | .float w₁, .float w₂ => floatTyEq w₁ w₂
    | .never, .never => true
    | .str, .str => true
    | .tuple fs₁, .tuple fs₂ => rigidTyListEqAux fuel fs₁ fs₂
    | .array e₁ n₁, .array e₂ n₂ =>
      Bool.and (Nat.beq n₁ n₂) (rigidTyEqAux fuel e₁ e₂)
    | .slice e₁, .slice e₂ => rigidTyEqAux fuel e₁ e₂
    | .ref m₁ p₁, .ref m₂ p₂ =>
      Bool.and (mutabilityEq m₁ m₂) (rigidTyEqAux fuel p₁ p₂)
    | .rawPtr m₁ p₁, .rawPtr m₂ p₂ =>
      Bool.and (mutabilityEq m₁ m₂) (rigidTyEqAux fuel p₁ p₂)
    | .adt d₁ args₁, .adt d₂ args₂ =>
      Bool.and (stringEq d₁ d₂) (rigidTyListEqAux fuel args₁ args₂)
    | .fnDef d₁ args₁, .fnDef d₂ args₂ =>
      Bool.and (stringEq d₁ d₂) (rigidTyListEqAux fuel args₁ args₂)
    | .fnPtr ins₁ out₁ saf₁ abi₁, .fnPtr ins₂ out₂ saf₂ abi₂ =>
      Bool.and
        (rigidTyListEqAux fuel ins₁ ins₂)
        (Bool.and
          (rigidTyEqAux fuel out₁ out₂)
          (Bool.and (safetyEq saf₁ saf₂) (callConvEq abi₁ abi₂)))
    | .closure d₁ up₁, .closure d₂ up₂ =>
      Bool.and (stringEq d₁ d₂) (rigidTyListEqAux fuel up₁ up₂)
    | .dynamic d₁, .dynamic d₂ => stringEq d₁ d₂
    | .foreign d₁, .foreign d₂ => stringEq d₁ d₂
    | .param idx₁ name₁, .param idx₂ name₂ =>
      Bool.and (Nat.beq idx₁ idx₂) (stringEq name₁ name₂)
    | .alias d₁ args₁, .alias d₂ args₂ =>
      Bool.and (stringEq d₁ d₂) (rigidTyListEqAux fuel args₁ args₂)
    | .other r₁, .other r₂ => stringEq r₁ r₂
    | _, _ => false

/--
Fuel-bounded pointwise structural equality on `List RigidTy` in `Init.Core`.
-/
@[reducible]
def rigidTyListEqAux : Nat → List RigidTy → List RigidTy → Bool
  | .zero, _, _ => false
  | .succ _, .nil, .nil => true
  | .succ fuel, x :: xs, y :: ys =>
    Bool.and
      (rigidTyEqAux (.succ fuel) x y)
      (rigidTyListEqAux (.succ fuel) xs ys)
  | .succ _, _, _ => false

end

/--
Compare two `RigidTy` values for structural equality using `defaultTyEqFuel`.
-/
@[reducible]
def rigidTyEq (a b : RigidTy) : Bool :=
  rigidTyEqAux defaultTyEqFuel a b

/--
Compare two `List RigidTy` lists for pointwise structural equality using
`defaultTyEqFuel`.
-/
@[reducible]
def rigidTyListEq (xs ys : List RigidTy) : Bool :=
  rigidTyListEqAux defaultTyEqFuel xs ys

/--
Compare two `Option RigidTy` values for structural equality.
-/
@[reducible]
def optionRigidTyEq : Option RigidTy → Option RigidTy → Bool
  | .none, .none => true
  | .some a, .some b => rigidTyEq a b
  | _, _ => false

/--
Look up an existing `FnPtrEntry` in `fnPtrs` with matching `(defPath, typeArgs, fnSig)`.

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "/// The alloc ID is used as a function pointer.
> Function {
>     instance: ty::Instance<'tcx>,
> },"
-/
@[reducible]
def findFnPtrEntry? :
    List FnPtrEntry → DefPath → List RigidTy → Option RigidTy → Option FnPtrEntry
  | .nil, _, _, _ => .none
  | entry :: rest, defPath, typeArgs, fnSig =>
    match
      Bool.and
        (stringEq entry.defPath defPath)
        (Bool.and
          (rigidTyListEq entry.typeArgs typeArgs)
          (optionRigidTyEq entry.fnSig fnSig))
    with
    | true => .some entry
    | false => findFnPtrEntry? rest defPath typeArgs fnSig

/--
Compute the next fresh function-pointer `AllocId` (`>= fnPtrAllocBase`) above
all existing entries in `fnPtrs`.
-/
@[reducible]
def nextFnPtrAllocId : List FnPtrEntry → AllocId
  | .nil => fnPtrAllocBase
  | entry :: rest =>
    let restNext := nextFnPtrAllocId rest
    let cand := Nat.add entry.allocId 1
    match Nat.ble restNext cand with
    | true => cand
    | false => restNext

/--
Intern a reified function pointer targeting `(defPath, typeArgs, fnSig)` in
`mem.fnPtrs`, reusing its existing `AllocId` if already registered or allocating
`nextFnPtrAllocId mem.fnPtrs` (`>= fnPtrAllocBase`) otherwise.

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "/// The alloc ID is used as a function pointer.
> Function {
>     instance: ty::Instance<'tcx>,
> },"
-/
@[reducible]
def internFnPtr
    (mem : Memory)
    (defPath : DefPath)
    (typeArgs : List RigidTy := .nil)
    (fnSig : Option RigidTy := .none) :
    AllocId × Memory :=
  match findFnPtrEntry? mem.fnPtrs defPath typeArgs fnSig with
  | .some existing => (existing.allocId, mem)
  | .none =>
    let allocId := nextFnPtrAllocId mem.fnPtrs
    let entry : FnPtrEntry := {
      allocId := allocId
      defPath := defPath
      typeArgs := typeArgs
      fnSig := fnSig
    }
    (allocId, { mem with fnPtrs := entry :: mem.fnPtrs })

/-!
## `dyn Trait` vtable environment (Episode 1, `ws-tcb-dyn-trait-unsize-and-vtable-dispatch`)

The vtable environment is harvested from the `CapturedMir.dynTypes` / `vtables`
/ `virtualMethods` tables of captured bodies the machine already holds. No
`Memory` / `MachineState` field and no `Value` constructor is added: wide `dyn`
pointers are `Value.aggregate 0 [dataWord, .ptr vtPtr ptrBytes]`.

Modeling choice (which bodies are consulted):
- `Rvalue`-level `dyn` evaluation (`Places.lean`) reads only the
  `SavedCallerFrame.callerBody`s on `Memory.callStack`, never
  `Memory.callees`, `Memory.activeCallee`, or `Memory.traitImpls`, exactly like
  every other `Rvalue` evaluator (whose results are invariant under replacing
  the callee context). `rustc-capture` attaches the same crate-level tables to
  every captured body, so any caller frame exposes the complete environment; an
  `Rvalue` evaluated in the modular root frame (empty `callStack`) sees an empty
  environment and every `dyn` operation there is `.unsupported`.
- Call-level lookups (`Terminators.lean`) may additionally read
  `Memory.callees`.
-/

/--
Base of the synthetic `AllocId` range reserved for vtable allocations
(`GlobalAlloc::VTable`).

Modeled property: the metadata word of a `dyn Trait` wide pointer is a pointer
to a vtable allocation distinct from every data allocation and every function
pointer allocation.

Reference (`compiler/rustc_middle/src/mir/interpret/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/mod.rs#L176-L185>

> "pub enum GlobalAlloc<'tcx> {
>     /// The alloc ID is used as a function pointer.
>     Function {
>         instance: ty::Instance<'tcx>,
>     },"

Modeling choice (not a Rust guarantee): vtable `AllocId`s live in
`[vtableAllocBase, vtableAllocBase + vtableAllocSpan) = [16384, 32768)`. This
range is (1) disjoint from function pointers (`>= fnPtrAllocBase = 65536`),
(2) strictly below the 32-bit stack-local page base `stackLocalAddrPageBase 4 =
32768` (and the 64-bit base `1048576`), so the canonical address
`allocId * 65536` of a vtable never aliases a stack local on either pointer
width and stays below `2^31` on 32-bit targets, and (3) far above the global
`AllocId`s `1..length allocations` that `rustc-capture` assigns. Collisions with
live Tree Borrows tags (also drawn from `1, 2, ...`) are detected at every use
(`lookupBorrow` on the vtable pointer must be `.none`) and fail closed.
-/
@[reducible]
def vtableAllocBase : AllocId := 16384

/-- Width of the reserved vtable `AllocId` range (see `vtableAllocBase`). -/
@[reducible]
def vtableAllocSpan : Nat := 16384

/--
Bodies whose dyn metadata tables are visible, in lookup priority order: the
optional explicit `currentBody`, then `bodies`.
-/
def dynSourceBodies (currentBody : Option CapturedMir) (bodies : List CapturedMir) :
    List CapturedMir :=
  match currentBody with
  | .some b => b :: bodies
  | .none => bodies

/-- The caller bodies saved on a call stack (innermost first). -/
def callerBodiesOf (callStack : List SavedCallerFrame) : List CapturedMir :=
  callStack.map (fun sf => sf.callerBody)

/-- Structural equality of `CapturedVTableSlot`s. -/
@[reducible]
def capturedVTableSlotBEq : CapturedVTableSlot → CapturedVTableSlot → Bool
  | .dropInPlace .none, .dropInPlace .none => true
  | .dropInPlace (.some a), .dropInPlace (.some b) => stringEq a b
  | .size, .size => true
  | .align, .align => true
  | .vacant, .vacant => true
  | .method p₁ a₁, .method p₂ a₂ => Bool.and (stringEq p₁ p₂) (rigidTyListEq a₁ a₂)
  | .traitVPtr i₁, .traitVPtr i₂ => Nat.beq i₁ i₂
  | _, _ => false

/-- Pointwise structural equality of `CapturedVTableSlot` lists. -/
@[reducible]
def capturedVTableSlotListBEq : List CapturedVTableSlot → List CapturedVTableSlot → Bool
  | .nil, .nil => true
  | a :: as, b :: bs => Bool.and (capturedVTableSlotBEq a b) (capturedVTableSlotListBEq as bs)
  | _, _ => false

/-- Structural equality of `CapturedVTable` records. -/
@[reducible]
def capturedVTableBEq (a b : CapturedVTable) : Bool :=
  Bool.and (Nat.beq a.vtableId b.vtableId)
    (Bool.and (Nat.beq a.vtableAllocId b.vtableAllocId)
      (Bool.and (rigidTyEq a.concreteTy b.concreteTy)
        (Bool.and (stringEq a.dynKey b.dynKey)
          (Bool.and (Nat.beq a.sizeBytes b.sizeBytes)
            (Bool.and (Nat.beq a.alignBytes b.alignBytes)
              (Bool.and (Bool.not (Bool.xor a.isUninhabited b.isUninhabited))
                (capturedVTableSlotListBEq a.slots b.slots)))))))

/-- Look up the vtable with synthetic allocation identifier `allocId`. -/
@[reducible]
def lookupVTableByAllocId : List CapturedVTable → AllocId → Option CapturedVTable
  | .nil, _ => .none
  | v :: vs, allocId =>
    match Nat.beq v.vtableAllocId allocId with
    | true => .some v
    | false => lookupVTableByAllocId vs allocId

/-- Look up the vtable built for `(concreteTy, dynKey)`. -/
@[reducible]
def lookupVTableFor : List CapturedVTable → RigidTy → DefPath → Option CapturedVTable
  | .nil, _, _ => .none
  | v :: vs, concreteTy, dynKey =>
    match Bool.and (stringEq v.dynKey dynKey) (rigidTyEq v.concreteTy concreteTy) with
    | true => .some v
    | false => lookupVTableFor vs concreteTy dynKey

/-- Look up the existential-predicate descriptor of `RigidTy.dynamic dynKey`. -/
@[reducible]
def lookupDynType : List CapturedDynType → DefPath → Option CapturedDynType
  | .nil, _ => .none
  | d :: ds, dynKey =>
    match stringEq d.dynKey dynKey with
    | true => .some d
    | false => lookupDynType ds dynKey

/-- Look up the `InstanceKind::Virtual` record of `(methodDefPath, dynKey)`. -/
@[reducible]
def lookupVirtualMethod :
    List CapturedVirtualMethod → DefPath → DefPath → Option CapturedVirtualMethod
  | .nil, _, _ => .none
  | m :: ms, methodDefPath, dynKey =>
    match Bool.and (stringEq m.methodDefPath methodDefPath) (stringEq m.dynKey dynKey) with
    | true => .some m
    | false => lookupVirtualMethod ms methodDefPath dynKey

/-- Merge `new` into `acc`, keeping the first record per `vtableAllocId`. -/
def dedupVTablesInto : List CapturedVTable → List CapturedVTable → List CapturedVTable
  | acc, .nil => acc
  | acc, v :: vs =>
    match lookupVTableByAllocId acc v.vtableAllocId with
    | .some _ => dedupVTablesInto acc vs
    | .none => dedupVTablesInto (acc ++ v :: .nil) vs

/-- `true` iff every record of `vs` agrees structurally with the record that
`acc` holds for its `vtableAllocId` (absent records are vacuously consistent). -/
def vtablesAgreeWith : List CapturedVTable → List CapturedVTable → Bool
  | _, .nil => true
  | acc, v :: vs =>
    Bool.and
      (match lookupVTableByAllocId acc v.vtableAllocId with
       | .some w => capturedVTableBEq v w
       | .none => true)
      (vtablesAgreeWith acc vs)

/--
Deduplicated vtable table visible from `(currentBody, bodies)`
(`dynSourceBodies`), keeping the first record per `vtableAllocId`.
-/
def collectBodyVTables (currentBody : Option CapturedMir) (bodies : List CapturedMir) :
    List CapturedVTable :=
  (dynSourceBodies currentBody bodies).foldl (fun acc b => dedupVTablesInto acc b.vtables) .nil

/-- `collectBodyVTables` over the caller bodies of `mem.callStack` followed by
`mem.callees` (call-level lookups only). -/
def collectMemoryVTables (currentBody : Option CapturedMir := .none) (mem : Memory) :
    List CapturedVTable :=
  collectBodyVTables currentBody (callerBodiesOf mem.callStack ++ mem.callees)

/-- Deduplicated `CapturedDynType` table visible from `(currentBody, bodies)`. -/
def collectBodyDynTypes (currentBody : Option CapturedMir) (bodies : List CapturedMir) :
    List CapturedDynType :=
  (dynSourceBodies currentBody bodies).foldl
    (fun acc b =>
      b.dynTypes.foldl
        (fun acc' d =>
          match lookupDynType acc' d.dynKey with
          | .some _ => acc'
          | .none => acc' ++ d :: .nil)
        acc)
    .nil

/-- Deduplicated `CapturedVirtualMethod` table visible from `(currentBody, bodies)`. -/
def collectBodyVirtualMethods (currentBody : Option CapturedMir) (bodies : List CapturedMir) :
    List CapturedVirtualMethod :=
  (dynSourceBodies currentBody bodies).foldl
    (fun acc b =>
      b.virtualMethods.foldl
        (fun acc' m =>
          match lookupVirtualMethod acc' m.methodDefPath m.dynKey with
          | .some _ => acc'
          | .none => acc' ++ m :: .nil)
        acc)
    .nil


/-- `collectBodyDynTypes` over the caller bodies of `mem.callStack` followed by
`mem.callees` (call-level lookups only). -/
def collectMemoryDynTypes (currentBody : Option CapturedMir := .none) (mem : Memory) :
    List CapturedDynType :=
  collectBodyDynTypes currentBody (callerBodiesOf mem.callStack ++ mem.callees)

/-- `collectBodyVirtualMethods` over the caller bodies of `mem.callStack` followed by
`mem.callees` (call-level lookups only). -/
def collectMemoryVirtualMethods (currentBody : Option CapturedMir := .none) (mem : Memory) :
    List CapturedVirtualMethod :=
  collectBodyVirtualMethods currentBody (callerBodiesOf mem.callStack ++ mem.callees)

/-- `true` iff every captured body visible from `(currentBody, bodies)` carries
a vtable table consistent with the deduplicated table `vts`. -/
def bodyVTablesConsistent (currentBody : Option CapturedMir) (bodies : List CapturedMir)
    (vts : List CapturedVTable) : Bool :=
  (dynSourceBodies currentBody bodies).all (fun b => vtablesAgreeWith vts b.vtables)

/-- `n` is a non-zero power of two. -/
@[reducible]
def isPowerOfTwoNat (n : Nat) : Bool :=
  Bool.and (Bool.not (Nat.beq n 0)) (Nat.beq (Nat.land n (Nat.sub n 1)) 0)

/--
Decidable well-formedness of one captured vtable on a target with
`ptrBytes`-byte pointers.

Modeled property: a vtable describes the layout of a sized concrete type; the
layout size is a multiple of its power-of-two alignment and the size of every
value is at most `isize::MAX`.

Reference (The Rust Reference 1.98.0, "Type layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html>

> "The alignment of a value specifies what addresses are valid to store the
> value at. ... Alignment is measured in bytes, and must be at least 1, and
> always a power of 2."
>
> "The size of a value is always a multiple of its alignment."

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `size_of_val_raw` safety contract):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L426-L429>

> "///     - a [trait object], then the vtable part of the pointer must point
> ///       to a valid vtable acquired by an unsizing coercion, and the size
> ///       of the *entire value* (dynamic tail length + statically sized prefix)
> ///       must fit in `isize`."

Justification: the checks are necessary conditions on any `rustc` layout; a
table violating them is not a faithful capture and every operation consulting it
fails closed (`.unsupported`). Header shape: the first three slots must be
`[.dropInPlace _, .size, .align]` (`TyCtxt::COMMON_VTABLE_ENTRIES`).
-/
def wfVTableEntry (ptrBytes : Nat) (v : CapturedVTable) : Bool :=
  let half := Nat.pow 2 (Nat.sub (Nat.mul 8 ptrBytes) 1)
  let headerOk : Bool :=
    match v.slots with
    | .dropInPlace _ :: .size :: .align :: _ => true
    | _ => false
  Bool.and (isPowerOfTwoNat v.alignBytes)
    (Bool.and (Nat.blt v.alignBytes half)
      (Bool.and (Nat.blt (Nat.add v.sizeBytes (Nat.sub v.alignBytes 1)) half)
        (Bool.and (Nat.beq (Nat.mod v.sizeBytes v.alignBytes) 0) headerOk)))

/-- `true` iff the `vtableAllocId`s of `vs` are pairwise distinct. -/
def vtableAllocIdsUnique : List CapturedVTable → Bool
  | .nil => true
  | v :: vs =>
    Bool.and
      (match lookupVTableByAllocId vs v.vtableAllocId with
       | .some _ => false
       | .none => true)
      (vtableAllocIdsUnique vs)

/-- `true` iff `allocId` is the `allocId` of some captured global allocation. -/
def isGlobalAllocIdIn : List CapturedAllocation → AllocId → Bool
  | .nil, _ => false
  | a :: as, allocId => Bool.or (Nat.beq a.allocId allocId) (isGlobalAllocIdIn as allocId)

/--
Decidable vtable-environment invariant `vtableEnvOk ptrBytes vts nextAllocId globals fnPtrs`.

Modeled property: every vtable pointer designates a vtable allocation that is
disjoint from data allocations (globals, stack locals) and function-pointer
allocations, so a metadata word can be resolved to exactly one vtable.

Checks, for every `v ∈ vts`: `wfVTableEntry ptrBytes v`; `vtableAllocId` is
non-zero, in `[vtableAllocBase, vtableAllocBase + vtableAllocSpan)`, strictly
below the stack-local page base of `ptrBytes` (`32768` on 32-bit, `1048576` on
64-bit), not below `mem.nextAllocId`, not the `allocId` of any global, and not a
registered function pointer; and the identifiers are pairwise distinct. The
memory components are passed individually (`Memory.nextAllocId`,
`Memory.globals`, `Memory.fnPtrs`) so the invariant never depends on frame
bookkeeping.

Reference: see `vtableAllocBase` and `CapturedVTable`.

Unsupported: when the invariant fails every `dyn` operation fails closed with
`.unsupported` (never `.ub`).
-/
def vtableEnvOk (ptrBytes : Nat) (vts : List CapturedVTable) (nextAllocId : AllocId)
    (globals : List CapturedAllocation) (fnPtrs : List FnPtrEntry) : Bool :=
  let stackBase : Nat :=
    match Nat.ble 8 ptrBytes with
    | true => 1048576
    | false => 32768
  Bool.and (vtableAllocIdsUnique vts)
    (vts.all (fun v =>
      Bool.and (wfVTableEntry ptrBytes v)
        (Bool.and (Nat.ble vtableAllocBase v.vtableAllocId)
          (Bool.and (Nat.blt v.vtableAllocId (Nat.add vtableAllocBase vtableAllocSpan))
            (Bool.and (Nat.blt v.vtableAllocId stackBase)
              (Bool.and (Nat.ble nextAllocId v.vtableAllocId)
                (Bool.and (Bool.not (isGlobalAllocIdIn globals v.vtableAllocId))
                  (match lookupFnPtr fnPtrs v.vtableAllocId with
                   | .some _ => false
                   | .none => true))))))))

/--
Register `body` in `mem.callees` (appended, so existing callees keep priority)
unless a callee with the same `defPath` is already linked, making `body`'s dyn
metadata tables visible to the call-level lookups (`collectMemoryVTables`,
`collectMemoryVirtualMethods`) when `body` executes as the modular root
(single-body unit and correspondence tests). `Rvalue`-level `dyn` evaluation
reads caller frames only and is unaffected.

Modeling note: this is an environment-construction helper with no Rust
counterpart; it changes only which captured tables are visible.
-/
def withBodyDynMetadata (body : CapturedMir) (mem : Memory) : Memory :=
  match mem.callees.any (fun c => stringEq c.defPath body.defPath) with
  | true => mem
  | false => { mem with callees := mem.callees ++ body :: .nil }

/--
Whether trait-object types `a` and `b` have the same predicate list up to auto
traits, the relation the interpreter uses to check a vtable against the
expected trait object type (`check_vtable_for_type`).

Reference (`compiler/rustc_const_eval/src/interpret/traits.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_const_eval/src/interpret/traits.rs#L72-L78>

> "// We check validity by comparing the lists of predicates for equality. We *could* instead
> // check that the dynamic type to which the vtable belongs satisfies all the expected
> // predicates, but that would likely be a lot slower and seems unnecessarily permissive.
>
> // FIXME: we are skipping auto traits for now, but might revisit this in the future.
> let mut sorted_vtable: Vec<_> = vtable_dyn_type.without_auto_traits().collect();"

Justification: equal keys are trivially compatible; otherwise the captured
`predicateKey`s (predicate lists without auto traits) must agree. Missing
descriptors make distinct keys incompatible, which callers treat as `.ub` only
after the vtable pointer itself has been resolved.
-/
def dynKeysCompatible (dts : List CapturedDynType) (a b : DefPath) : Bool :=
  match stringEq a b with
  | true => true
  | false =>
    match lookupDynType dts a, lookupDynType dts b with
    | .some da, .some db => stringEq da.predicateKey db.predicateKey
    | _, _ => false

/--
`true` iff the descriptor of `dynKey` (if captured) marks the type as fully
modeled: no unresolved existential binder (`charon#1640`) and every supertrait /
projection outlives obligation discharged. Types without a descriptor are
modeled only when they carry no generic or auto-trait components, which
`rustc-capture` guarantees by emitting a descriptor for every other key.
-/
def dynTypeModeled (dts : List CapturedDynType) (dynKey : DefPath) : Bool :=
  match lookupDynType dts dynKey with
  | .some d => Bool.and (Bool.not d.hasUnresolvedExistentialBinder) d.supertraitOutlivesOk
  | .none => true

/-- `true` iff every element of `xs` occurs in `ys` (string equality). -/
def defPathsSubset (xs ys : List DefPath) : Bool :=
  xs.all (fun x => ys.any (fun y => stringEq x y))


end Trusted.Rustc.V2026_08_01.MirSemantics
