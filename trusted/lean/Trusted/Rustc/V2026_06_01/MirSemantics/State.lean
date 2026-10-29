import Trusted.Refinement
import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Terminators
import Trusted.Rustc.V2026_06_01.MirAst.Body

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

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

Constructors `.active`, `.reserved`, `.frozen`, and `.disabled` model the four
permission states of the Tree Borrows aliasing discipline for references (`&T`,
`&mut T`) and raw borrows (`&raw const`, `&raw mut`):
- `.active` and `.reserved` permit both reads and writes through the tag;
- `.frozen` permits reads and rejects writes as undefined behavior; and
- `.disabled` rejects both reads and writes as undefined behavior.

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
-/
inductive TreeBorrowPerm : Type where
  /-- Mutable borrow with active read/write permission (`Active`). -/
  | active : TreeBorrowPerm
  /-- Mutable borrow in reserved state prior to first write (`Reserved`). -/
  | reserved : TreeBorrowPerm
  /-- Shared or immutable borrow with read-only permission (`Frozen`). -/
  | frozen : TreeBorrowPerm
  /-- Invalidated borrow tag; any access is undefined behavior (`Disabled`). -/
  | disabled : TreeBorrowPerm

/--
0-based local variable index alias for borrow-table target references.
-/
abbrev LocalIdx : Type := Local

/--
Borrow-table entry associating a pointer provenance `tag` with its target stack
local, sub-place projection path, optional explicit byte sub-range
`[rangeOffset, rangeOffset + rangeLen)`, `TreeBorrowPerm` permission, and
optional function-entry lifetime protector identifier (`RetagKind.fnEntry`).

When `rangeLen == 0`, overlap with writes is governed structurally by
`targetProjection`; when `rangeLen > 0`, overlap with byte-ranged writes is
governed by the half-open interval `[rangeOffset, rangeOffset + rangeLen)`.

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

/--
Saved caller activation record pushed onto `Memory.callStack` when executing a
non-diverging `TerminatorKind.call` and popped by `TerminatorKind.return_`.

Snapshots the caller's active lifetime protectors so that protectors activated
via `RetagKind.fnEntry` during the callee frame are deactivated upon
`TerminatorKind.return_`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L812-L818>

> "/// Returns from the function.
> ///
> /// Like function calls, the exact semantics of returns in Rust are unclear.
> /// Returning very likely at least assigns the value currently in the return
> /// place (`_0`) to the place specified in the associated `Call` terminator
> /// in the calling function, as if assigned via `dest = move _0`.
> Return,"
-/
structure SavedCallerFrame : Type where
  /-- Caller `CapturedMir` body to restore on `TerminatorKind.return_`. -/
  callerBody : CapturedMir
  /-- Caller `StackFrame` after evaluating the call's argument operands. -/
  frame : StackFrame
  /-- Caller destination `Place` receiving the callee's `_0` return value. -/
  destination : Place
  /-- Caller basic block index jumped to after writing `destination`. -/
  returnTarget : BasicBlockIdx
  /-- Optional caller lifetime protector identifier preserved across the call. -/
  callerProtector : Option Nat := .none
  /-- Snapshot of active lifetime protectors prior to entering the callee frame,
      restored on `TerminatorKind.return_`. -/
  calleeProtectors : List Nat := .nil

/--
Abstract heap, global allocation, Tree Borrows tag table, active function-entry
lifetime protectors, and interprocedural call stack store.
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
  callStack := .nil
  activeCallee := .none
  activeProtectors := .nil
  nextProtector := 1
  callerLocals := .nil

/--
Small-step machine configuration for `CapturedMir` execution.
-/
structure MachineState : Type where
  /-- Active stack frame. -/
  frame : StackFrame
  /-- Heap, borrow-tag, and call-stack memory state. -/
  memory : Memory

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

end Trusted.Rustc.V2026_06_01.MirSemantics
