import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Terminators

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR basic blocks, local declarations,
global allocations, and captured bodies for `rustc 1.98.0-nightly`
(`14210df0e 2026-05-31`, `#99`, `#101`, `#103`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L65-L88>

> "/// The \"runtime MIR\" dialect, used for CTFE, optimizations, and codegen.
> ///
> /// The semantic differences between analysis MIR and runtime MIR are as follows.
> ///
> /// - Drops: In analysis MIR, `Drop` terminators represent *conditional* drops; roughly
> ///   speaking, if dataflow analysis determines that the place being dropped is uninitialized,
> ///   the drop will not be executed. ... In runtime MIR, the drops are unconditional; when a
> ///   `Drop` terminator is reached, if the type has drop glue that drop glue is always executed.
> ///   This may be UB if the underlying place is not initialized."
-/

/--
A single basic block in a MIR control-flow graph, modeling
`rustc_middle::mir::BasicBlockData`.

Fields `statements`, `terminator`, and `isCleanup` correspond to
`BasicBlockData::statements`, `BasicBlockData::terminator`, and
`BasicBlockData::is_cleanup`. Because every completed MIR basic block in
`Runtime(PostCleanup)` has `Some(terminator)` (`anneal-rustc-capture` rejects
incomplete blocks), `terminator` is stored directly rather than wrapped in
`Option`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L1319-L1342>

> "pub struct BasicBlockData<'tcx> {
>     /// List of statements in this block.
>     pub statements: Vec<Statement<'tcx>>,
>
>     /// Terminator for this block.
>     ///
>     /// N.B., this should generally ONLY be `None` during construction.
>     /// Therefore, you should generally access it via the
>     /// `terminator()` or `terminator_mut()` methods. The only
>     /// exception is that certain passes, such as `simplify_cfg`, swap
>     /// out the terminator temporarily with `None` while they continue
>     /// to recurse over the set of basic blocks.
>     pub terminator: Option<Terminator<'tcx>>,
>
>     /// If true, this block lies on an unwind path. This is used
>     /// during codegen where distinct kinds of basic blocks may be
>     /// generated (particularly for MSVC cleanup). Unwind blocks must
>     /// only branch to other unwind blocks.
>     pub is_cleanup: bool,
> }"
-/
structure BasicBlockData : Type where
  /-- Sequential statements executed before `terminator`. -/
  statements : List Statement
  /-- Control-flow transfer ending the basic block. -/
  terminator : Terminator
  /-- True if this block is part of an unwinding cleanup path (`is_cleanup`). -/
  isCleanup : Bool

/--
Declaration of a MIR local variable, modeling `rustc_middle::mir::LocalDecl`.

Fields `mutability` and `ty` correspond to `LocalDecl::mutability` and
`LocalDecl::ty`, while `debugName` records the user-facing variable identifier
from `VarDebugInfo` when available.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L966-L976>

> "pub struct LocalDecl<'tcx> {
>     /// Whether this is a mutable binding (i.e., `let x` vs `let mut x`).
>     ///
>     /// Temporaries and the return place are always mutable.
>     pub mutability: Mutability,
>
>     pub local_info: ClearCrossCrate<Box<LocalInfo<'tcx>>>,
>
>     /// The type of this local.
>     pub ty: Ty<'tcx>,
>
>     /// User-written type annotations on this local.
>     pub user_ty: Option<Box<UserTypeProjections>>,
>
>     /// The *syntactic* (i.e., not visibility) source scope the local is defined
>     /// in.
>     pub source_info: SourceInfo,
> }"
-/
structure LocalDecl : Type where
  /-- Mutability of the local binding (`mut` vs. immutable). -/
  mutability : Mutability
  /-- Monomorphized type and layout index of the local. -/
  ty : Ty
  /-- Optional user-visible variable name from debug info. -/
  debugName : Option String

/--
Static global allocation entry captured from `tcx.global_alloc(alloc_id)`,
modeling `rustc_middle::mir::interpret::Allocation` (`R-CONST-01`).

Field `allocId` identifies the `AllocId`, `bytes` records the byte
initialization mask (`Option UInt8`, where `.none` represents an uninitialized
byte), `relocations` records pointer provenance relocations at byte offsets,
`align` records the allocation's required alignment, and `mutability` records
whether the allocation is immutable or `static mut`.

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L21-L27>

> "pub struct ConstAlloc<'tcx> {
>     /// The value lives here, at offset 0, and that allocation definitely is an `AllocKind::Memory`
>     /// (so you can use `AllocMap::unwrap_memory`).
>     pub alloc_id: AllocId,
>     pub ty: Ty<'tcx>,
> }"
-/
structure CapturedAllocation : Type where
  /-- Allocation identifier (`AllocId`). -/
  allocId : AllocId
  /-- Initialized byte values (`Option UInt8`, where `.none` represents an
      uninitialized padding byte). -/
  bytes : List (Option UInt8)
  /-- Pointer relocations `(byteOffset, targetProvenance)` stored within the
      allocation. -/
  relocations : List (Nat × ProvenancePtr)
  /-- Required alignment in bytes. -/
  align : Align
  /-- Mutability of the global allocation (`static` vs. `static mut`). -/
  mutability : Mutability

/--
Complete 1-to-1 captured `Runtime(PostCleanup)` MIR body and layout environment
emitted by `anneal-rustc-capture` into `Mir/<Item>.lean`, modeling
`rustc_middle::mir::Body` paired with its `FnAbi`, `LayoutTable`, and global
allocations (`#99`, `#101`, `#103`).

In `rustc_middle::mir::Body`:
- Local `0` (`RETURN_PLACE`) holds the return value,
- Locals `1..=arg_count` hold the function arguments, and
- Basic block `0` (`START_BLOCK`) is the entry block of `basic_blocks`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L206-L246>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L347-L352>

> "pub struct Body<'tcx> {
>     /// A list of basic blocks. References to basic block use a newtyped index type [`BasicBlock`]
>     /// that indexes into this vector.
>     pub basic_blocks: BasicBlocks<'tcx>,
>
>     /// Records how far through the \"desugaring and optimization\" process this particular
>     /// MIR has traversed. This is particularly useful when inlining, since in that context
>     /// we instantiate the promoted constants and add them to our promoted vector -- but those
>     /// promoted items have already been optimized, whereas ours have not. This field allows
>     /// us to see the difference and forego optimization on the inlined promoted items.
>     pub phase: MirPhase,
>     ...
>     /// Declarations of locals.
>     ///
>     /// The first local is the return value pointer, followed by `arg_count`
>     /// locals for the function arguments, followed by any user-declared
>     /// variables and temporaries.
>     pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
>     ...
>     /// The number of arguments this function takes.
>     ///
>     /// Starting at local 1, `arg_count` locals will be provided by the caller
>     /// and can be assumed to be initialized.
>     ///
>     /// If this MIR was built for a constant, this will be 0.
>     pub arg_count: usize,
> }"
>
> "debug_assert!(
>     local_decls.len() > arg_count,
>     \"expected at least {} locals in MIR for {:?}, found {}\",
>     arg_count + 1,
>     source.instance,
>     local_decls.len(),
> );"
-/
structure CapturedMir : Type where
  /-- Canonical `DefId` path of this item. -/
  defPath : DefPath
  /-- Recorded MIR dialect and phase (`MirPhaseTag.runtimePostCleanup`). -/
  phase : MirPhaseTag
  /-- Role of this body (subject function vs. contract helper). -/
  role : ContractRole
  /-- Number of function arguments (`arg_count`); locals `1..=argCount` hold the
      incoming arguments and local `0` holds the return place. -/
  argCount : Nat
  /-- Indexed declarations of all locals (`_0` through `_{n-1}`). -/
  localDecls : List LocalDecl
  /-- Indexed basic blocks (`bb0` through `bb_{m-1}`) forming the CFG; entry is
      `0`. -/
  basicBlocks : List BasicBlockData
  /-- Calling-convention ABI of this function. -/
  fnAbi : FnAbi
  /-- Compiler-computed layout table for all types referenced in this body. -/
  layouts : LayoutTable
  /-- Global/constant allocations referenced by this body. -/
  allocations : List CapturedAllocation

/--
Look up the `BasicBlockData` for 0-based basic-block index `bb` in
`m.basicBlocks`, returning `.none` if `bb` is out of bounds.
-/
def CapturedMir.getBlock? (m : CapturedMir) (bb : BasicBlockIdx) : Option BasicBlockData :=
  Trusted.Sequence.get? m.basicBlocks bb

/--
Look up the `LocalDecl` for 0-based local variable index `loc` in
`m.localDecls`, returning `.none` if `loc` is out of bounds.
-/
def CapturedMir.getLocalDecl? (m : CapturedMir) (loc : Local) : Option LocalDecl :=
  Trusted.Sequence.get? m.localDecls loc

/--
Test whether `m` was captured at `MirPhase::Runtime(RuntimePhase::PostCleanup)`
(`.runtimePostCleanup`).
-/
def CapturedMir.isRuntimePostCleanup (m : CapturedMir) : Bool :=
  match m.phase with
  | .runtimePostCleanup => true
  | _ => false

/--
Executable structural well-formedness check on a `CapturedMir` body.

This predicate verifies that:
1. `m.phase` is `.runtimePostCleanup`
   (`MirPhase::Runtime(RuntimePhase::PostCleanup)`),
2. `m.localDecls` is non-empty (so `RETURN_PLACE` `_0` exists) and has at least
   `m.argCount + 1` entries (`local_decls.len() > arg_count`), and
3. `m.basicBlocks` is non-empty (so `START_BLOCK` `bb0` exists).
-/
def CapturedMir.wellFormed (m : CapturedMir) : Bool :=
  Bool.and
    (CapturedMir.isRuntimePostCleanup m)
    (Bool.and
      (match m.localDecls with | .nil => false | _ :: _ => true)
      (Bool.and
        (Nat.ble (Nat.add m.argCount 1) (Trusted.Sequence.length m.localDecls))
        (match m.basicBlocks with | .nil => false | _ :: _ => true)))

end Trusted.Rustc.V2026_06_01.MirAst
