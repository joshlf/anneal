import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Trusted.Rustc.V2026_08_01.MirAst.Statements
import Trusted.Rustc.V2026_08_01.MirAst.Terminators

namespace Trusted.Rustc.V2026_08_01.MirAst

open Trusted.Rustc.V2026_08_01.Layout

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
  /-- Number of generic type parameters. -/
  typeParamCount : Nat := 0
  /-- Generic parameter definitions. -/
  genericParams : List GenericParamDef := .nil
  /-- Trait implementations. -/
  traitImpls : List TraitImplEntry := .nil

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




open Trusted.Sequence

/--
Instantiate a `ProjectionElem` by substituting `Ty` occurrences inside `.field`,
`.opaqueCast`, and `.unwrapUnsafeBinder`.
-/
@[reducible]
def ProjectionElem.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    ProjectionElem → ProjectionElem
  | .deref => .deref
  | .field fIdx ty => .field fIdx (Ty.instantiate tbl args ty)
  | .index idx => .index idx
  | .constantIndex offset minLength fromEnd =>
    .constantIndex offset minLength fromEnd
  | .subslice from_ to_ fromEnd => .subslice from_ to_ fromEnd
  | .downcast variantName variantIdx => .downcast variantName variantIdx
  | .opaqueCast ty => .opaqueCast (Ty.instantiate tbl args ty)
  | .unwrapUnsafeBinder ty => .unwrapUnsafeBinder (Ty.instantiate tbl args ty)

/--
Structurally instantiate a list of `ProjectionElem`s.
-/
@[reducible]
def ProjectionElem.instantiateList
    (tbl : LayoutTable)
    (args : TypeSubst) :
    List ProjectionElem → List ProjectionElem
  | .nil => .nil
  | elem :: rest =>
    ProjectionElem.instantiate tbl args elem ::
      ProjectionElem.instantiateList tbl args rest

/--
Universal identity theorem for `ProjectionElem.instantiate` on `.nil`.
-/
@[simp]
theorem ProjectionElem.instantiate_nil
    (tbl : LayoutTable) :
    (elem : ProjectionElem) →
    ProjectionElem.instantiate tbl .nil elem = elem
  | .deref => rfl
  | .field f ty => congrArg (ProjectionElem.field f) (Ty.instantiate_nil tbl ty)
  | .index _ => rfl
  | .constantIndex _ _ _ => rfl
  | .subslice _ _ _ => rfl
  | .downcast _ _ => rfl
  | .opaqueCast ty => congrArg ProjectionElem.opaqueCast (Ty.instantiate_nil tbl ty)
  | .unwrapUnsafeBinder ty =>
    congrArg ProjectionElem.unwrapUnsafeBinder (Ty.instantiate_nil tbl ty)

/--
Universal identity theorem for `ProjectionElem.instantiateList` on `.nil`.
-/
@[simp]
theorem ProjectionElem.instantiateList_nil
    (tbl : LayoutTable) :
    (elems : List ProjectionElem) →
    ProjectionElem.instantiateList tbl .nil elems = elems
  | .nil => rfl
  | e :: es =>
    congrArg2 List.cons
      (ProjectionElem.instantiate_nil tbl e)
      (ProjectionElem.instantiateList_nil tbl es)

/--
Instantiate a `Place` by instantiating all projection elements in
`p.projection`.
-/
@[reducible]
def Place.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (p : Place) :
    Place :=
  { p with projection := ProjectionElem.instantiateList tbl args p.projection }

/--
Universal identity theorem for `Place.instantiate` on `.nil`.
-/
@[simp]
theorem Place.instantiate_nil (tbl : LayoutTable) (p : Place) :
    Place.instantiate tbl .nil p = p := by
  cases p
  simp [Place.instantiate]

/--
Instantiate an `Operand` by instantiating its underlying `Place` or
`ConstOperand`.
-/
@[reducible]
def Operand.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    Operand → Operand
  | .copy place => .copy (Place.instantiate tbl args place)
  | .move place => .move (Place.instantiate tbl args place)
  | .constant c => .constant (ConstOperand.instantiate tbl args c)

/--
Structurally instantiate a list of `Operand`s.
-/
@[reducible]
def Operand.instantiateList
    (tbl : LayoutTable)
    (args : TypeSubst) :
    List Operand → List Operand
  | .nil => .nil
  | op :: rest =>
    Operand.instantiate tbl args op :: Operand.instantiateList tbl args rest

/--
Universal identity theorem for `Operand.instantiate` on `.nil`.
-/
@[simp]
theorem Operand.instantiate_nil
    (tbl : LayoutTable) :
    (op : Operand) → Operand.instantiate tbl .nil op = op
  | .copy p => congrArg Operand.copy (Place.instantiate_nil tbl p)
  | .move p => congrArg Operand.move (Place.instantiate_nil tbl p)
  | .constant c => congrArg Operand.constant (ConstOperand.instantiate_nil tbl c)

/--
Universal identity theorem for `Operand.instantiateList` on `.nil`.
-/
@[simp]
theorem Operand.instantiateList_nil
    (tbl : LayoutTable) :
    (ops : List Operand) → Operand.instantiateList tbl .nil ops = ops
  | .nil => rfl
  | op :: ops =>
    congrArg2 List.cons
      (Operand.instantiate_nil tbl op)
      (Operand.instantiateList_nil tbl ops)

/--
Instantiate an `AggregateKind` by substituting `Ty` occurrences in `.array` and
`.rawPtr`.
-/
@[reducible]
def AggregateKind.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    AggregateKind → AggregateKind
  | .array elemTy => .array (Ty.instantiate tbl args elemTy)
  | .tuple => .tuple
  | .adt defPath variantIdx activeField => .adt defPath variantIdx activeField
  | .closure defPath => .closure defPath
  | .coroutine defPath => .coroutine defPath
  | .rawPtr pointeeTy mutability =>
    .rawPtr (Ty.instantiate tbl args pointeeTy) mutability

/--
Universal identity theorem for `AggregateKind.instantiate` on `.nil`.
-/
@[simp]
theorem AggregateKind.instantiate_nil
    (tbl : LayoutTable) :
    (k : AggregateKind) → AggregateKind.instantiate tbl .nil k = k
  | .array elemTy => congrArg AggregateKind.array (Ty.instantiate_nil tbl elemTy)
  | .tuple => rfl
  | .adt _ _ _ => rfl
  | .closure _ => rfl
  | .coroutine _ => rfl
  | .rawPtr pointeeTy m =>
    congrArg (AggregateKind.rawPtr · m) (Ty.instantiate_nil tbl pointeeTy)

/--
Instantiate an `Rvalue` across all 15 constructors, substituting all nested
`Operand`, `Place`, `AggregateKind`, and `Ty` occurrences.
-/
@[reducible]
def Rvalue.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    Rvalue → Rvalue
  | .use op => .use (Operand.instantiate tbl args op)
  | .repeat op count => .repeat (Operand.instantiate tbl args op) count
  | .ref borrowKind place =>
    .ref borrowKind (Place.instantiate tbl args place)
  | .threadLocalRef defPath => .threadLocalRef defPath
  | .rawPtr mutability place =>
    .rawPtr mutability (Place.instantiate tbl args place)
  | .len place => .len (Place.instantiate tbl args place)
  | .cast kind op targetTy =>
    .cast kind (Operand.instantiate tbl args op) (Ty.instantiate tbl args targetTy)
  | .binaryOp op lhs rhs =>
    .binaryOp op (Operand.instantiate tbl args lhs) (Operand.instantiate tbl args rhs)
  | .nullaryOp op ty => .nullaryOp op (Ty.instantiate tbl args ty)
  | .unaryOp op val => .unaryOp op (Operand.instantiate tbl args val)
  | .discriminant place => .discriminant (Place.instantiate tbl args place)
  | .aggregate kind operands =>
    .aggregate
      (AggregateKind.instantiate tbl args kind)
      (Operand.instantiateList tbl args operands)
  | .shallowInitBox op contentTy =>
    .shallowInitBox
      (Operand.instantiate tbl args op)
      (Ty.instantiate tbl args contentTy)
  | .copyForDeref place => .copyForDeref (Place.instantiate tbl args place)
  | .wrapUnsafeBinder op targetTy =>
    .wrapUnsafeBinder
      (Operand.instantiate tbl args op)
      (Ty.instantiate tbl args targetTy)

/--
Universal identity theorem for `Rvalue.instantiate` on `.nil`.
-/
@[simp]
theorem Rvalue.instantiate_nil
    (tbl : LayoutTable) :
    (r : Rvalue) → Rvalue.instantiate tbl .nil r = r
  | .use op => congrArg Rvalue.use (Operand.instantiate_nil tbl op)
  | .repeat op count =>
    congrArg (Rvalue.repeat · count) (Operand.instantiate_nil tbl op)
  | .ref bk place => congrArg (Rvalue.ref bk) (Place.instantiate_nil tbl place)
  | .threadLocalRef _ => rfl
  | .rawPtr m place => congrArg (Rvalue.rawPtr m) (Place.instantiate_nil tbl place)
  | .len place => congrArg Rvalue.len (Place.instantiate_nil tbl place)
  | .cast kind op targetTy =>
    congrArg2 (Rvalue.cast kind)
      (Operand.instantiate_nil tbl op)
      (Ty.instantiate_nil tbl targetTy)
  | .binaryOp op lhs rhs =>
    congrArg2 (Rvalue.binaryOp op)
      (Operand.instantiate_nil tbl lhs)
      (Operand.instantiate_nil tbl rhs)
  | .nullaryOp op ty =>
    congrArg (Rvalue.nullaryOp op) (Ty.instantiate_nil tbl ty)
  | .unaryOp op val =>
    congrArg (Rvalue.unaryOp op) (Operand.instantiate_nil tbl val)
  | .discriminant place =>
    congrArg Rvalue.discriminant (Place.instantiate_nil tbl place)
  | .aggregate kind operands =>
    congrArg2 Rvalue.aggregate
      (AggregateKind.instantiate_nil tbl kind)
      (Operand.instantiateList_nil tbl operands)
  | .shallowInitBox op contentTy =>
    congrArg2 Rvalue.shallowInitBox
      (Operand.instantiate_nil tbl op)
      (Ty.instantiate_nil tbl contentTy)
  | .copyForDeref place =>
    congrArg Rvalue.copyForDeref (Place.instantiate_nil tbl place)
  | .wrapUnsafeBinder op targetTy =>
    congrArg2 Rvalue.wrapUnsafeBinder
      (Operand.instantiate_nil tbl op)
      (Ty.instantiate_nil tbl targetTy)

/--
Instantiate a `NonDivergingIntrinsic` by instantiating its operand(s).
-/
@[reducible]
def NonDivergingIntrinsic.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    NonDivergingIntrinsic → NonDivergingIntrinsic
  | .assume op => .assume (Operand.instantiate tbl args op)
  | .copyNonOverlapping src dst count =>
    .copyNonOverlapping
      (Operand.instantiate tbl args src)
      (Operand.instantiate tbl args dst)
      (Operand.instantiate tbl args count)

/--
Universal identity theorem for `NonDivergingIntrinsic.instantiate` on `.nil`.
-/
@[simp]
theorem NonDivergingIntrinsic.instantiate_nil
    (tbl : LayoutTable) :
    (intr : NonDivergingIntrinsic) →
    NonDivergingIntrinsic.instantiate tbl .nil intr = intr
  | .assume op =>
    congrArg NonDivergingIntrinsic.assume (Operand.instantiate_nil tbl op)
  | .copyNonOverlapping src dst count => by
    simp [NonDivergingIntrinsic.instantiate]

/--
Instantiate a `StatementKind` across all 12 constructors.
-/
@[reducible]
def StatementKind.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    StatementKind → StatementKind
  | .assign place rvalue =>
    .assign
      (Place.instantiate tbl args place)
      (Rvalue.instantiate tbl args rvalue)
  | .setDiscriminant place variantIdx =>
    .setDiscriminant (Place.instantiate tbl args place) variantIdx
  | .deinit place => .deinit (Place.instantiate tbl args place)
  | .storageLive local_ => .storageLive local_
  | .storageDead local_ => .storageDead local_
  | .retag kind place => .retag kind (Place.instantiate tbl args place)
  | .placeMention place => .placeMention (Place.instantiate tbl args place)
  | .intrinsic intr =>
    .intrinsic (NonDivergingIntrinsic.instantiate tbl args intr)
  | .constEvalCounter => .constEvalCounter
  | .nop => .nop
  | .coverage => .coverage
  | .backwardIncompatibleDropHint place =>
    .backwardIncompatibleDropHint (Place.instantiate tbl args place)

/--
Universal identity theorem for `StatementKind.instantiate` on `.nil`.
-/
@[simp]
theorem StatementKind.instantiate_nil
    (tbl : LayoutTable) :
    (sk : StatementKind) → StatementKind.instantiate tbl .nil sk = sk
  | .assign place rvalue =>
    congrArg2 StatementKind.assign
      (Place.instantiate_nil tbl place)
      (Rvalue.instantiate_nil tbl rvalue)
  | .setDiscriminant place vIdx =>
    congrArg (StatementKind.setDiscriminant · vIdx)
      (Place.instantiate_nil tbl place)
  | .deinit place => congrArg StatementKind.deinit (Place.instantiate_nil tbl place)
  | .storageLive _ => rfl
  | .storageDead _ => rfl
  | .retag kind place =>
    congrArg (StatementKind.retag kind) (Place.instantiate_nil tbl place)
  | .placeMention place =>
    congrArg StatementKind.placeMention (Place.instantiate_nil tbl place)
  | .intrinsic intr =>
    congrArg StatementKind.intrinsic
      (NonDivergingIntrinsic.instantiate_nil tbl intr)
  | .constEvalCounter => rfl
  | .nop => rfl
  | .coverage => rfl
  | .backwardIncompatibleDropHint place =>
    congrArg StatementKind.backwardIncompatibleDropHint
      (Place.instantiate_nil tbl place)

/--
Instantiate a `Statement`.
-/
@[reducible]
def Statement.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (s : Statement) :
    Statement :=
  { s with kind := StatementKind.instantiate tbl args s.kind }

/--
Structurally instantiate a list of `Statement`s.
-/
@[reducible]
def Statement.instantiateList
    (tbl : LayoutTable)
    (args : TypeSubst) :
    List Statement → List Statement
  | .nil => .nil
  | s :: rest =>
    Statement.instantiate tbl args s :: Statement.instantiateList tbl args rest

/--
Universal identity theorem for `Statement.instantiate` on `.nil`.
-/
@[simp]
theorem Statement.instantiate_nil (tbl : LayoutTable) (s : Statement) :
    Statement.instantiate tbl .nil s = s := by
  cases s
  simp [Statement.instantiate]

/--
Universal identity theorem for `Statement.instantiateList` on `.nil`.
-/
@[simp]
theorem Statement.instantiateList_nil
    (tbl : LayoutTable) :
    (ss : List Statement) → Statement.instantiateList tbl .nil ss = ss
  | .nil => rfl
  | s :: ss =>
    congrArg2 List.cons
      (Statement.instantiate_nil tbl s)
      (Statement.instantiateList_nil tbl ss)

/--
Instantiate a `TerminatorKind` across all 11 constructors.
-/
@[reducible]
def TerminatorKind.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    TerminatorKind → TerminatorKind
  | .goto target => .goto target
  | .switchInt discr targets =>
    .switchInt (Operand.instantiate tbl args discr) targets
  | .unwindResume => .unwindResume
  | .unwindTerminate => .unwindTerminate
  | .return_ => .return_
  | .unreachable => .unreachable
  | .drop place target unwind =>
    .drop (Place.instantiate tbl args place) target unwind
  | .call func callArgs destination target unwind =>
    .call
      (Operand.instantiate tbl args func)
      (Operand.instantiateList tbl args callArgs)
      (Place.instantiate tbl args destination)
      target
      unwind
  | .tailCall func callArgs =>
    .tailCall
      (Operand.instantiate tbl args func)
      (Operand.instantiateList tbl args callArgs)
  | .assert cond expected target unwind =>
    .assert (Operand.instantiate tbl args cond) expected target unwind
  | .inlineAsm template targets unwind =>
    .inlineAsm template targets unwind

/--
Universal identity theorem for `TerminatorKind.instantiate` on `.nil`.
-/
@[simp]
theorem TerminatorKind.instantiate_nil
    (tbl : LayoutTable) :
    (tk : TerminatorKind) → TerminatorKind.instantiate tbl .nil tk = tk
  | .goto _ => rfl
  | .switchInt discr targets =>
    congrArg (TerminatorKind.switchInt · targets)
      (Operand.instantiate_nil tbl discr)
  | .unwindResume => rfl
  | .unwindTerminate => rfl
  | .return_ => rfl
  | .unreachable => rfl
  | .drop place target unwind =>
    congrArg (TerminatorKind.drop · target unwind)
      (Place.instantiate_nil tbl place)
  | .call func callArgs destination target unwind => by
    simp [TerminatorKind.instantiate]
  | .tailCall func callArgs =>
    congrArg2 TerminatorKind.tailCall
      (Operand.instantiate_nil tbl func)
      (Operand.instantiateList_nil tbl callArgs)
  | .assert cond expected target unwind =>
    congrArg (TerminatorKind.assert · expected target unwind)
      (Operand.instantiate_nil tbl cond)
  | .inlineAsm _ _ _ => rfl

/--
Instantiate a `Terminator`.
-/
@[reducible]
def Terminator.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (t : Terminator) :
    Terminator :=
  { t with kind := TerminatorKind.instantiate tbl args t.kind }

/--
Universal identity theorem for `Terminator.instantiate` on `.nil`.
-/
@[simp]
theorem Terminator.instantiate_nil (tbl : LayoutTable) (t : Terminator) :
    Terminator.instantiate tbl .nil t = t := by
  cases t
  simp [Terminator.instantiate]

/--
Instantiate a `BasicBlockData` by structurally instantiating its `statements`
and `terminator`.
-/
@[reducible]
def BasicBlockData.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (b : BasicBlockData) :
    BasicBlockData :=
  { b with
    statements := Statement.instantiateList tbl args b.statements
    terminator := Terminator.instantiate tbl args b.terminator }

/--
Structurally instantiate a list of `BasicBlockData` blocks.
-/
@[reducible]
def BasicBlockData.instantiateList
    (tbl : LayoutTable)
    (args : TypeSubst) :
    List BasicBlockData → List BasicBlockData
  | .nil => .nil
  | b :: rest =>
    BasicBlockData.instantiate tbl args b ::
      BasicBlockData.instantiateList tbl args rest

/--
Universal identity theorem for `BasicBlockData.instantiate` on `.nil`.
-/
@[simp]
theorem BasicBlockData.instantiate_nil
    (tbl : LayoutTable)
    (b : BasicBlockData) :
    BasicBlockData.instantiate tbl .nil b = b := by
  cases b
  simp [BasicBlockData.instantiate]

/--
Universal identity theorem for `BasicBlockData.instantiateList` on `.nil`.
-/
@[simp]
theorem BasicBlockData.instantiateList_nil
    (tbl : LayoutTable) :
    (bs : List BasicBlockData) →
    BasicBlockData.instantiateList tbl .nil bs = bs
  | .nil => rfl
  | b :: bs =>
    congrArg2 List.cons
      (BasicBlockData.instantiate_nil tbl b)
      (BasicBlockData.instantiateList_nil tbl bs)

/--
Preservation of non-emptiness for `BasicBlockData.instantiateList`.
-/
@[simp]
theorem BasicBlockData.instantiateList_nonEmpty
    (tbl : LayoutTable)
    (args : TypeSubst) :
    (bs : List BasicBlockData) →
    (match BasicBlockData.instantiateList tbl args bs with
     | .nil => false
     | _ :: _ => true) =
    (match bs with
     | .nil => false
     | _ :: _ => true)
  | .nil => rfl
  | _ :: _ => rfl

/--
Preservation of length for `BasicBlockData.instantiateList`.
-/
@[simp]
theorem BasicBlockData.instantiateList_length
    (tbl : LayoutTable)
    (args : TypeSubst) :
    (bs : List BasicBlockData) →
    length (BasicBlockData.instantiateList tbl args bs) = length bs
  | .nil => rfl
  | _ :: bs =>
    congrArg Nat.succ (BasicBlockData.instantiateList_length tbl args bs)

/--
Instantiate a `LocalDecl` by instantiating its `ty`.
-/
@[reducible]
def LocalDecl.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (l : LocalDecl) :
    LocalDecl :=
  { l with ty := Ty.instantiate tbl args l.ty }

/--
Structurally instantiate a list of `LocalDecl`s.
-/
@[reducible]
def LocalDecl.instantiateList
    (tbl : LayoutTable)
    (args : TypeSubst) :
    List LocalDecl → List LocalDecl
  | .nil => .nil
  | d :: rest =>
    LocalDecl.instantiate tbl args d ::
      LocalDecl.instantiateList tbl args rest

/--
Universal identity theorem for `LocalDecl.instantiate` on `.nil`.
-/
@[simp]
theorem LocalDecl.instantiate_nil (tbl : LayoutTable) (l : LocalDecl) :
    LocalDecl.instantiate tbl .nil l = l := by
  cases l
  simp [LocalDecl.instantiate]

/--
Universal identity theorem for `LocalDecl.instantiateList` on `.nil`.
-/
@[simp]
theorem LocalDecl.instantiateList_nil
    (tbl : LayoutTable) :
    (ds : List LocalDecl) → LocalDecl.instantiateList tbl .nil ds = ds
  | .nil => rfl
  | d :: ds =>
    congrArg2 List.cons
      (LocalDecl.instantiate_nil tbl d)
      (LocalDecl.instantiateList_nil tbl ds)

/--
Preservation of non-emptiness for `LocalDecl.instantiateList`.
-/
@[simp]
theorem LocalDecl.instantiateList_nonEmpty
    (tbl : LayoutTable)
    (args : TypeSubst) :
    (ds : List LocalDecl) →
    (match LocalDecl.instantiateList tbl args ds with
     | .nil => false
     | _ :: _ => true) =
    (match ds with
     | .nil => false
     | _ :: _ => true)
  | .nil => rfl
  | _ :: _ => rfl

/--
Preservation of length for `LocalDecl.instantiateList`.
-/
@[simp]
theorem LocalDecl.instantiateList_length
    (tbl : LayoutTable)
    (args : TypeSubst) :
    (ds : List LocalDecl) →
    length (LocalDecl.instantiateList tbl args ds) = length ds
  | .nil => rfl
  | _ :: ds =>
    congrArg Nat.succ (LocalDecl.instantiateList_length tbl args ds)

/--
Test whether any non-parametric `LocalDecl` in `decls` uses layout table index
`targetIdx`.
-/
@[reducible]
def hasNonParamDeclAtIdx
    (args : TypeSubst)
    (targetIdx : Nat) :
    List LocalDecl → Bool
  | .nil => false
  | d :: rest =>
    let isNonParamHere :=
      Bool.and
        (Nat.beq d.ty.layoutIdx targetIdx)
        (Bool.not (RigidTy.hasSubstParam args d.ty.kind))
    match isNonParamHere with
    | true => true
    | false => hasNonParamDeclAtIdx args targetIdx rest

/--
Test whether any `LocalDecl` in `decls` whose `ty.layoutIdx` equals `targetIdx`
has a compound parametric `RigidTy` under `args`.
-/
@[reducible]
def hasCompoundParamDeclAtIdx
    (args : TypeSubst)
    (targetIdx : Nat) :
    List LocalDecl → Bool
  | .nil => false
  | d :: rest =>
    let isCompoundHere :=
      Bool.and
        (Nat.beq d.ty.layoutIdx targetIdx)
        (RigidTy.isCompoundSubstParam args d.ty.kind)
    match isCompoundHere with
    | true => true
    | false => hasCompoundParamDeclAtIdx args targetIdx rest

/--
Substitute `LayoutTable` entries referenced exclusively by `.param idx _`
`LocalDecl`s (where no non-parametric or compound parametric `LocalDecl` shares
`d.ty.layoutIdx`).
-/
@[reducible]
def substituteDeclParamLayoutsAux
    (allDecls : List LocalDecl)
    (args : TypeSubst) :
    List LocalDecl → List TypeLayout → List TypeLayout
  | .nil, entries => entries
  | d :: rest, entries =>
    let entries' :=
      match d.ty.kind with
      | .param idx _ =>
        match TypeSubst.lookup args idx with
        | .none => entries
        | .some (_, paramLayout) =>
          match
            Bool.or
              (hasNonParamDeclAtIdx args d.ty.layoutIdx allDecls)
              (hasCompoundParamDeclAtIdx args d.ty.layoutIdx allDecls)
          with
          | true => entries
          | false => setTypeLayoutAt entries d.ty.layoutIdx paramLayout
      | _ => entries
    substituteDeclParamLayoutsAux allDecls args rest entries'

/--
Recompute `LayoutTable` entries referenced by compound parametric `LocalDecl`s
(such as `(T, u32)`, `[T; N]`, `&T`, `*const T`, `Option<T>`, `Wrapper<T>`)
whose layout slot `d.ty.layoutIdx` is dedicated to that parametric type.
-/
@[reducible]
def recomputeDeclCompoundLayoutsAux
    (origTbl : LayoutTable)
    (allDecls : List LocalDecl)
    (args : TypeSubst) :
    List LocalDecl → List TypeLayout → List TypeLayout
  | .nil, entries => entries
  | d :: rest, entries =>
    let entries' :=
      match RigidTy.isCompoundSubstParam args d.ty.kind with
      | false => entries
      | true =>
        match hasNonParamDeclAtIdx args d.ty.layoutIdx allDecls with
        | true => entries
        | false =>
          match
            RigidTy.computeLayout
              origTbl.pointerBits
              entries
              args
              (LayoutTable.lookup origTbl d.ty.layoutIdx)
              d.ty.kind
          with
          | .some newLayout => setTypeLayoutAt entries d.ty.layoutIdx newLayout
          | .none => entries
    recomputeDeclCompoundLayoutsAux origTbl allDecls args rest entries'

/--
Instantiate `tbl : LayoutTable` for a `CapturedMir` body with `localDecls` and
`args : TypeSubst`, combining `LayoutTable.instantiate` with local parameter
slot substitution and compound local layout recomputation.
-/
@[reducible]
def LayoutTable.instantiateForDecls
    (tbl : LayoutTable)
    (localDecls : List LocalDecl)
    (args : TypeSubst) :
    LayoutTable :=
  match args with
  | .nil => LayoutTable.instantiate tbl .nil
  | _ :: _ =>
    let base := LayoutTable.instantiate tbl args
    let entriesWithParams :=
      substituteDeclParamLayoutsAux localDecls args localDecls base.entries
    { base with
      entries :=
        recomputeDeclCompoundLayoutsAux tbl localDecls args localDecls entriesWithParams }

/--
Universal identity theorem for `LayoutTable.instantiateForDecls` on `.nil`.
-/
@[simp]
theorem LayoutTable.instantiateForDecls_nil
    (tbl : LayoutTable)
    (localDecls : List LocalDecl) :
    LayoutTable.instantiateForDecls tbl localDecls .nil = tbl :=
  LayoutTable.instantiate_nil tbl

/--
Determine the `AbiPassMode` for an instantiated `TypeLayout`, preserving `origMode`
unless the instantiated layout is zero-sized (`.ignore`), a scalar (`.direct`),
or a scalar pair (`.pair`).
-/
@[reducible]
def ArgAbi.recomputeMode (origMode : AbiPassMode) (l : TypeLayout) : AbiPassMode :=
  match Nat.beq l.size.bytes 0 with
  | true => .ignore
  | false =>
    match l.backendRepr with
    | .scalar _ => .direct
    | .scalarPair _ _ => .pair
    | .memory =>
      match origMode with
      | .ignore => .indirect
      | m => m

/--
Instantiate an `ArgAbi` corresponding to optional local declaration `declOpt`
when `declOpt` has a parametric type under `args`.
-/
@[reducible]
def ArgAbi.instantiateForDecl
    (origTbl : LayoutTable)
    (instTbl : LayoutTable)
    (args : TypeSubst)
    (declOpt : Option LocalDecl)
    (abi : ArgAbi) :
    ArgAbi :=
  match declOpt with
  | .none => abi
  | .some decl =>
    match RigidTy.hasSubstParam args decl.ty.kind with
    | false => abi
    | true =>
      let instTy := Ty.instantiate origTbl args decl.ty
      let layoutOpt : Option TypeLayout :=
        match LayoutTable.lookup instTbl instTy.layoutIdx with
        | .some l => .some l
        | .none =>
          RigidTy.computeLayout
            origTbl.pointerBits
            instTbl.entries
            args
            (LayoutTable.lookup origTbl decl.ty.layoutIdx)
            decl.ty.kind
      match layoutOpt with
      | .none => abi
      | .some newLayout =>
        { layout := newLayout
          mode := ArgAbi.recomputeMode abi.mode newLayout }

/--
Structurally instantiate a list of `ArgAbi` descriptors against argument locals
`1 ..= args.length`.
-/
@[reducible]
def ArgAbi.instantiateListForDecls
    (origTbl : LayoutTable)
    (instTbl : LayoutTable)
    (args : TypeSubst) :
    List LocalDecl → List ArgAbi → List ArgAbi
  | _, .nil => .nil
  | .nil, a :: aRest =>
    ArgAbi.instantiateForDecl origTbl instTbl args .none a ::
      ArgAbi.instantiateListForDecls origTbl instTbl args .nil aRest
  | d :: dRest, a :: aRest =>
    ArgAbi.instantiateForDecl origTbl instTbl args (.some d) a ::
      ArgAbi.instantiateListForDecls origTbl instTbl args dRest aRest

/--
Universal identity theorem for `ArgAbi.instantiateForDecl` on `.nil`.
-/
@[simp]
theorem ArgAbi.instantiateForDecl_nil
    (origTbl instTbl : LayoutTable)
    (declOpt : Option LocalDecl)
    (abi : ArgAbi) :
    ArgAbi.instantiateForDecl origTbl instTbl .nil declOpt abi = abi := by
  cases declOpt with
  | none => rfl
  | some decl =>
    simp [ArgAbi.instantiateForDecl, RigidTy.hasSubstParam_nil]

/--
Universal identity theorem for `ArgAbi.instantiateListForDecls` on `.nil`.
-/
@[simp]
theorem ArgAbi.instantiateListForDecls_nil
    (origTbl instTbl : LayoutTable) :
    (decls : List LocalDecl) →
    (abis : List ArgAbi) →
    ArgAbi.instantiateListForDecls origTbl instTbl .nil decls abis = abis
  | _, .nil => rfl
  | .nil, a :: aRest =>
    congrArg2 List.cons
      (ArgAbi.instantiateForDecl_nil origTbl instTbl .none a)
      (ArgAbi.instantiateListForDecls_nil origTbl instTbl .nil aRest)
  | d :: dRest, a :: aRest =>
    congrArg2 List.cons
      (ArgAbi.instantiateForDecl_nil origTbl instTbl (.some d) a)
      (ArgAbi.instantiateListForDecls_nil origTbl instTbl dRest aRest)

/--
Instantiate a `FnAbi` against `localDecls` (`_0` return local and `_1..`
argument locals).
-/
@[reducible]
def FnAbi.instantiate
    (localDecls : List LocalDecl)
    (origTbl : LayoutTable)
    (instTbl : LayoutTable)
    (args : TypeSubst)
    (abi : FnAbi) :
    FnAbi :=
  let retDeclOpt :=
    match localDecls with
    | .nil => .none
    | d0 :: _ => .some d0
  let argDecls :=
    match localDecls with
    | .nil => .nil
    | _ :: dRest => dRest
  { abi with
    args := ArgAbi.instantiateListForDecls origTbl instTbl args argDecls abi.args
    ret := ArgAbi.instantiateForDecl origTbl instTbl args retDeclOpt abi.ret }

/--
Universal identity theorem for `FnAbi.instantiate` on `.nil`.
-/
@[simp]
theorem FnAbi.instantiate_nil
    (localDecls : List LocalDecl)
    (origTbl instTbl : LayoutTable)
    (abi : FnAbi) :
    FnAbi.instantiate localDecls origTbl instTbl .nil abi = abi := by
  cases abi
  simp [FnAbi.instantiate]

/--
Drop the first `n` generic parameter declarations from a `List GenericParamDef`.
-/
@[reducible]
def dropGenericParams : Nat → List GenericParamDef → List GenericParamDef
  | .zero, ps => ps
  | _, .nil => .nil
  | .succ k, _ :: ps => dropGenericParams k ps

/--
Instantiate a polymorphic `CapturedMir` body with concrete `(RigidTy × TypeLayout)`
arguments `args : TypeSubst`, substituting `.param idx _` across all `localDecls`,
`basicBlocks` (statements, rvalues, operands, places/projections, constants,
terminators), `fnAbi`, `layouts`, and `traitImpls`, and recomputing dependent
`TypeLayout` entries.
-/
@[reducible]
def CapturedMir.instantiate (m : CapturedMir) (args : TypeSubst) : CapturedMir :=
  let tbl' := LayoutTable.instantiateForDecls m.layouts m.localDecls args
  let substLen := TypeSubst.length args
  { m with
    localDecls := LocalDecl.instantiateList m.layouts args m.localDecls
    basicBlocks := BasicBlockData.instantiateList m.layouts args m.basicBlocks
    fnAbi := FnAbi.instantiate m.localDecls m.layouts tbl' args m.fnAbi
    layouts := tbl'
    typeParamCount := Nat.sub m.typeParamCount substLen
    genericParams := dropGenericParams substLen m.genericParams
    traitImpls := TraitImplEntry.instantiateList args m.traitImpls }

/--
Universal identity theorem `CapturedMir.instantiate_nil` over arbitrary
`m : CapturedMir`.
-/
@[simp]
theorem CapturedMir.instantiate_nil (m : CapturedMir) :
    m.instantiate .nil = m := by
  cases m
  dsimp [CapturedMir.instantiate, TypeSubst.length, dropGenericParams]
  rw [LocalDecl.instantiateList_nil,
      BasicBlockData.instantiateList_nil,
      FnAbi.instantiate_nil,
      LayoutTable.instantiateForDecls_nil,
      TraitImplEntry.instantiateList_nil]

/--
Universal identity theorem `CapturedMir.instantiate_empty_id` over arbitrary
`m : CapturedMir`.
-/
@[simp]
theorem CapturedMir.instantiate_empty_id (m : CapturedMir) :
    m.instantiate .nil = m :=
  CapturedMir.instantiate_nil m

/--
Universal identity theorem `instantiate_nil` over arbitrary `m : CapturedMir`.
-/
@[simp]
theorem instantiate_nil (m : CapturedMir) : m.instantiate .nil = m :=
  CapturedMir.instantiate_nil m

/--
Universal identity theorem `instantiate_empty_id` over arbitrary
`m : CapturedMir`.
-/
@[simp]
theorem instantiate_empty_id (m : CapturedMir) : m.instantiate .nil = m :=
  CapturedMir.instantiate_nil m

/--
`CapturedMir.instantiate` preserves `defPath` for all `m` and `args`.
-/
@[simp]
theorem CapturedMir.instantiate_defPath
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).defPath = m.defPath :=
  rfl

/--
`CapturedMir.instantiate` preserves `phase` for all `m` and `args`.
-/
@[simp]
theorem CapturedMir.instantiate_phase
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).phase = m.phase :=
  rfl

/--
`CapturedMir.instantiate` preserves `role` for all `m` and `args`.
-/
@[simp]
theorem CapturedMir.instantiate_role
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).role = m.role :=
  rfl

/--
`CapturedMir.instantiate` preserves `argCount` for all `m` and `args`.
-/
@[simp]
theorem CapturedMir.instantiate_argCount
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).argCount = m.argCount :=
  rfl

/--
`CapturedMir.instantiate` preserves `allocations` for all `m` and `args`.
-/
@[simp]
theorem CapturedMir.instantiate_allocations
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).allocations = m.allocations :=
  rfl

/--
`CapturedMir.instantiate` decrements `typeParamCount` by `TypeSubst.length args`.
-/
@[simp]
theorem CapturedMir.instantiate_typeParamCount
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).typeParamCount =
      Nat.sub m.typeParamCount (TypeSubst.length args) :=
  rfl

/--
`CapturedMir.instantiate` preserves `CapturedMir.isRuntimePostCleanup` for all
`m : CapturedMir` and `args : TypeSubst`.
-/
@[simp]
theorem CapturedMir.instantiate_isRuntimePostCleanup
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).isRuntimePostCleanup = m.isRuntimePostCleanup :=
  rfl

/--
`CapturedMir.instantiate` preserves `localDecls.length` for all
`m : CapturedMir` and `args : TypeSubst`.
-/
@[simp]
theorem CapturedMir.instantiate_localDecls_length
    (m : CapturedMir)
    (args : TypeSubst) :
    length (m.instantiate args).localDecls = length m.localDecls :=
  LocalDecl.instantiateList_length m.layouts args m.localDecls

/--
`CapturedMir.instantiate` preserves `basicBlocks.length` for all
`m : CapturedMir` and `args : TypeSubst`.
-/
@[simp]
theorem CapturedMir.instantiate_basicBlocks_length
    (m : CapturedMir)
    (args : TypeSubst) :
    length (m.instantiate args).basicBlocks = length m.basicBlocks :=
  BasicBlockData.instantiateList_length m.layouts args m.basicBlocks

/--
Non-vacuous universal well-formedness preservation theorem: instantiating any
`m : CapturedMir` with any `args : TypeSubst` preserves `CapturedMir.wellFormed`.
-/
@[simp]
theorem CapturedMir.instantiate_wellFormed
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).wellFormed = m.wellFormed := by
  dsimp [CapturedMir.wellFormed, CapturedMir.instantiate,
    CapturedMir.isRuntimePostCleanup]
  rw [LocalDecl.instantiateList_nonEmpty m.layouts args m.localDecls]
  rw [LocalDecl.instantiateList_length m.layouts args m.localDecls]
  rw [BasicBlockData.instantiateList_nonEmpty m.layouts args m.basicBlocks]

/--
Non-vacuous universal well-formedness preservation theorem (`instantiate_wellFormed`).
-/
@[simp]
theorem instantiate_wellFormed
    (m : CapturedMir)
    (args : TypeSubst) :
    (m.instantiate args).wellFormed = m.wellFormed :=
  CapturedMir.instantiate_wellFormed m args

end Trusted.Rustc.V2026_08_01.MirAst
