//! Deterministic Lean 4 source emitter for captured MIR bodies and compiler
//! layouts (`Mir/<Item>.lean`).
//!
//! Each emitted module imports `Trusted`, opens the
//! dialect namespace (`Trusted.Rustc.V2026_06_01`), and pairs human-readable
//! MIR/layout line comments with 1-to-1 `CapturedMir` and `LayoutTable`
//! constructors matching `trusted/lean/Trusted/Rustc/V2026_06_01/`.

use crate::manifest::MIR_DIALECT_V2026_06_01;

/// Byte size corresponding to `Trusted.Rustc.V2026_06_01.Layout.Size`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrSize {
    /// Size in bytes (`0` for zero-sized types).
    pub bytes: u64,
}

/// Byte alignment corresponding to `Trusted.Rustc.V2026_06_01.Layout.Align`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrAlign {
    /// Alignment in bytes (always a positive power of two).
    pub bytes: u64,
}

/// Inclusive wrapping validity range `[start, end_]` corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.WrappingRange`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrWrappingRange {
    /// Inclusive lower bound of the valid scalar bit pattern range.
    pub start: u128,
    /// Inclusive upper bound of the valid scalar bit pattern range.
    pub end_: u128,
}

/// Machine scalar primitive kind corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.PrimitiveKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrPrimitiveKind {
    /// Integer scalar with bit width (`8`, `16`, `32`, `64`, or `128`) and
    /// signedness.
    Int { bits: u64, signed: bool },
    /// IEEE 754 floating-point scalar with bit width (`16`, `32`, `64`, `128`).
    Float { bits: u64 },
    /// Machine pointer or fat-pointer component in the given address space.
    Pointer { address_space: u32 },
}

/// Scalar layout corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.ScalarLayout`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrScalarLayout {
    /// Initialized scalar whose bit pattern must lie within `valid_range`.
    Initialized {
        value: IrPrimitiveKind,
        valid_range: IrWrappingRange,
    },
    /// Union scalar that may contain uninitialized bytes.
    Union { value: IrPrimitiveKind },
}

/// Field offset placement corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.FieldsShape`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrFieldsShape {
    /// Scalar primitive with no subfields.
    Primitive,
    /// Union whose `count` fields all start at byte offset `0`.
    Union { count: usize },
    /// Homogeneous array or slice element layout with fixed `stride` and
    /// `count`.
    Array { stride: IrSize, count: u64 },
    /// Arbitrary struct or tuple field offsets indexed by source field order.
    Arbitrary {
        offsets: Vec<IrSize>,
        memory_index: Vec<usize>,
    },
}

/// Variant discrimination layout corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.VariantsShape`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrVariantsShape {
    /// Uninhabited type with zero variants.
    Empty,
    /// Single inhabited variant at `index`.
    Single { index: usize },
    /// Multi-variant enum discriminated by `tag` at `tag_field`.
    Multiple {
        tag: IrScalarLayout,
        tag_field: usize,
        variants: Vec<IrFieldsShape>,
    },
}

/// Backend representation corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.BackendRepr`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrBackendRepr {
    /// Single machine scalar register.
    Scalar(IrScalarLayout),
    /// Pair of machine scalar registers (e.g., fat pointer or `(u64, u64)`).
    ScalarPair(IrScalarLayout, IrScalarLayout),
    /// Aggregate stored in memory.
    Memory,
}

/// Complete layout record for a single monomorphized Rust type corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.TypeLayout`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrTypeLayout {
    /// Total byte size of the type.
    pub size: IrSize,
    /// Required ABI byte alignment of the type.
    pub align: IrAlign,
    /// Backend register vs. memory representation.
    pub backend_repr: IrBackendRepr,
    /// Top-level field offsets.
    pub fields: IrFieldsShape,
    /// Enum variant discrimination layout.
    pub variants: IrVariantsShape,
    /// True when `rustc` proves the type is uninhabited
    /// (`abi.is_uninhabited()`).
    pub is_uninhabited: bool,
    /// Optional per-field `LayoutTable` indices in source field order for
    /// single-variant `FieldsShape::Arbitrary` aggregates (`TypeLayout.fieldLayouts`).
    pub field_layouts: Vec<usize>,
}

/// Call-site argument passing mode corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.AbiPassMode`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrAbiPassMode {
    /// Zero-sized argument omitted from the call convention.
    Ignore,
    /// Passed directly by value in a single scalar or vector register.
    Direct,
    /// Passed in a pair of scalar registers.
    Pair,
    /// Passed indirectly by pointer in memory.
    Indirect,
}

/// Per-argument or return-value ABI descriptor corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.ArgAbi`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrArgAbi {
    /// Computed layout of the argument or return place.
    pub layout: IrTypeLayout,
    /// Calling convention passing mode.
    pub mode: IrAbiPassMode,
}

/// Calling convention tag corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.CallConv`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrCallConv {
    /// Standard Rust calling convention (`extern "Rust"`).
    Rust,
    /// Platform C calling convention (`extern "C"`).
    C,
    /// Compiler intrinsic pseudo-calling convention
    /// (`extern "rust-intrinsic"`).
    RustIntrinsic,
    /// Any other target-specific calling convention name.
    Other(String),
}

/// Function signature ABI corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.FnAbi`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrFnAbi {
    /// Argument ABI descriptors in declaration order.
    pub args: Vec<IrArgAbi>,
    /// Return place ABI descriptor.
    pub ret: IrArgAbi,
    /// Calling convention.
    pub conv: IrCallConv,
    /// Whether unwinding across calls to this function is permitted.
    pub can_unwind: bool,
}

/// Target layout table indexed by `IrTy::layout_idx`, corresponding to
/// `Trusted.Rustc.V2026_06_01.Layout.LayoutTable`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrLayoutTable {
    /// Target pointer width in bits (e.g., `64`).
    pub pointer_bits: u64,
    /// True if target endianness is little-endian.
    pub is_little_endian: bool,
    /// Deduplicated `TypeLayout` table indexed by `layout_idx`.
    pub entries: Vec<IrTypeLayout>,
}

/// Unsigned integer width corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.UintTy`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrUintTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

/// Signed integer width corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.IntTy`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrIntTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

/// IEEE 754 floating-point width corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.FloatTy`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrFloatTy {
    F16,
    F32,
    F64,
    F128,
}

/// Mutability flag corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Mutability`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrMutability {
    /// Shared / immutable (`Mut::Not`).
    Not,
    /// Exclusive / mutable (`Mut::Mut`).
    Mut,
}

/// Function pointer safety tag corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Safety`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrSafety {
    Safe,
    Unsafe,
}

/// Monomorphized post-cleanup MIR type structure corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.RigidTy`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrRigidTy {
    Bool,
    Char,
    Int(IrIntTy),
    Uint(IrUintTy),
    Float(IrFloatTy),
    Never,
    Str,
    Tuple(Vec<IrRigidTy>),
    Array(Box<IrRigidTy>, u64),
    Slice(Box<IrRigidTy>),
    Ref(IrMutability, Box<IrRigidTy>),
    RawPtr(IrMutability, Box<IrRigidTy>),
    Adt(String, Vec<IrRigidTy>),
    FnDef(String, Vec<IrRigidTy>),
    FnPtr(Vec<IrRigidTy>, Box<IrRigidTy>, IrSafety, IrCallConv),
    Closure(String, Vec<IrRigidTy>),
    Dynamic(String),
    Foreign(String),
    Other(String),
}

/// Paired structural type and index into `IrLayoutTable::entries`,
/// corresponding to `Trusted.Rustc.V2026_06_01.MirAst.Ty`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrTy {
    /// Structural type constructor.
    pub kind: IrRigidTy,
    /// Index into `IrCapturedMir::layouts.entries`.
    pub layout_idx: usize,
}

/// Single step in a place projection path corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrProjectionElem {
    /// Dereference a reference, raw pointer, or `Box` (`*p`).
    Deref,
    /// Project field `idx` with its monomorphized type (`p.idx`).
    Field(usize, IrTy),
    /// Index into an array or slice using the value in local `idx` (`p[_idx]`).
    Index(usize),
    /// Constant pattern-matching index into an array or slice.
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    /// Subslice projection (`p[from..to]`).
    Subslice {
        from_idx: u64,
        to_idx: u64,
        from_end: bool,
    },
    /// Narrow an enum place to variant `variant_idx` (`(p as Variant)`).
    Downcast(Option<String>, usize),
    /// Post-cleanup opaque cast projection.
    OpaqueCast(IrTy),
    /// Unwrap an unsafe binder type (`ProjectionElem::UnwrapUnsafeBinder`).
    UnwrapUnsafeBinder(IrTy),
}

/// Memory location expression rooted at a local variable slot corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Place`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrPlace {
    /// Root local variable index (`_0` is the return place).
    pub local_: usize,
    /// Ordered sequence of projections applied left-to-right to `local_`.
    pub projection: Vec<IrProjectionElem>,
}

/// Raw bit-pattern integer scalar constant corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.ScalarInt`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrScalarInt {
    /// Unsigned bit pattern (`0 .. 2^(8 * size_bytes)`).
    pub bits: u128,
    /// Width of the scalar in bytes (`1`, `2`, `4`, `8`, or `16`).
    pub size_bytes: u64,
}

/// Pointer constant carrying allocation provenance and byte offset,
/// corresponding to `Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrProvenancePtr {
    /// Referenced global or constant allocation identifier.
    pub alloc_id: u64,
    /// Byte offset within `alloc_id`.
    pub offset_bytes: u64,
}

/// Evaluated constant scalar corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.ConstScalar`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrConstScalar {
    /// Pure integer/bool/char/float bit-pattern scalar.
    Int(IrScalarInt),
    /// Pointer scalar with provenance and pointer byte width.
    Ptr(IrProvenancePtr, u64),
}

/// Evaluated constant value in post-cleanup MIR corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.ConstValue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrConstValue {
    /// Constant of a zero-sized type (e.g., `()` or a `FnDef` token).
    ZeroSized,
    /// Single evaluated scalar value.
    Scalar(IrConstScalar),
    /// Wide pointer slice constant (`data` scalar plus `meta` element count).
    Slice { data: IrConstScalar, meta: u64 },
    /// Aggregate constant stored in global allocation `alloc_id` at byte offset
    /// `offset_bytes`.
    Indirect { alloc_id: u64, offset_bytes: u64 },
    /// Unevaluated or symbolic constant item path.
    Unevaluated(String),
}

/// Typed constant operand corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.ConstOperand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrConstOperand {
    /// Type of the constant.
    pub ty: IrTy,
    /// Evaluated constant payload.
    pub val: IrConstValue,
}

/// Rvalue and terminator operand corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Operand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrOperand {
    /// Read the value at `place` without deinitializing it.
    Copy(IrPlace),
    /// Read the value at `place` and leave `place` uninitialized (`Move`).
    Move(IrPlace),
    /// Materialize a compile-time constant.
    Constant(IrConstOperand),
}

/// Binary arithmetic, bitwise, comparison, and pointer-offset operators
/// corresponding to `Trusted.Rustc.V2026_06_01.MirAst.BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrBinOp {
    Add,
    AddUnchecked,
    AddWithOverflow,
    Sub,
    SubUnchecked,
    SubWithOverflow,
    Mul,
    MulUnchecked,
    MulWithOverflow,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    ShlUnchecked,
    Shr,
    ShrUnchecked,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Cmp,
    Offset,
}

/// Unary operators corresponding to `Trusted.Rustc.V2026_06_01.MirAst.UnOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrUnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Nullary compile-time operators corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.NullOp`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrNullOp {
    SizeOf,
    AlignOf,
    OffsetOf(Vec<(usize, usize)>),
    UbChecks,
    ContractChecks,
}

/// Borrow flavor for `IrRvalue::Ref` corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.BorrowKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrBorrowKind {
    /// Shared borrow (`&place`).
    Shared,
    /// Mutable borrow (`&mut place`), optionally allowing two-phase borrows.
    Mut { allow_two_phase: bool },
}

/// Explicit cast flavor for `IrRvalue::Cast` corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.CastKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrCastKind {
    PointerExposeProvenance,
    PointerWithExposedProvenance,
    PointerCoercion(String),
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
    Subtype,
}

/// Aggregate construction flavor for `IrRvalue::Aggregate` corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.AggregateKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrAggregateKind {
    /// Fixed-size array literal `[op_0, ..., op_n]` with element type.
    Array(IrTy),
    /// Tuple literal `(op_0, ..., op_n)`.
    Tuple,
    /// Struct, enum variant, or union construction (`def_path`, `variant_idx`,
    /// optional active union field).
    Adt(String, usize, Option<usize>),
    /// Closure environment aggregate.
    Closure(String),
    /// Coroutine state aggregate.
    Coroutine(String),
    /// Raw pointer construction from thin pointer and metadata.
    RawPtr(IrTy, IrMutability),
}

/// Right-hand-side computation assigned to a `Place` in
/// `IrStatementKind::Assign`, corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrRvalue {
    Use(IrOperand),
    Repeat(IrOperand, u64),
    Ref(IrBorrowKind, IrPlace),
    ThreadLocalRef(String),
    RawPtr(IrMutability, IrPlace),
    Len(IrPlace),
    Cast(IrCastKind, IrOperand, IrTy),
    BinaryOp(IrBinOp, IrOperand, IrOperand),
    NullaryOp(IrNullOp, IrTy),
    UnaryOp(IrUnOp, IrOperand),
    Discriminant(IrPlace),
    Aggregate(IrAggregateKind, Vec<IrOperand>),
    ShallowInitBox(IrOperand, IrTy),
    CopyForDeref(IrPlace),
    WrapUnsafeBinder(IrOperand, IrTy),
}

/// Non-diverging intrinsics lowered directly as MIR statements, corresponding
/// to `Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrNonDivergingIntrinsic {
    /// `core::intrinsics::assume(op)`: UB if `op` evaluates to `false`.
    Assume(IrOperand),
    /// `core::intrinsics::copy_nonoverlapping(src, dst, count)`.
    CopyNonOverlapping {
        src: IrOperand,
        dst: IrOperand,
        count: IrOperand,
    },
}

/// Stacked Borrows / Tree Borrows retag kind corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.RetagKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrRetagKind {
    FnEntry,
    TwoPhase,
    Raw,
    Default,
}

/// Straight-line statement inside a basic block corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.StatementKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrStatementKind {
    Assign(IrPlace, IrRvalue),
    SetDiscriminant(IrPlace, usize),
    Deinit(IrPlace),
    StorageLive(usize),
    StorageDead(usize),
    Retag(IrRetagKind, IrPlace),
    PlaceMention(IrPlace),
    Intrinsic(IrNonDivergingIntrinsic),
    Coverage,
    ConstEvalCounter,
    BackwardIncompatibleDropHint(IrPlace),
    Nop,
}

/// Statement paired with its human-readable source span string corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.Statement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrStatement {
    pub kind: IrStatementKind,
    pub span: String,
    /// Optional human-readable statement comment (e.g., `_0 = const 42_u32`).
    pub comment: Option<String>,
}

/// Branch targets for `IrTerminatorKind::SwitchInt` corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.SwitchTargets`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrSwitchTargets {
    /// Explicit `(value_bits, target_bb)` arms tested in order.
    pub branches: Vec<(u128, usize)>,
    /// Fallback basic block when no explicit branch matches.
    pub otherwise: usize,
}

/// Action taken when an operation unwinds corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.UnwindAction`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrUnwindAction {
    /// Jump to cleanup basic block `bb`.
    Cleanup(usize),
    /// Unwinding from this operation is UB.
    Unreachable,
    /// Abort the process on unwind.
    Terminate,
    /// Continue unwinding out of the current frame.
    Continue,
}

/// Control-flow transfer at the end of a basic block corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrTerminatorKind {
    Goto(usize),
    SwitchInt(IrOperand, IrSwitchTargets),
    UnwindResume,
    UnwindTerminate,
    Return,
    Unreachable,
    Drop {
        place: IrPlace,
        target: usize,
        unwind: IrUnwindAction,
    },
    Call {
        func: IrOperand,
        args: Vec<IrOperand>,
        destination: IrPlace,
        target: Option<usize>,
        unwind: IrUnwindAction,
    },
    TailCall {
        func: IrOperand,
        args: Vec<IrOperand>,
    },
    Assert {
        cond: IrOperand,
        expected: bool,
        target: usize,
        unwind: IrUnwindAction,
    },
    InlineAsm {
        template: String,
        targets: Vec<usize>,
        unwind: IrUnwindAction,
    },
}

/// Basic block terminator paired with its human-readable source span string
/// corresponding to `Trusted.Rustc.V2026_06_01.MirAst.Terminator`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrTerminator {
    pub kind: IrTerminatorKind,
    pub span: String,
    /// Optional human-readable terminator comment (e.g., `return`).
    pub comment: Option<String>,
}

/// A single basic block in the control-flow graph corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrBasicBlockData {
    /// Sequential statements executed on entry to this block.
    pub statements: Vec<IrStatement>,
    /// Final control-flow transfer of the block.
    pub terminator: IrTerminator,
    /// True if this block lies on an unwinding cleanup path.
    pub is_cleanup: bool,
}

/// Declaration of a local variable slot in a MIR body (`_0` is the return
/// place, `_1 .. _arg_count` are incoming arguments), corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.LocalDecl`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrLocalDecl {
    /// Declared mutability (`let` vs. `let mut`).
    pub mutability: IrMutability,
    /// Monomorphized type and layout table index of this slot.
    pub ty: IrTy,
    /// Optional source variable name for diagnostics.
    pub debug_name: Option<String>,
}

/// MIR dialect phase tag recorded by `anneal-rustc-capture` corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.MirPhaseTag`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrMirPhaseTag {
    /// `MirPhase::Runtime(RuntimePhase::PostCleanup)` before optimization
    /// passes.
    RuntimePostCleanup,
    /// `MirPhase::Runtime(RuntimePhase::Optimized)` returned by
    /// `tcx.optimized_mir`.
    RuntimeOptimized,
    /// Other MIR phase name (e.g., `Const(MirForCtfe)`).
    Other(String),
}

/// Role of the captured item in Anneal's specification and verification
/// pipeline, corresponding to `Trusted.Rustc.V2026_06_01.MirAst.ContractRole`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrContractRole {
    /// Executable subject function or method under verification.
    Subject,
    /// Synthetic `anodized` precondition function (`__anodized_fn_requires_*`)
    /// attached to subject `DefPath`.
    Requires(String),
    /// Synthetic `anodized` postcondition function (`__anodized_fn_ensures_*`)
    /// attached to subject `DefPath`.
    Ensures(String),
    /// External sidecar contract (`#[anneal::external_spec]`) attached to
    /// subject `DefPath`.
    ExternalSpec(String),
    /// Pure ghost/model helper (`#[anneal::model]`).
    Model,
}

/// Read-only or static memory allocation referenced by `IrProvenancePtr` or
/// `IrConstValue::Indirect` inside a MIR body, corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrCapturedAllocation {
    /// Global allocation identifier matching `IrProvenancePtr::alloc_id`.
    pub alloc_id: u64,
    /// Byte payload (`None` represents an uninitialized byte).
    pub bytes: Vec<Option<u8>>,
    /// Pointer relocations stored at `(byte_offset, target_ptr)`.
    pub relocations: Vec<(u64, IrProvenancePtr)>,
    /// Required byte alignment of the allocation.
    pub align: IrAlign,
    /// Mutability of the allocation (`Not` for constants, `Mut` for `static
    /// mut`).
    pub mutability: IrMutability,
}

/// Complete captured MIR body, ABI, layout table, and constant allocations
/// emitted as `def body : CapturedMir` in `Mir/<Item>.lean`, corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrCapturedMir {
    /// Canonical crate-qualified `DefId` path of this item.
    pub def_path: String,
    /// MIR phase at which this body was extracted.
    pub phase: IrMirPhaseTag,
    /// Role of this item (subject vs. contract companion).
    pub role: IrContractRole,
    /// Number of incoming function arguments (`_1 .. _arg_count`).
    pub arg_count: usize,
    /// Local variable declarations indexed by `LocalId` (`0` is return place).
    pub local_decls: Vec<IrLocalDecl>,
    /// Control-flow graph basic blocks indexed by `BasicBlockId` (`0` is
    /// entry).
    pub basic_blocks: Vec<IrBasicBlockData>,
    /// Function call ABI.
    pub fn_abi: IrFnAbi,
    /// Layout table referenced by `IrTy::layout_idx`.
    pub layouts: IrLayoutTable,
    /// Referenced global/constant memory allocations.
    pub allocations: Vec<IrCapturedAllocation>,
}

/// Renders the standard file header for a generated `Mir/<Item>.lean` module.
pub fn render_mir_module_header(lean_module_namespace: &str, def_path: &str) -> String {
    format!(
        "import Trusted\n\n\
         namespace {lean_module_namespace}\n\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.Layout\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.MirAst\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.MirSemantics\n\
         open Trusted.VerificationResult\n\n\
         /-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `{def_path}`. -/\n"
    )
}

/// Formats a complete, deterministic Lean 4 module (`Mir/<Crate>/<Item>.lean`)
/// defining `layouts : LayoutTable`, `body : CapturedMir`, and
/// `defaultClaim : Claim`.
pub fn emit_mir_lean_module(lean_module_namespace: &str, mir: &IrCapturedMir) -> String {
    let mut out = render_mir_module_header(lean_module_namespace, &mir.def_path);
    out.push('\n');

    for (idx, layout) in mir.layouts.entries.iter().enumerate() {
        out.push_str(&format!(
            "-- TypeLayout[{}]: size={}, align={}\n",
            idx, layout.size.bytes, layout.align.bytes
        ));
    }
    out.push_str("def layouts : LayoutTable :=\n  ");
    out.push_str(&render_layout_table(&mir.layouts));
    out.push_str("\n\n");

    for (bb_idx, bb) in mir.basic_blocks.iter().enumerate() {
        out.push_str(&format!("-- bb{bb_idx}: {}\n", summarize_basic_block(bb)));
    }
    out.push_str("def body : CapturedMir :=\n  ");
    out.push_str(&render_captured_mir(mir));
    out.push_str("\n\n");

    out.push_str(
        "def defaultClaim : Claim :=\n  \
         { body := body, pre := fun _ => True, post := fun _ _ => True }\n\n",
    );
    out.push_str(&format!("end {lean_module_namespace}\n"));
    out
}

fn summarize_basic_block(bb: &IrBasicBlockData) -> String {
    let mut parts: Vec<String> = Vec::with_capacity(bb.statements.len() + 1);
    for stmt in &bb.statements {
        if matches!(stmt.kind, IrStatementKind::Retag(_, _))
            || (matches!(stmt.kind, IrStatementKind::StorageLive(_)) && stmt.comment.is_none())
        {
            continue;
        }
        if let Some(comment) = &stmt.comment {
            parts.push(sanitize_comment_line(comment));
        } else {
            parts.push(summarize_statement_kind(&stmt.kind));
        }
    }
    if let Some(comment) = &bb.terminator.comment {
        parts.push(sanitize_comment_line(comment));
    } else {
        parts.push(summarize_terminator_kind(&bb.terminator.kind));
    }
    parts.join("; ")
}

fn sanitize_comment_line(text: &str) -> String {
    text.chars()
        .map(|c| if c == '\n' || c == '\r' { ' ' } else { c })
        .collect::<String>()
        .trim()
        .to_owned()
}

fn summarize_place(place: &IrPlace) -> String {
    let mut s = format!("_{}", place.local_);
    for proj in &place.projection {
        match proj {
            IrProjectionElem::Deref => s = format!("(*{s})"),
            IrProjectionElem::Field(idx, _) => s.push_str(&format!(".{idx}")),
            IrProjectionElem::Index(local) => s.push_str(&format!("[_{local}]")),
            IrProjectionElem::ConstantIndex { offset, .. } => {
                s.push_str(&format!("[{offset}]"))
            }
            IrProjectionElem::Subslice {
                from_idx, to_idx, ..
            } => s.push_str(&format!("[{from_idx}..{to_idx}]")),
            IrProjectionElem::Downcast(Some(name), _) => {
                s = format!("({s} as {name})");
            }
            IrProjectionElem::Downcast(None, idx) => {
                s = format!("({s} as variant#{idx})");
            }
            IrProjectionElem::OpaqueCast(_) => s.push_str(".opaque"),
            IrProjectionElem::UnwrapUnsafeBinder(_) => s.push_str(".unwrap_binder"),
        }
    }
    s
}

fn summarize_operand(op: &IrOperand) -> String {
    match op {
        IrOperand::Copy(p) => format!("copy {}", summarize_place(p)),
        IrOperand::Move(p) => format!("move {}", summarize_place(p)),
        IrOperand::Constant(c) => match &c.val {
            IrConstValue::ZeroSized => String::from("const ()"),
            IrConstValue::Scalar(IrConstScalar::Int(si)) => {
                format!("const {}", si.bits)
            }
            IrConstValue::Scalar(IrConstScalar::Ptr(ptr, _)) => {
                format!("const alloc{}+{}", ptr.alloc_id, ptr.offset_bytes)
            }
            IrConstValue::Slice { meta, .. } => format!("const slice(len={meta})"),
            IrConstValue::Indirect {
                alloc_id,
                offset_bytes,
            } => format!("const indirect(alloc{alloc_id}+{offset_bytes})"),
            IrConstValue::Unevaluated(def_path) => format!("const {def_path}"),
        },
    }
}

fn summarize_rvalue(rv: &IrRvalue) -> String {
    match rv {
        IrRvalue::Use(op) => summarize_operand(op),
        IrRvalue::Repeat(op, count) => format!("[{}; {count}]", summarize_operand(op)),
        IrRvalue::Ref(IrBorrowKind::Shared, p) => format!("&{}", summarize_place(p)),
        IrRvalue::Ref(IrBorrowKind::Mut { .. }, p) => format!("&mut {}", summarize_place(p)),
        IrRvalue::ThreadLocalRef(path) => format!("thread_local_ref({path})"),
        IrRvalue::RawPtr(IrMutability::Not, p) => format!("&raw const {}", summarize_place(p)),
        IrRvalue::RawPtr(IrMutability::Mut, p) => format!("&raw mut {}", summarize_place(p)),
        IrRvalue::Len(p) => format!("Len({})", summarize_place(p)),
        IrRvalue::Cast(_, op, _) => format!("{} as _", summarize_operand(op)),
        IrRvalue::BinaryOp(op, lhs, rhs) => {
            format!(
                "{op:?}({}, {})",
                summarize_operand(lhs),
                summarize_operand(rhs)
            )
        }
        IrRvalue::NullaryOp(op, _) => format!("{op:?}()"),
        IrRvalue::UnaryOp(op, arg) => format!("{op:?}({})", summarize_operand(arg)),
        IrRvalue::Discriminant(p) => format!("discriminant({})", summarize_place(p)),
        IrRvalue::Aggregate(_, ops) => {
            let items: Vec<String> = ops.iter().map(summarize_operand).collect();
            format!("aggregate({})", items.join(", "))
        }
        IrRvalue::ShallowInitBox(op, _) => format!("ShallowInitBox({})", summarize_operand(op)),
        IrRvalue::CopyForDeref(p) => format!("CopyForDeref({})", summarize_place(p)),
        IrRvalue::WrapUnsafeBinder(op, _) => format!("WrapUnsafeBinder({})", summarize_operand(op)),
    }
}

fn summarize_statement_kind(kind: &IrStatementKind) -> String {
    match kind {
        IrStatementKind::Assign(p, rv) => {
            format!("{} = {}", summarize_place(p), summarize_rvalue(rv))
        }
        IrStatementKind::SetDiscriminant(p, idx) => {
            format!("discriminant({}) = {idx}", summarize_place(p))
        }
        IrStatementKind::Deinit(p) => format!("Deinit({})", summarize_place(p)),
        IrStatementKind::StorageLive(l) => format!("StorageLive(_{l})"),
        IrStatementKind::StorageDead(l) => format!("StorageDead(_{l})"),
        IrStatementKind::Retag(_, p) => format!("Retag({})", summarize_place(p)),
        IrStatementKind::PlaceMention(p) => format!("PlaceMention({})", summarize_place(p)),
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
            format!("assume({})", summarize_operand(op))
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
            src,
            dst,
            count,
        }) => format!(
            "copy_nonoverlapping({}, {}, {})",
            summarize_operand(src),
            summarize_operand(dst),
            summarize_operand(count)
        ),
        IrStatementKind::Coverage => String::from("Coverage"),
        IrStatementKind::ConstEvalCounter => String::from("ConstEvalCounter"),
        IrStatementKind::BackwardIncompatibleDropHint(p) => {
            format!("DropHint({})", summarize_place(p))
        }
        IrStatementKind::Nop => String::from("nop"),
    }
}

fn summarize_terminator_kind(kind: &IrTerminatorKind) -> String {
    match kind {
        IrTerminatorKind::Goto(bb) => format!("goto -> bb{bb}"),
        IrTerminatorKind::SwitchInt(op, targets) => {
            format!(
                "switchInt({}) -> otherwise bb{}",
                summarize_operand(op),
                targets.otherwise
            )
        }
        IrTerminatorKind::UnwindResume => String::from("resume"),
        IrTerminatorKind::UnwindTerminate => String::from("terminate"),
        IrTerminatorKind::Return => String::from("return"),
        IrTerminatorKind::Unreachable => String::from("unreachable"),
        IrTerminatorKind::Drop { place, target, .. } => {
            format!("drop({}) -> bb{target}", summarize_place(place))
        }
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            let rendered_args: Vec<String> = args.iter().map(summarize_operand).collect();
            let target_str = match target {
                Some(bb) => format!("bb{bb}"),
                None => String::from("diverging"),
            };
            format!(
                "{} = {}({}) -> {target_str}",
                summarize_place(destination),
                summarize_operand(func),
                rendered_args.join(", ")
            )
        }
        IrTerminatorKind::TailCall { func, args } => {
            let rendered_args: Vec<String> = args.iter().map(summarize_operand).collect();
            format!(
                "tailcall {}({})",
                summarize_operand(func),
                rendered_args.join(", ")
            )
        }
        IrTerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } => format!(
            "assert({}, {expected}) -> bb{target}",
            summarize_operand(cond)
        ),
        IrTerminatorKind::InlineAsm { .. } => String::from("asm!(...)"),
    }
}

/// Escapes a Rust string for inclusion inside a Lean 4 string literal
/// (`"..."`).
pub fn escape_lean_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => {
                let mut buf = [0u8; 4];
                for b in c.encode_utf8(&mut buf).as_bytes() {
                    out.push_str(&format!("\\x{b:02x}"));
                }
            }
            c => out.push(c),
        }
    }
    out
}

fn render_lean_str(s: &str) -> String {
    format!("\"{}\"", escape_lean_str(s))
}

fn render_bool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}

fn render_list<T, F>(items: &[T], mut f: F) -> String
where
    F: FnMut(&T) -> String,
{
    let mut rendered: Vec<String> = items.iter().map(&mut f).collect();
    let mut acc = String::from("List.nil");
    while let Some(elem) = rendered.pop() {
        acc = format!("(List.cons {elem} {acc})");
    }
    acc
}

fn render_size(s: IrSize) -> String {
    format!("{{ bytes := {} }}", s.bytes)
}

fn render_align(a: IrAlign) -> String {
    format!("{{ bytes := {} }}", a.bytes)
}

fn render_wrapping_range(r: IrWrappingRange) -> String {
    format!("{{ start := {}, end_ := {} }}", r.start, r.end_)
}

fn render_primitive_kind(p: IrPrimitiveKind) -> String {
    match p {
        IrPrimitiveKind::Int { bits, signed } => {
            format!("(PrimitiveKind.int {bits} {})", render_bool(signed))
        }
        IrPrimitiveKind::Float { bits } => format!("(PrimitiveKind.float {bits})"),
        IrPrimitiveKind::Pointer { address_space } => {
            format!("(PrimitiveKind.pointer {address_space})")
        }
    }
}

fn render_scalar_layout(s: IrScalarLayout) -> String {
    match s {
        IrScalarLayout::Initialized { value, valid_range } => format!(
            "(ScalarLayout.initialized {} {})",
            render_primitive_kind(value),
            render_wrapping_range(valid_range)
        ),
        IrScalarLayout::Union { value } => {
            format!("(ScalarLayout.union {})", render_primitive_kind(value))
        }
    }
}

fn render_fields_shape(f: &IrFieldsShape) -> String {
    match f {
        IrFieldsShape::Primitive => String::from("FieldsShape.primitive"),
        IrFieldsShape::Union { count } => format!("(FieldsShape.union {count})"),
        IrFieldsShape::Array { stride, count } => {
            format!("(FieldsShape.array {} {count})", render_size(*stride))
        }
        IrFieldsShape::Arbitrary {
            offsets,
            memory_index,
        } => format!(
            "(FieldsShape.arbitrary {} {})",
            render_list(offsets, |o| render_size(*o)),
            render_list(memory_index, |idx| idx.to_string())
        ),
    }
}

fn render_variants_shape(v: &IrVariantsShape) -> String {
    match v {
        IrVariantsShape::Empty => String::from("VariantsShape.empty"),
        IrVariantsShape::Single { index } => format!("(VariantsShape.single {index})"),
        IrVariantsShape::Multiple {
            tag,
            tag_field,
            variants,
        } => format!(
            "(VariantsShape.multiple {} {tag_field} {})",
            render_scalar_layout(*tag),
            render_list(variants, render_fields_shape)
        ),
    }
}

fn render_backend_repr(b: IrBackendRepr) -> String {
    match b {
        IrBackendRepr::Scalar(s) => format!("(BackendRepr.scalar {})", render_scalar_layout(s)),
        IrBackendRepr::ScalarPair(a, b) => format!(
            "(BackendRepr.scalarPair {} {})",
            render_scalar_layout(a),
            render_scalar_layout(b)
        ),
        IrBackendRepr::Memory => String::from("BackendRepr.memory"),
    }
}

fn render_type_layout(l: &IrTypeLayout) -> String {
    if l.field_layouts.is_empty() {
        format!(
            "{{ size := {}, align := {}, backendRepr := {}, fields := {}, variants := {}, isUninhabited := {} }}",
            render_size(l.size),
            render_align(l.align),
            render_backend_repr(l.backend_repr),
            render_fields_shape(&l.fields),
            render_variants_shape(&l.variants),
            render_bool(l.is_uninhabited)
        )
    } else {
        format!(
            "{{ size := {}, align := {}, backendRepr := {}, fields := {}, variants := {}, isUninhabited := {}, fieldLayouts := {} }}",
            render_size(l.size),
            render_align(l.align),
            render_backend_repr(l.backend_repr),
            render_fields_shape(&l.fields),
            render_variants_shape(&l.variants),
            render_bool(l.is_uninhabited),
            render_list(&l.field_layouts, |idx| idx.to_string())
        )
    }
}

fn render_abi_pass_mode(m: IrAbiPassMode) -> &'static str {
    match m {
        IrAbiPassMode::Ignore => "AbiPassMode.ignore",
        IrAbiPassMode::Direct => "AbiPassMode.direct",
        IrAbiPassMode::Pair => "AbiPassMode.pair",
        IrAbiPassMode::Indirect => "AbiPassMode.indirect",
    }
}

fn render_arg_abi(a: &IrArgAbi) -> String {
    format!(
        "{{ layout := {}, mode := {} }}",
        render_type_layout(&a.layout),
        render_abi_pass_mode(a.mode)
    )
}

fn render_call_conv(c: &IrCallConv) -> String {
    match c {
        IrCallConv::Rust => String::from("CallConv.rust"),
        IrCallConv::C => String::from("CallConv.c"),
        IrCallConv::RustIntrinsic => String::from("CallConv.rustIntrinsic"),
        IrCallConv::Other(s) => format!("(CallConv.other {})", render_lean_str(s)),
    }
}

fn render_fn_abi(f: &IrFnAbi) -> String {
    format!(
        "{{ args := {}, ret := {}, conv := {}, canUnwind := {} }}",
        render_list(&f.args, render_arg_abi),
        render_arg_abi(&f.ret),
        render_call_conv(&f.conv),
        render_bool(f.can_unwind)
    )
}

fn render_layout_table(t: &IrLayoutTable) -> String {
    format!(
        "{{ pointerBits := {}, isLittleEndian := {}, entries := {} }}",
        t.pointer_bits,
        render_bool(t.is_little_endian),
        render_list(&t.entries, render_type_layout)
    )
}

fn render_uint_ty(u: IrUintTy) -> &'static str {
    match u {
        IrUintTy::U8 => "UintTy.u8",
        IrUintTy::U16 => "UintTy.u16",
        IrUintTy::U32 => "UintTy.u32",
        IrUintTy::U64 => "UintTy.u64",
        IrUintTy::U128 => "UintTy.u128",
        IrUintTy::Usize => "UintTy.usize",
    }
}

fn render_int_ty(i: IrIntTy) -> &'static str {
    match i {
        IrIntTy::I8 => "IntTy.i8",
        IrIntTy::I16 => "IntTy.i16",
        IrIntTy::I32 => "IntTy.i32",
        IrIntTy::I64 => "IntTy.i64",
        IrIntTy::I128 => "IntTy.i128",
        IrIntTy::Isize => "IntTy.isize",
    }
}

fn render_float_ty(f: IrFloatTy) -> &'static str {
    match f {
        IrFloatTy::F16 => "FloatTy.f16",
        IrFloatTy::F32 => "FloatTy.f32",
        IrFloatTy::F64 => "FloatTy.f64",
        IrFloatTy::F128 => "FloatTy.f128",
    }
}

fn render_mutability(m: IrMutability) -> &'static str {
    match m {
        IrMutability::Not => "Mutability.not",
        IrMutability::Mut => "Mutability.mut",
    }
}

fn render_safety(s: IrSafety) -> &'static str {
    match s {
        IrSafety::Safe => "Safety.safe",
        IrSafety::Unsafe => "Safety.unsafe_",
    }
}

fn render_rigid_ty(r: &IrRigidTy) -> String {
    match r {
        IrRigidTy::Bool => String::from("RigidTy.bool"),
        IrRigidTy::Char => String::from("RigidTy.char"),
        IrRigidTy::Int(i) => format!("(RigidTy.int {})", render_int_ty(*i)),
        IrRigidTy::Uint(u) => format!("(RigidTy.uint {})", render_uint_ty(*u)),
        IrRigidTy::Float(f) => format!("(RigidTy.float {})", render_float_ty(*f)),
        IrRigidTy::Never => String::from("RigidTy.never"),
        IrRigidTy::Str => String::from("RigidTy.str"),
        IrRigidTy::Tuple(elems) => format!("(RigidTy.tuple {})", render_list(elems, render_rigid_ty)),
        IrRigidTy::Array(elem, len) => {
            format!("(RigidTy.array {} {len})", render_rigid_ty(elem))
        }
        IrRigidTy::Slice(elem) => format!("(RigidTy.slice {})", render_rigid_ty(elem)),
        IrRigidTy::Ref(m, pointee) => format!(
            "(RigidTy.ref {} {})",
            render_mutability(*m),
            render_rigid_ty(pointee)
        ),
        IrRigidTy::RawPtr(m, pointee) => format!(
            "(RigidTy.rawPtr {} {})",
            render_mutability(*m),
            render_rigid_ty(pointee)
        ),
        IrRigidTy::Adt(path, args) => format!(
            "(RigidTy.adt {} {})",
            render_lean_str(path),
            render_list(args, render_rigid_ty)
        ),
        IrRigidTy::FnDef(path, args) => format!(
            "(RigidTy.fnDef {} {})",
            render_lean_str(path),
            render_list(args, render_rigid_ty)
        ),
        IrRigidTy::FnPtr(inputs, output, safety, conv) => format!(
            "(RigidTy.fnPtr {} {} {} {})",
            render_list(inputs, render_rigid_ty),
            render_rigid_ty(output),
            render_safety(*safety),
            render_call_conv(conv)
        ),
        IrRigidTy::Closure(path, upvars) => format!(
            "(RigidTy.closure {} {})",
            render_lean_str(path),
            render_list(upvars, render_rigid_ty)
        ),
        IrRigidTy::Dynamic(path) => format!("(RigidTy.dynamic {})", render_lean_str(path)),
        IrRigidTy::Foreign(path) => format!("(RigidTy.foreign {})", render_lean_str(path)),
        IrRigidTy::Other(desc) => format!("(RigidTy.other {})", render_lean_str(desc)),
    }
}

fn render_ty(ty: &IrTy) -> String {
    format!(
        "{{ kind := {}, layoutIdx := {} }}",
        render_rigid_ty(&ty.kind),
        ty.layout_idx
    )
}

fn render_projection_elem(p: &IrProjectionElem) -> String {
    match p {
        IrProjectionElem::Deref => String::from("ProjectionElem.deref"),
        IrProjectionElem::Field(idx, ty) => {
            format!("(ProjectionElem.field {idx} {})", render_ty(ty))
        }
        IrProjectionElem::Index(local) => format!("(ProjectionElem.index {local})"),
        IrProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => format!(
            "(ProjectionElem.constantIndex {offset} {min_length} {})",
            render_bool(*from_end)
        ),
        IrProjectionElem::Subslice {
            from_idx,
            to_idx,
            from_end,
        } => format!(
            "(ProjectionElem.subslice {from_idx} {to_idx} {})",
            render_bool(*from_end)
        ),
        IrProjectionElem::Downcast(sym, idx) => {
            let sym_str = match sym {
                Some(s) => format!("(Option.some {})", render_lean_str(s)),
                None => String::from("Option.none"),
            };
            format!("(ProjectionElem.downcast {sym_str} {idx})")
        }
        IrProjectionElem::OpaqueCast(ty) => {
            format!("(ProjectionElem.opaqueCast {})", render_ty(ty))
        }
        IrProjectionElem::UnwrapUnsafeBinder(ty) => {
            format!("(ProjectionElem.unwrapUnsafeBinder {})", render_ty(ty))
        }
    }
}

fn render_place(p: &IrPlace) -> String {
    format!(
        "{{ local_ := {}, projection := {} }}",
        p.local_,
        render_list(&p.projection, render_projection_elem)
    )
}

fn render_scalar_int(si: IrScalarInt) -> String {
    format!("{{ bits := {}, sizeBytes := {} }}", si.bits, si.size_bytes)
}

fn render_provenance_ptr(ptr: IrProvenancePtr) -> String {
    format!(
        "{{ allocId := {}, offsetBytes := {} }}",
        ptr.alloc_id, ptr.offset_bytes
    )
}

fn render_const_scalar(cs: IrConstScalar) -> String {
    match cs {
        IrConstScalar::Int(si) => format!("(ConstScalar.int {})", render_scalar_int(si)),
        IrConstScalar::Ptr(ptr, size) => {
            format!("(ConstScalar.ptr {} {size})", render_provenance_ptr(ptr))
        }
    }
}

fn render_const_value(cv: &IrConstValue) -> String {
    match cv {
        IrConstValue::ZeroSized => String::from("ConstValue.zeroSized"),
        IrConstValue::Scalar(cs) => format!("(ConstValue.scalar {})", render_const_scalar(*cs)),
        IrConstValue::Slice { data, meta } => {
            format!("(ConstValue.slice {} {meta})", render_const_scalar(*data))
        }
        IrConstValue::Indirect {
            alloc_id,
            offset_bytes,
        } => format!("(ConstValue.indirect {alloc_id} {offset_bytes})"),
        IrConstValue::Unevaluated(path) => {
            format!("(ConstValue.unevaluated {})", render_lean_str(path))
        }
    }
}

fn render_const_operand(co: &IrConstOperand) -> String {
    format!(
        "{{ ty := {}, val := {} }}",
        render_ty(&co.ty),
        render_const_value(&co.val)
    )
}

fn render_operand(op: &IrOperand) -> String {
    match op {
        IrOperand::Copy(p) => format!("(Operand.copy {})", render_place(p)),
        IrOperand::Move(p) => format!("(Operand.move {})", render_place(p)),
        IrOperand::Constant(co) => format!("(Operand.constant {})", render_const_operand(co)),
    }
}

fn render_bin_op(op: IrBinOp) -> &'static str {
    match op {
        IrBinOp::Add => "BinOp.add",
        IrBinOp::AddUnchecked => "BinOp.addUnchecked",
        IrBinOp::AddWithOverflow => "BinOp.addWithOverflow",
        IrBinOp::Sub => "BinOp.sub",
        IrBinOp::SubUnchecked => "BinOp.subUnchecked",
        IrBinOp::SubWithOverflow => "BinOp.subWithOverflow",
        IrBinOp::Mul => "BinOp.mul",
        IrBinOp::MulUnchecked => "BinOp.mulUnchecked",
        IrBinOp::MulWithOverflow => "BinOp.mulWithOverflow",
        IrBinOp::Div => "BinOp.div",
        IrBinOp::Rem => "BinOp.rem",
        IrBinOp::BitXor => "BinOp.bitXor",
        IrBinOp::BitAnd => "BinOp.bitAnd",
        IrBinOp::BitOr => "BinOp.bitOr",
        IrBinOp::Shl => "BinOp.shl",
        IrBinOp::ShlUnchecked => "BinOp.shlUnchecked",
        IrBinOp::Shr => "BinOp.shr",
        IrBinOp::ShrUnchecked => "BinOp.shrUnchecked",
        IrBinOp::Eq => "BinOp.eq",
        IrBinOp::Lt => "BinOp.lt",
        IrBinOp::Le => "BinOp.le",
        IrBinOp::Ne => "BinOp.ne",
        IrBinOp::Ge => "BinOp.ge",
        IrBinOp::Gt => "BinOp.gt",
        IrBinOp::Cmp => "BinOp.cmp",
        IrBinOp::Offset => "BinOp.offset",
    }
}

fn render_un_op(op: IrUnOp) -> &'static str {
    match op {
        IrUnOp::Not => "UnOp.not",
        IrUnOp::Neg => "UnOp.neg",
        IrUnOp::PtrMetadata => "UnOp.ptrMetadata",
    }
}

fn render_null_op(op: &IrNullOp) -> String {
    match op {
        IrNullOp::SizeOf => String::from("NullOp.sizeOf"),
        IrNullOp::AlignOf => String::from("NullOp.alignOf"),
        IrNullOp::OffsetOf(fields) => format!(
            "(NullOp.offsetOf {})",
            render_list(fields, |(v, f)| format!("({v}, {f})"))
        ),
        IrNullOp::UbChecks => String::from("NullOp.ubChecks"),
        IrNullOp::ContractChecks => String::from("NullOp.contractChecks"),
    }
}

fn render_borrow_kind(bk: IrBorrowKind) -> String {
    match bk {
        IrBorrowKind::Shared => String::from("BorrowKind.shared"),
        IrBorrowKind::Mut { allow_two_phase } => {
            format!("(BorrowKind.mut {})", render_bool(allow_two_phase))
        }
    }
}

fn render_cast_kind(ck: &IrCastKind) -> String {
    match ck {
        IrCastKind::PointerExposeProvenance => String::from("CastKind.pointerExposeProvenance"),
        IrCastKind::PointerWithExposedProvenance => {
            String::from("CastKind.pointerWithExposedProvenance")
        }
        IrCastKind::PointerCoercion(tag) => {
            format!("(CastKind.pointerCoercion {})", render_lean_str(tag))
        }
        IrCastKind::IntToInt => String::from("CastKind.intToInt"),
        IrCastKind::FloatToInt => String::from("CastKind.floatToInt"),
        IrCastKind::FloatToFloat => String::from("CastKind.floatToFloat"),
        IrCastKind::IntToFloat => String::from("CastKind.intToFloat"),
        IrCastKind::PtrToPtr => String::from("CastKind.ptrToPtr"),
        IrCastKind::FnPtrToPtr => String::from("CastKind.fnPtrToPtr"),
        IrCastKind::Transmute => String::from("CastKind.transmute"),
        IrCastKind::Subtype => String::from("CastKind.subtype"),
    }
}

fn render_aggregate_kind(ak: &IrAggregateKind) -> String {
    match ak {
        IrAggregateKind::Array(ty) => format!("(AggregateKind.array {})", render_ty(ty)),
        IrAggregateKind::Tuple => String::from("AggregateKind.tuple"),
        IrAggregateKind::Adt(path, variant_idx, active_field) => {
            let field_str = match active_field {
                Some(idx) => format!("(Option.some {idx})"),
                None => String::from("Option.none"),
            };
            format!(
                "(AggregateKind.adt {} {variant_idx} {field_str})",
                render_lean_str(path)
            )
        }
        IrAggregateKind::Closure(path) => {
            format!("(AggregateKind.closure {})", render_lean_str(path))
        }
        IrAggregateKind::Coroutine(path) => {
            format!("(AggregateKind.coroutine {})", render_lean_str(path))
        }
        IrAggregateKind::RawPtr(ty, m) => format!(
            "(AggregateKind.rawPtr {} {})",
            render_ty(ty),
            render_mutability(*m)
        ),
    }
}

fn render_rvalue(rv: &IrRvalue) -> String {
    match rv {
        IrRvalue::Use(op) => format!("(Rvalue.use {})", render_operand(op)),
        IrRvalue::Repeat(op, count) => {
            format!("(Rvalue.repeat {} {count})", render_operand(op))
        }
        IrRvalue::Ref(bk, p) => {
            format!("(Rvalue.ref {} {})", render_borrow_kind(*bk), render_place(p))
        }
        IrRvalue::ThreadLocalRef(path) => {
            format!("(Rvalue.threadLocalRef {})", render_lean_str(path))
        }
        IrRvalue::RawPtr(m, p) => {
            format!("(Rvalue.rawPtr {} {})", render_mutability(*m), render_place(p))
        }
        IrRvalue::Len(p) => format!("(Rvalue.len {})", render_place(p)),
        IrRvalue::Cast(ck, op, ty) => format!(
            "(Rvalue.cast {} {} {})",
            render_cast_kind(ck),
            render_operand(op),
            render_ty(ty)
        ),
        IrRvalue::BinaryOp(op, lhs, rhs) => format!(
            "(Rvalue.binaryOp {} {} {})",
            render_bin_op(*op),
            render_operand(lhs),
            render_operand(rhs)
        ),
        IrRvalue::NullaryOp(op, ty) => {
            format!("(Rvalue.nullaryOp {} {})", render_null_op(op), render_ty(ty))
        }
        IrRvalue::UnaryOp(op, arg) => {
            format!("(Rvalue.unaryOp {} {})", render_un_op(*op), render_operand(arg))
        }
        IrRvalue::Discriminant(p) => format!("(Rvalue.discriminant {})", render_place(p)),
        IrRvalue::Aggregate(ak, ops) => format!(
            "(Rvalue.aggregate {} {})",
            render_aggregate_kind(ak),
            render_list(ops, render_operand)
        ),
        IrRvalue::ShallowInitBox(op, ty) => format!(
            "(Rvalue.shallowInitBox {} {})",
            render_operand(op),
            render_ty(ty)
        ),
        IrRvalue::CopyForDeref(p) => format!("(Rvalue.copyForDeref {})", render_place(p)),
        IrRvalue::WrapUnsafeBinder(op, ty) => format!(
            "(Rvalue.wrapUnsafeBinder {} {})",
            render_operand(op),
            render_ty(ty)
        ),
    }
}

fn render_non_diverging_intrinsic(ndi: &IrNonDivergingIntrinsic) -> String {
    match ndi {
        IrNonDivergingIntrinsic::Assume(op) => {
            format!("(NonDivergingIntrinsic.assume {})", render_operand(op))
        }
        IrNonDivergingIntrinsic::CopyNonOverlapping { src, dst, count } => format!(
            "(NonDivergingIntrinsic.copyNonOverlapping {} {} {})",
            render_operand(src),
            render_operand(dst),
            render_operand(count)
        ),
    }
}

fn render_retag_kind(rk: IrRetagKind) -> &'static str {
    match rk {
        IrRetagKind::FnEntry => "RetagKind.fnEntry",
        IrRetagKind::TwoPhase => "RetagKind.twoPhase",
        IrRetagKind::Raw => "RetagKind.raw",
        IrRetagKind::Default => "RetagKind.default",
    }
}

fn render_statement_kind(sk: &IrStatementKind) -> String {
    match sk {
        IrStatementKind::Assign(p, rv) => {
            format!("(StatementKind.assign {} {})", render_place(p), render_rvalue(rv))
        }
        IrStatementKind::SetDiscriminant(p, idx) => {
            format!("(StatementKind.setDiscriminant {} {idx})", render_place(p))
        }
        IrStatementKind::Deinit(p) => format!("(StatementKind.deinit {})", render_place(p)),
        IrStatementKind::StorageLive(l) => format!("(StatementKind.storageLive {l})"),
        IrStatementKind::StorageDead(l) => format!("(StatementKind.storageDead {l})"),
        IrStatementKind::Retag(rk, p) => {
            format!("(StatementKind.retag {} {})", render_retag_kind(*rk), render_place(p))
        }
        IrStatementKind::PlaceMention(p) => {
            format!("(StatementKind.placeMention {})", render_place(p))
        }
        IrStatementKind::Intrinsic(ndi) => format!(
            "(StatementKind.intrinsic {})",
            render_non_diverging_intrinsic(ndi)
        ),
        IrStatementKind::Coverage => String::from("StatementKind.coverage"),
        IrStatementKind::ConstEvalCounter => String::from("StatementKind.constEvalCounter"),
        IrStatementKind::BackwardIncompatibleDropHint(p) => {
            format!("(StatementKind.backwardIncompatibleDropHint {})", render_place(p))
        }
        IrStatementKind::Nop => String::from("StatementKind.nop"),
    }
}

fn render_statement(stmt: &IrStatement) -> String {
    format!(
        "{{ kind := {}, span := {} }}",
        render_statement_kind(&stmt.kind),
        render_lean_str(&stmt.span)
    )
}

fn render_switch_targets(st: &IrSwitchTargets) -> String {
    format!(
        "{{ branches := {}, otherwise := {} }}",
        render_list(&st.branches, |(val, bb)| format!("({val}, {bb})")),
        st.otherwise
    )
}

fn render_unwind_action(ua: IrUnwindAction) -> String {
    match ua {
        IrUnwindAction::Cleanup(bb) => format!("(UnwindAction.cleanup {bb})"),
        IrUnwindAction::Unreachable => String::from("UnwindAction.unreachable"),
        IrUnwindAction::Terminate => String::from("UnwindAction.terminate"),
        IrUnwindAction::Continue => String::from("UnwindAction.continue_"),
    }
}

fn render_terminator_kind(tk: &IrTerminatorKind) -> String {
    match tk {
        IrTerminatorKind::Goto(bb) => format!("(TerminatorKind.goto {bb})"),
        IrTerminatorKind::SwitchInt(op, st) => format!(
            "(TerminatorKind.switchInt {} {})",
            render_operand(op),
            render_switch_targets(st)
        ),
        IrTerminatorKind::UnwindResume => String::from("TerminatorKind.unwindResume"),
        IrTerminatorKind::UnwindTerminate => String::from("TerminatorKind.unwindTerminate"),
        IrTerminatorKind::Return => String::from("TerminatorKind.return_"),
        IrTerminatorKind::Unreachable => String::from("TerminatorKind.unreachable"),
        IrTerminatorKind::Drop {
            place,
            target,
            unwind,
        } => format!(
            "(TerminatorKind.drop {} {target} {})",
            render_place(place),
            render_unwind_action(*unwind)
        ),
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            let target_str = match target {
                Some(bb) => format!("(Option.some {bb})"),
                None => String::from("Option.none"),
            };
            format!(
                "(TerminatorKind.call {} {} {} {target_str} {})",
                render_operand(func),
                render_list(args, render_operand),
                render_place(destination),
                render_unwind_action(*unwind)
            )
        }
        IrTerminatorKind::TailCall { func, args } => format!(
            "(TerminatorKind.tailCall {} {})",
            render_operand(func),
            render_list(args, render_operand)
        ),
        IrTerminatorKind::Assert {
            cond,
            expected,
            target,
            unwind,
        } => format!(
            "(TerminatorKind.assert {} {} {target} {})",
            render_operand(cond),
            render_bool(*expected),
            render_unwind_action(*unwind)
        ),
        IrTerminatorKind::InlineAsm {
            template,
            targets,
            unwind,
        } => format!(
            "(TerminatorKind.inlineAsm {} {} {})",
            render_lean_str(template),
            render_list(targets, |t| t.to_string()),
            render_unwind_action(*unwind)
        ),
    }
}

fn render_terminator(term: &IrTerminator) -> String {
    format!(
        "{{ kind := {}, span := {} }}",
        render_terminator_kind(&term.kind),
        render_lean_str(&term.span)
    )
}

fn render_basic_block_data(bb: &IrBasicBlockData) -> String {
    let stmts: Vec<&IrStatement> = bb
        .statements
        .iter()
        .filter(|s| !matches!(s.kind, IrStatementKind::Retag(_, _)))
        .collect();
    format!(
        "{{ statements := {}, terminator := {}, isCleanup := {} }}",
        render_list(&stmts, |s| render_statement(s)),
        render_terminator(&bb.terminator),
        render_bool(bb.is_cleanup)
    )
}

fn render_local_decl(ld: &IrLocalDecl) -> String {
    let dbg = match &ld.debug_name {
        Some(s) => format!("(Option.some {})", render_lean_str(s)),
        None => String::from("Option.none"),
    };
    format!(
        "{{ mutability := {}, ty := {}, debugName := {dbg} }}",
        render_mutability(ld.mutability),
        render_ty(&ld.ty)
    )
}

fn render_mir_phase_tag(p: &IrMirPhaseTag) -> String {
    match p {
        IrMirPhaseTag::RuntimePostCleanup => String::from("MirPhaseTag.runtimePostCleanup"),
        IrMirPhaseTag::RuntimeOptimized => String::from("MirPhaseTag.runtimeOptimized"),
        IrMirPhaseTag::Other(s) => format!("(MirPhaseTag.other {})", render_lean_str(s)),
    }
}

fn render_contract_role(r: &IrContractRole) -> String {
    match r {
        IrContractRole::Subject => String::from("ContractRole.subject"),
        IrContractRole::Requires(subj) => {
            format!("(ContractRole.requires {})", render_lean_str(subj))
        }
        IrContractRole::Ensures(subj) => {
            format!("(ContractRole.ensures {})", render_lean_str(subj))
        }
        IrContractRole::ExternalSpec(subj) => {
            format!("(ContractRole.externalSpec {})", render_lean_str(subj))
        }
        IrContractRole::Model => String::from("ContractRole.model"),
    }
}

fn render_captured_allocation(alloc: &IrCapturedAllocation) -> String {
    let bytes_str = render_list(&alloc.bytes, |b| match b {
        Some(val) => format!("(Option.some (UInt8.ofNat {val}))"),
        None => String::from("Option.none"),
    });
    let relocs_str = render_list(&alloc.relocations, |(off, ptr)| {
        format!("({off}, {})", render_provenance_ptr(*ptr))
    });
    format!(
        "{{ allocId := {}, bytes := {bytes_str}, relocations := {relocs_str}, align := {}, mutability := {} }}",
        alloc.alloc_id,
        render_align(alloc.align),
        render_mutability(alloc.mutability)
    )
}

fn render_captured_mir(mir: &IrCapturedMir) -> String {
    format!(
        "{{\n    \
         defPath := {},\n    \
         phase := {},\n    \
         role := {},\n    \
         argCount := {},\n    \
         localDecls := {},\n    \
         basicBlocks := {},\n    \
         fnAbi := {},\n    \
         layouts := layouts,\n    \
         allocations := {}\n  \
         }}",
        render_lean_str(&mir.def_path),
        render_mir_phase_tag(&mir.phase),
        render_contract_role(&mir.role),
        mir.arg_count,
        render_list(&mir.local_decls, render_local_decl),
        render_list(&mir.basic_blocks, render_basic_block_data),
        render_fn_abi(&mir.fn_abi),
        render_list(&mir.allocations, render_captured_allocation)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emit_simple_const_return_module() {
        let u32_layout = IrTypeLayout {
            size: IrSize { bytes: 4 },
            align: IrAlign { bytes: 4 },
            backend_repr: IrBackendRepr::Scalar(IrScalarLayout::Initialized {
                value: IrPrimitiveKind::Int {
                    bits: 32,
                    signed: false,
                },
                valid_range: IrWrappingRange {
                    start: 0,
                    end_: u32::MAX as u128,
                },
            }),
            fields: IrFieldsShape::Primitive,
            variants: IrVariantsShape::Single { index: 0 },
            is_uninhabited: false,
            field_layouts: vec![],
        };
        let u32_ty = IrTy {
            kind: IrRigidTy::Uint(IrUintTy::U32),
            layout_idx: 0,
        };
        let mir = IrCapturedMir {
            def_path: String::from("demo::answer"),
            phase: IrMirPhaseTag::RuntimeOptimized,
            role: IrContractRole::Subject,
            arg_count: 0,
            local_decls: vec![IrLocalDecl {
                mutability: IrMutability::Mut,
                ty: u32_ty.clone(),
                debug_name: None,
            }],
            basic_blocks: vec![IrBasicBlockData {
                statements: vec![IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: 0,
                            projection: vec![],
                        },
                        IrRvalue::Use(IrOperand::Constant(IrConstOperand {
                            ty: u32_ty.clone(),
                            val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                                bits: 42,
                                size_bytes: 4,
                            })),
                        })),
                    ),
                    span: String::from("src/lib.rs:1:21: 1:23"),
                    comment: Some(String::from("_0 = const 42_u32")),
                }],
                terminator: IrTerminator {
                    kind: IrTerminatorKind::Return,
                    span: String::from("src/lib.rs:1:25: 1:25"),
                    comment: Some(String::from("return")),
                },
                is_cleanup: false,
            }],
            fn_abi: IrFnAbi {
                args: vec![],
                ret: IrArgAbi {
                    layout: u32_layout.clone(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![u32_layout],
            },
            allocations: vec![],
        };

        let code = emit_mir_lean_module("Mir.Demo.answer", &mir);
        assert!(code.starts_with("import Trusted\n"));
        assert!(code.contains("-- TypeLayout[0]: size=4, align=4\n"));
        assert!(code.contains("-- bb0: _0 = const 42_u32; return\n"));
        assert!(code.contains("def layouts : LayoutTable :="));
        assert!(code.contains("def body : CapturedMir :="));
        assert!(code.contains(
            "def defaultClaim : Claim :=\n  { body := body, pre := fun _ => True, post := fun _ _ => True }"
        ));
        assert!(code.ends_with("end Mir.Demo.answer\n"));
    }
}
