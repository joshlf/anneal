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
    Param { index: u32, name: String },
    Alias { def_path: String, args: Vec<IrRigidTy> },
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

/// Generic parameter definition corresponding to
/// `Trusted.Rustc.V2026_06_01.MirAst.GenericParamDef`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrGenericParamDef {
    pub index: u32,
    pub name: String,
}

/// Trait ref corresponding to `Trusted.Rustc.V2026_06_01.MirAst.TraitRef`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrTraitRef {
    pub def_path: String,
    pub args: Vec<IrRigidTy>,
}

/// Trait impl entry corresponding to `Trusted.Rustc.V2026_06_01.MirAst.TraitImplEntry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrTraitImplEntry {
    pub trait_ref: IrTraitRef,
    pub impl_path: String,
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
    /// Number of type parameters.
    pub type_param_count: usize,
    /// Generic parameters.
    pub generic_params: Vec<IrGenericParamDef>,
    /// Trait implementation entries.
    pub trait_impls: Vec<IrTraitImplEntry>,
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
    let def_path = sanitize_block_comment_text(def_path);
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

/// Flattens `text` to one line (like `sanitize_comment_line`) and breaks every Lean block-comment
/// delimiter (`/-` and `-/`) with a space, so captured text spliced into a generated `/-! ... -/`
/// docstring can neither close the comment early (injecting Lean commands into a trusted
/// `Mir/<Item>.lean` module) nor open a nested comment that swallows the rest of the module.
fn sanitize_block_comment_text(text: &str) -> String {
    let flat = sanitize_comment_line(text);
    let mut out = String::with_capacity(flat.len());
    let mut prev: Option<char> = None;
    for c in flat.chars() {
        if matches!((prev, c), (Some('/'), '-') | (Some('-'), '/')) {
            out.push(' ');
        }
        out.push(c);
        prev = Some(c);
    }
    out
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
                // Lean decodes `\xHH` as the *code point* `0xHH` (`Char.ofNat`), not as a UTF-8
                // byte, so a C1 control (`U+0080..=U+009F`) must be escaped by its code point:
                // escaping its two UTF-8 bytes would decode to two different characters. Every
                // `char::is_control` scalar (general category `Cc`) is at most `U+009F`.
                let code = u32::from(c);
                debug_assert!(code <= 0xff, "control character {c:?} exceeds `\\xHH`");
                out.push_str(&format!("\\x{code:02x}"));
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

pub fn render_rigid_ty_pub(r: &IrRigidTy) -> String {
    match r {
        IrRigidTy::Bool => String::from("RigidTy.bool"),
        IrRigidTy::Char => String::from("RigidTy.char"),
        IrRigidTy::Int(i) => format!("(RigidTy.int {})", render_int_ty(*i)),
        IrRigidTy::Uint(u) => format!("(RigidTy.uint {})", render_uint_ty(*u)),
        IrRigidTy::Float(f) => format!("(RigidTy.float {})", render_float_ty(*f)),
        IrRigidTy::Never => String::from("RigidTy.never"),
        IrRigidTy::Str => String::from("RigidTy.str"),
        IrRigidTy::Tuple(elems) => format!("(RigidTy.tuple {})", render_list(elems, render_rigid_ty_pub)),
        IrRigidTy::Array(elem, len) => {
            format!("(RigidTy.array {} {len})", render_rigid_ty_pub(elem))
        }
        IrRigidTy::Slice(elem) => format!("(RigidTy.slice {})", render_rigid_ty_pub(elem)),
        IrRigidTy::Ref(m, pointee) => format!(
            "(RigidTy.ref {} {})",
            render_mutability(*m),
            render_rigid_ty_pub(pointee)
        ),
        IrRigidTy::RawPtr(m, pointee) => format!(
            "(RigidTy.rawPtr {} {})",
            render_mutability(*m),
            render_rigid_ty_pub(pointee)
        ),
        IrRigidTy::Adt(path, args) => format!(
            "(RigidTy.adt {} {})",
            render_lean_str(path),
            render_list(args, render_rigid_ty_pub)
        ),
        IrRigidTy::FnDef(path, args) => format!(
            "(RigidTy.fnDef {} {})",
            render_lean_str(path),
            render_list(args, render_rigid_ty_pub)
        ),
        IrRigidTy::FnPtr(inputs, output, safety, conv) => format!(
            "(RigidTy.fnPtr {} {} {} {})",
            render_list(inputs, render_rigid_ty_pub),
            render_rigid_ty_pub(output),
            render_safety(*safety),
            render_call_conv(conv)
        ),
        IrRigidTy::Closure(path, upvars) => format!(
            "(RigidTy.closure {} {})",
            render_lean_str(path),
            render_list(upvars, render_rigid_ty_pub)
        ),
        IrRigidTy::Dynamic(path) => format!("(RigidTy.dynamic {})", render_lean_str(path)),
        IrRigidTy::Foreign(path) => format!("(RigidTy.foreign {})", render_lean_str(path)),
        IrRigidTy::Param { index, name } => format!(
            "(RigidTy.param {} {})",
            index,
            render_lean_str(name)
        ),
        IrRigidTy::Alias { def_path, args } => format!(
            "(RigidTy.alias {} {})",
            render_lean_str(def_path),
            render_list(args, render_rigid_ty_pub)
        ),
        IrRigidTy::Other(desc) => format!("(RigidTy.other {})", render_lean_str(desc)),
    }
}

fn render_ty(ty: &IrTy) -> String {
    format!(
        "{{ kind := {}, layoutIdx := {} }}",
        render_rigid_ty_pub(&ty.kind),
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

fn render_generic_param_def(p: &IrGenericParamDef) -> String {
    format!("{{ idx := {}, name := {} }}", p.index, render_lean_str(&p.name))
}

fn render_trait_ref(t: &IrTraitRef) -> String {
    format!(
        "{{ defPath := {}, args := {} }}",
        render_lean_str(&t.def_path),
        render_list(&t.args, render_rigid_ty_pub)
    )
}

fn render_trait_impl_entry(e: &IrTraitImplEntry) -> String {
    format!(
        "{{ traitRef := {}, implPath := {} }}",
        render_trait_ref(&e.trait_ref),
        render_lean_str(&e.impl_path)
    )
}

fn render_captured_mir(mir: &IrCapturedMir) -> String {
    let mut out = String::from("{\n");
    out.push_str(&format!("    defPath := {},\n", render_lean_str(&mir.def_path)));
    out.push_str(&format!("    phase := {},\n", render_mir_phase_tag(&mir.phase)));
    out.push_str(&format!("    role := {},\n", render_contract_role(&mir.role)));
    if mir.type_param_count > 0 {
        out.push_str(&format!("    typeParamCount := {},\n", mir.type_param_count));
    }
    if !mir.generic_params.is_empty() {
        out.push_str(&format!("    genericParams := {},\n", render_list(&mir.generic_params, render_generic_param_def)));
    }
    if !mir.trait_impls.is_empty() {
        out.push_str(&format!("    traitImpls := {},\n", render_list(&mir.trait_impls, render_trait_impl_entry)));
    }
    out.push_str(&format!("    argCount := {},\n", mir.arg_count));
    out.push_str(&format!("    localDecls := {},\n", render_list(&mir.local_decls, render_local_decl)));
    out.push_str(&format!("    basicBlocks := {},\n", render_list(&mir.basic_blocks, render_basic_block_data)));
    out.push_str(&format!("    fnAbi := {},\n", render_fn_abi(&mir.fn_abi)));
    out.push_str("    layouts := layouts,\n");
    out.push_str(&format!("    allocations := {}\n", render_list(&mir.allocations, render_captured_allocation)));
    out.push_str("  }");
    out
}

// ---------------------------------------------------------------------------
// Capture-time pre-indexed `Anneal.OpaqueCalleeTable` certificate modules.
// ---------------------------------------------------------------------------

/// Sorted Lean 4.34.1 parser-reserved ASCII tokens (extracted from `Lean.Parser.getTokenTable`
/// plus `Prop` / `Sort` / `Type` / `sorry` / `admit` / `prelude` / `module`) that cannot stand as
/// bare identifiers in `def <id>` or `namespace <id>`. `sanitize_lean_ident` escapes them with a
/// trailing `_`; `validate_lean_term_expr` and `validate_lean_dotted_name` reject them as bare
/// name components.
const LEAN_RESERVED_IDENTS: &[&str] = &[
    "Prop",
    "Sort",
    "StateRefT",
    "Type",
    "abbrev",
    "add_decl_doc",
    "admit",
    "assert!",
    "assert_not_exists",
    "assert_not_imported",
    "at",
    "attribute",
    "axiom",
    "bif",
    "binder_predicate",
    "break",
    "builtin_cbv_simproc",
    "builtin_cbv_simproc_decl",
    "builtin_dsimproc",
    "builtin_dsimproc_decl",
    "builtin_grind_propagator",
    "builtin_initialize",
    "builtin_simproc",
    "builtin_simproc_decl",
    "by",
    "by?",
    "by_elab",
    "calc",
    "catch",
    "cbv_eval",
    "cbv_simproc",
    "cbv_simproc_decl",
    "class",
    "coinductive",
    "coinductive_fixpoint",
    "continue",
    "dbg_trace",
    "debug_assert!",
    "declare_bitwise_int_theorems",
    "declare_bitwise_uint_theorems",
    "declare_command_config_elab",
    "declare_command_config_elab_legacy",
    "declare_config_elab",
    "declare_config_elab_legacy",
    "declare_core_config_elab",
    "declare_eval_bin",
    "declare_eval_bin_bitwise",
    "declare_eval_bin_bool_pred",
    "declare_int_theorems",
    "declare_simp_like_tactic",
    "declare_sint_simprocs",
    "declare_syntax_cat",
    "declare_term_config_elab",
    "declare_uint_simprocs",
    "declare_uint_theorems",
    "decreasing_by",
    "def",
    "def_eval_config_item",
    "deprecated_module",
    "deprecated_syntax",
    "deriving",
    "do",
    "docs_to_verso",
    "dsimproc",
    "dsimproc_decl",
    "elab",
    "elab_rules",
    "elab_stx_quot",
    "else",
    "end",
    "eval_prec",
    "eval_prio",
    "example",
    "exists",
    "export",
    "extends",
    "f!",
    "finally",
    "for",
    "forall",
    "from",
    "fun",
    "generalizing",
    "grind_annotated",
    "grind_pattern",
    "grind_propagator",
    "have",
    "haveI",
    "hiding",
    "idbg",
    "if",
    "import",
    "in",
    "include",
    "include_str",
    "inductive",
    "inductive_fixpoint",
    "inferInstanceAs",
    "infix",
    "infixl",
    "infixr",
    "init_grind_norm",
    "init_quot",
    "initialize",
    "instance",
    "leading_parser",
    "let",
    "letI",
    "let_delayed",
    "let_expr",
    "let_fun",
    "let_tmp",
    "local",
    "logNamedError",
    "logNamedErrorAt",
    "logNamedWarning",
    "logNamedWarningAt",
    "m!",
    "macro",
    "macro_rules",
    "match",
    "match_expr",
    "matches",
    "max_prec",
    "meta",
    "mod_cast",
    "module",
    "mut",
    "mutual",
    "namespace",
    "nat_lit",
    "no_index",
    "nofun",
    "nomatch",
    "noncomputable",
    "nonrec",
    "norm_cast_add_elim",
    "notation",
    "omit",
    "opaque",
    "open",
    "panic!",
    "partial",
    "partial_fixpoint",
    "postfix",
    "prefix",
    "prelude",
    "println!",
    "private",
    "protected",
    "public",
    "recommended_spelling",
    "register_builtin_option",
    "register_error_explanation",
    "register_grind_attr",
    "register_label_attr",
    "register_linter_set",
    "register_option",
    "register_parser_alias",
    "register_simp_attr",
    "register_sym_dsimp",
    "register_sym_simp",
    "register_sym_simp_attr",
    "register_tactic_tag",
    "register_try?_tactic",
    "renaming",
    "repeat",
    "reportDbgIssue!",
    "reportEMatchIssue!",
    "reportIssue!",
    "reprove",
    "return",
    "run_cmd",
    "run_elab",
    "run_meta",
    "s!",
    "scoped",
    "seal",
    "section",
    "set_library_suggestions",
    "set_option",
    "show",
    "show_panel_widgets",
    "show_term",
    "show_term_elab",
    "simproc",
    "simproc_decl",
    "sorry",
    "structure",
    "suffices",
    "syntax",
    "tactic_alt",
    "tactic_extension",
    "tactic_name",
    "tactic_tag",
    "termination_by",
    "termination_by?",
    "test_extern",
    "then",
    "theorem",
    "this",
    "throwError",
    "throwErrorAt",
    "throwNamedError",
    "throwNamedErrorAt",
    "trailing_parser",
    "try",
    "unif_hint",
    "universe",
    "unless",
    "unlock_limits",
    "unreachable!",
    "unsafe",
    "unseal",
    "until",
    "using",
    "using!",
    "variable",
    "where",
    "while",
    "with",
    "with_annotate_term",
    "with_weak_namespace",
    "without_expected_type",
];

fn is_reserved_lean_ident(s: &str) -> bool {
    LEAN_RESERVED_IDENTS.binary_search(&s).is_ok()
}

fn is_disallowed_guillemet_char(c: char) -> bool {
    c.is_control()
        || matches!(
            c,
            '\u{2028}'
                | '\u{2029}'
                | '\u{200B}'..='\u{200F}'
                | '\u{202A}'..='\u{202E}'
                | '\u{2066}'..='\u{2069}'
                | '\u{FEFF}'
        )
}

/// One callee of a capture-time `Anneal.OpaqueCalleeTable.OpaqueCalleeTable`, carrying exactly
/// the `CapturedMir` fields the Episode 1 certificate lemmas of
/// `theory/Anneal/OpaqueCalleeTable.lean` inspect: `defPath` (raw `findCallee?` lookup),
/// `typeParamCount` (monomorphic vs. free-generic resolution) and `traitImpls` (the table-wide
/// `flatMapTraitImpls` projection sealed behind `OpaqueCalleeTable.traitImpls`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrCalleeTableEntry {
    /// Identifier hint for this callee's certificate names (`cert_lookupRaw_<ident>`, ...). Any
    /// string is accepted: the emitter sanitizes it with `sanitize_lean_ident` and
    /// deterministically disambiguates collisions in entry order.
    pub lean_ident: String,
    /// Lean term of type `CapturedMir` naming the callee body (e.g. `Mir.Demo.leaf.body`),
    /// checked by `validate_lean_term_expr` and always emitted parenthesized.
    pub mir_body_expr: String,
    /// Exact `CapturedMir.defPath` of the body (emitted through `render_lean_str`).
    pub def_path: String,
    /// `CapturedMir.typeParamCount` of the body.
    pub type_param_count: usize,
    /// `CapturedMir.traitImpls` of the body, in capture order.
    pub trait_impls: Vec<IrTraitImplEntry>,
}

impl IrCalleeTableEntry {
    /// Builds the table entry for a body emitted by `emit_mir_lean_module` (whose `body`
    /// definition `mir_body_expr` names), copying its `defPath`, `typeParamCount` and
    /// `traitImpls` so the generated certificates agree with the emitted body by construction.
    pub fn from_captured_mir(
        lean_ident: impl Into<String>,
        mir_body_expr: impl Into<String>,
        mir: &IrCapturedMir,
    ) -> Self {
        Self {
            lean_ident: lean_ident.into(),
            mir_body_expr: mir_body_expr.into(),
            def_path: mir.def_path.clone(),
            type_param_count: mir.type_param_count,
            trait_impls: mir.trait_impls.clone(),
        }
    }
}

/// Sanitizes an identifier hint into a non-empty ASCII Lean 4 identifier that is valid both on
/// its own and as the suffix of a generated certificate name: every character outside
/// `[A-Za-z0-9_]` (including `.`, which would open a namespace, and non-ASCII letters) becomes
/// `_`; an empty or all-underscore result gets a `callee` prefix (a lone `_` is the hole token);
/// a leading digit gets a `_` prefix; and a reserved Lean keyword gets a trailing `_`.
pub fn sanitize_lean_ident(hint: &str) -> String {
    let mut ident: String = hint
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    if ident.bytes().all(|b| b == b'_') {
        ident.insert_str(0, "callee");
    }
    if ident.as_bytes()[0].is_ascii_digit() {
        ident.insert(0, '_');
    }
    if is_reserved_lean_ident(ident.as_str()) {
        ident.push('_');
    }
    ident
}

/// Injective, deterministic identifier assignment: returns `base` when unused, else the first
/// unused `base_1`, `base_2`, ... (checked against every identifier assigned so far, including
/// generated suffixes), and records the result as used.
fn claim_unique_ident(base: String, used: &mut std::collections::BTreeSet<String>) -> String {
    let mut candidate = base.clone();
    let mut n = 1usize;
    while used.contains(&candidate) {
        candidate = format!("{base}_{n}");
        n += 1;
    }
    used.insert(candidate.clone());
    candidate
}

/// Checks that `expr` is a single-line Lean term built only from identifiers (optionally
/// `«»`-quoted), numerals, `.`, `@`, spaces and balanced `()` / `[]`, so splicing it into a
/// generated module can never open a comment, string or char literal, terminate the enclosing
/// parentheses or start a new command. Reserved keywords (including `sorry` / `admit`), holes `_`,
/// malformed numerals (`0abc`, `123'!`), empty `«»`, and dangling `.` / `@` are rejected.
pub fn validate_lean_term_expr(expr: &str) -> Result<(), String> {
    if expr.contains(['\n', '\r']) {
        return Err("newline in Lean term".to_owned());
    }
    let trimmed = expr.trim_matches([' ', '\t']);
    if trimmed.is_empty() {
        return Err("empty Lean term".to_owned());
    }
    let mut chars = trimmed.chars().peekable();
    let mut brackets: Vec<char> = Vec::new();
    let mut saw_ident = false;
    // Previous token class: 0 = start/space/open-bracket, 1 = ident/`»`/`)`, 2 = `]`, 3 = numeral, 4 = `.`, 5 = `@`.
    let mut prev_kind = 0u8;

    while let Some(c) = chars.next() {
        match c {
            ' ' | '\t' => {
                if matches!(prev_kind, 4 | 5) {
                    return Err("dangling `.` or `@` in Lean term".to_owned());
                }
                prev_kind = 0;
            }
            '«' => {
                if prev_kind == 3 {
                    return Err("unexpected `«` immediately after numeral".to_owned());
                }
                let mut empty = true;
                loop {
                    match chars.next() {
                        Some('»') => break,
                        None => return Err("unterminated `«` in Lean term".to_owned()),
                        Some('«') => return Err("nested `«` in Lean term".to_owned()),
                        Some(ch) if is_disallowed_guillemet_char(ch) => {
                            return Err(format!("disallowed character {ch:?} inside `«»`"));
                        }
                        Some(_) => empty = false,
                    }
                }
                if empty {
                    return Err("empty `«»` component in Lean term".to_owned());
                }
                saw_ident = true;
                prev_kind = 1;
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                if prev_kind == 3 {
                    return Err("identifier character immediately after numeral".to_owned());
                }
                let mut component = String::from(c);
                while let Some(&nc) = chars.peek() {
                    if nc.is_ascii_alphanumeric() || matches!(nc, '_' | '\'' | '!' | '?') {
                        component.push(nc);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if component == "_" {
                    return Err("wildcard hole `_` is not allowed in Lean term".to_owned());
                }
                if is_reserved_lean_ident(&component) {
                    return Err(format!("reserved Lean keyword `{component}`"));
                }
                saw_ident = true;
                prev_kind = 1;
            }
            c if c.is_ascii_digit() => {
                if matches!(prev_kind, 1 | 4 | 5) {
                    return Err("unexpected numeral after identifier, `.`, or `@`".to_owned());
                }
                if c == '0' && matches!(chars.peek(), Some('x' | 'X' | 'b' | 'B' | 'o' | 'O')) {
                    let radix_ch = chars.next().unwrap();
                    let mut digits = 0usize;
                    while let Some(&nc) = chars.peek() {
                        let ok = match radix_ch {
                            'x' | 'X' => nc.is_ascii_hexdigit() || nc == '_',
                            'b' | 'B' => matches!(nc, '0' | '1' | '_'),
                            _ => matches!(nc, '0'..='7' | '_'),
                        };
                        if ok {
                            if nc != '_' {
                                digits += 1;
                            }
                            chars.next();
                        } else {
                            break;
                        }
                    }
                    if digits == 0 {
                        return Err(format!("malformed `0{radix_ch}` numeral in Lean term"));
                    }
                } else {
                    while let Some(&nc) = chars.peek() {
                        if nc.is_ascii_digit() || nc == '_' {
                            chars.next();
                        } else {
                            break;
                        }
                    }
                }
                if let Some(&nc) = chars.peek() {
                    if nc.is_ascii_alphabetic() || matches!(nc, '\'' | '!' | '?' | '«' | '.') {
                        return Err(format!("invalid character {nc:?} after numeral in Lean term"));
                    }
                }
                prev_kind = 3;
            }
            '.' => {
                if prev_kind != 1 {
                    return Err("`.` must follow an identifier, `»`, or `)` in Lean term".to_owned());
                }
                if !matches!(chars.peek(), Some(nc) if nc.is_ascii_alphabetic() || *nc == '_' || *nc == '«') {
                    return Err("`.` must be followed by an identifier component in Lean term".to_owned());
                }
                prev_kind = 4;
            }
            '@' => {
                if prev_kind != 0 {
                    return Err("`@` must appear at term start, after whitespace, or after `(` / `[`".to_owned());
                }
                if !matches!(chars.peek(), Some(nc) if nc.is_ascii_alphabetic() || matches!(nc, '_' | '«' | '(')) {
                    return Err("dangling `@` in Lean term".to_owned());
                }
                prev_kind = 5;
            }
            '(' | '[' => {
                if prev_kind == 4 || (c == '[' && prev_kind == 5) {
                    return Err(format!("unexpected `{c}` after `.` or `@` in Lean term"));
                }
                brackets.push(c);
                prev_kind = 0;
            }
            ')' | ']' => {
                if matches!(prev_kind, 4 | 5) {
                    return Err(format!("dangling `.` or `@` before `{c}` in Lean term"));
                }
                let open = if c == ')' { '(' } else { '[' };
                if brackets.pop() != Some(open) {
                    return Err(format!("unbalanced `{c}` in Lean term"));
                }
                prev_kind = if c == ')' { 1 } else { 2 };
            }
            _ => return Err(format!("disallowed character {c:?} in Lean term")),
        }
    }
    if matches!(prev_kind, 4 | 5) {
        return Err("trailing `.` or `@` in Lean term".to_owned());
    }
    if !brackets.is_empty() {
        return Err("unclosed `(` / `[` in Lean term".to_owned());
    }
    if !saw_ident {
        return Err("Lean term must reference at least one identifier".to_owned());
    }
    Ok(())
}

/// Checks that `name` is a dotted Lean name (`A.B.C`) whose components are ASCII identifiers
/// (`[A-Za-z_][A-Za-z0-9_']*`, neither the hole `_` nor a reserved keyword) or non-empty
/// `«»`-quoted components without control or format characters, so it can be spliced into generated
/// `import` / `namespace` / `end` lines.
pub fn validate_lean_dotted_name(name: &str) -> Result<(), String> {
    let mut chars = name.chars().peekable();
    loop {
        match chars.peek().copied() {
            Some('«') => {
                chars.next();
                let mut empty = true;
                loop {
                    match chars.next() {
                        Some('»') => break,
                        None | Some('«') => {
                            return Err(format!("malformed `«»` component in Lean name {name:?}"));
                        }
                        Some(c) if is_disallowed_guillemet_char(c) => {
                            return Err(format!("disallowed character in Lean name {name:?}"));
                        }
                        Some(_) => empty = false,
                    }
                }
                if empty {
                    return Err(format!("empty `«»` component in Lean name {name:?}"));
                }
            }
            Some(c) if c.is_ascii_alphabetic() || c == '_' => {
                let mut component = String::new();
                while let Some(&c) = chars.peek() {
                    if !(c.is_ascii_alphanumeric() || c == '_' || c == '\'') {
                        break;
                    }
                    component.push(c);
                    chars.next();
                }
                if component == "_" || is_reserved_lean_ident(&component) {
                    return Err(format!("invalid component `{component}` in Lean name {name:?}"));
                }
            }
            _ => return Err(format!("invalid Lean name {name:?}")),
        }
        match chars.next() {
            None => return Ok(()),
            Some('.') => {}
            Some(c) => return Err(format!("unexpected character {c:?} in Lean name {name:?}")),
        }
    }
}

/// Formats a complete, deterministic proof-side Lean 4 module sealing `entries` into a
/// pre-indexed `Anneal.OpaqueCalleeTable.OpaqueCalleeTable` with one-time and per-callee `O(1)`
/// lookup certificates. Equivalent to `emit_opaque_callee_table_lean_module_with_imports` with
/// no extra imports (so `mir_body_expr` must then name bodies visible through `Trusted` and
/// `Anneal.OpaqueCalleeTable`).
pub fn emit_opaque_callee_table_lean_module(
    lean_module_namespace: &str,
    entries: &[IrCalleeTableEntry],
) -> String {
    emit_opaque_callee_table_lean_module_with_imports(lean_module_namespace, &[], entries)
}

/// Formats a complete, deterministic proof-side Lean 4 module sealing `entries` into a
/// pre-indexed `Anneal.OpaqueCalleeTable.OpaqueCalleeTable`, against the frozen Episode 1
/// signatures of `theory/Anneal/OpaqueCalleeTable.lean`:
///
/// - `import Trusted`, `import Anneal.OpaqueCalleeTable`, then each of `extra_imports` (e.g. the
///   `Mir.<Crate>.<Item>` modules defining the bodies) once, in order, so the file compiles
///   standalone. This proof-side module is never imported by a trusted `Mir/<Item>.lean` module,
///   which keeps importing `Trusted` only.
/// - Right-nested suffixes `calleeSuffix{M} := List.nil`, `calleeSuffix{k} := List.cons e_k
///   calleeSuffix{k+1}`, then `calleeList := calleeSuffix0` and
///   `table := OpaqueCalleeTable.ofList calleeList`, keeping every entry (shadowed ones included)
///   in capture order, exactly as `findCallee?` and `flatMapTraitImpls` see them.
/// - `cert_traitImpls : table.traitImpls = <flat traitImpls list>`, proven once per table.
/// - For the first entry `k` with each `defPath` (a later entry with an equal `defPath` is
///   shadowed: `findCallee?` resolves the path to entry `k`, so no certificate is emitted for it):
///   `cert_lookupRaw_<ident>` via `lookupRaw_ofList_append_cons_of_skips` (one kernel-evaluated
///   `stringEq` skip fact over the prefix plus `rfl` on the body's `defPath`); for a monomorphic
///   body, `cert_lookup_mono_<ident>` via `lookupCallee_hit_mono`; and for a generic body whose
///   `defPath` no entry registers as a trait method (`TraitRef.defPath`), `cert_noImpl_<ident>`
///   and the `tbl.toList`-free `cert_lookup_free_poly_<ident>` (with `extra = []`) via
///   `lookupCallee_hit_free_poly_opaque`.
///
/// Each certificate re-checks the entry against the body it names (`rfl` on `defPath` and
/// `typeParamCount`, kernel evaluation of the trait-impl facts), so an inconsistent entry makes
/// the module fail to elaborate rather than state anything false.
///
/// # Panics
///
/// Panics if `lean_module_namespace` or an extra import is not a valid dotted Lean name
/// (`validate_lean_dotted_name`), or if an entry's `mir_body_expr` is rejected by
/// `validate_lean_term_expr`.
pub fn emit_opaque_callee_table_lean_module_with_imports(
    lean_module_namespace: &str,
    extra_imports: &[&str],
    entries: &[IrCalleeTableEntry],
) -> String {
    if let Err(err) = validate_lean_dotted_name(lean_module_namespace) {
        panic!("invalid OpaqueCalleeTable module namespace: {err}");
    }
    let mut imports: Vec<&str> = vec!["Trusted", "Anneal.OpaqueCalleeTable"];
    for &import in extra_imports {
        if let Err(err) = validate_lean_dotted_name(import) {
            panic!("invalid OpaqueCalleeTable module import: {err}");
        }
        if !imports.contains(&import) {
            imports.push(import);
        }
    }
    let bodies: Vec<String> = entries
        .iter()
        .enumerate()
        .map(|(k, entry)| {
            if let Err(err) = validate_lean_term_expr(&entry.mir_body_expr) {
                panic!("invalid `mir_body_expr` for OpaqueCalleeTable entry {k}: {err}");
            }
            format!("({})", entry.mir_body_expr.trim())
        })
        .collect();
    let m = entries.len();

    let mut out = String::new();
    for import in &imports {
        out.push_str(&format!("import {import}\n"));
    }
    out.push_str(&format!(
        "\nnamespace {lean_module_namespace}\n\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.Layout\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.MirAst\n\
         open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.MirSemantics\n\
         open Anneal.OpaqueCalleeTable\n\n\
         /-! Capture-time pre-indexed `OpaqueCalleeTable` over {m} captured callee bodies, with a \
         one-time `traitImpls` certificate and per-callee `O(1)` lookup certificates. -/\n\n"
    ));

    out.push_str(&format!("def calleeSuffix{m} : List CapturedMir := List.nil\n"));
    for k in (0..m).rev() {
        out.push_str(&format!(
            "def calleeSuffix{k} : List CapturedMir := List.cons {} calleeSuffix{}\n",
            bodies[k],
            k + 1
        ));
    }
    out.push_str(
        "\ndef calleeList : List CapturedMir := calleeSuffix0\n\n\
         def table : OpaqueCalleeTable := OpaqueCalleeTable.ofList calleeList\n\n",
    );

    let flat_trait_impls: Vec<&IrTraitImplEntry> =
        entries.iter().flat_map(|entry| entry.trait_impls.iter()).collect();
    out.push_str(&format!(
        "/-- One-time per-table `traitImpls` certificate. -/\n\
         theorem cert_traitImpls : table.traitImpls = {} := by\n  \
         unfold table\n  \
         rw [traitImpls_ofList]\n  \
         decide +kernel\n\n",
        render_list(&flat_trait_impls, |entry| render_trait_impl_entry(entry))
    ));

    let mut used_idents = std::collections::BTreeSet::new();
    let mut first_index: std::collections::BTreeMap<&str, usize> =
        std::collections::BTreeMap::new();
    for (k, entry) in entries.iter().enumerate() {
        if let Some(&j) = first_index.get(entry.def_path.as_str()) {
            out.push_str(&format!(
                "-- Callee [{k}] is shadowed by callee [{j}] (equal `defPath`): `lookupRaw` \
                 resolves to [{j}], so no certificate is emitted for [{k}].\n\n"
            ));
            continue;
        }
        first_index.insert(entry.def_path.as_str(), k);
        let ident = claim_unique_ident(sanitize_lean_ident(&entry.lean_ident), &mut used_idents);
        let def_path = render_lean_str(&entry.def_path);
        let body = &bodies[k];
        let next = k + 1;
        out.push_str(&format!(
            "/-- Raw `O(1)` lookup certificate for callee [{k}]. -/\n\
             theorem cert_lookupRaw_{ident} :\n    \
             table.lookupRaw {def_path} = Option.some {body} :=\n  \
             lookupRaw_ofList_append_cons_of_skips (pre := {}) (post := calleeSuffix{next})\n    \
             (by decide +kernel) (rfl : {body}.defPath = {def_path})\n\n",
            render_list(&bodies[..k], |b| b.clone())
        ));
        if entry.type_param_count == 0 {
            out.push_str(&format!(
                "/-- Direct `O(1)` monomorphic lookup certificate for callee [{k}]. -/\n\
                 theorem cert_lookup_mono_{ident} (callerLayouts : LayoutTable)\n    \
                 (extra : List TraitImplEntry) :\n    \
                 table.lookup callerLayouts {def_path} List.nil extra = Option.some {body} :=\n  \
                 lookupCallee_hit_mono cert_lookupRaw_{ident} (rfl : {body}.typeParamCount = 0)\n\n"
            ));
        } else if !flat_trait_impls
            .iter()
            .any(|impl_entry| impl_entry.trait_ref.def_path == entry.def_path)
        {
            let arity = entry.type_param_count;
            out.push_str(&format!(
                "/-- No `TraitImplEntry` of the table targets callee [{k}] (stated over the sealed \
                 `table.traitImpls`, exactly the `hnoTbl` premise of \
                 `lookupCallee_hit_free_poly_of_noImpl_opaque`). -/\n\
                 theorem cert_noImpl_{ident} :\n    \
                 hasTraitImplForDefPath table.traitImpls {def_path} = false := by\n  \
                 rw [cert_traitImpls]\n  \
                 decide +kernel\n\n\
                 /-- `tbl.toList`-free and `impls`-list-free `O(1)` free-generic lookup \
                 certificate for callee [{k}] with arbitrary caller `extra` (`O(|extra|)`). -/\n\
                 theorem cert_lookup_free_poly_extra_{ident} (callerLayouts : LayoutTable)\n    \
                 (firstArg : RigidTy) (restArgs : List RigidTy) (extra : List TraitImplEntry)\n    \
                 (argLayouts : List TypeLayout)\n    \
                 (hextra : hasTraitImplForDefPath extra {def_path} = false)\n    \
                 (harity : (List.cons firstArg restArgs).length = {arity})\n    \
                 (hlay : instantiationLayouts? callerLayouts (List.cons firstArg restArgs) =\n      \
                 Option.some argLayouts) :\n    \
                 table.lookup callerLayouts {def_path} (List.cons firstArg restArgs) extra =\n      \
                 Option.some ({body}.instantiate ((List.cons firstArg restArgs).zip argLayouts)) :=\n  \
                 lookupCallee_hit_free_poly_of_noImpl_opaque cert_noImpl_{ident} hextra\n    \
                 cert_lookupRaw_{ident} (harity.trans (rfl : {arity} = {body}.typeParamCount)) hlay\n\n\
                 /-- `tbl.toList`-free `O(1)` free-generic lookup certificate for callee [{k}] \
                 (`extra = []`). -/\n\
                 theorem cert_lookup_free_poly_{ident} (callerLayouts : LayoutTable)\n    \
                 (firstArg : RigidTy) (restArgs : List RigidTy) (argLayouts : List TypeLayout)\n    \
                 (harity : (List.cons firstArg restArgs).length = {arity})\n    \
                 (hlay : instantiationLayouts? callerLayouts (List.cons firstArg restArgs) =\n      \
                 Option.some argLayouts) :\n    \
                 table.lookup callerLayouts {def_path} (List.cons firstArg restArgs) List.nil =\n      \
                 Option.some ({body}.instantiate ((List.cons firstArg restArgs).zip argLayouts)) :=\n  \
                 cert_lookup_free_poly_extra_{ident} callerLayouts firstArg restArgs List.nil\n    \
                 argLayouts rfl harity hlay\n\n"
            ));
        }
    }

    out.push_str(&format!("end {lean_module_namespace}\n"));
    out
}

// ---------------------------------------------------------------------------
// `DecidableEq`-without-redundant-`BEq` (`LawfulBEq`) deriving hygiene.
// ---------------------------------------------------------------------------

/// If `s` starts with `open` (`(` or `[`) and that opener's matching `close` (`)` or `]`) occurs in
/// `s` (ignoring delimiters inside `"..."` strings and `«...»` guillemets), returns the byte index
/// of that matching `close`.
fn find_matching_delim(s: &str, open: char, close: char) -> Option<usize> {
    if !s.starts_with(open) {
        return None;
    }
    let mut depth = 0usize;
    let mut in_str = false;
    let mut escaped = false;
    let mut in_gui = false;
    for (i, c) in s.char_indices() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        if in_gui {
            if c == '»' {
                in_gui = false;
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '«' => in_gui = true,
            _ if c == open => depth += 1,
            _ if c == close => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Strips leading `@[...]` attributes (including nested brackets like `@[aesop safe [constructors]]`)
/// and outer parentheses wrapping the entire entry, then splits the remaining entry into
/// `(head_class_ref, arg_tail)` while respecting `«...»` guillemets and parenthesized heads like
/// `(CustomHandler) opt`.
fn parse_deriving_entry(entry: &str) -> (&str, &str) {
    let mut s = entry.trim();
    while let Some(after_at) = s.strip_prefix('@') {
        let after_at = after_at.trim_start();
        if !after_at.starts_with('[') {
            break;
        }
        match find_matching_delim(after_at, '[', ']') {
            Some(close) => s = after_at[close + 1..].trim_start(),
            None => return ("", ""),
        }
    }
    loop {
        let t = s.trim();
        if let Some(close) = find_matching_delim(t, '(', ')') {
            if close + 1 == t.len() {
                s = &t[1..close];
                continue;
            }
        }
        s = t;
        break;
    }
    if s.is_empty() {
        return ("", "");
    }
    if s.starts_with('(') {
        if let Some(close) = find_matching_delim(s, '(', ')') {
            let inner = s[1..close].trim();
            let (head, inner_args) = parse_deriving_entry(inner);
            let outer_args = s[close + 1..].trim();
            // Keep *every* argument in the tail: `(Handler a) b` must neither dedup against
            // `Handler a` / `(Handler a) c` nor ever classify as a unary class.
            let tail = if inner_args.is_empty() {
                outer_args
            } else if outer_args.is_empty() {
                inner_args
            } else {
                // `inner_args` is a non-empty subslice of `s`: span it through `outer_args`.
                &s[inner_args.as_ptr() as usize - s.as_ptr() as usize..]
            };
            return (head, tail);
        }
        return ("", "");
    }
    let mut in_gui = false;
    let mut head_end = s.len();
    for (i, c) in s.char_indices() {
        if in_gui {
            if c == '»' {
                in_gui = false;
            }
            continue;
        }
        if c == '«' {
            in_gui = true;
            continue;
        }
        if c.is_whitespace() || matches!(c, '(' | '[' | '{' | '⟨' | '⦃') {
            head_end = i;
            break;
        }
    }
    (&s[..head_end], s[head_end..].trim())
}

/// Splits a dotted Lean identifier on `.` outside `«...»` guillemets.
fn split_dotted_outside_guillemets(head: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut start = 0usize;
    let mut in_gui = false;
    for (i, c) in head.char_indices() {
        if in_gui {
            if c == '»' {
                in_gui = false;
            }
        } else if c == '«' {
            in_gui = true;
        } else if c == '.' {
            parts.push(&head[start..i]);
            start = i + 1;
        }
    }
    parts.push(&head[start..]);
    parts
}

fn unwrap_guillemet_component(comp: &str) -> &str {
    comp.strip_prefix('«')
        .and_then(|s| s.strip_suffix('»'))
        .unwrap_or(comp)
}

/// Unqualified unary class name of a `deriving` entry (`_root_.BEq`, `Foo.DecidableEq`,
/// `@[expose] BEq`, `(BEq)`, `Lean.«BEq»`, and `«a b».BEq` map to `Some("BEq")` /
/// `Some("DecidableEq")`, whereas an atomic guillemet containing a dot `«Not.BEq»` maps to
/// `Some("Not.BEq")` and a multi-argument class term `Custom.BEq opt` maps to `None`).
fn deriving_unary_class_core(entry: &str) -> Option<&str> {
    let (head, arg_tail) = parse_deriving_entry(entry);
    if head.is_empty() || !arg_tail.is_empty() {
        return None;
    }
    let last = *split_dotted_outside_guillemets(head).last()?;
    Some(unwrap_guillemet_component(last))
}

/// Deduplication key of a `deriving` entry: attributes and outer parentheses stripped, leading
/// `_root_.` removed, simple ASCII guillemets (`«DecidableEq»` -> `DecidableEq`) normalized, and
/// trailing arguments whitespace-collapsed.
fn deriving_class_dedup_key(entry: &str) -> String {
    let (head, arg_tail) = parse_deriving_entry(entry);
    if head.is_empty() {
        return String::new();
    }
    let raw_parts = split_dotted_outside_guillemets(head);
    let parts = if raw_parts.len() > 1 && unwrap_guillemet_component(raw_parts[0]) == "_root_" {
        &raw_parts[1..]
    } else {
        &raw_parts[..]
    };
    let norm_head: String = parts
        .iter()
        .map(|&comp| {
            let unq = unwrap_guillemet_component(comp);
            let is_plain_ident = !unq.is_empty()
                && unq.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'')
                && !unq.as_bytes()[0].is_ascii_digit()
                && unq != "_"
                && !is_reserved_lean_ident(unq);
            if is_plain_ident {
                unq.to_owned()
            } else {
                comp.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(".");
    if arg_tail.is_empty() {
        norm_head
    } else {
        let norm_args = arg_tail.split_whitespace().collect::<Vec<_>>().join(" ");
        format!("{norm_head} {norm_args}")
    }
}

/// Sanitizes the classes of one `deriving` clause (cl/1022563952): whenever `DecidableEq`
/// (possibly qualified, parenthesized or `@[...]`-attributed) is present, every unary `BEq` entry
/// (in any of those forms) is dropped, so the derived structural `BEq` instance never shadows
/// `instBEqOfDecidableEq` and core's `instLawfulBEq` (`beq_iff_eq`) keeps applying. Entries are
/// trimmed, empty entries dropped, and duplicates (same class reference) removed keeping the
/// first occurrence, preserving order.
pub fn sanitize_deriving_classes<'a>(classes: &[&'a str]) -> Vec<&'a str> {
    let has_decidable_eq = classes
        .iter()
        .any(|class| deriving_unary_class_core(class) == Some("DecidableEq"));
    let mut seen: Vec<String> = Vec::new();
    let mut out = Vec::new();
    for &class in classes {
        let class = class.trim();
        let (head, _) = parse_deriving_entry(class);
        if head.is_empty()
            || (has_decidable_eq && deriving_unary_class_core(class) == Some("BEq"))
        {
            continue;
        }
        let key = deriving_class_dedup_key(class);
        if !seen.contains(&key) {
            seen.push(key);
            out.push(class);
        }
    }
    out
}

/// Renders a `deriving` clause over `sanitize_deriving_classes(classes)` (`""` when no class
/// remains), the only way Lean code generated by this module may spell a `deriving` clause.
pub fn render_deriving_clause(classes: &[&str]) -> String {
    let classes = sanitize_deriving_classes(classes);
    if classes.is_empty() {
        String::new()
    } else {
        format!("deriving {}", classes.join(", "))
    }
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
            role: IrContractRole::Subject, type_param_count: 0, generic_params: vec![], trait_impls: vec![],
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

    #[test]
    fn emit_polymorphic_module_with_trait_impl_and_alias() {
        let param_placeholder = IrTypeLayout {
            size: IrSize { bytes: 0 },
            align: IrAlign { bytes: 1 },
            backend_repr: IrBackendRepr::Memory,
            fields: IrFieldsShape::Primitive,
            variants: IrVariantsShape::Single { index: 0 },
            is_uninhabited: false,
            field_layouts: vec![],
        };
        let tuple_layout = IrTypeLayout {
            size: IrSize { bytes: 0 },
            align: IrAlign { bytes: 1 },
            backend_repr: IrBackendRepr::Memory,
            fields: IrFieldsShape::Arbitrary {
                offsets: vec![IrSize { bytes: 0 }, IrSize { bytes: 0 }],
                memory_index: vec![0, 1],
            },
            variants: IrVariantsShape::Single { index: 0 },
            is_uninhabited: false,
            field_layouts: vec![0, 0],
        };
        let param_ty = IrTy {
            kind: IrRigidTy::Param {
                index: 0,
                name: String::from("T"),
            },
            layout_idx: 0,
        };
        let alias_ty = IrTy {
            kind: IrRigidTy::Alias {
                def_path: String::from("demo::MyTrait::Assoc"),
                args: vec![param_ty.kind.clone()],
            },
            layout_idx: 1,
        };
        let mir = IrCapturedMir {
            def_path: String::from("demo::<Wrapper<T> as MyTrait>::method"),
            phase: IrMirPhaseTag::RuntimeOptimized,
            role: IrContractRole::Subject,
            type_param_count: 1,
            generic_params: vec![IrGenericParamDef {
                index: 0,
                name: String::from("T"),
            }],
            trait_impls: vec![IrTraitImplEntry {
                trait_ref: IrTraitRef {
                    def_path: String::from("demo::MyTrait::method"),
                    args: vec![IrRigidTy::Adt(
                        String::from("demo::Wrapper"),
                        vec![param_ty.kind.clone()],
                    )],
                },
                impl_path: String::from("demo::<Wrapper<T> as MyTrait>::method"),
            }],
            arg_count: 1,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: alias_ty,
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: param_ty,
                    debug_name: Some(String::from("x")),
                },
            ],
            basic_blocks: vec![IrBasicBlockData {
                statements: vec![],
                terminator: IrTerminator {
                    kind: IrTerminatorKind::Return,
                    span: String::from("<dummy>"),
                    comment: None,
                },
                is_cleanup: false,
            }],
            fn_abi: IrFnAbi {
                args: vec![IrArgAbi {
                    layout: param_placeholder.clone(),
                    mode: IrAbiPassMode::Direct,
                }],
                ret: IrArgAbi {
                    layout: tuple_layout.clone(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: false,
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![param_placeholder, tuple_layout],
            },
            allocations: vec![],
        };

        let code = emit_mir_lean_module("Mir.Demo.Wrapper_T_as_MyTrait_method", &mir);
        assert!(code.contains("typeParamCount := 1"));
        assert!(code.contains("genericParams := (List.cons { idx := 0, name := \"T\" } List.nil)"));
        assert!(code.contains("traitImpls := (List.cons { traitRef := { defPath := \"demo::MyTrait::method\", args := (List.cons (RigidTy.adt \"demo::Wrapper\" (List.cons (RigidTy.param 0 \"T\") List.nil)) List.nil) }, implPath := \"demo::<Wrapper<T> as MyTrait>::method\" } List.nil)"));
        assert!(code.contains("(RigidTy.alias \"demo::MyTrait::Assoc\" (List.cons (RigidTy.param 0 \"T\") List.nil))"));
        assert!(code.contains("fieldLayouts := (List.cons 0 (List.cons 0 List.nil))"));
    }
}

#[cfg(test)]
mod opaque_callee_table_tests {
    use super::*;
    use std::collections::BTreeSet;
    use std::ffi::OsStr;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    fn u32_layout() -> IrTypeLayout {
        IrTypeLayout {
            size: IrSize { bytes: 4 },
            align: IrAlign { bytes: 4 },
            backend_repr: IrBackendRepr::Scalar(IrScalarLayout::Initialized {
                value: IrPrimitiveKind::Int { bits: 32, signed: false },
                valid_range: IrWrappingRange { start: 0, end_: u32::MAX as u128 },
            }),
            fields: IrFieldsShape::Primitive,
            variants: IrVariantsShape::Single { index: 0 },
            is_uninhabited: false,
            field_layouts: vec![],
        }
    }

    /// A captured `fn() -> u32 { answer }` body with the given identity fields.
    fn fixture_mir(
        def_path: &str,
        type_param_count: usize,
        trait_impls: Vec<IrTraitImplEntry>,
        answer: u128,
    ) -> IrCapturedMir {
        let layout = u32_layout();
        let u32_ty = IrTy { kind: IrRigidTy::Uint(IrUintTy::U32), layout_idx: 0 };
        IrCapturedMir {
            def_path: def_path.to_owned(),
            phase: IrMirPhaseTag::RuntimeOptimized,
            role: IrContractRole::Subject,
            type_param_count,
            generic_params: (0..type_param_count)
                .map(|i| IrGenericParamDef { index: i as u32, name: format!("T{i}") })
                .collect(),
            trait_impls,
            arg_count: 0,
            local_decls: vec![IrLocalDecl {
                mutability: IrMutability::Mut,
                ty: u32_ty.clone(),
                debug_name: None,
            }],
            basic_blocks: vec![IrBasicBlockData {
                statements: vec![IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace { local_: 0, projection: vec![] },
                        IrRvalue::Use(IrOperand::Constant(IrConstOperand {
                            ty: u32_ty.clone(),
                            val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                                bits: answer,
                                size_bytes: 4,
                            })),
                        })),
                    ),
                    span: String::from("src/lib.rs:1:1: 1:2"),
                    comment: None,
                }],
                terminator: IrTerminator {
                    kind: IrTerminatorKind::Return,
                    span: String::from("src/lib.rs:1:3: 1:3"),
                    comment: None,
                },
                is_cleanup: false,
            }],
            fn_abi: IrFnAbi {
                args: vec![],
                ret: IrArgAbi { layout: layout.clone(), mode: IrAbiPassMode::Direct },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts: IrLayoutTable { pointer_bits: 64, is_little_endian: true, entries: vec![layout] },
            allocations: vec![],
        }
    }

    fn entry(
        ident: &str,
        body: &str,
        def_path: &str,
        type_param_count: usize,
        trait_impls: Vec<IrTraitImplEntry>,
    ) -> IrCalleeTableEntry {
        IrCalleeTableEntry {
            lean_ident: ident.to_owned(),
            mir_body_expr: body.to_owned(),
            def_path: def_path.to_owned(),
            type_param_count,
            trait_impls,
        }
    }

    fn trait_impl(trait_def_path: &str, impl_path: &str) -> IrTraitImplEntry {
        IrTraitImplEntry {
            trait_ref: IrTraitRef {
                def_path: trait_def_path.to_owned(),
                args: vec![IrRigidTy::Uint(IrUintTy::U32)],
            },
            impl_path: impl_path.to_owned(),
        }
    }

    /// Names of the `theorem`s of emitted Lean code, in order.
    fn theorem_names(code: &str) -> Vec<&str> {
        code.lines()
            .filter_map(|line| line.strip_prefix("theorem "))
            .map(|rest| rest.split([' ', ':']).next().unwrap())
            .collect()
    }

    /// Decodes a Lean 4 string-literal body exactly like `Lean.Syntax.decodeQuotedChar`
    /// (`\xHH` / `\uHHHH` denote code points).
    fn decode_lean_str_body(body: &str) -> String {
        let mut out = String::new();
        let mut chars = body.chars();
        while let Some(c) = chars.next() {
            if c != '\\' {
                assert_ne!(c, '"', "unescaped quote in {body:?}");
                out.push(c);
                continue;
            }
            let decoded = match chars.next().expect("dangling backslash") {
                '\\' => '\\',
                '"' => '"',
                '\'' => '\'',
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                escape @ ('x' | 'u') => {
                    let digits = if escape == 'x' { 2 } else { 4 };
                    let hex: String = chars.by_ref().take(digits).collect();
                    char::from_u32(u32::from_str_radix(&hex, 16).unwrap()).unwrap()
                }
                other => panic!("invalid Lean escape `\\{other}` in {body:?}"),
            };
            out.push(decoded);
        }
        out
    }

    #[test]
    fn callee_table_multi_callee_mono_module_shape() {
        let entries = vec![
            entry("demo::a", "Mir.Demo.A.body", "demo::a", 0, vec![]),
            entry("demo::b", " Mir.Demo.B.body ", "demo::b", 0, vec![]),
            entry("demo::c", "Mir.Demo.C.body", "demo::c", 0, vec![]),
        ];
        let code = emit_opaque_callee_table_lean_module("Gen.Demo.Callees", &entries);
        assert_eq!(code, emit_opaque_callee_table_lean_module("Gen.Demo.Callees", &entries));
        assert!(code.starts_with(
            "import Trusted\nimport Anneal.OpaqueCalleeTable\n\nnamespace Gen.Demo.Callees\n\n"
        ));
        for open in ["Layout", "MirAst", "MirSemantics"] {
            assert!(code.contains(&format!("open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.{open}\n")));
        }
        assert!(code.contains("open Anneal.OpaqueCalleeTable\n"));
        assert!(code.contains(
            "def calleeSuffix3 : List CapturedMir := List.nil\n\
             def calleeSuffix2 : List CapturedMir := List.cons (Mir.Demo.C.body) calleeSuffix3\n\
             def calleeSuffix1 : List CapturedMir := List.cons (Mir.Demo.B.body) calleeSuffix2\n\
             def calleeSuffix0 : List CapturedMir := List.cons (Mir.Demo.A.body) calleeSuffix1\n\n\
             def calleeList : List CapturedMir := calleeSuffix0\n\n\
             def table : OpaqueCalleeTable := OpaqueCalleeTable.ofList calleeList\n"
        ));
        assert!(code.contains(
            "theorem cert_traitImpls : table.traitImpls = List.nil := by\n  unfold table\n  \
             rw [traitImpls_ofList]\n  decide +kernel\n"
        ));
        assert!(code.contains(
            "theorem cert_lookupRaw_demo__c :\n    \
             table.lookupRaw \"demo::c\" = Option.some (Mir.Demo.C.body) :=\n  \
             lookupRaw_ofList_append_cons_of_skips (pre := (List.cons (Mir.Demo.A.body) \
             (List.cons (Mir.Demo.B.body) List.nil))) (post := calleeSuffix3)\n    \
             (by decide +kernel) (rfl : (Mir.Demo.C.body).defPath = \"demo::c\")\n"
        ));
        assert!(code.contains(
            "lookupRaw_ofList_append_cons_of_skips (pre := List.nil) (post := calleeSuffix1)\n"
        ));
        assert!(code.contains(
            "theorem cert_lookup_mono_demo__b (callerLayouts : LayoutTable)\n    \
             (extra : List TraitImplEntry) :\n    \
             table.lookup callerLayouts \"demo::b\" List.nil extra = Option.some (Mir.Demo.B.body) :=\n  \
             lookupCallee_hit_mono cert_lookupRaw_demo__b (rfl : (Mir.Demo.B.body).typeParamCount = 0)\n"
        ));
        assert_eq!(
            theorem_names(&code),
            vec![
                "cert_traitImpls",
                "cert_lookupRaw_demo__a",
                "cert_lookup_mono_demo__a",
                "cert_lookupRaw_demo__b",
                "cert_lookup_mono_demo__b",
                "cert_lookupRaw_demo__c",
                "cert_lookup_mono_demo__c",
            ]
        );
        assert!(!code.contains("free_poly") && !code.contains("noImpl"));
        assert!(code.ends_with("end Gen.Demo.Callees\n"));
    }

    #[test]
    fn callee_table_generic_free_poly_certificates() {
        let entries = vec![
            entry("demo::leaf", "Mir.Demo.Leaf.body", "demo::leaf", 0, vec![]),
            entry("demo::poly", "Mir.Demo.Poly.body", "demo::poly", 2, vec![]),
        ];
        let code = emit_opaque_callee_table_lean_module("Gen.Poly", &entries);
        assert!(code.contains(
            "theorem cert_noImpl_demo__poly :\n    \
             hasTraitImplForDefPath table.traitImpls \"demo::poly\" = false := by\n  \
             rw [cert_traitImpls]\n  decide +kernel\n"
        ));
        assert!(code.contains(
            "theorem cert_lookup_free_poly_extra_demo__poly (callerLayouts : LayoutTable)\n    \
             (firstArg : RigidTy) (restArgs : List RigidTy) (extra : List TraitImplEntry)\n    \
             (argLayouts : List TypeLayout)\n    \
             (hextra : hasTraitImplForDefPath extra \"demo::poly\" = false)\n    \
             (harity : (List.cons firstArg restArgs).length = 2)\n    \
             (hlay : instantiationLayouts? callerLayouts (List.cons firstArg restArgs) =\n      \
             Option.some argLayouts) :\n    \
             table.lookup callerLayouts \"demo::poly\" (List.cons firstArg restArgs) extra =\n      \
             Option.some ((Mir.Demo.Poly.body).instantiate ((List.cons firstArg restArgs).zip argLayouts)) :=\n  \
             lookupCallee_hit_free_poly_of_noImpl_opaque cert_noImpl_demo__poly hextra\n    \
             cert_lookupRaw_demo__poly (harity.trans (rfl : 2 = (Mir.Demo.Poly.body).typeParamCount)) hlay\n"
        ));
        assert!(code.contains(
            "theorem cert_lookup_free_poly_demo__poly (callerLayouts : LayoutTable)\n    \
             (firstArg : RigidTy) (restArgs : List RigidTy) (argLayouts : List TypeLayout)\n    \
             (harity : (List.cons firstArg restArgs).length = 2)\n    \
             (hlay : instantiationLayouts? callerLayouts (List.cons firstArg restArgs) =\n      \
             Option.some argLayouts) :\n    \
             table.lookup callerLayouts \"demo::poly\" (List.cons firstArg restArgs) List.nil =\n      \
             Option.some ((Mir.Demo.Poly.body).instantiate ((List.cons firstArg restArgs).zip argLayouts)) :=\n  \
             cert_lookup_free_poly_extra_demo__poly callerLayouts firstArg restArgs List.nil\n    \
             argLayouts rfl harity hlay\n"
        ));
        assert_eq!(
            theorem_names(&code),
            vec![
                "cert_traitImpls",
                "cert_lookupRaw_demo__leaf",
                "cert_lookup_mono_demo__leaf",
                "cert_lookupRaw_demo__poly",
                "cert_noImpl_demo__poly",
                "cert_lookup_free_poly_extra_demo__poly",
                "cert_lookup_free_poly_demo__poly",
            ]
        );
    }

    #[test]
    fn callee_table_trait_impls_are_flattened_and_block_free_poly_certificates() {
        let area_impl = trait_impl("demo::Area::area", "demo::<Square as Area>::area");
        let show_impl = trait_impl("demo::Show::show", "demo::<Square as Show>::show");
        let entries = vec![
            entry(
                "square_area",
                "Mir.Demo.SquareArea.body",
                "demo::<Square as Area>::area",
                0,
                vec![area_impl.clone()],
            ),
            // Registered as a trait method by another entry.
            entry("area", "Mir.Demo.AreaMethod.body", "demo::Area::area", 1, vec![]),
            // Registered as a trait method by its own entry.
            entry("display", "Mir.Demo.Show.body", "demo::Show::show", 1, vec![show_impl.clone()]),
            entry("free", "Mir.Demo.Free.body", "demo::free", 1, vec![]),
        ];
        let code = emit_opaque_callee_table_lean_module("Gen.Traits", &entries);
        let flat = render_list(&[area_impl, show_impl], render_trait_impl_entry);
        assert!(code.contains(&format!("theorem cert_traitImpls : table.traitImpls = {flat} := by\n")));
        assert_eq!(
            theorem_names(&code),
            vec![
                "cert_traitImpls",
                "cert_lookupRaw_square_area",
                "cert_lookup_mono_square_area",
                "cert_lookupRaw_area",
                "cert_lookupRaw_display",
                "cert_lookupRaw_free",
                "cert_noImpl_free",
                "cert_lookup_free_poly_extra_free",
                "cert_lookup_free_poly_free",
            ]
        );
    }

    #[test]
    fn callee_table_empty_table() {
        let code = emit_opaque_callee_table_lean_module("Gen.Empty", &[]);
        assert!(code.contains(
            "def calleeSuffix0 : List CapturedMir := List.nil\n\n\
             def calleeList : List CapturedMir := calleeSuffix0\n\n\
             def table : OpaqueCalleeTable := OpaqueCalleeTable.ofList calleeList\n"
        ));
        assert!(code.contains("theorem cert_traitImpls : table.traitImpls = List.nil := by\n"));
        assert_eq!(theorem_names(&code), vec!["cert_traitImpls"]);
        assert!(!code.contains("calleeSuffix1"));
        assert!(code.ends_with("end Gen.Empty\n"));
    }

    #[test]
    fn callee_table_shadowed_duplicate_def_path_gets_no_certificate() {
        let entries = vec![
            entry("first", "Mir.Demo.Leaf.body", "demo::leaf", 0, vec![]),
            entry("other", "Mir.Demo.Other.body", "demo::other", 1, vec![]),
            entry("first", "Mir.Demo.LeafShadow.body", "demo::leaf", 0, vec![]),
            entry("other", "Mir.Demo.OtherShadow.body", "demo::other", 1, vec![]),
        ];
        let code = emit_opaque_callee_table_lean_module("Gen.Shadow", &entries);
        // Shadowed bodies stay in the sealed list, in capture order.
        assert!(code.contains(
            "def calleeSuffix3 : List CapturedMir := List.cons (Mir.Demo.OtherShadow.body) calleeSuffix4\n\
             def calleeSuffix2 : List CapturedMir := List.cons (Mir.Demo.LeafShadow.body) calleeSuffix3\n"
        ));
        assert!(code.contains("-- Callee [2] is shadowed by callee [0] (equal `defPath`)"));
        assert!(code.contains("-- Callee [3] is shadowed by callee [1] (equal `defPath`)"));
        assert_eq!(
            theorem_names(&code),
            vec![
                "cert_traitImpls",
                "cert_lookupRaw_first",
                "cert_lookup_mono_first",
                "cert_lookupRaw_other",
                "cert_noImpl_other",
                "cert_lookup_free_poly_extra_other",
                "cert_lookup_free_poly_other",
            ]
        );
        // No certificate ever inspects or returns a shadowed body, and shadowed entries claim
        // no identifier.
        assert!(!code.contains("(Mir.Demo.LeafShadow.body)."));
        assert!(!code.contains("(Mir.Demo.OtherShadow.body)."));
        assert!(!code.contains("Option.some (Mir.Demo.LeafShadow.body)"));
        assert!(!code.contains("first_1") && !code.contains("other_1"));
    }

    #[test]
    fn lean_reserved_idents_is_strictly_sorted() {
        assert!(
            LEAN_RESERVED_IDENTS.windows(2).all(|w| w[0] < w[1]),
            "LEAN_RESERVED_IDENTS must be strictly sorted for binary_search"
        );
    }

    #[test]
    fn sanitize_lean_ident_cases() {
        for (hint, want) in [
            ("demo::leaf", "demo__leaf"),
            ("a_b", "a_b"),
            ("a.b", "a_b"),
            ("", "callee"),
            ("_", "callee_"),
            ("__", "callee__"),
            ("0abc", "_0abc"),
            ("def", "def_"),
            ("end", "end_"),
            ("sorry", "sorry_"),
            ("Type", "Type_"),
            ("repeat", "repeat_"),
            ("exists", "exists_"),
            ("matches", "matches_"),
            ("while", "while_"),
            ("until", "until_"),
            ("seal", "seal_"),
            ("elab", "elab_"),
            ("prelude", "prelude_"),
            ("coinductive", "coinductive_"),
            ("builtin_initialize", "builtin_initialize_"),
            ("declare_syntax_cat", "declare_syntax_cat_"),
            ("defs", "defs"),
            ("x'", "x_"),
            ("théorème", "th_or_me"),
            ("<T as Tr>::m", "_T_as_Tr___m"),
        ] {
            assert_eq!(sanitize_lean_ident(hint), want, "hint {hint:?}");
        }
    }

    #[test]
    fn callee_table_identifier_collisions_and_keywords_are_disambiguated() {
        let hints = ["a::b", "a__b", "a__b_1", "def", "def_", "", "_"];
        let entries: Vec<_> = hints
            .iter()
            .enumerate()
            .map(|(k, hint)| entry(hint, &format!("Mir.Demo.E{k}.body"), &format!("demo::e{k}"), 0, vec![]))
            .collect();
        let code = emit_opaque_callee_table_lean_module("Gen.Idents", &entries);
        let names = theorem_names(&code);
        let raw: Vec<&str> =
            names.iter().filter_map(|name| name.strip_prefix("cert_lookupRaw_")).collect();
        assert_eq!(raw, vec!["a__b", "a__b_1", "a__b_1_1", "def_", "def__1", "callee", "callee_"]);
        let unique: BTreeSet<&str> = names.iter().copied().collect();
        assert_eq!(unique.len(), names.len(), "{names:?}");
        for name in names {
            assert!(name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'), "{name}");
        }
    }

    #[test]
    fn def_path_escaping_round_trips_through_lean_string_literals() {
        let tricky = "demo::we\"ird\\path\n\r\t\u{0}\u{1b}\u{7f}\u{85}\u{9f}é→\u{2028}🦀";
        let escaped = escape_lean_str(tricky);
        assert!(!escaped.chars().any(|c| c.is_control()), "{escaped:?}");
        assert_eq!(decode_lean_str_body(&escaped), tricky);
        // Regression: a C1 control is escaped by code point, not by its UTF-8 bytes `\xc2\x85`.
        assert_eq!(escape_lean_str("\u{85}"), "\\x85");
        assert_eq!(escape_lean_str("\u{0}\u{7f}"), "\\x00\\x7f");
        assert_eq!(escape_lean_str("\"\\"), "\\\"\\\\");

        let code = emit_opaque_callee_table_lean_module(
            "Gen.Escape",
            &[entry("weird", "Mir.Demo.Weird.body", tricky, 0, vec![])],
        );
        let lit = render_lean_str(tricky);
        assert!(code.contains(&format!("table.lookupRaw {lit} = Option.some (Mir.Demo.Weird.body)")));
        assert!(code.contains(&format!("(rfl : (Mir.Demo.Weird.body).defPath = {lit})")));
        assert!(code.contains(&format!("table.lookup callerLayouts {lit} List.nil extra")));
        assert!(!code.contains(tricky));
        assert!(!code.chars().any(|c| c.is_control() && c != '\n'));
    }

    #[test]
    fn mir_module_header_neutralizes_comment_delimiters_and_imports_trusted_only() {
        let mir = fixture_mir("demo::x -/ axiom bad : False /- y\nz", 0, vec![], 1);
        let code = emit_mir_lean_module("Mir.Demo.X", &mir);
        let doc = code.lines().find(|line| line.starts_with("/-! ")).unwrap();
        assert!(doc.ends_with(" -/"), "{doc}");
        let inner = &doc[3..doc.len() - 2];
        assert!(!inner.contains("-/") && !inner.contains("/-"), "{doc}");
        assert!(!code.lines().any(|line| line.starts_with("axiom")));
        // TrustedBoundary statement-origin isolation: a trusted `Mir/<Item>.lean` module imports
        // `Trusted` only, never `Anneal.*` (in particular not `Anneal.OpaqueCalleeTable`).
        let imports: Vec<&str> = code.lines().filter(|line| line.starts_with("import ")).collect();
        assert_eq!(imports, vec!["import Trusted"]);
        assert_eq!(sanitize_block_comment_text("a/-/b\n-/"), "a/ - /b - /");
    }

    #[test]
    fn validate_lean_term_expr_accepts_references_and_rejects_injection() {
        for ok in [
            "Mir.Demo.leaf.body",
            " Mir.Demo.leaf.body ",
            "@Mir.Demo.leaf.body",
            "(Mir.Demo.leaf.body)",
            "Mir.«my-crate».leaf.body",
            "Foo.mk 3 (Bar.x') [y]",
            "Foo.mk 0xff 0b101 0o77 [] ()",
            "x!",
            "is_ok?",
        ] {
            assert_eq!(validate_lean_term_expr(ok), Ok(()), "{ok:?}");
        }
        for bad in [
            "", "   ", "a\nb", "Mir.X.body\n", "a -- c", "a /- c -/", "\"s\"", "'a'", "a)", "(a",
            "[a)", "a; b", "a := b", "Mir.def.body", "Mir.repeat.body", "Mir.exists.body",
            "Mir.elab.body", "sorry", "s!", "_", "Mir._.body", "x end Foo", "«»", "Mir.«».body",
            "«a", "«a\nb»", "Mir.«a\u{202e}b».body", "Mir.«a\u{2028}b».body", "a «b «c» »", "a,b",
            "a{b}", "a#b", "a\\b", "a`b", "$x", "a ⟨b⟩", "@", "@ ", "@)", "a@b", "@@x", ".", ".x",
            "Mir.", "Mir..body", "Mir.0", "0abc", "123'!", "0x", "()", "[]", "42",
        ] {
            assert!(validate_lean_term_expr(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn validate_lean_dotted_name_cases() {
        for ok in ["Mir", "Mir.Demo.leaf", "Gen._private", "Mir.«my-crate».x", "A'.B"] {
            assert_eq!(validate_lean_dotted_name(ok), Ok(()), "{ok:?}");
        }
        for bad in [
            "", ".", "Mir.", ".Mir", "Mir..Demo", "Mir.Demo\nimport Evil", "Mir Demo", "0Mir",
            "Mir._", "Mir.end", "Mir.repeat", "Mir.exists", "Mir.elab", "Mir.prelude",
            "Mir.coinductive", "Mir.«»", "Mir.«a", "Mir.«a\u{202e}b»", "Mir-Demo", "Mir.Demo -- x",
        ] {
            assert!(validate_lean_dotted_name(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    #[should_panic(expected = "invalid `mir_body_expr`")]
    fn emitter_rejects_injected_body_expr() {
        emit_opaque_callee_table_lean_module(
            "Gen.Bad",
            &[entry("x", "Mir.X.body)\n\naxiom bad : False\n#check (", "demo::x", 0, vec![])],
        );
    }

    #[test]
    #[should_panic(expected = "invalid OpaqueCalleeTable module namespace")]
    fn emitter_rejects_invalid_namespace() {
        emit_opaque_callee_table_lean_module("Gen.Bad\nend Gen.Bad", &[]);
    }

    #[test]
    #[should_panic(expected = "invalid OpaqueCalleeTable module import")]
    fn emitter_rejects_invalid_import() {
        emit_opaque_callee_table_lean_module_with_imports("Gen.Ok", &["Mir.X\naxiom bad : False"], &[]);
    }

    #[test]
    fn with_imports_emits_each_import_once_in_order() {
        let code = emit_opaque_callee_table_lean_module_with_imports(
            "Gen.Imp",
            &["Mir.Demo.B", "Trusted", "Mir.Demo.A", "Mir.Demo.B", "Anneal.OpaqueCalleeTable"],
            &[],
        );
        assert!(code.starts_with(
            "import Trusted\nimport Anneal.OpaqueCalleeTable\nimport Mir.Demo.B\nimport Mir.Demo.A\n\n\
             namespace Gen.Imp\n"
        ));
        assert_eq!(
            emit_opaque_callee_table_lean_module("Gen.Imp", &[]),
            emit_opaque_callee_table_lean_module_with_imports("Gen.Imp", &[], &[])
        );
    }

    #[test]
    fn from_captured_mir_copies_identity_fields() {
        let mir = fixture_mir("demo::poly", 2, vec![trait_impl("demo::Tr::m", "demo::<u32 as Tr>::m")], 7);
        let built = IrCalleeTableEntry::from_captured_mir("poly", String::from("Mir.Demo.Poly.body"), &mir);
        assert_eq!(
            built,
            IrCalleeTableEntry {
                lean_ident: "poly".to_owned(),
                mir_body_expr: "Mir.Demo.Poly.body".to_owned(),
                def_path: "demo::poly".to_owned(),
                type_param_count: 2,
                trait_impls: mir.trait_impls.clone(),
            }
        );
    }

    #[test]
    fn sanitize_deriving_classes_drops_redundant_beq() {
        let cases: &[(&[&str], &[&str])] = &[
            (&["BEq", "DecidableEq"], &["DecidableEq"]),
            (&["DecidableEq", "BEq", "Repr"], &["DecidableEq", "Repr"]),
            (&["Repr", "BEq", "Hashable"], &["Repr", "BEq", "Hashable"]),
            (&["_root_.BEq", "Foo.DecidableEq"], &["Foo.DecidableEq"]),
            (&["@[expose] BEq", "@[expose] DecidableEq"], &["@[expose] DecidableEq"]),
            (&["(BEq)", " DecidableEq "], &["DecidableEq"]),
            (&["Lean.«BEq»", "«DecidableEq»"], &["«DecidableEq»"]),
            (&["BEqLike", "DecidableEq", "MyBEq"], &["BEqLike", "DecidableEq", "MyBEq"]),
            (
                &["Repr", "Repr", "DecidableEq", "_root_.DecidableEq", "@[expose] DecidableEq"],
                &["Repr", "DecidableEq"],
            ),
            (&["", "  ", "Hashable", "@[expose]"], &["Hashable"]),
            (&["BEq", "BEq"], &["BEq"]),
            (
                &["ToJson (opt := 1)", "ToJson  (opt := 1)", "BEq", "DecidableEq"],
                &["ToJson (opt := 1)", "DecidableEq"],
            ),
            // Guillemets containing spaces or parens before `.BEq` / `.DecidableEq`:
            (&["«a b».BEq", "«c(d)».DecidableEq"], &["«c(d)».DecidableEq"]),
            // Single atomic guillemet component containing `.` is NOT namespace-qualified `BEq`:
            (&["«Not.BEq»", "DecidableEq"], &["«Not.BEq»", "DecidableEq"]),
            // Nested `[...]` inside `@[...]` attributes:
            (
                &["@[aesop safe [constructors]] BEq", "@[aesop safe [constructors]] DecidableEq"],
                &["@[aesop safe [constructors]] DecidableEq"],
            ),
            // Parenthesized head with trailing arguments must be preserved and deduplicated:
            (
                &["(CustomHandler) opt", "((CustomHandler) opt)", "BEq", "DecidableEq"],
                &["(CustomHandler) opt", "DecidableEq"],
            ),
            (
                // Regression: outer arguments after a parenthesized class application are part
                // of the class reference (never dropped, deduplicated away, or read as unary).
                &["Handler a", "(Handler a) b", "(Handler a) c", "(BEq a) b", "DecidableEq"],
                &["Handler a", "(Handler a) b", "(Handler a) c", "(BEq a) b", "DecidableEq"],
            ),
            // Multi-argument handler whose head ends in `.BEq` is not core's unary `BEq`:
            (&["CustomPkg.BEq opt", "DecidableEq"], &["CustomPkg.BEq opt", "DecidableEq"]),
        ];
        for (input, want) in cases {
            assert_eq!(sanitize_deriving_classes(input), want.to_vec(), "{input:?}");
        }
    }

    #[test]
    fn render_deriving_clause_hygiene() {
        assert_eq!(render_deriving_clause(&[]), "");
        assert_eq!(render_deriving_clause(&["BEq"]), "deriving BEq");
        assert_eq!(
            render_deriving_clause(&["Repr", "BEq", "DecidableEq", "Hashable"]),
            "deriving Repr, DecidableEq, Hashable"
        );
        assert_eq!(
            render_deriving_clause(&["BEq", "@[expose] DecidableEq"]),
            "deriving @[expose] DecidableEq"
        );
    }

    /// Splits a `deriving` class list on top-level commas outside brackets, quotes, and `«...»`.
    fn split_top_level_commas(s: &str) -> Vec<&str> {
        let mut out = Vec::new();
        let mut start = 0usize;
        let mut depth = 0usize;
        let mut in_gui = false;
        let mut in_str = false;
        let mut escaped = false;
        for (i, c) in s.char_indices() {
            if in_str {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    in_str = false;
                }
                continue;
            }
            if in_gui {
                if c == '»' {
                    in_gui = false;
                }
                continue;
            }
            match c {
                '"' => in_str = true,
                '«' => in_gui = true,
                '(' | '[' | '{' | '⟨' | '⦃' => depth += 1,
                ')' | ']' | '}' | '⟩' | '⦄' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => {
                    out.push(&s[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        out.push(&s[start..]);
        out
    }

    /// `(1-based line, clause)` of every `deriving` clause in `text` (inline, multiline, or
    /// `deriving [noncomputable] instance ... for`) naming both a `BEq` and a `DecidableEq` class.
    fn redundant_beq_deriving_clauses(text: &str) -> Vec<(usize, String)> {
        let keyword = ["der", "iving"].concat();
        let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
        let normalized = text.replace("\\n", "\n");
        let mut hits = Vec::new();
        let mut from = 0usize;
        while let Some(pos) = normalized[from..].find(&keyword).map(|p| p + from) {
            let after = pos + keyword.len();
            let standalone = normalized[..pos].chars().next_back().is_none_or(|c| !is_ident(c) && c != '.')
                && normalized[after..].chars().next().is_none_or(|c| !is_ident(c));
            from = after;
            if !standalone {
                continue;
            }
            let line_no = 1 + normalized[..pos].bytes().filter(|&b| b == b'\n').count();
            let mut rest = &normalized[after..];
            if let Some(q) = rest.find('"') {
                rest = &rest[..q];
            }
            // Collect continuation lines while the previous trimmed line ends with `,` or `deriving`.
            let mut acc = String::new();
            for (li, raw_line) in rest.lines().enumerate() {
                if li > 0 && !acc.trim_end().ends_with(',') && !acc.trim().is_empty() {
                    break;
                }
                if !acc.is_empty() {
                    acc.push(' ');
                }
                acc.push_str(raw_line);
            }
            let mut words = acc.trim_start();
            for prefix in ["noncomputable ", "instance "] {
                if let Some(r) = words.strip_prefix(prefix) {
                    words = r.trim_start();
                }
            }
            let classes = words.find(" for ").map_or(words, |end| &words[..end]);
            let cores: Vec<&str> = split_top_level_commas(classes)
                .into_iter()
                .filter_map(deriving_unary_class_core)
                .collect();
            if cores.contains(&"BEq") && cores.contains(&"DecidableEq") {
                hits.push((line_no, acc.trim().to_owned()));
            }
        }
        hits
    }

    #[test]
    fn audit_no_generated_deriving_clause_combines_beq_and_decidable_eq() {
        let kw = ["der", "iving"].concat();
        // Canaries: the audit detects every spelling it must reject (including multiline and bracketed args) ...
        for bad in [
            format!("{kw} BEq, DecidableEq"),
            format!("  {kw} Repr,\n    _root_.BEq,\n    @[expose] DecidableEq"),
            format!("{kw} Handler [a, b], BEq, DecidableEq"),
            format!("{kw} instance BEq, DecidableEq for Foo"),
            format!("{kw} noncomputable instance (BEq), Foo.DecidableEq for Foo α, (Bar β)"),
            format!("out.push_str(\"{kw} DecidableEq,\\n  BEq\\n\")"),
        ] {
            assert_eq!(redundant_beq_deriving_clauses(&bad).len(), 1, "{bad}");
        }
        // ... and accepts lawful ones.
        for good in [
            format!("{kw} DecidableEq, Repr"),
            format!("{kw} BEq, Hashable"),
            format!("{kw} instance DecidableEq for Foo"),
            String::from("omit [DecidableEq α] in theorem t : BEq α := inferInstance"),
            render_deriving_clause(&["BEq", "DecidableEq"]),
            format!("re{kw}_x BEq, DecidableEq"),
        ] {
            assert!(redundant_beq_deriving_clauses(&good).is_empty(), "{good}");
        }
        // Zero Lean templates, docstrings or tests in this file spell a redundant clause ...
        assert_eq!(redundant_beq_deriving_clauses(include_str!("lean_emit.rs")), vec![]);
        // ... and neither does any module the emitters produce.
        let leaf = fixture_mir("demo::leaf", 0, vec![], 1);
        let poly = fixture_mir("demo::poly", 1, vec![trait_impl("demo::Tr::m", "demo::<u32 as Tr>::m")], 2);
        let entries = vec![
            IrCalleeTableEntry::from_captured_mir("leaf", "Mir.Demo.Leaf.body", &leaf),
            IrCalleeTableEntry::from_captured_mir("poly", "Mir.Demo.Poly.body", &poly),
        ];
        for code in [
            emit_mir_lean_module("Mir.Demo.Leaf", &leaf),
            emit_mir_lean_module("Mir.Demo.Poly", &poly),
            emit_opaque_callee_table_lean_module_with_imports(
                "Gen.Audit",
                &["Mir.Demo.Leaf", "Mir.Demo.Poly"],
                &entries,
            ),
        ] {
            assert_eq!(redundant_beq_deriving_clauses(&code), vec![]);
        }
    }

    /// Lean toolchain for the end-to-end kernel check: `lake` (`ANNEAL_LAKE`, else elan's
    /// `~/.elan/bin/lake`, else `PATH`), run from the repository root whose `.lake/build` holds
    /// the `Trusted` and `Anneal.OpaqueCalleeTable` `.olean`s.
    struct LeanE2e {
        lake: PathBuf,
        repo_root: PathBuf,
    }

    impl LeanE2e {
        fn detect() -> Result<Self, String> {
            let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .canonicalize()
                .map_err(|err| format!("repository root: {err}"))?;
            for olean in ["Trusted.olean", "Anneal/OpaqueCalleeTable.olean"] {
                let path = repo_root.join(".lake/build/lib/lean").join(olean);
                if !path.is_file() {
                    return Err(format!(
                        "{} is missing (run `lake build +Anneal.OpaqueCalleeTable`)",
                        path.display()
                    ));
                }
            }
            let lake = std::env::var_os("ANNEAL_LAKE")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME")
                        .map(|home| PathBuf::from(home).join(".elan/bin/lake"))
                        .filter(|path| path.is_file())
                })
                .or_else(|| {
                    std::env::var_os("PATH").and_then(|paths| {
                        std::env::split_paths(&paths)
                            .map(|dir| dir.join("lake"))
                            .find(|path| path.is_file())
                    })
                })
                .ok_or_else(|| "no `lake` executable found".to_owned())?;
            Ok(Self { lake, repo_root })
        }

        /// `lake env lean <args>` from the repository root with `stage` on `LEAN_PATH`; returns
        /// whether it succeeded and its combined output.
        fn lean(&self, stage: &Path, args: &[&OsStr]) -> (bool, String) {
            let output = Command::new(&self.lake)
                .arg("env")
                .arg("lean")
                .args(args)
                .current_dir(&self.repo_root)
                .env("LEAN_PATH", stage)
                .output()
                .expect("failed to spawn `lake env lean`");
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            (output.status.success(), text)
        }

        /// Writes `code` to `stage/<module path>.lean` and compiles it to its `.olean`.
        fn compile(&self, stage: &Path, module: &str, code: &str) -> (bool, String) {
            let src = stage.join(module.split('.').collect::<PathBuf>()).with_extension("lean");
            std::fs::create_dir_all(src.parent().unwrap()).unwrap();
            std::fs::write(&src, code).unwrap();
            let olean = src.with_extension("olean");
            let root = format!("--root={}", stage.display());
            self.lean(stage, &[OsStr::new(&root), OsStr::new("-o"), olean.as_os_str(), src.as_os_str()])
        }
    }

    /// Temporary staging directory outside the checkout, removed on drop unless
    /// `ANNEAL_KEEP_LEAN_E2E_DIR` is set.
    struct StageDir(PathBuf);

    impl Drop for StageDir {
        fn drop(&mut self) {
            if std::env::var_os("ANNEAL_KEEP_LEAN_E2E_DIR").is_none() {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
    }

    /// 1-based line numbers of the `<file>:<line>:<col>: error` diagnostics in Lean output.
    fn lean_error_lines(output: &str, file: &str) -> Vec<usize> {
        output
            .lines()
            .filter_map(|line| {
                let rest = line.split(file).nth(1)?.strip_prefix(':')?;
                let (line_no, rest) = rest.split_once(':')?;
                let (_col, rest) = rest.split_once(':')?;
                rest.trim_start().starts_with("error").then(|| line_no.parse().ok()).flatten()
            })
            .collect()
    }

    /// End-to-end Lean 4 kernel check: stages emitted `Mir/<Item>.lean` modules and an emitted
    /// `OpaqueCalleeTable` module in a temporary directory outside the checkout, compiles them
    /// with `lake env lean` against this checkout's `.lake/build`, exercises the certificates
    /// from a downstream driver (including their axiom footprint), and checks that certificates
    /// for entries inconsistent with their bodies are rejected. Skips (with a message) when the
    /// Lean build is unavailable, unless `ANNEAL_REQUIRE_LEAN_E2E` is set.
    #[test]
    fn e2e_lean_kernel_checks_emitted_mir_and_callee_table_modules() {
        let lean = match LeanE2e::detect() {
            Ok(lean) => lean,
            Err(reason) => {
                assert!(
                    std::env::var_os("ANNEAL_REQUIRE_LEAN_E2E").is_none(),
                    "Lean e2e required but unavailable: {reason}"
                );
                eprintln!("SKIPPED e2e_lean_kernel_checks_emitted_mir_and_callee_table_modules: {reason}");
                return;
            }
        };
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let stage_dir = StageDir(
            std::env::temp_dir().join(format!("anneal-lean-emit-e2e-{}-{nanos}", std::process::id())),
        );
        std::fs::create_dir_all(&stage_dir.0).unwrap();
        let stage = stage_dir.0.canonicalize().unwrap();
        assert!(!stage.starts_with(&lean.repo_root), "staging dir must be outside the checkout");

        let weird_path = "demo::we\"ird\\path\n\t\u{1}\u{7f}\u{85}é→";
        let area_impl = trait_impl("demo::Area::area", "demo::<Square as Area>::area");
        // (module, `lean_ident` hint, captured body)
        let items = vec![
            ("Mir.Demo.Leaf", "demo::leaf", fixture_mir("demo::leaf", 0, vec![], 1)),
            ("Mir.Demo.Poly", "demo::poly", fixture_mir("demo::poly", 2, vec![], 2)),
            (
                "Mir.Demo.SquareArea",
                "demo::<Square as Area>::area",
                fixture_mir("demo::<Square as Area>::area", 0, vec![area_impl], 3),
            ),
            ("Mir.Demo.AreaMethod", "demo::Area::area", fixture_mir("demo::Area::area", 1, vec![], 4)),
            ("Mir.Demo.LeafShadow", "demo::leaf", fixture_mir("demo::leaf", 0, vec![], 5)),
            ("Mir.Demo.Collide", "demo::leaf", fixture_mir("demo::leaf_2", 0, vec![], 6)),
            ("Mir.Demo.Weird", "end", fixture_mir(weird_path, 0, vec![], 7)),
        ];
        let mut entries = Vec::new();
        for (module, hint, mir) in &items {
            let code = emit_mir_lean_module(module, mir);
            let (ok, out) = lean.compile(&stage, module, &code);
            assert!(ok, "emitted {module} failed to elaborate:\n{out}\n--- source ---\n{code}");
            entries.push(IrCalleeTableEntry::from_captured_mir(*hint, format!("{module}.body"), mir));
        }
        let imports: Vec<&str> = items.iter().map(|(module, _, _)| *module).collect();

        let table = emit_opaque_callee_table_lean_module_with_imports("Gen.DemoCallees", &imports, &entries);
        let names = theorem_names(&table);
        assert_eq!(
            names,
            vec![
                "cert_traitImpls",
                "cert_lookupRaw_demo__leaf",
                "cert_lookup_mono_demo__leaf",
                "cert_lookupRaw_demo__poly",
                "cert_noImpl_demo__poly",
                "cert_lookup_free_poly_extra_demo__poly",
                "cert_lookup_free_poly_demo__poly",
                "cert_lookupRaw_demo___Square_as_Area___area",
                "cert_lookup_mono_demo___Square_as_Area___area",
                "cert_lookupRaw_demo__Area__area",
                "cert_lookupRaw_demo__leaf_1",
                "cert_lookup_mono_demo__leaf_1",
                "cert_lookupRaw_end_",
                "cert_lookup_mono_end_",
            ]
        );
        let (ok, out) = lean.compile(&stage, "Gen.DemoCallees", &table);
        assert!(ok, "emitted OpaqueCalleeTable module failed to elaborate:\n{out}\n--- source ---\n{table}");
        assert!(!out.contains("sorry"), "{out}");

        let weird_chars: Vec<String> =
            weird_path.chars().map(|c| format!("Char.ofNat {}", u32::from(c))).collect();
        let axiom_queries: String =
            names.iter().map(|name| format!("#print axioms Gen.DemoCallees.{name}\n")).collect();
        let driver = format!(
            "import Gen.DemoCallees\n\n\
             open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.Layout\n\
             open Trusted.Rustc.{MIR_DIALECT_V2026_06_01}.MirAst\n\
             open Anneal.OpaqueCalleeTable\n\n\
             -- Use-site `O(1)` rewriting with an emitted monomorphic certificate.\n\
             example (cl : LayoutTable) :\n    \
             Gen.DemoCallees.table.lookup cl \"demo::leaf\" [] [] = some Mir.Demo.Leaf.body := by\n  \
             rw [Gen.DemoCallees.cert_lookup_mono_demo__leaf]\n\n\
             -- Use-site `O(1)` rewriting with both `extra = []` and non-empty caller `extra`\n\
             -- free-polymorphic certificates (without unfolding `table.traitImpls`).\n\
             def sampleCallerLayouts : LayoutTable := Mir.Demo.Leaf.layouts\n\
             def samplePolyTys : List RigidTy := [RigidTy.uint UintTy.u32, RigidTy.bool]\n\
             def samplePolyLayouts : List TypeLayout :=\n  \
             (instantiationLayouts? sampleCallerLayouts samplePolyTys).getD []\n\
             def sampleUnrelatedImpl : TraitImplEntry :=\n  \
             {{ traitRef := {{ defPath := \"demo::Other::other\", args := [RigidTy.bool] }},\n    \
             implPath := \"demo::<bool as Other>::other\" }}\n\n\
             example :\n    \
             Gen.DemoCallees.table.lookup sampleCallerLayouts \"demo::poly\" samplePolyTys [] =\n      \
             some (Mir.Demo.Poly.body.instantiate (samplePolyTys.zip samplePolyLayouts)) :=\n  \
             Gen.DemoCallees.cert_lookup_free_poly_demo__poly sampleCallerLayouts\n    \
             (RigidTy.uint UintTy.u32) [RigidTy.bool] samplePolyLayouts rfl (by decide +kernel)\n\n\
             example :\n    \
             Gen.DemoCallees.table.lookup sampleCallerLayouts \"demo::poly\" samplePolyTys\n      \
             [sampleUnrelatedImpl] =\n      \
             some (Mir.Demo.Poly.body.instantiate (samplePolyTys.zip samplePolyLayouts)) :=\n  \
             Gen.DemoCallees.cert_lookup_free_poly_extra_demo__poly sampleCallerLayouts\n    \
             (RigidTy.uint UintTy.u32) [RigidTy.bool] [sampleUnrelatedImpl] samplePolyLayouts\n    \
             (by decide +kernel) rfl (by decide +kernel)\n\n\
             -- Captured def paths survive Lean string escaping character-for-character.\n\
             example : (Mir.Demo.Weird.body).defPath.toList = [{}] := by decide +kernel\n\n\
             {axiom_queries}",
            weird_chars.join(", ")
        );
        let driver_path = stage.join("Driver.lean");
        std::fs::write(&driver_path, &driver).unwrap();
        let (ok, out) = lean.lean(&stage, &[driver_path.as_os_str()]);
        assert!(ok, "driver failed:\n{out}\n--- source ---\n{driver}");
        assert!(!out.contains("error") && !out.contains("sorry"), "{out}");
        let axiom_reports =
            out.matches("depends on axioms").count() + out.matches("does not depend on any axioms").count();
        assert_eq!(axiom_reports, names.len(), "{out}");
        for forbidden in ["sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler"] {
            assert!(!out.contains(forbidden), "a certificate depends on {forbidden}:\n{out}");
        }

        // Negative controls: certificates for entries inconsistent with the bodies they name
        // (wrong `defPath`, wrong `typeParamCount`, or forged `traitImpls`) are rejected, never
        // silently accepted.
        let bad_entries = vec![
            IrCalleeTableEntry {
                def_path: "demo::leaf".to_owned(),
                ..IrCalleeTableEntry::from_captured_mir("bad_path", "Mir.Demo.Poly.body", &items[1].2)
            },
            IrCalleeTableEntry {
                type_param_count: 0,
                ..IrCalleeTableEntry::from_captured_mir("bad_arity", "Mir.Demo.AreaMethod.body", &items[3].2)
            },
            IrCalleeTableEntry {
                trait_impls: vec![],
                ..IrCalleeTableEntry::from_captured_mir("bad_traits", "Mir.Demo.SquareArea.body", &items[2].2)
            },
        ];
        let bad = emit_opaque_callee_table_lean_module_with_imports("Gen.BadCallees", &imports, &bad_entries);
        let bad_path = stage.join("BadCallees.lean");
        std::fs::write(&bad_path, &bad).unwrap();
        let (ok, out) = lean.lean(&stage, &[bad_path.as_os_str()]);
        assert!(!ok, "inconsistent certificates were accepted:\n{out}\n--- source ---\n{bad}");
        for unexpected in ["unknown identifier", "unknown constant", "unexpected token", "unknown namespace"] {
            assert!(!out.contains(unexpected), "negative control failed for the wrong reason:\n{out}");
        }
        let error_lines = lean_error_lines(&out, "BadCallees.lean");
        let lines: Vec<&str> = bad.lines().collect();
        for name in ["cert_traitImpls", "cert_lookupRaw_bad_path", "cert_lookup_mono_bad_arity"] {
            let start = 1 + lines.iter().position(|line| line.starts_with(&format!("theorem {name} "))).unwrap();
            let end = start + lines[start..].iter().position(|line| line.is_empty()).unwrap();
            assert!(
                error_lines.iter().any(|line| (start..=end).contains(line)),
                "no error reported inside {name} (lines {start}..={end}):\n{out}\n--- source ---\n{bad}"
            );
        }
    }
}
