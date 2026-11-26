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
    Param {
        index: u32,
        name: String,
    },
    Alias {
        def_path: String,
        args: Vec<IrRigidTy>,
    },
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
///
/// # Panics
///
/// Panics if `lean_module_namespace` is not a valid dotted Lean namespace path
/// (`validate_lean_dotted_name`), preventing namespace/import injection into trusted
/// `Mir/<Item>.lean` modules while permitting captured item stems like `Mir.Demo.end`.
pub fn render_mir_module_header(lean_module_namespace: &str, def_path: &str) -> String {
    if let Err(err) = validate_lean_dotted_name(lean_module_namespace) {
        panic!("invalid Mir module namespace: {err}");
    }
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
        let raw = match &stmt.comment {
            Some(comment) => comment.clone(),
            None => summarize_statement_kind(&stmt.kind),
        };
        parts.push(sanitize_comment_line(&raw));
    }
    let term_raw = match &bb.terminator.comment {
        Some(comment) => comment.clone(),
        None => summarize_terminator_kind(&bb.terminator.kind),
    };
    parts.push(sanitize_comment_line(&term_raw));
    parts.join("; ")
}

fn sanitize_comment_line(text: &str) -> String {
    text.chars()
        .map(|c| {
            if is_disallowed_guillemet_char(c) {
                ' '
            } else {
                c
            }
        })
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
            IrProjectionElem::ConstantIndex { offset, .. } => s.push_str(&format!("[{offset}]")),
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
/// (`"..."`), escaping control characters (`\xHH`) as well as Unicode line/paragraph
/// separators and bidirectional/zero-width format characters (`\uHHHH`, preventing
/// Trojan-Source BiDi overrides in generated `.lean` files while preserving exact
/// `String` scalar values in Lean).
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
            c if is_disallowed_guillemet_char(c) && u32::from(c) <= 0xffff => {
                let code = u32::from(c);
                out.push_str(&format!("\\u{code:04x}"));
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
    match b {
        true => "true",
        false => "false",
    }
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
        IrRigidTy::Tuple(elems) => format!(
            "(RigidTy.tuple {})",
            render_list(elems, render_rigid_ty_pub)
        ),
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
        IrRigidTy::Param { index, name } => {
            format!("(RigidTy.param {} {})", index, render_lean_str(name))
        }
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
            format!(
                "(Rvalue.ref {} {})",
                render_borrow_kind(*bk),
                render_place(p)
            )
        }
        IrRvalue::ThreadLocalRef(path) => {
            format!("(Rvalue.threadLocalRef {})", render_lean_str(path))
        }
        IrRvalue::RawPtr(m, p) => {
            format!(
                "(Rvalue.rawPtr {} {})",
                render_mutability(*m),
                render_place(p)
            )
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
            format!(
                "(Rvalue.nullaryOp {} {})",
                render_null_op(op),
                render_ty(ty)
            )
        }
        IrRvalue::UnaryOp(op, arg) => {
            format!(
                "(Rvalue.unaryOp {} {})",
                render_un_op(*op),
                render_operand(arg)
            )
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
            format!(
                "(StatementKind.assign {} {})",
                render_place(p),
                render_rvalue(rv)
            )
        }
        IrStatementKind::SetDiscriminant(p, idx) => {
            format!("(StatementKind.setDiscriminant {} {idx})", render_place(p))
        }
        IrStatementKind::Deinit(p) => format!("(StatementKind.deinit {})", render_place(p)),
        IrStatementKind::StorageLive(l) => format!("(StatementKind.storageLive {l})"),
        IrStatementKind::StorageDead(l) => format!("(StatementKind.storageDead {l})"),
        IrStatementKind::Retag(rk, p) => {
            format!(
                "(StatementKind.retag {} {})",
                render_retag_kind(*rk),
                render_place(p)
            )
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
            format!(
                "(StatementKind.backwardIncompatibleDropHint {})",
                render_place(p)
            )
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
    format!(
        "{{ idx := {}, name := {} }}",
        p.index,
        render_lean_str(&p.name)
    )
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
    out.push_str(&format!(
        "    defPath := {},\n",
        render_lean_str(&mir.def_path)
    ));
    out.push_str(&format!(
        "    phase := {},\n",
        render_mir_phase_tag(&mir.phase)
    ));
    out.push_str(&format!(
        "    role := {},\n",
        render_contract_role(&mir.role)
    ));
    if mir.type_param_count > 0 {
        out.push_str(&format!(
            "    typeParamCount := {},\n",
            mir.type_param_count
        ));
    }
    if !mir.generic_params.is_empty() {
        out.push_str(&format!(
            "    genericParams := {},\n",
            render_list(&mir.generic_params, render_generic_param_def)
        ));
    }
    if !mir.trait_impls.is_empty() {
        out.push_str(&format!(
            "    traitImpls := {},\n",
            render_list(&mir.trait_impls, render_trait_impl_entry)
        ));
    }
    out.push_str(&format!("    argCount := {},\n", mir.arg_count));
    out.push_str(&format!(
        "    localDecls := {},\n",
        render_list(&mir.local_decls, render_local_decl)
    ));
    out.push_str(&format!(
        "    basicBlocks := {},\n",
        render_list(&mir.basic_blocks, render_basic_block_data)
    ));
    out.push_str(&format!("    fnAbi := {},\n", render_fn_abi(&mir.fn_abi)));
    out.push_str("    layouts := layouts,\n");
    out.push_str(&format!(
        "    allocations := {}\n",
        render_list(&mir.allocations, render_captured_allocation)
    ));
    out.push_str("  }");
    out
}

// ---------------------------------------------------------------------------
// LCNF constructor-size budget of `emit_mir_lean_module` (Lean `v4.34.1` `IR/Checker.lean`)
// ---------------------------------------------------------------------------

/// Scalar-area budget, in bytes, of every constructor `emit_mir_lean_module` renders.
///
/// Lean `v4.34.1`'s IR checker (`IR/Checker.lean`, `checkExpr` on `.ctor`) rejects a
/// constructor whose scalar area (`ssize + usize * 8`) exceeds
/// `LEAN_IR_MAX_CTOR_SCALAR_BYTES` ("has too many scalar fields"), and the debug C runtime
/// asserts the strict `scalar_sz < 1024` in `lean_alloc_ctor`. `960 = 1024 - 64` stays below
/// both.
const MAX_LCNF_CTOR_SCALAR_BYTES: usize = 960;

/// Boxed-field budget of every constructor `emit_mir_lean_module` renders.
///
/// The IR checker rejects more than `LEAN_IR_MAX_CTOR_OBJ_FIELDS` boxed fields ("has too many
/// fields") and `lean_alloc_ctor` asserts `num_objs < 256`. `240 = 256 - 16` stays below both.
const MAX_LCNF_CTOR_OBJ_FIELDS: usize = 240;

/// Declared-field budget (erased fields included) of every constructor `emit_mir_lean_module`
/// renders.
///
/// Independently of the IR checker, Lean `v4.34.1` stops elaborating wide structures: the
/// `structure` command fails with "maximum recursion depth has been reached" (default
/// `maxRecDepth`) at `520` fields while `500` fields elaborate, and the derived `BEq` instance
/// already fails at `256` fields. The cap equals `MAX_LCNF_CTOR_OBJ_FIELDS`.
const MAX_LCNF_CTOR_DECLARED_FIELDS: usize = 240;

/// `LEAN_MAX_CTOR_SCALARS_SIZE` (`lean.h`): the largest constructor scalar area, in bytes, that
/// the IR checker accepts.
const LEAN_IR_MAX_CTOR_SCALAR_BYTES: usize = 1024;

/// `LEAN_MAX_CTOR_FIELDS` (`lean.h`): the largest number of boxed fields of one constructor that
/// the IR checker accepts.
const LEAN_IR_MAX_CTOR_OBJ_FIELDS: usize = 256;

/// Width, in bytes, of the widest unboxed LCNF scalar (`UInt64`, `USize`, `Float`).
const MAX_LCNF_SCALAR_FIELD_BYTES: usize = 8;

// Every budget stays strictly below the Lean limits.
const _: () = assert!(
    MAX_LCNF_CTOR_SCALAR_BYTES < LEAN_IR_MAX_CTOR_SCALAR_BYTES
        && MAX_LCNF_CTOR_OBJ_FIELDS < LEAN_IR_MAX_CTOR_OBJ_FIELDS
        && MAX_LCNF_CTOR_DECLARED_FIELDS >= MAX_LCNF_CTOR_OBJ_FIELDS,
    "LCNF constructor budgets must stay below the Lean limits"
);

/// A Lean constructor that [`emit_mir_lean_module`] may render, with its number of explicit
/// fields (defaulted structure fields included).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MirModuleCtorArity {
    /// Structure or constructor name: `Layout.*` and `MirAst.*` under
    /// `Trusted.Rustc.V2026_06_01`, `VerificationResult.Claim` under `Trusted`, or a prelude
    /// constructor.
    lean_name: &'static str,
    /// Number of explicit fields.
    fields: usize,
}

const fn mir_ctor(lean_name: &'static str, fields: usize) -> MirModuleCtorArity {
    MirModuleCtorArity { lean_name, fields }
}

/// Every structure and every constructor with fields declared in
/// `trusted/lean/Trusted/Rustc/V2026_06_01/{Layout.lean,MirAst/*.lean}`, plus
/// `VerificationResult.Claim` and the prelude constructors `List.cons`, `Option.some`, and
/// `Prod.mk`: a superset of the constructors [`emit_mir_lean_module`] renders.
///
/// `ctor_arity_tests::mir_module_ctor_arities_match_trusted_lean_sources` re-derives the trusted
/// entries from the Lean sources.
const MIR_MODULE_CTOR_ARITIES: &[MirModuleCtorArity] = &[
    mir_ctor("Layout.Size", 1),
    mir_ctor("Layout.Align", 1),
    mir_ctor("Layout.WrappingRange", 2),
    mir_ctor("Layout.PrimitiveKind.int", 2),
    mir_ctor("Layout.PrimitiveKind.float", 1),
    mir_ctor("Layout.PrimitiveKind.pointer", 1),
    mir_ctor("Layout.ScalarLayout.initialized", 2),
    mir_ctor("Layout.ScalarLayout.union", 1),
    mir_ctor("Layout.FieldsShape.union", 1),
    mir_ctor("Layout.FieldsShape.array", 2),
    mir_ctor("Layout.FieldsShape.arbitrary", 2),
    mir_ctor("Layout.VariantsShape.single", 1),
    mir_ctor("Layout.VariantsShape.multiple", 3),
    mir_ctor("Layout.BackendRepr.scalar", 1),
    mir_ctor("Layout.BackendRepr.scalarPair", 2),
    mir_ctor("Layout.TypeLayout", 8),
    mir_ctor("Layout.ArgAbi", 2),
    mir_ctor("Layout.CallConv.other", 1),
    mir_ctor("Layout.FnAbi", 4),
    mir_ctor("Layout.LayoutTable", 3),
    mir_ctor("MirAst.BasicBlockData", 3),
    mir_ctor("MirAst.LocalDecl", 3),
    mir_ctor("MirAst.CapturedAllocation", 5),
    mir_ctor("MirAst.CapturedMir", 12),
    mir_ctor("MirAst.ProjectionElem.field", 2),
    mir_ctor("MirAst.ProjectionElem.index", 1),
    mir_ctor("MirAst.ProjectionElem.constantIndex", 3),
    mir_ctor("MirAst.ProjectionElem.subslice", 3),
    mir_ctor("MirAst.ProjectionElem.downcast", 2),
    mir_ctor("MirAst.ProjectionElem.opaqueCast", 1),
    mir_ctor("MirAst.ProjectionElem.unwrapUnsafeBinder", 1),
    mir_ctor("MirAst.Place", 2),
    mir_ctor("MirAst.Operand.copy", 1),
    mir_ctor("MirAst.Operand.move", 1),
    mir_ctor("MirAst.Operand.constant", 1),
    mir_ctor("MirAst.NullOp.offsetOf", 1),
    mir_ctor("MirAst.BorrowKind.mut", 1),
    mir_ctor("MirAst.CastKind.pointerCoercion", 1),
    mir_ctor("MirAst.AggregateKind.array", 1),
    mir_ctor("MirAst.AggregateKind.adt", 3),
    mir_ctor("MirAst.AggregateKind.closure", 1),
    mir_ctor("MirAst.AggregateKind.coroutine", 1),
    mir_ctor("MirAst.AggregateKind.rawPtr", 2),
    mir_ctor("MirAst.Rvalue.use", 1),
    mir_ctor("MirAst.Rvalue.repeat", 2),
    mir_ctor("MirAst.Rvalue.ref", 2),
    mir_ctor("MirAst.Rvalue.threadLocalRef", 1),
    mir_ctor("MirAst.Rvalue.rawPtr", 2),
    mir_ctor("MirAst.Rvalue.len", 1),
    mir_ctor("MirAst.Rvalue.cast", 3),
    mir_ctor("MirAst.Rvalue.binaryOp", 3),
    mir_ctor("MirAst.Rvalue.nullaryOp", 2),
    mir_ctor("MirAst.Rvalue.unaryOp", 2),
    mir_ctor("MirAst.Rvalue.discriminant", 1),
    mir_ctor("MirAst.Rvalue.aggregate", 2),
    mir_ctor("MirAst.Rvalue.shallowInitBox", 2),
    mir_ctor("MirAst.Rvalue.copyForDeref", 1),
    mir_ctor("MirAst.Rvalue.wrapUnsafeBinder", 2),
    mir_ctor("MirAst.NonDivergingIntrinsic.assume", 1),
    mir_ctor("MirAst.NonDivergingIntrinsic.copyNonOverlapping", 3),
    mir_ctor("MirAst.StatementKind.assign", 2),
    mir_ctor("MirAst.StatementKind.setDiscriminant", 2),
    mir_ctor("MirAst.StatementKind.deinit", 1),
    mir_ctor("MirAst.StatementKind.storageLive", 1),
    mir_ctor("MirAst.StatementKind.storageDead", 1),
    mir_ctor("MirAst.StatementKind.retag", 2),
    mir_ctor("MirAst.StatementKind.placeMention", 1),
    mir_ctor("MirAst.StatementKind.intrinsic", 1),
    mir_ctor("MirAst.StatementKind.backwardIncompatibleDropHint", 1),
    mir_ctor("MirAst.Statement", 2),
    mir_ctor("MirAst.SwitchTargets", 2),
    mir_ctor("MirAst.UnwindAction.cleanup", 1),
    mir_ctor("MirAst.TerminatorKind.goto", 1),
    mir_ctor("MirAst.TerminatorKind.switchInt", 2),
    mir_ctor("MirAst.TerminatorKind.drop", 3),
    mir_ctor("MirAst.TerminatorKind.call", 5),
    mir_ctor("MirAst.TerminatorKind.tailCall", 2),
    mir_ctor("MirAst.TerminatorKind.assert", 4),
    mir_ctor("MirAst.TerminatorKind.inlineAsm", 3),
    mir_ctor("MirAst.Terminator", 2),
    mir_ctor("MirAst.RigidTy.param", 2),
    mir_ctor("MirAst.RigidTy.alias", 2),
    mir_ctor("MirAst.RigidTy.int", 1),
    mir_ctor("MirAst.RigidTy.uint", 1),
    mir_ctor("MirAst.RigidTy.float", 1),
    mir_ctor("MirAst.RigidTy.tuple", 1),
    mir_ctor("MirAst.RigidTy.array", 2),
    mir_ctor("MirAst.RigidTy.slice", 1),
    mir_ctor("MirAst.RigidTy.ref", 2),
    mir_ctor("MirAst.RigidTy.rawPtr", 2),
    mir_ctor("MirAst.RigidTy.adt", 2),
    mir_ctor("MirAst.RigidTy.fnDef", 2),
    mir_ctor("MirAst.RigidTy.fnPtr", 4),
    mir_ctor("MirAst.RigidTy.closure", 2),
    mir_ctor("MirAst.RigidTy.dynamic", 1),
    mir_ctor("MirAst.RigidTy.foreign", 1),
    mir_ctor("MirAst.RigidTy.other", 1),
    mir_ctor("MirAst.Ty", 2),
    mir_ctor("MirAst.ScalarInt", 2),
    mir_ctor("MirAst.ProvenancePtr", 2),
    mir_ctor("MirAst.ConstScalar.int", 1),
    mir_ctor("MirAst.ConstScalar.ptr", 2),
    mir_ctor("MirAst.ConstValue.scalar", 1),
    mir_ctor("MirAst.ConstValue.slice", 2),
    mir_ctor("MirAst.ConstValue.indirect", 2),
    mir_ctor("MirAst.ConstValue.unevaluated", 1),
    mir_ctor("MirAst.ConstOperand", 2),
    mir_ctor("MirAst.MirPhaseTag.other", 1),
    mir_ctor("MirAst.ContractRole.requires", 1),
    mir_ctor("MirAst.ContractRole.ensures", 1),
    mir_ctor("MirAst.ContractRole.externalSpec", 1),
    mir_ctor("MirAst.GenericParamDef", 2),
    mir_ctor("MirAst.TraitRef", 2),
    mir_ctor("MirAst.TraitImplEntry", 2),
    mir_ctor("VerificationResult.Claim", 4),
    mir_ctor("List.cons", 2),
    mir_ctor("Option.some", 1),
    mir_ctor("Prod.mk", 2),
];

/// Whether two ASCII/UTF-8 names are byte-identical, usable in `const` context.
const fn same_lean_name(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut index = 0;
    while index < a.len() {
        if a[index] != b[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// True when every constructor of `arities` has a non-empty name that no other entry repeats and
/// fits the LCNF budgets even if each field takes the worst case:
/// `MAX_LCNF_SCALAR_FIELD_BYTES` scalar bytes and one boxed field.
const fn mir_module_ctor_arities_fit(arities: &[MirModuleCtorArity]) -> bool {
    let mut index = 0;
    while index < arities.len() {
        let arity = arities[index];
        if arity.lean_name.is_empty()
            || arity.fields > MAX_LCNF_CTOR_OBJ_FIELDS
            || arity.fields > MAX_LCNF_CTOR_DECLARED_FIELDS
            || arity.fields.saturating_mul(MAX_LCNF_SCALAR_FIELD_BYTES) > MAX_LCNF_CTOR_SCALAR_BYTES
        {
            return false;
        }
        let mut other = index + 1;
        while other < arities.len() {
            if same_lean_name(arity.lean_name, arities[other].lean_name) {
                return false;
            }
            other += 1;
        }
        index += 1;
    }
    true
}

// Pre-emission LCNF check of `emit_mir_lean_module`, at compile time.
const _: () = assert!(
    mir_module_ctor_arities_fit(MIR_MODULE_CTOR_ARITIES),
    "a MIR module constructor exceeds the LCNF constructor budget"
);

// ---------------------------------------------------------------------------
// Lean name, comment and string-literal hygiene of emitted `Mir/<Item>.lean` modules.
// ---------------------------------------------------------------------------

/// Sorted Lean 4.34.1 parser-reserved ASCII tokens (extracted from `Lean.Parser.getTokenTable`
/// plus `Prop` / `Sort` / `Type` / `sorry` / `admit` / `prelude` / `module`) that cannot stand as
/// bare identifiers in `def <id>` or `namespace <id>`. `validate_lean_dotted_name` rejects them as
/// the first (keyword-lexable) component of a generated namespace.
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
            // Complete Unicode General Category `Cf` (Format) + `Zl` / `Zp` (Line/Paragraph
            // Separator) across both the BMP (`<= U+FFFF`, escaped as `\uHHHH` in Lean string
            // literals) and supplementary planes (`> U+FFFF`, including invisible Unicode Tag
            // characters `U+E0001` and `U+E0020..=U+E007F`, rejected in guillemet identifiers
            // and scrubbed from generated comments).
            '\u{00AD}'
                | '\u{0600}'..='\u{0605}'
                | '\u{061C}'
                | '\u{06DD}'
                | '\u{070F}'
                | '\u{0890}'..='\u{0891}'
                | '\u{08E2}'
                | '\u{180E}'
                | '\u{200B}'..='\u{200F}'
                | '\u{2028}'..='\u{202E}'
                | '\u{2060}'..='\u{2064}'
                | '\u{2066}'..='\u{206F}'
                | '\u{FEFF}'
                | '\u{FFF9}'..='\u{FFFB}'
                | '\u{110BD}'
                | '\u{110CD}'
                | '\u{13430}'..='\u{1343F}'
                | '\u{1BCA0}'..='\u{1BCA3}'
                | '\u{1D173}'..='\u{1D17A}'
                | '\u{E0001}'
                | '\u{E0020}'..='\u{E007F}'
        )
}

/// Checks that `name` is a dotted Lean name (`A.B.C`) whose components are ASCII identifiers
/// (`[A-Za-z_][A-Za-z0-9_']*`, not `_`, with reserved keywords rejected on the first component
/// where Lean can lex them as keywords) or non-empty `«»`-quoted components without control or
/// format characters, so it can be spliced into generated `import` / `namespace` / `end` lines.
fn validate_lean_dotted_name(name: &str) -> Result<(), String> {
    let mut chars = name.chars().peekable();
    // Only the first component of a dotted name can lex as a keyword (`Mir.Demo.end` is one
    // identifier), so reserved-keyword rejection applies to it alone.
    let mut first = true;
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
                if component == "_" || (first && is_reserved_lean_ident(&component)) {
                    return Err(format!(
                        "invalid component `{component}` in Lean name {name:?}"
                    ));
                }
            }
            _ => return Err(format!("invalid Lean name {name:?}")),
        }
        match chars.next() {
            None => return Ok(()),
            Some('.') => first = false,
            Some(c) => return Err(format!("unexpected character {c:?} in Lean name {name:?}")),
        }
    }
}

// ---------------------------------------------------------------------------
// `DecidableEq`-without-redundant-`BEq` (`LawfulBEq`) deriving hygiene.
// ---------------------------------------------------------------------------

fn is_lean_ident_cont_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?')
}

/// If `s[start..]` begins with a Lean 4 character literal (`'x'`, `'\''`, `'\"'`, `'\x41'`,
/// `'\u0041'`, `'\u{41}'`), returns the byte offset immediately after its closing `'`.
fn skip_lean_char_lit_bytes(s: &str, start: usize) -> Option<usize> {
    let rest = s.get(start..)?.strip_prefix('\'')?;
    let mut it = rest.char_indices();
    let (_, c1) = it.next()?;
    if c1 == '\\' {
        let (_, esc) = it.next()?;
        match esc {
            '\\' | '\'' | '"' | 'n' | 'r' | 't' | '0' => {
                let (close_rel, close_ch) = it.next()?;
                (close_ch == '\'').then_some(start + 1 + close_rel + 1)
            }
            'x' => {
                for _ in 0..2 {
                    if !it.next()?.1.is_ascii_hexdigit() {
                        return None;
                    }
                }
                let (close_rel, close_ch) = it.next()?;
                (close_ch == '\'').then_some(start + 1 + close_rel + 1)
            }
            'u' => {
                let (_, u0) = it.next()?;
                if u0 == '{' {
                    let mut digits = 0usize;
                    loop {
                        let (_, ch) = it.next()?;
                        if ch == '}' {
                            break;
                        }
                        if !ch.is_ascii_hexdigit() || digits >= 8 {
                            return None;
                        }
                        digits += 1;
                    }
                    if digits == 0 {
                        return None;
                    }
                } else {
                    if !u0.is_ascii_hexdigit() {
                        return None;
                    }
                    for _ in 0..3 {
                        if !it.next()?.1.is_ascii_hexdigit() {
                            return None;
                        }
                    }
                }
                let (close_rel, close_ch) = it.next()?;
                (close_ch == '\'').then_some(start + 1 + close_rel + 1)
            }
            _ => None,
        }
    } else if !matches!(c1, '\'' | '\n' | '\r') {
        let (close_rel, close_ch) = it.next()?;
        (close_ch == '\'').then_some(start + 1 + close_rel + 1)
    } else {
        None
    }
}

/// If `s[start..]` begins with a Lean 4 raw string literal (`r"..."` or `r#"..."#`), returns the
/// byte offset past its closing delimiter (or `s.len()` when unclosed).
fn skip_lean_raw_str_bytes(s: &str, start: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.get(start).copied() != Some(b'r') {
        return None;
    }
    let mut k = start + 1;
    while k < bytes.len() && bytes[k] == b'#' {
        k += 1;
    }
    if bytes.get(k).copied() != Some(b'"') {
        return None;
    }
    let hashes = k - (start + 1);
    let mut close = String::with_capacity(1 + hashes);
    close.push('"');
    for _ in 0..hashes {
        close.push('#');
    }
    Some(
        s[k + 1..]
            .find(&close)
            .map_or(s.len(), |rel| k + 1 + rel + close.len()),
    )
}

/// True iff `s[quote_start..]` starts with `"` immediately preceded by `<ident>!` (not `»!`,
/// `123!`, or `'a'!`), forming a Lean 4 `<ident>!"..."` interpolated string literal.
fn is_lean_interp_quote_at(s: &str, quote_start: usize) -> bool {
    let prefix = &s[..quote_start];
    let Some(before_bang) = prefix.strip_suffix('!') else {
        return false;
    };
    if before_bang.ends_with('»') {
        return false;
    }
    let mut ident_chars = before_bang
        .chars()
        .rev()
        .take_while(|&c| is_lean_ident_cont_char(c));
    let Some(mut first) = ident_chars.next() else {
        return false;
    };
    for ch in ident_chars {
        first = ch;
    }
    first.is_alphabetic() || first == '_'
}

/// Byte offset past a `«...»` guillemet token starting at `s[start..]`, bounded to the current
/// line so an unclosed `«` never swallows across `\n`.
fn skip_lean_guillemet_bytes(s: &str, start: usize) -> usize {
    let body = &s[start + '«'.len_utf8()..];
    let line_body = body.find('\n').map_or(body, |nl| &body[..nl]);
    line_body.find('»').map_or(start + '«'.len_utf8(), |rel| {
        start + '«'.len_utf8() + rel + '»'.len_utf8()
    })
}

/// Byte offset past a `"`-opened Lean string or `<ident>!"..."` interpolated string literal at
/// `s[start..]` (or `s.len()` when unclosed).
fn skip_lean_str_or_interp_bytes(s: &str, start: usize) -> usize {
    if !is_lean_interp_quote_at(s, start) {
        let mut escaped = false;
        for (rel, c) in s[start + 1..].char_indices() {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                return start + 1 + rel + 1;
            }
        }
        return s.len();
    }
    let mut j = start + 1;
    while j < s.len() {
        let rest = &s[j..];
        let c = rest.chars().next().unwrap();
        if c == '\\' {
            j += 1;
            if let Some(esc) = s[j..].chars().next() {
                j += esc.len_utf8();
            }
        } else if c == '"' {
            return j + 1;
        } else if c == '{' {
            match find_matching_delim(rest, '{', '}') {
                Some(close) => j += close + 1,
                None => return s.len(),
            }
        } else {
            j += c.len_utf8();
        }
    }
    s.len()
}

/// Strips Lean `--` line comments and nested `/- ... -/` block comments from `s`, preserving
/// `"..."` strings, `r#"..."#` raw strings (not preceded by an identifier or `.` projection),
/// `'...'` character literals, and single-line `«...»` guillemets, while recursively stripping
/// comments inside `<ident>!"{...}"` interpolation holes so newline-flattening in
/// `render_deriving_clause` can never turn an in-hole `--` into a line comment swallowing `}"` or
/// subsequent classes.
fn strip_lean_deriving_comments(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut i = 0usize;
    let mut prev_ident = false;
    let mut prev_dot = false;
    while i < s.len() {
        let rest = &s[i..];
        if rest.starts_with("--") {
            out.push(' ');
            i = rest.find('\n').map_or(s.len(), |nl| i + nl);
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with("/-") {
            let mut depth = 1usize;
            let mut cur = i + 2;
            while depth > 0 && cur < s.len() {
                let tail = &s[cur..];
                if tail.starts_with("/-") {
                    depth += 1;
                    cur += 2;
                } else if tail.starts_with("-/") {
                    depth -= 1;
                    cur += 2;
                } else {
                    cur += tail.chars().next().unwrap().len_utf8();
                }
            }
            out.push(' ');
            i = cur;
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with('«') {
            let end = skip_lean_guillemet_bytes(s, i);
            out.push_str(&s[i..end]);
            prev_ident = end > i + '«'.len_utf8();
            prev_dot = false;
            i = end;
        } else if let Some(end) = (!prev_ident && !prev_dot && rest.starts_with('r'))
            .then(|| skip_lean_raw_str_bytes(s, i))
            .flatten()
        {
            out.push_str(&s[i..end]);
            i = end;
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with('"') {
            if is_lean_interp_quote_at(s, i) {
                out.push('"');
                let mut j = i + 1;
                while j < s.len() {
                    let tail = &s[j..];
                    let c = tail.chars().next().unwrap();
                    if c == '\\' {
                        out.push('\\');
                        j += 1;
                        if let Some(esc) = s[j..].chars().next() {
                            out.push(esc);
                            j += esc.len_utf8();
                        }
                    } else if c == '"' {
                        out.push('"');
                        j += 1;
                        break;
                    } else if c == '{' {
                        match find_matching_delim(tail, '{', '}') {
                            Some(close) => {
                                out.push('{');
                                out.push_str(&strip_lean_deriving_comments(&tail[1..close]));
                                out.push('}');
                                j += close + 1;
                            }
                            None => {
                                out.push('{');
                                out.push_str(&strip_lean_deriving_comments(&tail[1..]));
                                j = s.len();
                            }
                        }
                    } else {
                        out.push(c);
                        j += c.len_utf8();
                    }
                }
                i = j;
            } else {
                let end = skip_lean_str_or_interp_bytes(s, i);
                out.push_str(&s[i..end]);
                i = end;
            }
            prev_ident = false;
            prev_dot = false;
        } else if let Some(end) = (!prev_ident && rest.starts_with('\''))
            .then(|| skip_lean_char_lit_bytes(s, i))
            .flatten()
        {
            out.push_str(&s[i..end]);
            i = end;
            prev_ident = false;
            prev_dot = false;
        } else {
            let c = rest.chars().next().unwrap();
            out.push(c);
            i += c.len_utf8();
            prev_ident = is_lean_ident_cont_char(c);
            prev_dot = c == '.';
        }
    }
    out
}

/// If `s` starts with `open` (`(`, `[`, or `{`) and that opener's matching `close` (`)`, `]`, or
/// `}`) occurs in `s` (ignoring delimiters inside comments, `"..."` / `<ident>!"..."` strings,
/// `r#"..."#` raw strings, `'...'` character literals, and single-line `«...»` guillemets),
/// returns the byte index of that matching `close`.
fn find_matching_delim(s: &str, open: char, close: char) -> Option<usize> {
    if !s.starts_with(open) {
        return None;
    }
    let mut depth = 0usize;
    let mut i = 0usize;
    let mut prev_ident = false;
    let mut prev_dot = false;
    while i < s.len() {
        let rest = &s[i..];
        if rest.starts_with("--") {
            i = rest.find('\n').map_or(s.len(), |nl| i + nl);
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with("/-") {
            let mut cdepth = 1usize;
            let mut cur = i + 2;
            while cdepth > 0 && cur < s.len() {
                let tail = &s[cur..];
                if tail.starts_with("/-") {
                    cdepth += 1;
                    cur += 2;
                } else if tail.starts_with("-/") {
                    cdepth -= 1;
                    cur += 2;
                } else {
                    cur += tail.chars().next().unwrap().len_utf8();
                }
            }
            i = cur;
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with('«') {
            let end = skip_lean_guillemet_bytes(s, i);
            prev_ident = end > i + '«'.len_utf8();
            prev_dot = false;
            i = end;
        } else if let Some(end) = (!prev_ident && !prev_dot && rest.starts_with('r'))
            .then(|| skip_lean_raw_str_bytes(s, i))
            .flatten()
        {
            i = end;
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with('"') {
            i = skip_lean_str_or_interp_bytes(s, i);
            prev_ident = false;
            prev_dot = false;
        } else if let Some(end) = (!prev_ident && rest.starts_with('\''))
            .then(|| skip_lean_char_lit_bytes(s, i))
            .flatten()
        {
            i = end;
            prev_ident = false;
            prev_dot = false;
        } else {
            let c = rest.chars().next().unwrap();
            if c == open {
                depth += 1;
            } else if c == close {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            prev_ident = is_lean_ident_cont_char(c);
            prev_dot = c == '.';
            i += c.len_utf8();
        }
    }
    None
}

/// Strips comments, leading `@[...]` attributes (including nested brackets like
/// `@[aesop safe [constructors]]`), and outer parentheses wrapping the entire entry, then splits
/// the remaining entry into `(head_class_ref, arg_tail)` while respecting `«...»` guillemets,
/// `.{...}` universe annotations, char/string literals, and curried parenthesized heads like
/// `(Handler a) b`. Never returns `("", "")` on a non-empty class body.
fn parse_deriving_entry(entry: &str) -> (String, String) {
    let cleaned = strip_lean_deriving_comments(entry);
    parse_deriving_entry_clean(cleaned.trim())
}

fn parse_deriving_entry_clean(raw: &str) -> (String, String) {
    let mut s = raw.trim();
    loop {
        if let Some(after_at) = s.strip_prefix('@') {
            let after_at = after_at.trim_start();
            if after_at.starts_with('[') {
                match find_matching_delim(after_at, '[', ']') {
                    Some(close) => {
                        s = after_at[close + 1..].trim();
                        continue;
                    }
                    None => return (s.to_owned(), String::new()),
                }
            }
        }
        if let Some(close) = find_matching_delim(s, '(', ')').filter(|&close| close + 1 == s.len())
        {
            s = s[1..close].trim();
            continue;
        }
        break;
    }
    if s.is_empty() {
        return (String::new(), String::new());
    }
    if s.starts_with('(') {
        if let Some(close) = find_matching_delim(s, '(', ')') {
            let inner = s[1..close].trim();
            let (head, inner_args) = parse_deriving_entry_clean(inner);
            let outer_args = s[close + 1..].trim();
            if head.is_empty() {
                return (s.to_owned(), String::new());
            }
            let tail = match (inner_args.is_empty(), outer_args.is_empty()) {
                (true, _) => outer_args.to_owned(),
                (false, true) => inner_args,
                (false, false) => format!("{inner_args} {outer_args}"),
            };
            return (head, tail);
        }
        return (s.to_owned(), String::new());
    }
    let mut in_gui = false;
    let mut head_end = s.len();
    let mut i = 0usize;
    while i < s.len() {
        let rest = &s[i..];
        let c = rest.chars().next().unwrap();
        if in_gui {
            if c == '»' {
                in_gui = false;
            }
            i += c.len_utf8();
            continue;
        }
        if c == '«' {
            in_gui = true;
            i += c.len_utf8();
            continue;
        }
        if let Some(u_close) = (c == '.' && rest[1..].starts_with('{'))
            .then(|| find_matching_delim(&rest[1..], '{', '}'))
            .flatten()
        {
            i += 1 + u_close + 1;
            continue;
        }
        if c.is_whitespace() || matches!(c, '(' | '[' | '{' | '⟨' | '⦃' | '"' | '\'') {
            head_end = i;
            break;
        }
        i += c.len_utf8();
    }
    (s[..head_end].to_owned(), s[head_end..].trim().to_owned())
}

/// Splits a trailing `.{...}` universe annotation off `head` (outside `«...»` guillemets).
fn split_universe_suffix(head: &str) -> (&str, &str) {
    let mut in_gui = false;
    for (i, c) in head.char_indices() {
        if in_gui {
            if c == '»' {
                in_gui = false;
            }
        } else if c == '«' {
            in_gui = true;
        } else if (c == '.' && head[i + 1..].starts_with('{'))
            .then(|| find_matching_delim(&head[i + 1..], '{', '}'))
            .flatten()
            .is_some_and(|close| i + 1 + close + 1 == head.len())
        {
            return (&head[..i], &head[i..]);
        }
    }
    (head, "")
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
/// `@[expose] BEq`, `(BEq)`, `BEq.{0}`, `Lean.«BEq»`, and `«a b».BEq` map to `Some("BEq")` /
/// `Some("DecidableEq")`, whereas an atomic guillemet containing a dot `«Not.BEq»` maps to
/// `Some("Not.BEq")` and a multi-argument class term `Custom.BEq opt` maps to `None`).
fn deriving_unary_class_core(entry: &str) -> Option<String> {
    let (head, arg_tail) = parse_deriving_entry(entry);
    if head.is_empty() || !arg_tail.is_empty() {
        return None;
    }
    let (base_head, _) = split_universe_suffix(&head);
    let last = *split_dotted_outside_guillemets(base_head).last()?;
    Some(unwrap_guillemet_component(last).to_owned())
}

/// Deduplication key of a `deriving` entry: comments, attributes, and outer parentheses stripped,
/// leading `_root_.` removed, simple ASCII guillemets (`«DecidableEq»` -> `DecidableEq`)
/// normalized, universe annotations preserved, and arguments whitespace-collapsed.
fn deriving_class_dedup_key(entry: &str) -> String {
    let (head, arg_tail) = parse_deriving_entry(entry);
    if head.is_empty() {
        return String::new();
    }
    let (base_head, univ_suffix) = split_universe_suffix(&head);
    let raw_parts = split_dotted_outside_guillemets(base_head);
    let parts = if raw_parts.len() > 1 && unwrap_guillemet_component(raw_parts[0]) == "_root_" {
        &raw_parts[1..]
    } else {
        &raw_parts[..]
    };
    let mut norm_head: String = parts
        .iter()
        .map(|&comp| {
            let unq = unwrap_guillemet_component(comp);
            // In Lean 4 `Name`, `«foo»` and `foo` denote the identical name component `.str _ "foo"`
            // whenever `foo` contains no `.` (including keyword components such as `Foo.«end».H` vs
            // `Foo.end.H` and `«end»` vs `_root_.end`); keep guillemets only when `unq` would
            // introduce a `.` split or empty/hole/non-ident ambiguity.
            let is_plain_ident = !unq.is_empty()
                && unq
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'')
                && !unq.as_bytes()[0].is_ascii_digit()
                && unq != "_";
            if is_plain_ident {
                unq.to_owned()
            } else {
                comp.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(".");
    if !univ_suffix.is_empty() {
        let inner = &univ_suffix[2..univ_suffix.len() - 1];
        let norm_univ = inner.split_whitespace().collect::<Vec<_>>().join(" ");
        norm_head.push_str(&format!(".{{{norm_univ}}}"));
    }
    if arg_tail.is_empty() {
        norm_head
    } else {
        let norm_args = arg_tail.split_whitespace().collect::<Vec<_>>().join(" ");
        format!("{norm_head} {norm_args}")
    }
}

/// End offset of the Lean string literal (`"..."`, or an `<ident>!"..."` interpolated string
/// whose `{...}` holes are matched by `find_matching_delim`) starting at `s[start] == '"'`, or
/// `None` when it is never closed.
fn lean_str_end(s: &str, start: usize) -> Option<usize> {
    let interp = is_lean_interp_quote_at(s, start);
    let mut j = start + 1;
    while j < s.len() {
        let rest = &s[j..];
        let c = rest.chars().next().unwrap();
        if c == '\\' {
            j += 1;
            j += s[j..].chars().next().map_or(0, char::len_utf8);
        } else if c == '"' {
            return Some(j + 1);
        } else if interp && c == '{' {
            j += find_matching_delim(rest, '{', '}')? + 1;
        } else {
            j += c.len_utf8();
        }
    }
    None
}

/// Byte offset of the first string, raw string, interpolated string (including one with an
/// unclosed `{` hole), or `«...»` guillemet that `s` (already comment-stripped) opens but never
/// closes, or `s.len()` when every such construct is closed. `render_deriving_clause` cuts each
/// entry there, so a malformed entry can never open a literal that swallows the `, <class>`
/// separators and the generated lines after it (just as an unclosed `/-` drops the rest of its
/// own entry).
fn first_unterminated_lean_literal(s: &str) -> usize {
    let mut i = 0usize;
    let mut prev_ident = false;
    let mut prev_dot = false;
    while i < s.len() {
        let rest = &s[i..];
        let raw_hashes = rest
            .strip_prefix('r')
            .map(|tail| tail.bytes().take_while(|&b| b == b'#').count());
        if rest.starts_with('«') {
            let end = skip_lean_guillemet_bytes(s, i);
            if end == i + '«'.len_utf8() {
                return i;
            }
            i = end;
            prev_ident = true;
            prev_dot = false;
        } else if let Some(hashes) = raw_hashes
            .filter(|&h| !prev_ident && !prev_dot && rest.as_bytes().get(1 + h) == Some(&b'"'))
        {
            let body_start = i + 1 + hashes + 1;
            let close = format!("\"{}", "#".repeat(hashes));
            match s[body_start..].find(&close) {
                Some(rel) => i = body_start + rel + close.len(),
                None => return i,
            }
            prev_ident = false;
            prev_dot = false;
        } else if rest.starts_with('"') {
            match lean_str_end(s, i) {
                Some(end) => i = end,
                None => return i,
            }
            prev_ident = false;
            prev_dot = false;
        } else if let Some(end) = (!prev_ident && rest.starts_with('\''))
            .then(|| skip_lean_char_lit_bytes(s, i))
            .flatten()
        {
            i = end;
            prev_ident = false;
            prev_dot = false;
        } else {
            let c = rest.chars().next().unwrap();
            i += c.len_utf8();
            prev_ident = is_lean_ident_cont_char(c);
            prev_dot = c == '.';
        }
    }
    s.len()
}

/// Sanitizes the classes of one `deriving` clause (cl/1022563952): whenever `DecidableEq`
/// (possibly qualified, parenthesized, universe-annotated, commented, or `@[...]`-attributed) is
/// present, every unary `BEq` entry (in any of those forms) is dropped, so the derived structural
/// `BEq` instance never shadows `instBEqOfDecidableEq` and core's `instLawfulBEq` (`beq_iff_eq`)
/// keeps applying. Entries are trimmed, empty/comment-only entries dropped, and duplicates (same
/// class reference) removed keeping the first occurrence, preserving order.
pub fn sanitize_deriving_classes<'a>(classes: &[&'a str]) -> Vec<&'a str> {
    let has_decidable_eq = classes
        .iter()
        .any(|class| deriving_unary_class_core(class).as_deref() == Some("DecidableEq"));
    let mut seen: Vec<String> = Vec::new();
    let mut out = Vec::new();
    for &class in classes {
        let class = class.trim();
        let (head, _) = parse_deriving_entry(class);
        if head.is_empty()
            || (has_decidable_eq && deriving_unary_class_core(class).as_deref() == Some("BEq"))
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
/// remains), stripping `--` / `/- ... -/` comments and flattening newlines/control/format chars per
/// entry so an inline `--` or unclosed `/-` in one entry can never comment out `, <next_class>` or
/// inject multiline commands.
pub fn render_deriving_clause(classes: &[&str]) -> String {
    let rendered: Vec<String> = sanitize_deriving_classes(classes)
        .into_iter()
        .map(|entry| {
            let stripped = strip_lean_deriving_comments(entry);
            sanitize_comment_line(&stripped[..first_unterminated_lean_literal(&stripped)])
        })
        .filter(|entry| !entry.is_empty())
        .collect();
    if rendered.is_empty() {
        String::new()
    } else {
        format!("deriving {}", rendered.join(", "))
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
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: vec![],
            trait_impls: vec![],
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
        assert!(code.contains(
            "(RigidTy.alias \"demo::MyTrait::Assoc\" (List.cons (RigidTy.param 0 \"T\") List.nil))"
        ));
        assert!(code.contains("fieldLayouts := (List.cons 0 (List.cons 0 List.nil))"));
    }
}

#[cfg(test)]
mod ctor_arity_tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::{Path, PathBuf};

    fn demo_answer_mir() -> IrCapturedMir {
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
        IrCapturedMir {
            def_path: String::from("demo::answer"),
            phase: IrMirPhaseTag::RuntimeOptimized,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: vec![],
            trait_impls: vec![],
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
                            ty: u32_ty,
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
        }
    }

    #[test]
    fn mir_module_ctor_arities_fit_the_lcnf_budget() {
        assert!(mir_module_ctor_arities_fit(MIR_MODULE_CTOR_ARITIES));
        let widest = MIR_MODULE_CTOR_ARITIES
            .iter()
            .max_by_key(|arity| arity.fields)
            .expect("non-empty table");
        assert_eq!(
            (widest.lean_name, widest.fields),
            ("MirAst.CapturedMir", 12)
        );
        let fits = |lean_name, fields| mir_module_ctor_arities_fit(&[mir_ctor(lean_name, fields)]);
        // 241 boxed fields exceed the object budget.
        assert!(!fits("Synthetic.objects", 241));
        // 121 worst-case fields need 968 scalar bytes; 120 need exactly 960.
        assert!(!fits("Synthetic.scalars", 121));
        assert!(fits("Synthetic.largest", 120));
        // Empty and duplicated names are rejected.
        assert!(!fits("", 1));
        let duplicated = [
            mir_ctor("Synthetic.twice", 1),
            mir_ctor("Synthetic.twice", 2),
        ];
        assert!(!mir_module_ctor_arities_fit(&duplicated));
        let distinct = [mir_ctor("Synthetic.a", 1), mir_ctor("Synthetic.ab", 2)];
        assert!(mir_module_ctor_arities_fit(&distinct));
        // The guard is compile-time only: the emitted module is unchanged (SHA-256 of the
        // module emitted by the pre-guard emitter, base `9110fbec`).
        let emitted = emit_mir_lean_module("Mir.Demo.answer", &demo_answer_mir());
        assert_eq!(
            crate::manifest::sha256_hex(emitted.as_bytes()),
            "41f365d3e8274ca6da09dc4f0daecdc72fd0ecee8b06c7d5d761a4deace348e9"
        );
    }

    #[test]
    fn rendered_mir_module_ctors_are_in_the_arity_table() {
        let known: BTreeSet<&str> = MIR_MODULE_CTOR_ARITIES
            .iter()
            .map(|arity| match arity.lean_name.split_once('.') {
                Some(("Layout" | "MirAst", rest)) => rest,
                _ => arity.lean_name,
            })
            .collect();
        let module = emit_mir_lean_module("Mir.Demo.answer", &demo_answer_mir());
        let applied: BTreeSet<&str> = module
            .match_indices('(')
            .filter_map(|(offset, _)| {
                let rest = &module[offset + 1..];
                let head_len = rest
                    .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
                    .unwrap_or(rest.len());
                let head = &rest[..head_len];
                (head.contains('.') && rest[head_len..].starts_with(' ')).then_some(head)
            })
            .collect();
        assert!(applied.contains("RigidTy.uint") && applied.contains("List.cons"));
        // `UInt8.ofNat` is a function, not a constructor.
        let unknown: Vec<&str> = applied
            .into_iter()
            .filter(|head| !known.contains(head) && *head != "UInt8.ofNat")
            .collect();
        assert!(
            unknown.is_empty(),
            "constructors missing from the table: {unknown:?}"
        );
    }

    /// Removes Lean comments, keeping string literals and line structure.
    fn strip_lean_comments(text: &str) -> String {
        let chars: Vec<char> = text.chars().collect();
        let mut out = String::with_capacity(text.len());
        let mut index = 0;
        let mut depth = 0usize;
        while index < chars.len() {
            let current = chars[index];
            let next = chars.get(index + 1).copied();
            if depth == 0 && current == '"' {
                out.push(current);
                index += 1;
                while index < chars.len() && chars[index] != '"' {
                    if chars[index] == '\\' && index + 1 < chars.len() {
                        out.push(chars[index]);
                        index += 1;
                    }
                    out.push(chars[index]);
                    index += 1;
                }
                if index < chars.len() {
                    out.push('"');
                    index += 1;
                }
            } else if current == '/' && next == Some('-') {
                depth += 1;
                index += 2;
            } else if depth > 0 && current == '-' && next == Some('/') {
                depth -= 1;
                index += 2;
            } else if depth > 0 {
                if current == '\n' {
                    out.push('\n');
                }
                index += 1;
            } else if current == '-' && next == Some('-') {
                while index < chars.len() && chars[index] != '\n' {
                    index += 1;
                }
            } else {
                out.push(current);
                index += 1;
            }
        }
        out
    }

    /// Number of binder names in the explicit, implicit, and instance binder groups of one
    /// inductive constructor entry (the text after `|`), plus arrows of an arrow-style type.
    fn lean_ctor_entry_arity(entry: &str) -> (String, usize) {
        let entry = entry.trim_start();
        let name: String = entry
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
            .collect();
        let rest = &entry[name.len()..];
        let mut arity = 0;
        let mut depth = 0usize;
        let mut group = String::new();
        let mut result_type = None;
        for (offset, c) in rest.char_indices() {
            match c {
                '(' | '{' | '[' | '\u{2983}' => {
                    if depth > 0 {
                        group.push(c);
                    }
                    depth += 1;
                }
                ')' | '}' | ']' | '\u{2984}' => {
                    depth -= 1;
                    if depth == 0 {
                        let names = group.split(':').next().unwrap_or("");
                        arity += names.split_whitespace().count();
                        group.clear();
                    } else {
                        group.push(c);
                    }
                }
                ':' if depth == 0 => {
                    result_type = Some(&rest[offset + 1..]);
                    break;
                }
                _ if depth > 0 => group.push(c),
                _ => {}
            }
        }
        if let Some(result_type) = result_type {
            let mut nesting = 0i32;
            for c in result_type.chars() {
                match c {
                    '(' | '{' | '[' => nesting += 1,
                    ')' | '}' | ']' => nesting -= 1,
                    '\u{2192}' if nesting == 0 => arity += 1,
                    _ => {}
                }
            }
        }
        (name, arity)
    }

    /// `(name, explicit field count, is_structure)` of every structure and inductive
    /// constructor declared at the top level of a Lean source file.
    fn lean_decl_arities(text: &str) -> Vec<(String, usize, bool)> {
        let stripped = strip_lean_comments(text);
        let lines: Vec<&str> = stripped.lines().collect();
        let mut out = Vec::new();
        let mut index = 0;
        while index < lines.len() {
            let line = lines[index];
            index += 1;
            let (is_structure, rest) = if let Some(rest) = line.strip_prefix("structure ") {
                (true, rest)
            } else if let Some(rest) = line.strip_prefix("inductive ") {
                (false, rest)
            } else {
                continue;
            };
            let type_name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
                .collect();
            let body_start = index;
            while index < lines.len()
                && (lines[index].is_empty() || lines[index].starts_with([' ', '\t']))
            {
                index += 1;
            }
            let body = &lines[body_start..index];
            if is_structure {
                let fields = body
                    .iter()
                    .filter(|line| {
                        let Some(field) = line.strip_prefix("  ") else {
                            return false;
                        };
                        let name_len = field
                            .chars()
                            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
                            .count();
                        name_len > 0
                            && !field.starts_with(|c: char| c.is_ascii_digit())
                            && field[name_len..].starts_with(" :")
                    })
                    .count();
                out.push((type_name, fields, true));
            } else {
                let mut entries: Vec<String> = Vec::new();
                for line in body {
                    if let Some(entry) = line.trim_start().strip_prefix('|') {
                        entries.push(entry.to_owned());
                    } else if let Some(last) = entries.last_mut() {
                        last.push('\n');
                        last.push_str(line);
                    }
                }
                for entry in entries {
                    let (ctor, arity) = lean_ctor_entry_arity(&entry);
                    out.push((format!("{type_name}.{ctor}"), arity, false));
                }
            }
        }
        out
    }

    #[test]
    fn mir_module_ctor_arities_match_trusted_lean_sources() {
        let dialect =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean/Trusted/Rustc/V2026_06_01");
        let mut sources = vec![(String::from("Layout"), dialect.join("Layout.lean"))];
        let mut mir_ast: Vec<PathBuf> = std::fs::read_dir(dialect.join("MirAst"))
            .expect("MirAst sources")
            .map(|entry| entry.expect("MirAst entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "lean"))
            .collect();
        mir_ast.sort();
        assert!(!mir_ast.is_empty());
        sources.extend(
            mir_ast
                .into_iter()
                .map(|path| (String::from("MirAst"), path)),
        );

        let mut expected: BTreeMap<String, usize> = BTreeMap::new();
        for (prefix, path) in &sources {
            let text = std::fs::read_to_string(path).expect("trusted Lean source");
            for (name, fields, is_structure) in lean_decl_arities(&text) {
                if is_structure || fields > 0 {
                    let previous = expected.insert(format!("{prefix}.{name}"), fields);
                    assert_eq!(previous, None, "duplicate declaration {name}");
                }
            }
        }
        let verification = std::fs::read_to_string(dialect.join("../../VerificationResult.lean"))
            .expect("VerificationResult.lean");
        let claim = lean_decl_arities(&verification)
            .into_iter()
            .find(|(name, _, is_structure)| name == "Claim" && *is_structure)
            .expect("structure Claim");
        expected.insert(String::from("VerificationResult.Claim"), claim.1);
        for (name, fields) in [("List.cons", 2), ("Option.some", 1), ("Prod.mk", 2)] {
            expected.insert(String::from(name), fields);
        }

        let table: BTreeMap<String, usize> = MIR_MODULE_CTOR_ARITIES
            .iter()
            .map(|arity| (arity.lean_name.to_owned(), arity.fields))
            .collect();
        assert_eq!(
            table.len(),
            MIR_MODULE_CTOR_ARITIES.len(),
            "duplicate table entries"
        );
        assert_eq!(table, expected);
        assert_eq!(table.get("Layout.TypeLayout"), Some(&8));
        assert_eq!(table.get("MirAst.CapturedMir"), Some(&12));
        assert_eq!(table.get("MirAst.TerminatorKind.call"), Some(&5));
    }
}

#[cfg(test)]
mod lean_emit_hygiene_tests {
    use super::*;
    use std::ffi::OsStr;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    fn u32_layout() -> IrTypeLayout {
        IrTypeLayout {
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
        let u32_ty = IrTy {
            kind: IrRigidTy::Uint(IrUintTy::U32),
            layout_idx: 0,
        };
        IrCapturedMir {
            def_path: def_path.to_owned(),
            phase: IrMirPhaseTag::RuntimeOptimized,
            role: IrContractRole::Subject,
            type_param_count,
            generic_params: (0..type_param_count)
                .map(|i| IrGenericParamDef {
                    index: i as u32,
                    name: format!("T{i}"),
                })
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
                        IrPlace {
                            local_: 0,
                            projection: vec![],
                        },
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
                ret: IrArgAbi {
                    layout: layout.clone(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![layout],
            },
            allocations: vec![],
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
    fn lean_reserved_idents_is_strictly_sorted() {
        assert!(
            LEAN_RESERVED_IDENTS.windows(2).all(|w| w[0] < w[1]),
            "LEAN_RESERVED_IDENTS must be strictly sorted for binary_search"
        );
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
        assert_eq!(escape_lean_str("\u{2028}\u{202e}"), "\\u2028\\u202e");
        assert_eq!(escape_lean_str("\"\\"), "\\\"\\\\");

        // The emitted `Mir` module renders `defPath` through the same escaping.
        let code = emit_mir_lean_module("Mir.Demo.Weird", &fixture_mir(tricky, 0, vec![], 1));
        let lit = render_lean_str(tricky);
        assert!(code.contains(&format!("defPath := {lit}")), "{code}");
        assert!(!code.contains(tricky));
        assert!(!code.chars().any(|c| c.is_control() && c != '\n'));
    }

    #[test]
    fn mir_module_header_neutralizes_comment_delimiters_and_imports_trusted_only() {
        let mut mir = fixture_mir(
            "demo::x -/ axiom bad : False /- y\nz\u{2028}\u{202e}end",
            0,
            vec![],
            1,
        );
        let u32_ty = mir.local_decls[0].ty.clone();
        // Regression (B2): when `stmt.comment` / `terminator.comment` is `None`,
        // `summarize_basic_block` falls back to `summarize_statement_kind` /
        // `summarize_terminator_kind`, which splice `Unevaluated(def_path)`,
        // `ThreadLocalRef(path)`, and `Downcast(Some(name), _)` into `-- bb0: ...`.
        // Embedded `\n`, `\r`, `\u{85}`, `\u{2028}`, or BiDi overrides must never break out of
        // the `-- bb0:` line comment into trusted `Mir/<Item>.lean`.
        mir.basic_blocks[0].statements.push(IrStatement {
            kind: IrStatementKind::Assign(
                IrPlace {
                    local_: 0,
                    projection: vec![IrProjectionElem::Downcast(
                        Some(String::from("Variant\naxiom bad_downcast : False")),
                        0,
                    )],
                },
                IrRvalue::ThreadLocalRef(String::from(
                    "demo::TLS\raxiom bad_tls : False\u{2028}def injected := 1",
                )),
            ),
            span: String::from("src/lib.rs:2:1: 2:2"),
            comment: None,
        });
        mir.basic_blocks[0].terminator = IrTerminator {
            kind: IrTerminatorKind::Call {
                func: IrOperand::Constant(IrConstOperand {
                    ty: u32_ty,
                    val: IrConstValue::Unevaluated(String::from(
                        "demo::callee\naxiom bad_call : False\u{85}theorem evil : False := sorry",
                    )),
                }),
                args: vec![],
                destination: IrPlace {
                    local_: 0,
                    projection: vec![],
                },
                target: None,
                unwind: IrUnwindAction::Terminate,
            },
            span: String::from("src/lib.rs:3:1: 3:2"),
            comment: None,
        };
        let code = emit_mir_lean_module("Mir.Demo.X", &mir);
        let doc = code.lines().find(|line| line.starts_with("/-! ")).unwrap();
        assert!(doc.ends_with(" -/"), "{doc}");
        let inner = &doc[3..doc.len() - 2];
        assert!(!inner.contains("-/") && !inner.contains("/-"), "{doc}");
        assert!(
            !code.lines().any(|line| {
                let t = line.trim_start();
                t.starts_with("axiom") || t.starts_with("theorem") || t.starts_with("def injected")
            }),
            "comment breakout in emitted Mir module:\n{code}"
        );
        assert!(
            !code
                .chars()
                .any(|c| c != '\n' && is_disallowed_guillemet_char(c)),
            "disallowed control/format character in emitted Mir module:\n{code:?}"
        );
        // TrustedBoundary statement-origin isolation: a trusted `Mir/<Item>.lean` module imports
        // `Trusted` only, never `Anneal.*` (in particular not `Anneal.OpaqueCalleeTable`).
        let imports: Vec<&str> = code
            .lines()
            .filter(|line| line.starts_with("import "))
            .collect();
        assert_eq!(imports, vec!["import Trusted"]);
        assert_eq!(sanitize_block_comment_text("a/-/b\n-/"), "a/ - /b - /");
    }

    #[test]
    fn validate_lean_dotted_name_cases() {
        for ok in [
            "Mir",
            "Mir.Demo.leaf",
            "Gen._private",
            "Mir.«my-crate».x",
            "A'.B",
            "Mir.end",
            "Mir.repeat",
            "Mir.exists",
            "Mir.elab",
            "Mir.prelude",
            "Mir.coinductive",
            "Mir.Demo.end",
        ] {
            assert_eq!(validate_lean_dotted_name(ok), Ok(()), "{ok:?}");
        }
        for bad in [
            "",
            ".",
            "Mir.",
            ".Mir",
            "Mir..Demo",
            "Mir.Demo\nimport Evil",
            "Mir Demo",
            "0Mir",
            "Mir._",
            "end",
            "repeat",
            "end.Mir",
            "exists",
            "Mir.«»",
            "Mir.«a",
            "Mir.«a\u{202e}b»",
            "Mir-Demo",
            "Mir.Demo -- x",
        ] {
            assert!(validate_lean_dotted_name(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn sanitize_deriving_classes_drops_redundant_beq() {
        let cases: &[(&[&str], &[&str])] = &[
            (&["BEq", "DecidableEq"], &["DecidableEq"]),
            (&["DecidableEq", "BEq", "Repr"], &["DecidableEq", "Repr"]),
            (&["Repr", "BEq", "Hashable"], &["Repr", "BEq", "Hashable"]),
            (&["_root_.BEq", "Foo.DecidableEq"], &["Foo.DecidableEq"]),
            (
                &["@[expose] BEq", "@[expose] DecidableEq"],
                &["@[expose] DecidableEq"],
            ),
            (&["(BEq)", " DecidableEq "], &["DecidableEq"]),
            (&["Lean.«BEq»", "«DecidableEq»"], &["«DecidableEq»"]),
            (
                &["BEqLike", "DecidableEq", "MyBEq"],
                &["BEqLike", "DecidableEq", "MyBEq"],
            ),
            (
                &[
                    "Repr",
                    "Repr",
                    "DecidableEq",
                    "_root_.DecidableEq",
                    "@[expose] DecidableEq",
                ],
                &["Repr", "DecidableEq"],
            ),
            (&["", "  ", "Hashable", "@[expose]"], &["Hashable"]),
            (&["BEq", "BEq"], &["BEq"]),
            (
                &[
                    "ToJson (opt := 1)",
                    "ToJson  (opt := 1)",
                    "BEq",
                    "DecidableEq",
                ],
                &["ToJson (opt := 1)", "DecidableEq"],
            ),
            // Guillemets containing spaces or parens before `.BEq` / `.DecidableEq`:
            (
                &["«a b».BEq", "«c(d)».DecidableEq"],
                &["«c(d)».DecidableEq"],
            ),
            // Single atomic guillemet component containing `.` is NOT namespace-qualified `BEq`:
            (&["«Not.BEq»", "DecidableEq"], &["«Not.BEq»", "DecidableEq"]),
            // Nested `[...]` inside `@[...]` attributes:
            (
                &[
                    "@[aesop safe [constructors]] BEq",
                    "@[aesop safe [constructors]] DecidableEq",
                ],
                &["@[aesop safe [constructors]] DecidableEq"],
            ),
            // Parenthesized head with trailing arguments must be preserved and deduplicated:
            (
                &[
                    "(CustomHandler) opt",
                    "((CustomHandler) opt)",
                    "BEq",
                    "DecidableEq",
                ],
                &["(CustomHandler) opt", "DecidableEq"],
            ),
            (
                // Regression: outer arguments after a parenthesized class application are part
                // of the class reference (never dropped, deduplicated away, or read as unary).
                &[
                    "Handler a",
                    "(Handler a) b",
                    "(Handler a) c",
                    "(BEq a) b",
                    "DecidableEq",
                ],
                &[
                    "Handler a",
                    "(Handler a) b",
                    "(Handler a) c",
                    "(BEq a) b",
                    "DecidableEq",
                ],
            ),
            // Multi-argument handler whose head ends in `.BEq` is not core's unary `BEq`:
            (
                &["CustomPkg.BEq opt", "DecidableEq"],
                &["CustomPkg.BEq opt", "DecidableEq"],
            ),
            // Char literals, raw strings, comments, universe annotations, curried parens, and
            // unclosed delimiters (never silently delete a non-empty class entry):
            (
                &[
                    "/- a -/ @[expose] /- b -/ BEq /- c -/",
                    "BEq -- trailing note\n",
                    "BEq.{0}",
                    "(Handler '\"')",
                    "(Handler ')') opt",
                    "(Handler r#\")\"#)",
                    "(Handler s!\"a {\\\"b\\\"} )\")",
                    "Handler.{0}",
                    "Handler.{ 0 }",
                    "Handler.{1}",
                    "Handler a b",
                    "(Handler a) b",
                    "((Handler a)) b",
                    "(Handler a ) b",
                    "Handler (a b)",
                    "Foo.«end».Handler",
                    "Foo.end.Handler",
                    "«end»",
                    "_root_.end",
                    "_root_.«end»",
                    "(UnclosedHandler",
                    "/- only comment -/",
                    "DecidableEq.{0}",
                ],
                &[
                    "(Handler '\"')",
                    "(Handler ')') opt",
                    "(Handler r#\")\"#)",
                    "(Handler s!\"a {\\\"b\\\"} )\")",
                    "Handler.{0}",
                    "Handler.{1}",
                    "Handler a b",
                    "Handler (a b)",
                    "Foo.«end».Handler",
                    "«end»",
                    "(UnclosedHandler",
                    "DecidableEq.{0}",
                ],
            ),
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
        // Inline `--` or unclosed `/-` in an earlier entry must never swallow `, Hashable`:
        assert_eq!(
            render_deriving_clause(&[
                "Repr -- note",
                "BEq /- unclosed",
                "DecidableEq",
                "Hashable\n"
            ]),
            "deriving Repr, DecidableEq, Hashable"
        );
        assert_eq!(
            render_deriving_clause(&["Repr /- unclosed", "Hashable"]),
            "deriving Repr, Hashable"
        );
        // Comments inside `<ident>!"{...}"` interpolation holes must be stripped before
        // newline-flattening so `--` never swallows the closing `}"` or `, DecidableEq`:
        assert_eq!(
            render_deriving_clause(&["Handler s!\"{x -- hole note\n}\"", "BEq", "DecidableEq"]),
            "deriving Handler s!\"{x   }\", DecidableEq"
        );
        assert_eq!(
            render_deriving_clause(&[
                "Handler s!\"{x /- nested /- c -/ -/}\"",
                "BEq",
                "DecidableEq",
            ]),
            "deriving Handler s!\"{x  }\", DecidableEq"
        );
        // `.r"..."` is a field projection `.r` applied to a normal string (not raw `r"..."`),
        // so escaped `\"` stays inside the string and `--` / `)` inside it are preserved:
        assert_eq!(
            render_deriving_clause(&[
                "Handler (foo.r\"\\\" -- not a comment\")",
                "BEq",
                "DecidableEq",
            ]),
            "deriving Handler (foo.r\"\\\" -- not a comment\"), DecidableEq"
        );
        assert_eq!(
            sanitize_deriving_classes(&["(Handler (foo.r\"\\\" )\"))", "BEq", "DecidableEq"]),
            vec!["(Handler (foo.r\"\\\" )\"))", "DecidableEq"]
        );
        // An entry that opens a string, raw string, interpolation (or hole), or `«` it never
        // closes is cut where that literal starts, so it can never swallow `, <class>` or the
        // generated lines after the clause (an unclosed `/-` already drops its entry's rest):
        assert_eq!(
            render_deriving_clause(&["Handler s!\"{x /- c}\"", "BEq", "DecidableEq"]),
            "deriving Handler s!, DecidableEq"
        );
        assert_eq!(
            render_deriving_clause(&["Handler \"open", "Repr"]),
            "deriving Handler, Repr"
        );
        assert_eq!(
            render_deriving_clause(&["Handler \"esc\\\"", "Repr"]),
            "deriving Handler, Repr"
        );
        assert_eq!(
            render_deriving_clause(&["Handler r#\"raw\"", "Repr"]),
            "deriving Handler, Repr"
        );
        assert_eq!(
            render_deriving_clause(&["Foo «bar", "Repr"]),
            "deriving Foo, Repr"
        );
        // Closed literals (including nested strings in holes, `'"'`, `.r"..."` projections, and raw
        // strings) are kept verbatim:
        assert_eq!(
            render_deriving_clause(&[
                "Handler s!\"{\"}\"}\"",
                "(Handler '\"')",
                "Handler (foo.r\"x\")",
                "Handler r#\"a\"b\"#",
                "Foo.«a b»",
            ]),
            "deriving Handler s!\"{\"}\"}\", (Handler '\"'), Handler (foo.r\"x\"), \
             Handler r#\"a\"b\"#, Foo.«a b»"
        );
    }

    #[test]
    #[should_panic(expected = "invalid Mir module namespace")]
    fn mir_emitter_rejects_injected_namespace() {
        let mir = fixture_mir("demo::x", 0, vec![], 1);
        emit_mir_lean_module(
            "Mir.Demo.X\nimport Anneal.OpaqueCalleeTable\nnamespace Mir.Demo.X",
            &mir,
        );
    }

    #[test]
    #[should_panic(expected = "invalid Mir module namespace")]
    fn mir_emitter_rejects_standalone_keyword_namespace() {
        let mir = fixture_mir("demo::x", 0, vec![], 1);
        emit_mir_lean_module("end", &mir);
    }

    /// Splits a `deriving` class list on top-level commas outside brackets, comments, strings,
    /// raw strings, char literals, and `«...»`.
    fn split_top_level_commas(s: &str) -> Vec<&str> {
        let mut out = Vec::new();
        let mut start = 0usize;
        let mut depth = 0usize;
        let mut i = 0usize;
        let mut prev_ident = false;
        let mut prev_dot = false;
        while i < s.len() {
            let rest = &s[i..];
            if rest.starts_with("--") {
                i = rest.find('\n').map_or(s.len(), |nl| i + nl);
                prev_ident = false;
                prev_dot = false;
            } else if rest.starts_with("/-") {
                let mut cdepth = 1usize;
                let mut cur = i + 2;
                while cdepth > 0 && cur < s.len() {
                    let tail = &s[cur..];
                    if tail.starts_with("/-") {
                        cdepth += 1;
                        cur += 2;
                    } else if tail.starts_with("-/") {
                        cdepth -= 1;
                        cur += 2;
                    } else {
                        cur += tail.chars().next().unwrap().len_utf8();
                    }
                }
                i = cur;
                prev_ident = false;
                prev_dot = false;
            } else if rest.starts_with('«') {
                let end = skip_lean_guillemet_bytes(s, i);
                prev_ident = end > i + '«'.len_utf8();
                prev_dot = false;
                i = end;
            } else if let Some(end) = (!prev_ident && !prev_dot && rest.starts_with('r'))
                .then(|| skip_lean_raw_str_bytes(s, i))
                .flatten()
            {
                i = end;
                prev_ident = false;
                prev_dot = false;
            } else if rest.starts_with('"') {
                i = skip_lean_str_or_interp_bytes(s, i);
                prev_ident = false;
                prev_dot = false;
            } else if let Some(end) = (!prev_ident && rest.starts_with('\''))
                .then(|| skip_lean_char_lit_bytes(s, i))
                .flatten()
            {
                i = end;
                prev_ident = false;
                prev_dot = false;
            } else {
                let c = rest.chars().next().unwrap();
                match c {
                    '(' | '[' | '{' | '⟨' | '⦃' => depth += 1,
                    ')' | ']' | '}' | '⟩' | '⦄' => depth = depth.saturating_sub(1),
                    ',' if depth == 0 => {
                        out.push(&s[start..i]);
                        start = i + 1;
                    }
                    _ => {}
                }
                prev_ident = is_lean_ident_cont_char(c);
                prev_dot = c == '.';
                i += c.len_utf8();
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
            let standalone = normalized[..pos]
                .chars()
                .next_back()
                .is_none_or(|c| !is_ident(c) && c != '.')
                && normalized[after..]
                    .chars()
                    .next()
                    .is_none_or(|c| !is_ident(c));
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
            let cores: Vec<String> = split_top_level_commas(classes)
                .into_iter()
                .filter_map(deriving_unary_class_core)
                .collect();
            if cores.iter().any(|c| c == "BEq") && cores.iter().any(|c| c == "DecidableEq") {
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
        assert_eq!(
            redundant_beq_deriving_clauses(include_str!("lean_emit.rs")),
            vec![]
        );
        // ... and neither does any module the emitters produce.
        let leaf = fixture_mir("demo::leaf", 0, vec![], 1);
        let poly = fixture_mir(
            "demo::poly",
            1,
            vec![trait_impl("demo::Tr::m", "demo::<u32 as Tr>::m")],
            2,
        );
        for code in [
            emit_mir_lean_module("Mir.Demo.Leaf", &leaf),
            emit_mir_lean_module("Mir.Demo.Poly", &poly),
        ] {
            assert_eq!(redundant_beq_deriving_clauses(&code), vec![]);
        }
    }

    /// Lean toolchain for the end-to-end kernel check: `lake` (`ANNEAL_LAKE`, else elan's
    /// `~/.elan/bin/lake`, else `PATH`), run from the repository root whose `.lake/build` holds
    /// the `Trusted` `.olean`.
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
            let olean = repo_root.join(".lake/build/lib/lean/Trusted.olean");
            if !olean.is_file() {
                return Err(format!(
                    "{} is missing (run `lake build Trusted`)",
                    olean.display()
                ));
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
            let src = stage
                .join(module.split('.').collect::<PathBuf>())
                .with_extension("lean");
            std::fs::create_dir_all(src.parent().unwrap()).unwrap();
            std::fs::write(&src, code).unwrap();
            let olean = src.with_extension("olean");
            let root = format!("--root={}", stage.display());
            self.lean(
                stage,
                &[
                    OsStr::new(&root),
                    OsStr::new("-o"),
                    olean.as_os_str(),
                    src.as_os_str(),
                ],
            )
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
                rest.trim_start()
                    .starts_with("error")
                    .then(|| line_no.parse().ok())
                    .flatten()
            })
            .collect()
    }

    /// End-to-end Lean 4 kernel check: stages emitted `Mir/<Item>.lean` modules (including
    /// `Mir.Demo.end`, whose final namespace component is a Lean keyword, carrying control, BiDi
    /// and comment-breakout payloads in its captured paths) in a temporary directory outside the
    /// checkout, compiles them with `lake env lean` against this checkout's `.lake/build`, checks
    /// from a downstream driver that captured def paths survive escaping character-for-character
    /// (with a standard axiom footprint), and checks that a false `defPath` claim and every
    /// comment-breakout declaration are rejected. Skips (with a message) when the Lean build is
    /// unavailable, unless `ANNEAL_REQUIRE_LEAN_E2E` is set.
    #[test]
    fn e2e_lean_kernel_checks_emitted_mir_modules() {
        let lean = match LeanE2e::detect() {
            Ok(lean) => lean,
            Err(reason) => {
                assert!(
                    std::env::var_os("ANNEAL_REQUIRE_LEAN_E2E").is_none(),
                    "Lean e2e required but unavailable: {reason}"
                );
                eprintln!("SKIPPED e2e_lean_kernel_checks_emitted_mir_modules: {reason}");
                return;
            }
        };
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let stage_dir = StageDir(std::env::temp_dir().join(format!(
            "anneal-lean-emit-e2e-{}-{nanos}",
            std::process::id()
        )));
        std::fs::create_dir_all(&stage_dir.0).unwrap();
        let stage = stage_dir.0.canonicalize().unwrap();
        assert!(
            !stage.starts_with(&lean.repo_root),
            "staging dir must be outside the checkout"
        );

        let weird_path = "demo::we\"ird\\path\n\t\u{1}\u{7f}\u{85}\u{2028}\u{202e}é→";
        let mut weird_mir = fixture_mir(weird_path, 0, vec![], 7);
        let weird_u32_ty = weird_mir.local_decls[0].ty.clone();
        weird_mir.basic_blocks[0].statements.push(IrStatement {
            kind: IrStatementKind::Assign(
                IrPlace {
                    local_: 0,
                    projection: vec![],
                },
                IrRvalue::Use(IrOperand::Constant(IrConstOperand {
                    ty: weird_u32_ty,
                    val: IrConstValue::Unevaluated(String::from(
                        "demo::CONST\naxiom bad_e2e_comment_breakout : False",
                    )),
                })),
            ),
            span: String::from("src/lib.rs:2:1: 2:2"),
            comment: None,
        });
        let area_impl = trait_impl("demo::Area::area", "demo::<Square as Area>::area");
        let items = vec![
            ("Mir.Demo.Leaf", fixture_mir("demo::leaf", 0, vec![], 1)),
            ("Mir.Demo.Poly", fixture_mir("demo::poly", 2, vec![], 2)),
            (
                "Mir.Demo.SquareArea",
                fixture_mir("demo::<Square as Area>::area", 0, vec![area_impl], 3),
            ),
            ("Mir.Demo.end", weird_mir),
        ];
        for (module, mir) in &items {
            let code = emit_mir_lean_module(module, mir);
            assert_eq!(redundant_beq_deriving_clauses(&code), vec![], "{module}");
            let (ok, out) = lean.compile(&stage, module, &code);
            assert!(
                ok,
                "emitted {module} failed to elaborate:\n{out}\n--- source ---\n{code}"
            );
            assert!(
                !out.contains("sorry") && !out.contains("warning"),
                "{module}:\n{out}"
            );
        }
        let imports: String = items
            .iter()
            .map(|(module, _)| format!("import {module}\n"))
            .collect();

        let weird_chars: Vec<String> = weird_path
            .chars()
            .map(|c| format!("Char.ofNat {}", u32::from(c)))
            .collect();
        let driver = format!(
            "{imports}\n\
             -- Captured def paths survive Lean string escaping character-for-character (including\n\
             -- inside a module/body whose final component is a Lean keyword `Mir.Demo.end`).\n\
             theorem e2e_weird_def_path : (Mir.Demo.end.body).defPath.toList = [{}] := rfl\n\n\
             theorem e2e_identity_fields :\n    \
             Mir.Demo.Leaf.body.defPath = \"demo::leaf\" ∧ Mir.Demo.Poly.body.typeParamCount = 2 ∧\n      \
             Mir.Demo.SquareArea.body.defPath = \"demo::<Square as Area>::area\" :=\n  \
             ⟨rfl, rfl, rfl⟩\n\n\
             #print axioms e2e_weird_def_path\n\
             #print axioms e2e_identity_fields\n",
            weird_chars.join(", ")
        );
        let driver_path = stage.join("Driver.lean");
        std::fs::write(&driver_path, &driver).unwrap();
        let (ok, out) = lean.lean(&stage, &[driver_path.as_os_str()]);
        assert!(ok, "driver failed:\n{out}\n--- source ---\n{driver}");
        assert!(!out.contains("error") && !out.contains("sorry"), "{out}");
        let axiom_reports = out.matches("depends on axioms").count()
            + out.matches("does not depend on any axioms").count();
        assert_eq!(axiom_reports, 2, "{out}");
        // Core's `String.toList` (UTF-8 `ByteArray` decoding) itself depends on
        // `Classical.choice`, so only the identity-field theorem is pinned axiom-free.
        assert!(
            out.contains("'e2e_identity_fields' does not depend on any axioms"),
            "{out}"
        );
        for forbidden in ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"] {
            assert!(
                !out.contains(forbidden),
                "an e2e theorem depends on {forbidden}:\n{out}"
            );
        }

        // Negative controls: a false `defPath` claim is rejected by the kernel, and no
        // comment-breakout payload ever became a declaration.
        let bad = format!(
            "{imports}\n\
             theorem e2e_bad_def_path : Mir.Demo.Leaf.body.defPath = \"demo::poly\" := by\n  \
             decide +kernel\n"
        );
        let bad_path = stage.join("BadDriver.lean");
        std::fs::write(&bad_path, &bad).unwrap();
        let (ok, out) = lean.lean(&stage, &[bad_path.as_os_str()]);
        assert!(!ok, "a false defPath claim was accepted:\n{out}");
        // Lean capitalizes some diagnostics (`Unknown identifier`): compare case-insensitively.
        let lower = out.to_lowercase();
        for unexpected in [
            "unknown identifier",
            "unknown constant",
            "unexpected token",
            "unknown namespace",
        ] {
            assert!(
                !lower.contains(unexpected),
                "negative control failed for the wrong reason:\n{out}"
            );
        }
        // The only error is the kernel `decide` refutation on the theorem's tactic line.
        assert_eq!(
            lean_error_lines(&out, "BadDriver.lean"),
            vec![items.len() + 3],
            "{out}"
        );
        assert!(out.contains("is false"), "{out}");
        for name in [
            "bad_e2e_comment_breakout",
            "Mir.Demo.end.bad_e2e_comment_breakout",
        ] {
            let probe = format!("{imports}\n#check @{name}\n");
            let probe_path = stage.join("Probe.lean");
            std::fs::write(&probe_path, &probe).unwrap();
            let (ok, out) = lean.lean(&stage, &[probe_path.as_os_str()]);
            assert!(!ok, "comment breakout declared `{name}`:\n{out}");
            let lower = out.to_lowercase();
            assert!(
                lower.contains("unknown identifier") || lower.contains("unknown constant"),
                "breakout probe for `{name}` failed for the wrong reason:\n{out}"
            );
            assert_eq!(
                lean_error_lines(&out, "Probe.lean"),
                vec![items.len() + 2],
                "{out}"
            );
        }
    }
}

#[cfg(test)]
mod format_char_escape_tests {
    use super::*;

    #[test]
    fn escape_lean_str_escapes_every_bidi_and_invisible_format_char() {
        for c in [
            '\u{0600}', '\u{0605}', '\u{061C}', '\u{06DD}', '\u{070F}', '\u{0890}', '\u{0891}',
            '\u{08E2}', '\u{180E}', '\u{200B}', '\u{200E}', '\u{200F}', '\u{202A}', '\u{202E}',
            '\u{2028}', '\u{2029}', '\u{2060}', '\u{2064}', '\u{2066}', '\u{2069}', '\u{206A}',
            '\u{206F}', '\u{FEFF}', '\u{FFF9}', '\u{FFFB}',
        ] {
            assert_eq!(
                escape_lean_str(&c.to_string()),
                format!("\\u{:04x}", u32::from(c)),
                "{c:?}"
            );
        }
        // U+00AD SOFT HYPHEN is <= 0xFF and escaped as `\u00ad`.
        assert_eq!(escape_lean_str("\u{00AD}"), "\\u00ad");
        // Supplementary-plane format/tag chars (`Cf` > U+FFFF) are rejected in guillemets and
        // scrubbed from comments without corrupting Lean string literals (which only have 4-digit
        // `\uHHHH` escapes).
        for tag in ['\u{E0001}', '\u{E0020}', '\u{E007F}'] {
            assert!(validate_lean_dotted_name(&format!("Mir.«a{tag}b»")).is_err());
            assert_eq!(sanitize_comment_line(&format!("a{tag}b")), "a b");
            assert_eq!(escape_lean_str(&tag.to_string()), tag.to_string());
        }
        // Visible non-ASCII text stays verbatim.
        assert_eq!(escape_lean_str("é→ü"), "é→ü");
    }
}
