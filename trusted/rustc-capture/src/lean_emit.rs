//! Deterministic Lean 4 source emitter for captured MIR bodies and compiler
//! layouts (`Mir/<Item>.lean`).
//!
//! Each emitted module imports `Trusted`, opens the
//! dialect namespace (`Trusted.Rustc.V2026_06_01`), and pairs human-readable
//! MIR/layout line comments with 1-to-1 `CapturedMir` and `LayoutTable`
//! constructors matching `trusted/lean/Trusted/Rustc/V2026_06_01/`.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Range;

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
// The variants mirror the Lean constructors one-to-one; boxing `CopyNonOverlapping` would
// change the IR shape that `mir_lower.rs` builds.
#[allow(clippy::large_enum_variant)]
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
///
/// Every constructor of the module is one of [`MIR_MODULE_CTOR_ARITIES`], whose fit within the
/// LCNF constructor budgets is asserted at compile time; [`try_emit_mir_lean_module`] re-checks
/// it before emitting.
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
// LCNF constructor-size guard (Lean `v4.34.1` `IR/Checker.lean` limits)
// ---------------------------------------------------------------------------

/// Scalar-area budget, in bytes, of every constructor the LCNF guard emits.
///
/// Lean `v4.34.1`'s IR checker (`IR/Checker.lean`, `checkExpr` on `.ctor`) rejects a
/// constructor whose scalar area (`ssize + usize * 8`) exceeds
/// [`LEAN_IR_MAX_CTOR_SCALAR_BYTES`] ("has too many scalar fields"), and the debug C runtime
/// asserts the strict `scalar_sz < 1024` in `lean_alloc_ctor`. `960 = 1024 - 64` stays below
/// both.
pub const MAX_LCNF_CTOR_SCALAR_BYTES: usize = 960;

/// Boxed-field budget of every constructor the LCNF guard emits.
///
/// The IR checker rejects more than [`LEAN_IR_MAX_CTOR_OBJ_FIELDS`] boxed fields ("has too many
/// fields") and `lean_alloc_ctor` asserts `num_objs < 256`. `240 = 256 - 16` stays below both.
pub const MAX_LCNF_CTOR_OBJ_FIELDS: usize = 240;

/// Declared-field budget (erased fields included) of every constructor the LCNF guard emits.
///
/// Independently of the IR checker, Lean `v4.34.1` stops elaborating wide structures: the
/// `structure` command fails with "maximum recursion depth has been reached" (default
/// `maxRecDepth`) at `520` fields while `500` fields elaborate, and the derived `BEq` instance
/// already fails at `256` fields. At `240` fields, a structure deriving `Inhabited`, `Repr`,
/// `BEq` and `Hashable` elaborates. A constructor within the two IR budgets may still declare
/// `960` one-byte scalar fields plus any number of erased fields, so the guard also caps the
/// declared fields. The cap equals [`MAX_LCNF_CTOR_OBJ_FIELDS`], so splits forced by boxed
/// fields (`300 x Nat` into `[240, 60]`) are unchanged.
pub const MAX_LCNF_CTOR_DECLARED_FIELDS: usize = 240;

/// `LEAN_MAX_CTOR_SCALARS_SIZE` (`lean.h`): the largest constructor scalar area, in bytes, that
/// the IR checker accepts.
pub const LEAN_IR_MAX_CTOR_SCALAR_BYTES: usize = 1024;

/// `LEAN_MAX_CTOR_FIELDS` (`lean.h`): the largest number of boxed fields of one constructor that
/// the IR checker accepts.
pub const LEAN_IR_MAX_CTOR_OBJ_FIELDS: usize = 256;

/// Width, in bytes, of the widest unboxed LCNF scalar (`UInt64`, `USize`, `Float`).
pub const MAX_LCNF_SCALAR_FIELD_BYTES: usize = 8;

// Every guard budget stays strictly below the Lean limits, and any two wrapper fields (at most
// `MAX_LCNF_SCALAR_FIELD_BYTES` scalar bytes or one boxed field each) fit one constructor, so
// every wrapper level of `plan_lcnf_ctor_layout_levels` shrinks.
const _: () = assert!(
    MAX_LCNF_CTOR_SCALAR_BYTES < LEAN_IR_MAX_CTOR_SCALAR_BYTES
        && MAX_LCNF_CTOR_OBJ_FIELDS < LEAN_IR_MAX_CTOR_OBJ_FIELDS
        && MAX_LCNF_CTOR_DECLARED_FIELDS >= MAX_LCNF_CTOR_OBJ_FIELDS
        && 2 * MAX_LCNF_SCALAR_FIELD_BYTES <= MAX_LCNF_CTOR_SCALAR_BYTES
        && MAX_LCNF_CTOR_OBJ_FIELDS >= 2,
    "LCNF guard budgets must stay below the Lean limits and fit any two wrapper fields"
);

/// How Lean `v4.34.1` stores one structure field after LCNF erasure and IR lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LcnfFieldKind {
    /// Unboxed scalar of `bytes` bytes in the constructor's scalar area. Valid widths are `1`
    /// (`Bool`, `UInt8`, `Int8`, enumeration types with fewer than `256` constructors), `2`
    /// (`UInt16`, `Int16`), `4` (`UInt32`, `Int32`, `Char`, `Float32`) and `8` (`UInt64`,
    /// `Int64`, `USize`, `ISize`, `Float`). A structure with exactly one relevant field of such a
    /// type is unboxed the same way.
    Scalar {
        /// Width in bytes (`1`, `2`, `4`, or `8`).
        bytes: usize,
    },
    /// Boxed `lean_object *` field: `Nat`, `Int`, `String`, `Unit`, `List _`, `Array _`,
    /// `Option _`, and `Type`-valued structures with zero or at least two relevant fields.
    ObjectRef,
    /// Computationally irrelevant field erased by LCNF (a proof of a proposition, a type, or a
    /// type former): no scalar bytes and no boxed field.
    Irrelevant,
}

impl LcnfFieldKind {
    /// Scalar-area bytes this field occupies in its constructor.
    pub const fn scalar_bytes(self) -> usize {
        match self {
            Self::Scalar { bytes } => bytes,
            Self::ObjectRef | Self::Irrelevant => 0,
        }
    }

    /// Boxed fields this field occupies in its constructor (`0` or `1`).
    pub const fn obj_fields(self) -> usize {
        match self {
            Self::ObjectRef => 1,
            Self::Scalar { .. } | Self::Irrelevant => 0,
        }
    }

    /// True unless the field is erased.
    pub const fn is_relevant(self) -> bool {
        !matches!(self, Self::Irrelevant)
    }

    /// True unless the field is a `Scalar` whose width is not `1`, `2`, `4`, or `8` bytes.
    pub const fn is_valid(self) -> bool {
        match self {
            Self::Scalar { bytes } => matches!(bytes, 1 | 2 | 4 | 8),
            Self::ObjectRef | Self::Irrelevant => true,
        }
    }

    /// The kind of a field whose type is the given builtin Lean type, or `None` when the type
    /// is not in this table.
    ///
    /// Every entry agrees with Lean `v4.34.1` (probed in
    /// `lcnf_tests::lcnf_live_lean_builtin_kinds_match_model`). The function returns `None` for
    /// every other type, including user structures (unboxed when they have exactly one relevant
    /// field) and enumeration types (`1`-byte scalars), so callers classify those explicitly.
    pub fn of_builtin_lean_ty(lean_ty: &str) -> Option<Self> {
        match lean_ty.trim() {
            "Bool" | "UInt8" | "Int8" => Some(Self::Scalar { bytes: 1 }),
            "UInt16" | "Int16" => Some(Self::Scalar { bytes: 2 }),
            "UInt32" | "Int32" | "Char" | "Float32" => Some(Self::Scalar { bytes: 4 }),
            "UInt64" | "Int64" | "USize" | "ISize" | "Float" => Some(Self::Scalar { bytes: 8 }),
            "Nat" | "Int" | "String" | "Unit" => Some(Self::ObjectRef),
            "True" | "Prop" | "Type" => Some(Self::Irrelevant),
            _ => None,
        }
    }
}

/// One field of a structure emitted through the LCNF guard.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LcnfFieldSpec {
    /// Lean field name: an ASCII identifier that is not a Lean keyword.
    pub name: String,
    /// Lean type of the field, emitted verbatim (trimmed).
    pub lean_ty: String,
    /// How Lean stores the field.
    pub kind: LcnfFieldKind,
}

impl LcnfFieldSpec {
    /// A field with an explicit kind.
    pub fn new(name: impl Into<String>, lean_ty: impl Into<String>, kind: LcnfFieldKind) -> Self {
        Self {
            name: name.into(),
            lean_ty: lean_ty.into(),
            kind,
        }
    }

    /// A field whose kind follows from a builtin Lean type
    /// ([`LcnfFieldKind::of_builtin_lean_ty`]).
    pub fn builtin(
        name: impl Into<String>,
        lean_ty: impl Into<String>,
    ) -> Result<Self, LcnfLayoutError> {
        let name = name.into();
        let lean_ty = lean_ty.into();
        match LcnfFieldKind::of_builtin_lean_ty(&lean_ty) {
            Some(kind) => Ok(Self::new(name, lean_ty, kind)),
            None => Err(LcnfLayoutError::UnknownBuiltinLeanType {
                field: name,
                lean_ty,
            }),
        }
    }
}

/// How a constructor (a guard `Part` or wrapper) is stored as a field of its parent wrapper.
///
/// This models Lean `v4.34.1`'s trivial-structure optimization (`hasTrivialStructure?`): a
/// single-constructor structure with exactly one relevant field is represented by that field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CtorReprKind {
    /// At least two relevant fields, or one boxed relevant field: one boxed field in the
    /// parent.
    BoxedObject,
    /// Exactly one relevant field, an unboxed scalar of `bytes` bytes: the parent stores the
    /// scalar unboxed. A wrapper over single-`UInt64` parts therefore needs `8` scalar bytes per
    /// part, not one pointer per part.
    UnboxedScalar {
        /// Width in bytes of the single relevant scalar field.
        bytes: usize,
    },
    /// No relevant field (every field is erased, or there are no fields).
    ///
    /// Lean erases such a constructor in its parent only if the structure is itself a
    /// proposition (Lean infers `Prop` for a structure whose fields are all proofs). A
    /// structure with an erased type field, or with no fields at all, is a `Type` stored as a
    /// `lean_box(0)` object: Lean `v4.34.1` rejects `300` fields of
    /// `structure Z : Type where h : True` with "has too many fields". The guard therefore
    /// charges one boxed field ([`CtorReprKind::parent_field_kind`]).
    Erased,
}

impl CtorReprKind {
    /// Representation of a constructor whose fields have the given kinds.
    pub fn of_kinds(kinds: &[LcnfFieldKind]) -> Self {
        let mut relevant = kinds.iter().copied().filter(|kind| kind.is_relevant());
        match (relevant.next(), relevant.next()) {
            (None, _) => Self::Erased,
            (Some(LcnfFieldKind::Scalar { bytes }), None) => Self::UnboxedScalar { bytes },
            (Some(_), _) => Self::BoxedObject,
        }
    }

    /// Representation of a constructor with the given fields.
    pub fn of_fields(fields: &[LcnfFieldSpec]) -> Self {
        let kinds: Vec<LcnfFieldKind> = fields.iter().map(|field| field.kind).collect();
        Self::of_kinds(&kinds)
    }

    /// Kind of the parent-wrapper field that holds a constructor with this representation.
    /// `Erased` is charged as a boxed field (see [`CtorReprKind::Erased`]).
    pub const fn parent_field_kind(self) -> LcnfFieldKind {
        match self {
            Self::UnboxedScalar { bytes } => LcnfFieldKind::Scalar { bytes },
            Self::BoxedObject | Self::Erased => LcnfFieldKind::ObjectRef,
        }
    }
}

/// `IR/Checker.lean` constructor limit, in the order `checkExpr` tests them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IrCtorLimit {
    /// More than [`LEAN_IR_MAX_CTOR_OBJ_FIELDS`] boxed fields.
    Fields,
    /// More than [`LEAN_IR_MAX_CTOR_SCALAR_BYTES`] scalar bytes.
    Scalar,
}

impl IrCtorLimit {
    /// The diagnostic Lean `v4.34.1` reports for this limit
    /// (`constructor '<name>' has too many ...`).
    pub const fn lean_diagnostic(self) -> &'static str {
        match self {
            Self::Fields => "has too many fields",
            Self::Scalar => "has too many scalar fields",
        }
    }
}

/// Scalar-area bytes, boxed fields, and declared fields of one constructor.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct LcnfCtorFootprint {
    /// Bytes in the scalar area (`ssize + usize * 8`).
    pub scalar_bytes: usize,
    /// Boxed (`lean_object *`) fields.
    pub obj_fields: usize,
    /// Declared fields, erased ones included.
    pub declared_fields: usize,
}

impl LcnfCtorFootprint {
    /// Footprint of a constructor whose fields have the given kinds.
    pub fn of_kinds<I: IntoIterator<Item = LcnfFieldKind>>(kinds: I) -> Self {
        kinds
            .into_iter()
            .fold(Self::default(), |footprint, kind| footprint.with(kind))
    }

    /// Footprint of a constructor with the given fields.
    pub fn of_fields(fields: &[LcnfFieldSpec]) -> Self {
        Self::of_kinds(fields.iter().map(|field| field.kind))
    }

    /// This footprint extended by one field of kind `kind`.
    pub const fn with(self, kind: LcnfFieldKind) -> Self {
        Self {
            scalar_bytes: self.scalar_bytes.saturating_add(kind.scalar_bytes()),
            obj_fields: self.obj_fields.saturating_add(kind.obj_fields()),
            declared_fields: self.declared_fields.saturating_add(1),
        }
    }

    /// The first IR-checker limit this constructor violates, in `checkExpr` order, or `None`
    /// when Lean `v4.34.1` accepts it.
    pub const fn ir_violation(self) -> Option<IrCtorLimit> {
        if self.obj_fields > LEAN_IR_MAX_CTOR_OBJ_FIELDS {
            Some(IrCtorLimit::Fields)
        } else if self.scalar_bytes > LEAN_IR_MAX_CTOR_SCALAR_BYTES {
            Some(IrCtorLimit::Scalar)
        } else {
            None
        }
    }

    /// True when the IR checker accepts this constructor.
    pub const fn is_ir_accepted(self) -> bool {
        self.ir_violation().is_none()
    }

    /// True when this constructor fits the guard budgets `max_scalar_bytes` / `max_obj_fields`
    /// and [`MAX_LCNF_CTOR_DECLARED_FIELDS`].
    pub const fn fits_budget(self, max_scalar_bytes: usize, max_obj_fields: usize) -> bool {
        self.scalar_bytes <= max_scalar_bytes
            && self.obj_fields <= max_obj_fields
            && self.declared_fields <= MAX_LCNF_CTOR_DECLARED_FIELDS
    }
}

/// The first IR-checker limit a constructor with `fields` violates, or `None`.
pub fn ir_ctor_violation(fields: &[LcnfFieldSpec]) -> Option<IrCtorLimit> {
    LcnfCtorFootprint::of_fields(fields).ir_violation()
}

/// Checks that Lean `v4.34.1`'s IR checker accepts a constructor with `fields`, returning its
/// footprint.
pub fn check_ir_ctor_accepted(
    fields: &[LcnfFieldSpec],
) -> Result<LcnfCtorFootprint, LcnfLayoutError> {
    check_field_kinds(fields)?;
    let footprint = LcnfCtorFootprint::of_fields(fields);
    match footprint.ir_violation() {
        None => Ok(footprint),
        Some(limit) => Err(LcnfLayoutError::IrCtorRejected { limit, footprint }),
    }
}

/// Error raised by the LCNF guard. Every error is raised before any Lean text is produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LcnfLayoutError {
    /// A per-constructor budget is zero.
    ZeroBudget {
        max_scalar_bytes: usize,
        max_obj_fields: usize,
    },
    /// A per-constructor budget reaches a Lean runtime limit (`scalar_sz < 1024`,
    /// `num_objs < 256`).
    BudgetAtLeanLimit {
        max_scalar_bytes: usize,
        max_obj_fields: usize,
    },
    /// A `Scalar` field whose width is not `1`, `2`, `4`, or `8` bytes.
    InvalidScalarWidth { field: String, bytes: usize },
    /// A single field that does not fit an otherwise empty constructor.
    FieldExceedsBudget {
        field: String,
        scalar_bytes: usize,
        max_scalar_bytes: usize,
    },
    /// A structure, field, or `deriving` name that is not a plain Lean identifier.
    InvalidLeanName { what: &'static str, name: String },
    /// Two fields with the same name.
    DuplicateFieldName { name: String },
    /// Two identical `deriving` entries.
    DuplicateDerive { name: String },
    /// An empty or malformed field type (control character, comment, or `:=`).
    InvalidLeanType { field: String, lean_ty: String },
    /// [`LcnfFieldSpec::builtin`] on a type outside [`LcnfFieldKind::of_builtin_lean_ty`].
    UnknownBuiltinLeanType { field: String, lean_ty: String },
    /// A field name that would collide with a declaration the split layout generates.
    ReservedFieldName { name: String },
    /// In a split layout, a field type that mentions a field, the structure, or `self`.
    DependentFieldType { field: String, depends_on: String },
    /// A constructor that the IR checker rejects.
    IrCtorRejected {
        limit: IrCtorLimit,
        footprint: LcnfCtorFootprint,
    },
    /// A layout plan that violates an invariant of [`LcnfCtorLayoutPlan::validate`].
    MalformedPlan { reason: String },
    /// No expression for a field in [`render_lcnf_guarded_ctor_expr`].
    MissingFieldExpr { field: String },
    /// An expression for a name that is not a field.
    UnknownFieldExpr { field: String },
    /// Two expressions for the same field.
    DuplicateFieldExpr { field: String },
    /// An empty expression, or one with a control character.
    InvalidFieldExpr { field: String },
    /// A constructor of [`MIR_MODULE_CTOR_ARITIES`] (or another arity table) over the budget.
    MirCtorOverBudget {
        lean_name: &'static str,
        fields: usize,
    },
}

impl fmt::Display for LcnfLayoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroBudget {
                max_scalar_bytes,
                max_obj_fields,
            } => write!(
                f,
                "LCNF budget must be positive (scalar {max_scalar_bytes} B, objects {max_obj_fields})"
            ),
            Self::BudgetAtLeanLimit {
                max_scalar_bytes,
                max_obj_fields,
            } => write!(
                f,
                "LCNF budget (scalar {max_scalar_bytes} B, objects {max_obj_fields}) must stay below \
                 the Lean limits ({LEAN_IR_MAX_CTOR_SCALAR_BYTES} B, {LEAN_IR_MAX_CTOR_OBJ_FIELDS} objects)"
            ),
            Self::InvalidScalarWidth { field, bytes } => write!(
                f,
                "field `{field}`: scalar width {bytes} B is not 1, 2, 4, or 8"
            ),
            Self::FieldExceedsBudget {
                field,
                scalar_bytes,
                max_scalar_bytes,
            } => write!(
                f,
                "field `{field}` ({scalar_bytes} B) exceeds the {max_scalar_bytes} B constructor budget"
            ),
            Self::InvalidLeanName { what, name } => {
                write!(f, "invalid Lean {what} name `{name}`")
            }
            Self::DuplicateFieldName { name } => write!(f, "duplicate field `{name}`"),
            Self::DuplicateDerive { name } => write!(f, "duplicate deriving entry `{name}`"),
            Self::InvalidLeanType { field, lean_ty } => {
                write!(f, "field `{field}`: invalid Lean type `{lean_ty}`")
            }
            Self::UnknownBuiltinLeanType { field, lean_ty } => write!(
                f,
                "field `{field}`: `{lean_ty}` is not a builtin Lean type with a known LCNF kind"
            ),
            Self::ReservedFieldName { name } => write!(
                f,
                "field `{name}` collides with a declaration of the split LCNF layout"
            ),
            Self::DependentFieldType { field, depends_on } => write!(
                f,
                "field `{field}`: its type mentions `{depends_on}`, which a split LCNF layout cannot scope"
            ),
            Self::IrCtorRejected { limit, footprint } => write!(
                f,
                "constructor rejected by IR/Checker ({}): {} scalar bytes, {} object fields",
                limit.lean_diagnostic(),
                footprint.scalar_bytes,
                footprint.obj_fields
            ),
            Self::MalformedPlan { reason } => write!(f, "malformed LCNF layout plan: {reason}"),
            Self::MissingFieldExpr { field } => write!(f, "no expression for field `{field}`"),
            Self::UnknownFieldExpr { field } => {
                write!(f, "expression for unknown field `{field}`")
            }
            Self::DuplicateFieldExpr { field } => {
                write!(f, "duplicate expression for field `{field}`")
            }
            Self::InvalidFieldExpr { field } => {
                write!(f, "invalid expression for field `{field}`")
            }
            Self::MirCtorOverBudget { lean_name, fields } => write!(
                f,
                "MIR module constructor `{lean_name}` with {fields} fields exceeds the LCNF budget"
            ),
        }
    }
}

impl std::error::Error for LcnfLayoutError {}

/// Per-constructor limits applied by the chunker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LcnfCtorBudget {
    max_scalar_bytes: usize,
    max_obj_fields: usize,
}

impl LcnfCtorBudget {
    /// The default budget, which every wrapper level uses.
    const DEFAULT: Self = Self {
        max_scalar_bytes: MAX_LCNF_CTOR_SCALAR_BYTES,
        max_obj_fields: MAX_LCNF_CTOR_OBJ_FIELDS,
    };

    fn checked(max_scalar_bytes: usize, max_obj_fields: usize) -> Result<Self, LcnfLayoutError> {
        if max_scalar_bytes == 0 || max_obj_fields == 0 {
            return Err(LcnfLayoutError::ZeroBudget {
                max_scalar_bytes,
                max_obj_fields,
            });
        }
        if max_scalar_bytes >= LEAN_IR_MAX_CTOR_SCALAR_BYTES
            || max_obj_fields >= LEAN_IR_MAX_CTOR_OBJ_FIELDS
        {
            return Err(LcnfLayoutError::BudgetAtLeanLimit {
                max_scalar_bytes,
                max_obj_fields,
            });
        }
        Ok(Self {
            max_scalar_bytes,
            max_obj_fields,
        })
    }

    const fn allows(self, footprint: LcnfCtorFootprint) -> bool {
        footprint.fits_budget(self.max_scalar_bytes, self.max_obj_fields)
    }
}

fn check_field_kinds(fields: &[LcnfFieldSpec]) -> Result<(), LcnfLayoutError> {
    match fields.iter().find(|field| !field.kind.is_valid()) {
        Some(field) => Err(LcnfLayoutError::InvalidScalarWidth {
            field: field.name.clone(),
            bytes: field.kind.scalar_bytes(),
        }),
        None => Ok(()),
    }
}

fn check_fields_fit(
    fields: &[LcnfFieldSpec],
    budget: LcnfCtorBudget,
) -> Result<(), LcnfLayoutError> {
    check_field_kinds(fields)?;
    match fields
        .iter()
        .find(|field| !budget.allows(LcnfCtorFootprint::default().with(field.kind)))
    {
        Some(field) => Err(LcnfLayoutError::FieldExceedsBudget {
            field: field.name.clone(),
            scalar_bytes: field.kind.scalar_bytes(),
            max_scalar_bytes: budget.max_scalar_bytes,
        }),
        None => Ok(()),
    }
}

/// Greedy, order-preserving chunking of `kinds` into contiguous ranges, each allowed by
/// `budget`. A kind starts a new range only when the current range is non-empty and adding the
/// kind would exceed a budget. Every kind must individually fit `budget`.
fn chunk_kind_ranges(kinds: &[LcnfFieldKind], budget: LcnfCtorBudget) -> Vec<Range<usize>> {
    let mut ranges = Vec::new();
    let mut start = 0;
    let mut current = LcnfCtorFootprint::default();
    for (index, &kind) in kinds.iter().enumerate() {
        let extended = current.with(kind);
        if index > start && !budget.allows(extended) {
            ranges.push(start..index);
            start = index;
            current = LcnfCtorFootprint::default().with(kind);
        } else {
            current = extended;
        }
    }
    if start < kinds.len() {
        ranges.push(start..kinds.len());
    }
    ranges
}

/// Greedy, order-preserving two-budget chunker.
///
/// Splits `fields` into consecutive parts. A field joins the current part when the part then
/// stays within `max_scalar_bytes` scalar bytes, `max_obj_fields` boxed fields, and
/// [`MAX_LCNF_CTOR_DECLARED_FIELDS`] declared fields; otherwise it starts the next part.
/// Concatenating the parts gives back `fields`.
///
/// Rejects zero budgets, budgets at or above the Lean limits, invalid scalar widths, and any
/// field that alone exceeds `max_scalar_bytes`.
pub fn chunk_lcnf_ctor_fields(
    fields: &[LcnfFieldSpec],
    max_scalar_bytes: usize,
    max_obj_fields: usize,
) -> Result<Vec<Vec<LcnfFieldSpec>>, LcnfLayoutError> {
    let budget = LcnfCtorBudget::checked(max_scalar_bytes, max_obj_fields)?;
    check_fields_fit(fields, budget)?;
    let kinds: Vec<LcnfFieldKind> = fields.iter().map(|field| field.kind).collect();
    Ok(chunk_kind_ranges(&kinds, budget)
        .into_iter()
        .map(|range| fields[range].to_vec())
        .collect())
}

/// Field kinds of a single wrapper constructor holding one field per part, each stored the way
/// Lean stores the part ([`CtorReprKind::parent_field_kind`]).
pub fn lcnf_wrapper_field_kinds(parts: &[Vec<LcnfFieldSpec>]) -> Vec<LcnfFieldKind> {
    parts
        .iter()
        .map(|part| CtorReprKind::of_fields(part).parent_field_kind())
        .collect()
}

/// One constructor of an [`LcnfCtorLayoutPlan`] level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LcnfLayoutCtor {
    /// Contiguous children: original field indices on level `0`, constructor indices of the
    /// level below on wrapper levels.
    pub children: Range<usize>,
    /// Kind of each field of this constructor, one per child.
    pub field_kinds: Vec<LcnfFieldKind>,
    /// Footprint of this constructor.
    pub footprint: LcnfCtorFootprint,
    /// How the parent wrapper stores this constructor.
    pub repr: CtorReprKind,
}

/// Multi-level constructor layout of one structure.
///
/// Level `0` holds the `Part` constructors over the original fields. Each further level holds
/// wrapper constructors with one field per constructor of the level below. The last level is
/// the root and has exactly one constructor. A plan whose only level is the root is flat: the
/// structure is emitted unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LcnfCtorLayoutPlan {
    fields: Vec<LcnfFieldSpec>,
    part_budget: LcnfCtorBudget,
    levels: Vec<Vec<LcnfLayoutCtor>>,
}

/// Name of the field through which a wrapper holds constructor `child_index` of level
/// `child_level`: `part<j>` for parts, `level<L>_part<j>` for wrappers (`j` counts from `1`).
pub fn lcnf_child_field_name(child_level: usize, child_index: usize) -> String {
    if child_level == 0 {
        format!("part{}", child_index + 1)
    } else {
        format!("level{child_level}_part{}", child_index + 1)
    }
}

/// Index of the constructor of `ctors` whose children contain `child`.
fn ctor_containing(ctors: &[LcnfLayoutCtor], child: usize) -> Option<usize> {
    let index = ctors.partition_point(|ctor| ctor.children.end <= child);
    ctors
        .get(index)
        .filter(|ctor| ctor.children.contains(&child))
        .map(|_| index)
}

impl LcnfCtorLayoutPlan {
    /// The original fields, in order.
    pub fn fields(&self) -> &[LcnfFieldSpec] {
        &self.fields
    }

    /// The levels, from the `Part` level to the root level.
    pub fn levels(&self) -> &[Vec<LcnfLayoutCtor>] {
        &self.levels
    }

    /// Number of constructors on each level (the last entry is `1`).
    pub fn ctor_counts_per_level(&self) -> Vec<usize> {
        self.levels.iter().map(Vec::len).collect()
    }

    /// True when the structure is emitted as one flat constructor.
    pub fn is_flat(&self) -> bool {
        self.levels.len() == 1
    }

    /// The root constructor.
    pub fn root(&self) -> &LcnfLayoutCtor {
        &self.levels[self.levels.len() - 1][0]
    }

    /// The `(max_scalar_bytes, max_obj_fields)` budget of the `Part` level.
    pub fn part_budget(&self) -> (usize, usize) {
        (
            self.part_budget.max_scalar_bytes,
            self.part_budget.max_obj_fields,
        )
    }

    /// The fields of each `Part` constructor.
    pub fn parts(&self) -> Vec<&[LcnfFieldSpec]> {
        self.levels[0]
            .iter()
            .map(|ctor| &self.fields[ctor.children.clone()])
            .collect()
    }

    /// Lean name of constructor `index` on `level` when the root structure is `struct_name`:
    /// `<struct_name>` for the root, `<struct_name>.Part<j>` on level `0`, and
    /// `<struct_name>.Level<L>_Part<j>` on wrapper levels (`j` counts from `1`).
    pub fn ctor_lean_name(&self, struct_name: &str, level: usize, index: usize) -> String {
        if level + 1 == self.levels.len() {
            struct_name.to_owned()
        } else if level == 0 {
            format!("{struct_name}.Part{}", index + 1)
        } else {
            format!("{struct_name}.Level{level}_Part{}", index + 1)
        }
    }

    /// Field names leading from the root to original field `field_index`, ending with the
    /// field's own name (`[name]` for a flat plan, `[part<j>, name]` for one wrapper level).
    pub fn field_projection_path(&self, field_index: usize) -> Option<Vec<String>> {
        let field = self.fields.get(field_index)?;
        let mut path = vec![field.name.clone()];
        let mut child = ctor_containing(&self.levels[0], field_index)?;
        for level in 1..self.levels.len() {
            let parent = ctor_containing(&self.levels[level], child)?;
            path.push(lcnf_child_field_name(level - 1, child));
            child = parent;
        }
        path.reverse();
        Some(path)
    }

    /// [`LcnfCtorLayoutPlan::field_projection_path`] of the field named `name`.
    pub fn field_projection_path_by_name(&self, name: &str) -> Option<Vec<String>> {
        let index = self.fields.iter().position(|field| field.name == name)?;
        self.field_projection_path(index)
    }

    /// Checks every invariant of the plan.
    ///
    /// The `Part` level partitions the fields in order and every wrapper level partitions the
    /// level below in order, so no field or constructor is lost, duplicated, or reordered.
    /// Every constructor records the kinds, footprint and representation of its children, fits
    /// its budget (the `Part` budget on level `0`, the default budget on wrapper levels) and
    /// the IR-checker limits. Each wrapper level has fewer constructors than the level below,
    /// and the root level has exactly one constructor.
    pub fn validate(&self) -> Result<(), LcnfLayoutError> {
        let malformed = |reason: String| Err(LcnfLayoutError::MalformedPlan { reason });
        let Some(root_level) = self.levels.last() else {
            return malformed(String::from("no levels"));
        };
        if root_level.len() != 1 {
            return malformed(format!("root level has {} constructors", root_level.len()));
        }
        for (level, ctors) in self.levels.iter().enumerate() {
            let (expected_children, budget) = if level == 0 {
                (self.fields.len(), self.part_budget)
            } else {
                (self.levels[level - 1].len(), LcnfCtorBudget::DEFAULT)
            };
            if level > 0 && ctors.len() >= expected_children {
                return malformed(format!(
                    "level {level} has {} constructors over {expected_children}",
                    ctors.len()
                ));
            }
            let mut next = 0;
            for (index, ctor) in ctors.iter().enumerate() {
                let children = ctor.children.clone();
                if children.start != next || children.end < children.start {
                    return malformed(format!(
                        "level {level} constructor {index} is not contiguous"
                    ));
                }
                let empty_root = level == 0 && self.fields.is_empty() && ctors.len() == 1;
                if children.is_empty() && !empty_root {
                    return malformed(format!("level {level} constructor {index} is empty"));
                }
                next = children.end;
                if next > expected_children {
                    return malformed(format!("level {level} constructor {index} is out of range"));
                }
                let expected_kinds: Vec<LcnfFieldKind> = if level == 0 {
                    self.fields[children]
                        .iter()
                        .map(|field| field.kind)
                        .collect()
                } else {
                    self.levels[level - 1][children]
                        .iter()
                        .map(|child| child.repr.parent_field_kind())
                        .collect()
                };
                if ctor.field_kinds != expected_kinds
                    || ctor.footprint != LcnfCtorFootprint::of_kinds(expected_kinds.iter().copied())
                    || ctor.repr != CtorReprKind::of_kinds(&expected_kinds)
                {
                    return malformed(format!(
                        "level {level} constructor {index} does not match its children"
                    ));
                }
                if let Some(limit) = ctor.footprint.ir_violation() {
                    return Err(LcnfLayoutError::IrCtorRejected {
                        limit,
                        footprint: ctor.footprint,
                    });
                }
                if !budget.allows(ctor.footprint) {
                    return malformed(format!(
                        "level {level} constructor {index} exceeds its budget: {:?}",
                        ctor.footprint
                    ));
                }
            }
            if next != expected_children {
                return malformed(format!(
                    "level {level} covers {next} of {expected_children} children"
                ));
            }
        }
        Ok(())
    }
}

fn build_layout_level(kinds: &[LcnfFieldKind], ranges: Vec<Range<usize>>) -> Vec<LcnfLayoutCtor> {
    ranges
        .into_iter()
        .map(|children| {
            let field_kinds = kinds[children.clone()].to_vec();
            LcnfLayoutCtor {
                footprint: LcnfCtorFootprint::of_kinds(field_kinds.iter().copied()),
                repr: CtorReprKind::of_kinds(&field_kinds),
                field_kinds,
                children,
            }
        })
        .collect()
}

/// Plans the multi-level constructor layout of a structure with `fields`.
///
/// Level `0` is [`chunk_lcnf_ctor_fields`] under `max_scalar_bytes` / `max_obj_fields` (the
/// guard passes [`MAX_LCNF_CTOR_SCALAR_BYTES`] / [`MAX_LCNF_CTOR_OBJ_FIELDS`]). While a level
/// has more than one constructor, the next level re-chunks one wrapper field per constructor,
/// stored as Lean stores it ([`CtorReprKind::parent_field_kind`]: an unboxed scalar for a part
/// with one relevant scalar field, otherwise a boxed field), under the default budgets. Any two
/// wrapper fields fit one constructor, so every wrapper level shrinks and the plan ends at
/// exactly one root constructor; an empty field list yields one empty root constructor. The
/// plan is checked with [`LcnfCtorLayoutPlan::validate`] before it is returned.
pub fn plan_lcnf_ctor_layout_levels(
    fields: &[LcnfFieldSpec],
    max_scalar_bytes: usize,
    max_obj_fields: usize,
) -> Result<LcnfCtorLayoutPlan, LcnfLayoutError> {
    let part_budget = LcnfCtorBudget::checked(max_scalar_bytes, max_obj_fields)?;
    check_field_specs(fields)?;
    check_fields_fit(fields, part_budget)?;
    let kinds: Vec<LcnfFieldKind> = fields.iter().map(|field| field.kind).collect();
    let part_ranges = if kinds.is_empty() {
        vec![Range::default()]
    } else {
        chunk_kind_ranges(&kinds, part_budget)
    };
    let mut levels = vec![build_layout_level(&kinds, part_ranges)];
    // Each wrapper level shrinks, so `levels[0].len()` wrapper levels always suffice.
    let mut fuel = levels[0].len();
    while levels[levels.len() - 1].len() > 1 {
        let below = &levels[levels.len() - 1];
        let child_kinds: Vec<LcnfFieldKind> = below
            .iter()
            .map(|ctor| ctor.repr.parent_field_kind())
            .collect();
        let ranges = chunk_kind_ranges(&child_kinds, LcnfCtorBudget::DEFAULT);
        if fuel == 0 || ranges.len() >= below.len() {
            return Err(LcnfLayoutError::MalformedPlan {
                reason: format!(
                    "wrapper level {} does not shrink ({} -> {} constructors)",
                    levels.len(),
                    below.len(),
                    ranges.len()
                ),
            });
        }
        fuel -= 1;
        levels.push(build_layout_level(&child_kinds, ranges));
    }
    let plan = LcnfCtorLayoutPlan {
        fields: fields.to_vec(),
        part_budget,
        levels,
    };
    plan.validate()?;
    Ok(plan)
}

/// Lean keywords rejected as structure, field, and `deriving` name components
/// (whitespace-separated).
const LEAN_RESERVED_WORDS: &str = concat!(
    "Prop Sort Type abbrev at attribute axiom break by calc catch class continue ",
    "decreasing_by def deriving do elab else end example export extends finally for forall ",
    "from fun have hiding if import in include inductive infix infixl infixr instance let ",
    "local macro match meta mut mutual namespace noncomputable nofun nomatch notation omit ",
    "opaque open partial postfix prefix private protected public renaming return scoped ",
    "section set_option show structure suffices syntax termination_by then theorem this try ",
    "universe unless unsafe using variable where with ",
);

/// Declarations Lean generates in a structure's namespace, which an accessor of a split layout
/// must not shadow (whitespace-separated).
const LEAN_STRUCTURE_AUX_NAMES: &str = concat!(
    "below binductionOn brecOn casesOn ctorIdx ext ext_iff ibelow mk noConfusion ",
    "noConfusionType rec recOn toCtorIdx ",
);

/// True for an ASCII Lean identifier component that is not a keyword: `[A-Za-z_][A-Za-z0-9_']*`
/// other than `_`.
fn is_lean_ident_component(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
        && name != "_"
        && !LEAN_RESERVED_WORDS
            .split_whitespace()
            .any(|word| word == name)
}

/// True for a dot-separated sequence of [`is_lean_ident_component`] components.
fn is_lean_decl_name(name: &str) -> bool {
    name.split('.').all(is_lean_ident_component)
}

/// ASCII identifier atoms of a Lean type: maximal runs of `[A-Za-z0-9_']`. Every reference to a
/// field named by an ASCII identifier appears as one of these atoms.
fn lean_ident_atoms(lean_ty: &str) -> impl Iterator<Item = &str> {
    lean_ty
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '\''))
        .filter(|atom| !atom.is_empty())
}

fn check_lean_ty(field: &str, lean_ty: &str) -> Result<(), LcnfLayoutError> {
    let ty = lean_ty.trim();
    if ty.is_empty()
        || ty.chars().any(char::is_control)
        || ty.contains("--")
        || ty.contains("/-")
        || ty.contains(":=")
    {
        return Err(LcnfLayoutError::InvalidLeanType {
            field: field.to_owned(),
            lean_ty: lean_ty.to_owned(),
        });
    }
    Ok(())
}

fn check_field_specs(fields: &[LcnfFieldSpec]) -> Result<(), LcnfLayoutError> {
    let mut seen = HashSet::with_capacity(fields.len());
    for field in fields {
        if !is_lean_ident_component(&field.name) {
            return Err(LcnfLayoutError::InvalidLeanName {
                what: "field",
                name: field.name.clone(),
            });
        }
        if !seen.insert(field.name.as_str()) {
            return Err(LcnfLayoutError::DuplicateFieldName {
                name: field.name.clone(),
            });
        }
        check_lean_ty(&field.name, &field.lean_ty)?;
    }
    Ok(())
}

/// Checks the structure name, the `deriving` entries and the plan, and, for a split layout,
/// that no field name collides with a generated declaration and no field type depends on a
/// field, on the structure itself, or on the accessor binder `self`.
fn check_lcnf_emission(
    struct_name: &str,
    plan: &LcnfCtorLayoutPlan,
    derives: &[&str],
) -> Result<(), LcnfLayoutError> {
    if !is_lean_decl_name(struct_name) {
        return Err(LcnfLayoutError::InvalidLeanName {
            what: "structure",
            name: struct_name.to_owned(),
        });
    }
    let mut seen_derives = HashSet::with_capacity(derives.len());
    for &derive in derives {
        if !is_lean_decl_name(derive) {
            return Err(LcnfLayoutError::InvalidLeanName {
                what: "deriving",
                name: derive.to_owned(),
            });
        }
        if !seen_derives.insert(derive) {
            return Err(LcnfLayoutError::DuplicateDerive {
                name: derive.to_owned(),
            });
        }
    }
    check_field_specs(&plan.fields)?;
    plan.validate()?;
    if plan.is_flat() {
        return Ok(());
    }
    let top = plan.levels.len() - 1;
    let mut reserved: HashSet<String> = LEAN_STRUCTURE_AUX_NAMES
        .split_whitespace()
        .map(str::to_owned)
        .collect();
    for (level, ctors) in plan.levels[..top].iter().enumerate() {
        for index in 0..ctors.len() {
            reserved.insert(if level == 0 {
                format!("Part{}", index + 1)
            } else {
                format!("Level{level}_Part{}", index + 1)
            });
        }
    }
    for child in plan.root().children.clone() {
        reserved.insert(lcnf_child_field_name(top - 1, child));
    }
    let struct_leaf = struct_name.rsplit('.').next().unwrap_or(struct_name);
    let field_names: HashSet<&str> = plan
        .fields
        .iter()
        .map(|field| field.name.as_str())
        .collect();
    for field in &plan.fields {
        if reserved.contains(&field.name) {
            return Err(LcnfLayoutError::ReservedFieldName {
                name: field.name.clone(),
            });
        }
        if let Some(atom) = lean_ident_atoms(&field.lean_ty)
            .find(|&atom| atom == "self" || atom == struct_leaf || field_names.contains(atom))
        {
            return Err(LcnfLayoutError::DependentFieldType {
                field: field.name.clone(),
                depends_on: atom.to_owned(),
            });
        }
    }
    Ok(())
}

/// Renders the Lean declarations of `plan` for a structure named `struct_name`.
///
/// A flat plan renders the conventional `structure <struct_name> where` with one line per field
/// and an optional `deriving` line, exactly as without the guard. A split plan renders, in
/// dependency order, one `structure <struct_name>.Part<j>` per part, one
/// `structure <struct_name>.Level<L>_Part<j>` per intermediate wrapper, the root
/// `structure <struct_name>` (each with the same `deriving` line), and then one
/// `abbrev <struct_name>.<field> (self : <struct_name>) : <type> := self.<path>` accessor per
/// original field, so `s.<field>` keeps working and reads exactly the original field.
pub fn render_lcnf_guarded_structure(
    struct_name: &str,
    plan: &LcnfCtorLayoutPlan,
    derives: &[&str],
) -> Result<String, LcnfLayoutError> {
    check_lcnf_emission(struct_name, plan, derives)?;
    let deriving = if derives.is_empty() {
        String::new()
    } else {
        format!("  deriving {}\n", derives.join(", "))
    };
    let mut out = String::new();
    for (level, ctors) in plan.levels.iter().enumerate() {
        for (index, ctor) in ctors.iter().enumerate() {
            if !out.is_empty() {
                out.push('\n');
            }
            out.push_str(&format!(
                "structure {} where\n",
                plan.ctor_lean_name(struct_name, level, index)
            ));
            for child in ctor.children.clone() {
                if level == 0 {
                    let field = &plan.fields[child];
                    out.push_str(&format!("  {} : {}\n", field.name, field.lean_ty.trim()));
                } else {
                    out.push_str(&format!(
                        "  {} : {}\n",
                        lcnf_child_field_name(level - 1, child),
                        plan.ctor_lean_name(struct_name, level - 1, child)
                    ));
                }
            }
            out.push_str(&deriving);
        }
    }
    if !plan.is_flat() {
        out.push('\n');
        for (index, field) in plan.fields.iter().enumerate() {
            let path = plan.field_projection_path(index).ok_or_else(|| {
                LcnfLayoutError::MalformedPlan {
                    reason: format!("no projection path for field `{}`", field.name),
                }
            })?;
            out.push_str(&format!(
                "abbrev {struct_name}.{} (self : {struct_name}) : {} := self.{}\n",
                field.name,
                field.lean_ty.trim(),
                path.join(".")
            ));
        }
    }
    Ok(out)
}

/// Emits the Lean declarations of a structure named `struct_name` with `fields`, deriving
/// `derives`, under the default guard budgets.
///
/// When the fields fit one constructor within [`MAX_LCNF_CTOR_SCALAR_BYTES`],
/// [`MAX_LCNF_CTOR_OBJ_FIELDS`] and [`MAX_LCNF_CTOR_DECLARED_FIELDS`], the output is the flat
/// structure, unchanged. Otherwise it is the `Part` / `Level` layout of
/// [`plan_lcnf_ctor_layout_levels`] with accessors ([`render_lcnf_guarded_structure`]); every
/// emitted constructor then fits the budgets. The `deriving` line is repeated on every emitted
/// structure: Lean `v4.34.1` derives `Inhabited`, `Repr`, `BEq` and `Hashable` for structures at
/// the budget, but its `DecidableEq` handler already fails ("maximum recursion depth has been
/// reached") on a flat `128`-field structure.
pub fn emit_lcnf_guarded_structure(
    struct_name: &str,
    fields: &[LcnfFieldSpec],
    derives: &[&str],
) -> Result<String, LcnfLayoutError> {
    let plan =
        plan_lcnf_ctor_layout_levels(fields, MAX_LCNF_CTOR_SCALAR_BYTES, MAX_LCNF_CTOR_OBJ_FIELDS)?;
    render_lcnf_guarded_structure(struct_name, &plan, derives)
}

fn render_lcnf_ctor_expr_at(
    struct_name: &str,
    plan: &LcnfCtorLayoutPlan,
    exprs: &[&str],
    level: usize,
    index: usize,
) -> String {
    let ctor = &plan.levels[level][index];
    let items: Vec<String> = ctor
        .children
        .clone()
        .map(|child| {
            if level == 0 {
                format!("{} := ({})", plan.fields[child].name, exprs[child])
            } else {
                format!(
                    "{} := {}",
                    lcnf_child_field_name(level - 1, child),
                    render_lcnf_ctor_expr_at(struct_name, plan, exprs, level - 1, child)
                )
            }
        })
        .collect();
    let body = if items.is_empty() {
        String::from("{ }")
    } else {
        format!("{{ {} }}", items.join(", "))
    };
    format!(
        "({body} : {})",
        plan.ctor_lean_name(struct_name, level, index)
    )
}

/// Renders a Lean term of type `struct_name` built from one expression per field.
///
/// `field_exprs` pairs every field name of `plan` with a Lean expression, in any order. The term
/// is a type-ascribed structure instance per constructor:
/// `({ f := (e), ... } : <struct_name>)` for a flat plan and nested
/// `({ part1 := ({ f := (e), ... } : <struct_name>.Part1), ... } : <struct_name>)` for a split
/// plan, so projecting any field through its accessor returns its expression.
pub fn render_lcnf_guarded_ctor_expr(
    struct_name: &str,
    field_exprs: &[(&str, &str)],
    plan: &LcnfCtorLayoutPlan,
) -> Result<String, LcnfLayoutError> {
    if !is_lean_decl_name(struct_name) {
        return Err(LcnfLayoutError::InvalidLeanName {
            what: "structure",
            name: struct_name.to_owned(),
        });
    }
    plan.validate()?;
    let index_of: HashMap<&str, usize> = plan
        .fields
        .iter()
        .enumerate()
        .map(|(index, field)| (field.name.as_str(), index))
        .collect();
    let mut exprs: Vec<Option<&str>> = vec![None; plan.fields.len()];
    for &(name, expr) in field_exprs {
        let Some(&index) = index_of.get(name) else {
            return Err(LcnfLayoutError::UnknownFieldExpr {
                field: name.to_owned(),
            });
        };
        if exprs[index].is_some() {
            return Err(LcnfLayoutError::DuplicateFieldExpr {
                field: name.to_owned(),
            });
        }
        if expr.trim().is_empty() || expr.chars().any(char::is_control) {
            return Err(LcnfLayoutError::InvalidFieldExpr {
                field: name.to_owned(),
            });
        }
        exprs[index] = Some(expr.trim());
    }
    let mut complete = Vec::with_capacity(exprs.len());
    for (index, expr) in exprs.into_iter().enumerate() {
        match expr {
            Some(expr) => complete.push(expr),
            None => {
                return Err(LcnfLayoutError::MissingFieldExpr {
                    field: plan.fields[index].name.clone(),
                });
            }
        }
    }
    Ok(render_lcnf_ctor_expr_at(
        struct_name,
        plan,
        &complete,
        plan.levels.len() - 1,
        0,
    ))
}

/// A Lean constructor that [`emit_mir_lean_module`] may render, with its number of explicit
/// fields (defaulted structure fields included).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MirModuleCtorArity {
    /// Structure or constructor name: `Layout.*` and `MirAst.*` under
    /// `Trusted.Rustc.V2026_06_01`, `VerificationResult.Claim` under `Trusted`, or a prelude
    /// constructor.
    pub lean_name: &'static str,
    /// Number of explicit fields.
    pub fields: usize,
}

const fn mir_ctor(lean_name: &'static str, fields: usize) -> MirModuleCtorArity {
    MirModuleCtorArity { lean_name, fields }
}

/// Every structure and every constructor with fields declared in
/// `trusted/lean/Trusted/Rustc/V2026_06_01/{Layout.lean,MirAst/*.lean}`, plus
/// `VerificationResult.Claim` and the prelude constructors `List.cons`, `Option.some`, and
/// `Prod.mk`: a superset of the constructors [`emit_mir_lean_module`] renders.
///
/// `lcnf_tests::mir_module_ctor_arities_match_trusted_lean_sources` re-derives the trusted
/// entries from the Lean sources.
pub const MIR_MODULE_CTOR_ARITIES: &[MirModuleCtorArity] = &[
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
    mir_ctor("Layout.TypeLayout", 7),
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

/// True when every constructor of `arities` fits the LCNF budgets even if each field takes the
/// worst case: [`MAX_LCNF_SCALAR_FIELD_BYTES`] scalar bytes and one boxed field.
const fn mir_module_ctor_arities_fit(arities: &[MirModuleCtorArity]) -> bool {
    let mut index = 0;
    while index < arities.len() {
        let fields = arities[index].fields;
        if fields > MAX_LCNF_CTOR_OBJ_FIELDS
            || fields > MAX_LCNF_CTOR_DECLARED_FIELDS
            || fields.saturating_mul(MAX_LCNF_SCALAR_FIELD_BYTES) > MAX_LCNF_CTOR_SCALAR_BYTES
        {
            return false;
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

/// Checks that every constructor of `arities` fits the LCNF budgets with worst-case fields and
/// returns the worst-case footprint of the widest one.
pub fn validate_mir_module_ctor_arities(
    arities: &[MirModuleCtorArity],
) -> Result<LcnfCtorFootprint, LcnfLayoutError> {
    let mut widest = LcnfCtorFootprint::default();
    for arity in arities {
        let footprint = LcnfCtorFootprint {
            scalar_bytes: arity.fields.saturating_mul(MAX_LCNF_SCALAR_FIELD_BYTES),
            obj_fields: arity.fields,
            declared_fields: arity.fields,
        };
        if !footprint.fits_budget(MAX_LCNF_CTOR_SCALAR_BYTES, MAX_LCNF_CTOR_OBJ_FIELDS) {
            return Err(LcnfLayoutError::MirCtorOverBudget {
                lean_name: arity.lean_name,
                fields: arity.fields,
            });
        }
        if footprint.declared_fields > widest.declared_fields {
            widest = footprint;
        }
    }
    Ok(widest)
}

/// [`emit_mir_lean_module`] after the pre-emission LCNF check.
///
/// `emit_mir_lean_module` renders lists (locals, blocks, statements, operands, layouts,
/// allocation bytes) as `List.cons` chains and every other value with a fixed constructor of
/// [`MIR_MODULE_CTOR_ARITIES`], so no constructor grows with the size of `mir`. This function
/// re-checks that table ([`validate_mir_module_ctor_arities`], also asserted at compile time)
/// and returns exactly the text of `emit_mir_lean_module`.
pub fn try_emit_mir_lean_module(
    lean_module_namespace: &str,
    mir: &IrCapturedMir,
) -> Result<String, LcnfLayoutError> {
    validate_mir_module_ctor_arities(MIR_MODULE_CTOR_ARITIES)?;
    Ok(emit_mir_lean_module(lean_module_namespace, mir))
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
mod lcnf_tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};
    use std::fs::File;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    use LcnfFieldKind::{Irrelevant, ObjectRef};

    const BOOL: LcnfFieldKind = LcnfFieldKind::Scalar { bytes: 1 };
    const U64: LcnfFieldKind = LcnfFieldKind::Scalar { bytes: 8 };

    fn uniform(
        count: usize,
        prefix: &str,
        lean_ty: &str,
        kind: LcnfFieldKind,
    ) -> Vec<LcnfFieldSpec> {
        (0..count)
            .map(|index| LcnfFieldSpec::new(format!("{prefix}{index}"), lean_ty, kind))
            .collect()
    }

    fn u64s(count: usize) -> Vec<LcnfFieldSpec> {
        uniform(count, "f", "UInt64", U64)
    }

    fn nats(count: usize) -> Vec<LcnfFieldSpec> {
        uniform(count, "f", "Nat", ObjectRef)
    }

    fn part_scalar_bytes(parts: &[Vec<LcnfFieldSpec>]) -> Vec<usize> {
        parts
            .iter()
            .map(|part| LcnfCtorFootprint::of_fields(part).scalar_bytes)
            .collect()
    }

    fn part_obj_fields(parts: &[Vec<LcnfFieldSpec>]) -> Vec<usize> {
        parts
            .iter()
            .map(|part| LcnfCtorFootprint::of_fields(part).obj_fields)
            .collect()
    }

    fn default_plan(fields: &[LcnfFieldSpec]) -> LcnfCtorLayoutPlan {
        plan_lcnf_ctor_layout_levels(fields, MAX_LCNF_CTOR_SCALAR_BYTES, MAX_LCNF_CTOR_OBJ_FIELDS)
            .expect("default LCNF plan")
    }

    fn level_scalar_bytes(plan: &LcnfCtorLayoutPlan, level: usize) -> Vec<usize> {
        plan.levels()[level]
            .iter()
            .map(|ctor| ctor.footprint.scalar_bytes)
            .collect()
    }

    fn level_obj_fields(plan: &LcnfCtorLayoutPlan, level: usize) -> Vec<usize> {
        plan.levels()[level]
            .iter()
            .map(|ctor| ctor.footprint.obj_fields)
            .collect()
    }

    /// Follows `path` from the root of `plan` and returns the original field index it reaches.
    fn resolve_projection(plan: &LcnfCtorLayoutPlan, path: &[String]) -> Option<usize> {
        let (field_name, wrapper_fields) = path.split_last()?;
        let mut level = plan.levels().len() - 1;
        let mut index = 0;
        for name in wrapper_fields {
            if level == 0 {
                return None;
            }
            let ctor = &plan.levels()[level][index];
            index = ctor
                .children
                .clone()
                .find(|&child| lcnf_child_field_name(level - 1, child) == *name)?;
            level -= 1;
        }
        if level != 0 {
            return None;
        }
        plan.levels()[0][index]
            .children
            .clone()
            .find(|&field| plan.fields()[field].name == *field_name)
    }

    /// Checks that `plan` loses, duplicates, and reorders nothing, and that every field's
    /// projection path reads exactly that field.
    fn assert_lossless(plan: &LcnfCtorLayoutPlan) {
        plan.validate().expect("valid plan");
        assert_eq!(plan.parts().concat(), plan.fields());
        for level in 1..plan.levels().len() {
            let covered: Vec<usize> = plan.levels()[level]
                .iter()
                .flat_map(|ctor| ctor.children.clone())
                .collect();
            let below: Vec<usize> = (0..plan.levels()[level - 1].len()).collect();
            assert_eq!(
                covered, below,
                "level {level} does not wrap the level below losslessly"
            );
        }
        assert_eq!(plan.ctor_counts_per_level().last(), Some(&1));
        for (index, field) in plan.fields().iter().enumerate() {
            let path = plan.field_projection_path(index).expect("projection path");
            assert_eq!(path.len(), plan.levels().len());
            assert_eq!(path.last(), Some(&field.name));
            assert_eq!(
                resolve_projection(plan, &path),
                Some(index),
                "path {path:?}"
            );
            assert_eq!(plan.field_projection_path_by_name(&field.name), Some(path));
        }
        assert_eq!(plan.field_projection_path(plan.fields().len()), None);
    }

    #[test]
    fn lcnf_field_kind_accounting() {
        assert_eq!(
            (U64.scalar_bytes(), U64.obj_fields(), U64.is_relevant()),
            (8, 0, true)
        );
        assert_eq!(
            (
                ObjectRef.scalar_bytes(),
                ObjectRef.obj_fields(),
                ObjectRef.is_relevant()
            ),
            (0, 1, true)
        );
        assert_eq!(
            (
                Irrelevant.scalar_bytes(),
                Irrelevant.obj_fields(),
                Irrelevant.is_relevant()
            ),
            (0, 0, false)
        );
        for bytes in [1, 2, 4, 8] {
            assert!(LcnfFieldKind::Scalar { bytes }.is_valid());
        }
        for bytes in [0, 3, 16] {
            assert!(!LcnfFieldKind::Scalar { bytes }.is_valid());
        }
        assert_eq!(
            LcnfCtorFootprint::of_kinds([U64, ObjectRef, Irrelevant, BOOL]),
            LcnfCtorFootprint {
                scalar_bytes: 9,
                obj_fields: 1,
                declared_fields: 4
            }
        );
        assert_eq!(IrCtorLimit::Fields.lean_diagnostic(), "has too many fields");
        assert_eq!(
            IrCtorLimit::Scalar.lean_diagnostic(),
            "has too many scalar fields"
        );
    }

    /// Every type [`LcnfFieldKind::of_builtin_lean_ty`] classifies; each one is probed against
    /// Lean by [`lcnf_live_lean_builtin_kinds_match_model`].
    const BUILTIN_LEAN_TYPES: &[&str] = &[
        "Bool", "UInt8", "Int8", "UInt16", "Int16", "UInt32", "Int32", "Char", "Float32", "UInt64",
        "Int64", "USize", "ISize", "Float", "Nat", "Int", "String", "Unit", "True", "Prop", "Type",
    ];

    #[test]
    fn builtin_lean_types_have_their_lean_kinds() {
        let scalar = |bytes| Some(LcnfFieldKind::Scalar { bytes });
        let expected = [
            ("Bool", scalar(1)),
            ("UInt8", scalar(1)),
            ("Int8", scalar(1)),
            ("UInt16", scalar(2)),
            ("Int16", scalar(2)),
            ("UInt32", scalar(4)),
            ("Int32", scalar(4)),
            ("Char", scalar(4)),
            ("Float32", scalar(4)),
            ("UInt64", scalar(8)),
            ("Int64", scalar(8)),
            ("USize", scalar(8)),
            ("ISize", scalar(8)),
            ("Float", scalar(8)),
            ("Nat", Some(ObjectRef)),
            ("Int", Some(ObjectRef)),
            ("String", Some(ObjectRef)),
            ("Unit", Some(ObjectRef)),
            ("True", Some(Irrelevant)),
            ("Prop", Some(Irrelevant)),
            ("Type", Some(Irrelevant)),
            (" UInt64 ", scalar(8)),
            ("List Nat", None),
            ("Fin 3", None),
            ("UInt128", None),
            ("Point", None),
        ];
        for (lean_ty, kind) in expected {
            assert_eq!(
                LcnfFieldKind::of_builtin_lean_ty(lean_ty),
                kind,
                "`{lean_ty}`"
            );
        }
        assert!(
            BUILTIN_LEAN_TYPES
                .iter()
                .all(|ty| LcnfFieldKind::of_builtin_lean_ty(ty).is_some())
        );
        assert_eq!(
            LcnfFieldSpec::builtin("c", "Char").map(|f| f.kind),
            Ok(LcnfFieldKind::Scalar { bytes: 4 })
        );
        assert!(matches!(
            LcnfFieldSpec::builtin("x", "Fin 3"),
            Err(LcnfLayoutError::UnknownBuiltinLeanType { .. })
        ));
    }

    #[test]
    fn ctor_repr_models_trivial_structure_unboxing() {
        assert_eq!(
            CtorReprKind::of_kinds(&[U64]),
            CtorReprKind::UnboxedScalar { bytes: 8 }
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[Irrelevant, BOOL, Irrelevant]),
            CtorReprKind::UnboxedScalar { bytes: 1 }
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[ObjectRef]),
            CtorReprKind::BoxedObject
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[Irrelevant, ObjectRef]),
            CtorReprKind::BoxedObject
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[BOOL, BOOL]),
            CtorReprKind::BoxedObject
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[U64, Irrelevant, ObjectRef]),
            CtorReprKind::BoxedObject
        );
        assert_eq!(
            CtorReprKind::of_kinds(&[Irrelevant, Irrelevant]),
            CtorReprKind::Erased
        );
        assert_eq!(CtorReprKind::of_kinds(&[]), CtorReprKind::Erased);
        assert_eq!(
            CtorReprKind::UnboxedScalar { bytes: 8 }.parent_field_kind(),
            U64
        );
        assert_eq!(CtorReprKind::BoxedObject.parent_field_kind(), ObjectRef);
        assert_eq!(CtorReprKind::Erased.parent_field_kind(), ObjectRef);
        assert_eq!(
            CtorReprKind::of_fields(&u64s(1)),
            CtorReprKind::UnboxedScalar { bytes: 8 }
        );
    }

    // The 11 boundary cases of `PROTOTYPE_REPORT.md` §4.3 (Lean `v4.34.1` verdicts reproduced by
    // `lcnf_live_lean_probe_matches_model`).

    #[test]
    fn boundary_01_flat_130_uint64_1040b_rejected_scalar() {
        let fields = u64s(130);
        let footprint = LcnfCtorFootprint::of_fields(&fields);
        assert_eq!((footprint.scalar_bytes, footprint.obj_fields), (1040, 0));
        assert_eq!(ir_ctor_violation(&fields), Some(IrCtorLimit::Scalar));
        assert!(matches!(
            check_ir_ctor_accepted(&fields),
            Err(LcnfLayoutError::IrCtorRejected {
                limit: IrCtorLimit::Scalar,
                ..
            })
        ));
    }

    #[test]
    fn boundary_02_split_130_uint64_960b_parts_accepted() {
        let fields = u64s(130);
        let parts = chunk_lcnf_ctor_fields(&fields, 960, 240).unwrap();
        assert_eq!(part_scalar_bytes(&parts), [960, 80]);
        assert_eq!(part_obj_fields(&parts), [0, 0]);
        assert!(parts.iter().all(|part| ir_ctor_violation(part).is_none()));
        let wrapper = LcnfCtorFootprint::of_kinds(lcnf_wrapper_field_kinds(&parts));
        assert_eq!((wrapper.scalar_bytes, wrapper.obj_fields), (0, 2));
        assert!(wrapper.is_ir_accepted());
        assert_eq!(parts.concat(), fields);
        let plan = default_plan(&fields);
        assert_eq!(plan.ctor_counts_per_level(), [2, 1]);
        assert_eq!(level_scalar_bytes(&plan, 0), [960, 80]);
        assert_eq!(
            (level_scalar_bytes(&plan, 1), level_obj_fields(&plan, 1)),
            (vec![0], vec![2])
        );
        assert_lossless(&plan);
    }

    #[test]
    fn boundary_03_flat_128_uint64_1024b_accepted_by_ir_but_split_by_guard() {
        let fields = u64s(128);
        assert_eq!(LcnfCtorFootprint::of_fields(&fields).scalar_bytes, 1024);
        assert_eq!(ir_ctor_violation(&fields), None);
        assert_eq!(
            check_ir_ctor_accepted(&fields).map(|f| f.scalar_bytes),
            Ok(1024)
        );
        // The guard keeps a 64-byte margin: 1024 B is over its 960 B budget.
        let plan = default_plan(&fields);
        assert_eq!(level_scalar_bytes(&plan, 0), [960, 64]);
    }

    #[test]
    fn boundary_04_flat_129_uint64_1032b_rejected_scalar() {
        let fields = u64s(129);
        assert_eq!(LcnfCtorFootprint::of_fields(&fields).scalar_bytes, 1032);
        assert_eq!(ir_ctor_violation(&fields), Some(IrCtorLimit::Scalar));
    }

    #[test]
    fn boundary_05_flat_256_nat_accepted() {
        let fields = nats(256);
        let footprint = LcnfCtorFootprint::of_fields(&fields);
        assert_eq!((footprint.scalar_bytes, footprint.obj_fields), (0, 256));
        assert_eq!(ir_ctor_violation(&fields), None);
    }

    #[test]
    fn boundary_06_flat_257_nat_rejected_fields() {
        assert_eq!(ir_ctor_violation(&nats(257)), Some(IrCtorLimit::Fields));
    }

    #[test]
    fn boundary_07_flat_300_nat_rejected_fields_with_zero_scalar_bytes() {
        let fields = nats(300);
        assert_eq!(LcnfCtorFootprint::of_fields(&fields).scalar_bytes, 0);
        assert_eq!(ir_ctor_violation(&fields), Some(IrCtorLimit::Fields));
    }

    #[test]
    fn boundary_08_split_300_nat_240_objects_accepted() {
        let fields = nats(300);
        let parts = chunk_lcnf_ctor_fields(&fields, 960, 240).unwrap();
        assert_eq!(part_obj_fields(&parts), [240, 60]);
        assert_eq!(part_scalar_bytes(&parts), [0, 0]);
        let wrapper = LcnfCtorFootprint::of_kinds(lcnf_wrapper_field_kinds(&parts));
        assert_eq!((wrapper.scalar_bytes, wrapper.obj_fields), (0, 2));
        let plan = default_plan(&fields);
        assert_eq!(plan.ctor_counts_per_level(), [2, 1]);
        assert_lossless(&plan);
    }

    #[test]
    fn boundary_09_split_121_uint64_singleton_tail_is_unboxed_in_wrapper() {
        let fields = u64s(121);
        let parts = chunk_lcnf_ctor_fields(&fields, 960, 240).unwrap();
        assert_eq!(part_scalar_bytes(&parts), [960, 8]);
        assert_eq!(
            CtorReprKind::of_fields(&parts[0]),
            CtorReprKind::BoxedObject
        );
        assert_eq!(
            CtorReprKind::of_fields(&parts[1]),
            CtorReprKind::UnboxedScalar { bytes: 8 }
        );
        let wrapper = LcnfCtorFootprint::of_kinds(lcnf_wrapper_field_kinds(&parts));
        assert_eq!((wrapper.scalar_bytes, wrapper.obj_fields), (8, 1));
        assert!(wrapper.is_ir_accepted());
        let plan = default_plan(&fields);
        assert_eq!(plan.root().field_kinds, [ObjectRef, U64]);
        assert_lossless(&plan);
    }

    #[test]
    fn boundary_10_one_wrapper_over_300_single_uint64_parts_rejected_scalar() {
        let parts = chunk_lcnf_ctor_fields(&u64s(300), 8, 240).unwrap();
        assert_eq!(parts.len(), 300);
        assert!(parts.iter().all(|part| ir_ctor_violation(part).is_none()));
        let wrapper_kinds = lcnf_wrapper_field_kinds(&parts);
        let wrapper = LcnfCtorFootprint::of_kinds(wrapper_kinds.iter().copied());
        assert_eq!((wrapper.scalar_bytes, wrapper.obj_fields), (2400, 0));
        // Lean reports the scalar limit; a one-pointer-per-part model would blame the fields.
        assert_eq!(wrapper.ir_violation(), Some(IrCtorLimit::Scalar));
        let pointer_only = LcnfCtorFootprint::of_kinds(wrapper_kinds.iter().map(|_| ObjectRef));
        assert_eq!(pointer_only.ir_violation(), Some(IrCtorLimit::Fields));
    }

    #[test]
    fn boundary_11_layout_300_single_uint64_parts_levels_300_3_1() {
        let fields = u64s(300);
        let plan = plan_lcnf_ctor_layout_levels(&fields, 8, 240).unwrap();
        assert_eq!(plan.part_budget(), (8, 240));
        assert_eq!(plan.ctor_counts_per_level(), [300, 3, 1]);
        assert_eq!(level_scalar_bytes(&plan, 0), vec![8; 300]);
        assert_eq!(level_scalar_bytes(&plan, 1), [960, 960, 480]);
        assert_eq!(level_obj_fields(&plan, 1), [0, 0, 0]);
        assert_eq!(
            (level_scalar_bytes(&plan, 2), level_obj_fields(&plan, 2)),
            (vec![0], vec![3])
        );
        assert!(
            plan.levels()
                .iter()
                .flatten()
                .all(|ctor| ctor.footprint.is_ir_accepted())
        );
        assert_lossless(&plan);
    }

    #[test]
    fn erased_prop_fields_cost_no_scalar_bytes_and_no_objects() {
        let mut fields = Vec::new();
        for index in 0..130 {
            fields.push(LcnfFieldSpec::new(format!("x{index}"), "UInt64", U64));
            if index < 100 {
                fields.push(LcnfFieldSpec::new(
                    format!("h{index}"),
                    "x0 = x0",
                    Irrelevant,
                ));
            }
        }
        assert_eq!(
            LcnfCtorFootprint::of_fields(&fields),
            LcnfCtorFootprint {
                scalar_bytes: 1040,
                obj_fields: 0,
                declared_fields: 230
            }
        );
        let parts = chunk_lcnf_ctor_fields(&fields, 960, 240).unwrap();
        assert_eq!(part_scalar_bytes(&parts), [960, 80]);
        assert_eq!(part_obj_fields(&parts), [0, 0]);
        assert_eq!(parts.concat(), fields);
        // 256 boxed fields plus erased ones still pass the IR checker.
        let mut boxed = nats(256);
        boxed.extend(uniform(200, "h", "True", Irrelevant));
        assert_eq!(ir_ctor_violation(&boxed), None);
    }

    #[test]
    fn declared_field_budget_splits_wide_scalar_and_proof_runs() {
        let bools = uniform(600, "b", "Bool", BOOL);
        // 600 B and no object: the IR checker would accept it, but `structure` cannot
        // elaborate 600 fields.
        assert_eq!(ir_ctor_violation(&bools), None);
        let parts = chunk_lcnf_ctor_fields(&bools, 960, 240).unwrap();
        assert_eq!(
            parts.iter().map(Vec::len).collect::<Vec<_>>(),
            [240, 240, 120]
        );
        let plan = default_plan(&bools);
        assert_eq!(plan.ctor_counts_per_level(), [3, 1]);
        assert_eq!(
            plan.root().footprint,
            LcnfCtorFootprint {
                scalar_bytes: 0,
                obj_fields: 3,
                declared_fields: 3
            }
        );
        assert_lossless(&plan);

        let mut proofs = nats(240);
        proofs.extend(uniform(300, "h", "True", Irrelevant));
        let plan = default_plan(&proofs);
        let part_sizes: Vec<usize> = plan.levels()[0]
            .iter()
            .map(|ctor| ctor.children.len())
            .collect();
        assert_eq!(part_sizes, [240, 240, 60]);
        let reprs: Vec<CtorReprKind> = plan.levels()[0].iter().map(|ctor| ctor.repr).collect();
        assert_eq!(
            reprs,
            [
                CtorReprKind::BoxedObject,
                CtorReprKind::Erased,
                CtorReprKind::Erased
            ]
        );
        assert_eq!(plan.root().field_kinds, [ObjectRef; 3]);
        assert_lossless(&plan);
    }

    fn mixed_fields(count: usize, seed: u64) -> Vec<LcnfFieldSpec> {
        let kinds = [
            ("Bool", BOOL),
            ("UInt16", LcnfFieldKind::Scalar { bytes: 2 }),
            ("UInt32", LcnfFieldKind::Scalar { bytes: 4 }),
            ("UInt64", U64),
            ("Nat", ObjectRef),
            ("True", Irrelevant),
        ];
        let mut state = seed | 1;
        (0..count)
            .map(|index| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                let (lean_ty, kind) = kinds[(state % kinds.len() as u64) as usize];
                LcnfFieldSpec::new(format!("m{index}"), lean_ty, kind)
            })
            .collect()
    }

    #[test]
    fn multi_level_layout_ends_at_one_accepted_root_for_many_shapes() {
        let sizes = [
            0, 1, 2, 3, 119, 120, 121, 239, 240, 241, 255, 256, 257, 511, 1000, 4096,
        ];
        let budgets = [(960, 240), (8, 240), (8, 1), (1, 1), (16, 2), (1023, 255)];
        for &count in &sizes {
            let shapes = [
                u64s(count),
                nats(count),
                uniform(count, "b", "Bool", BOOL),
                uniform(count, "h", "True", Irrelevant),
                mixed_fields(count, count as u64 + 7),
            ];
            for fields in &shapes {
                for &(max_scalar_bytes, max_obj_fields) in &budgets {
                    match plan_lcnf_ctor_layout_levels(fields, max_scalar_bytes, max_obj_fields) {
                        Ok(plan) => {
                            assert_lossless(&plan);
                            for (level, ctors) in plan.levels().iter().enumerate() {
                                let (scalar, objects) = if level == 0 {
                                    (max_scalar_bytes, max_obj_fields)
                                } else {
                                    (MAX_LCNF_CTOR_SCALAR_BYTES, MAX_LCNF_CTOR_OBJ_FIELDS)
                                };
                                for ctor in ctors {
                                    assert!(ctor.footprint.fits_budget(scalar, objects));
                                    assert!(ctor.footprint.is_ir_accepted());
                                }
                                if level > 0 {
                                    assert!(ctors.len() < plan.levels()[level - 1].len());
                                }
                            }
                            if count > 0 {
                                assert_eq!(
                                    plan.root().children.len(),
                                    plan.levels().iter().rev().nth(1).map_or(count, Vec::len)
                                );
                            }
                        }
                        Err(LcnfLayoutError::FieldExceedsBudget { scalar_bytes, .. }) => {
                            assert!(scalar_bytes > max_scalar_bytes);
                        }
                        Err(error) => panic!("unexpected error for {count} fields: {error}"),
                    }
                }
            }
        }
        let deep = plan_lcnf_ctor_layout_levels(&u64s(30_000), 8, 240).unwrap();
        assert_eq!(deep.ctor_counts_per_level(), [30_000, 250, 2, 1]);
        assert_lossless(&deep);
    }

    #[test]
    fn guard_rejects_invalid_budgets_and_field_kinds() {
        let fields = u64s(3);
        for (scalar, objects) in [(0, 240), (960, 0), (0, 0)] {
            assert!(matches!(
                chunk_lcnf_ctor_fields(&fields, scalar, objects),
                Err(LcnfLayoutError::ZeroBudget { .. })
            ));
        }
        for (scalar, objects) in [(1024, 240), (960, 256), (4096, 1000)] {
            assert!(matches!(
                plan_lcnf_ctor_layout_levels(&fields, scalar, objects),
                Err(LcnfLayoutError::BudgetAtLeanLimit { .. })
            ));
        }
        assert!(plan_lcnf_ctor_layout_levels(&fields, 1023, 255).is_ok());
        for bytes in [0, 3, 16] {
            let bad = [LcnfFieldSpec::new(
                "w",
                "UInt128",
                LcnfFieldKind::Scalar { bytes },
            )];
            assert_eq!(
                chunk_lcnf_ctor_fields(&bad, 960, 240),
                Err(LcnfLayoutError::InvalidScalarWidth {
                    field: String::from("w"),
                    bytes
                })
            );
            assert!(matches!(
                check_ir_ctor_accepted(&bad),
                Err(LcnfLayoutError::InvalidScalarWidth { .. })
            ));
        }
        assert_eq!(
            chunk_lcnf_ctor_fields(&u64s(1), 4, 240),
            Err(LcnfLayoutError::FieldExceedsBudget {
                field: String::from("f0"),
                scalar_bytes: 8,
                max_scalar_bytes: 4
            })
        );
        assert_eq!(chunk_lcnf_ctor_fields(&[], 960, 240), Ok(vec![]));
    }

    #[test]
    fn guard_rejects_invalid_lean_names_and_types() {
        for name in [
            "", "1x", "_", "end", "where", "a.b", "x y", "\u{3b1}", "f-1",
        ] {
            let fields = [LcnfFieldSpec::new(name, "Nat", ObjectRef)];
            assert!(
                matches!(
                    plan_lcnf_ctor_layout_levels(&fields, 960, 240),
                    Err(LcnfLayoutError::InvalidLeanName { what: "field", .. })
                ),
                "field name `{name}`"
            );
        }
        let duplicate = [
            LcnfFieldSpec::new("x", "Nat", ObjectRef),
            LcnfFieldSpec::new("x", "Bool", BOOL),
        ];
        assert_eq!(
            plan_lcnf_ctor_layout_levels(&duplicate, 960, 240),
            Err(LcnfLayoutError::DuplicateFieldName {
                name: String::from("x")
            })
        );
        for lean_ty in [
            "",
            "  ",
            "Nat -- note",
            "Nat /- c -/",
            "Nat\nNat",
            "Nat := 0",
        ] {
            let fields = [LcnfFieldSpec::new("x", lean_ty, ObjectRef)];
            assert!(
                matches!(
                    plan_lcnf_ctor_layout_levels(&fields, 960, 240),
                    Err(LcnfLayoutError::InvalidLeanType { .. })
                ),
                "type `{lean_ty:?}`"
            );
        }
        let small = u64s(2);
        for struct_name in ["", "Foo..Bar", "9Foo", "Foo.end", "Foo Bar", ".Foo", "Foo."] {
            assert!(
                matches!(
                    emit_lcnf_guarded_structure(struct_name, &small, &[]),
                    Err(LcnfLayoutError::InvalidLeanName {
                        what: "structure",
                        ..
                    })
                ),
                "structure name `{struct_name}`"
            );
        }
        assert!(emit_lcnf_guarded_structure("Foo.Bar_2'", &small, &["Lean.ToJson"]).is_ok());
        assert!(matches!(
            emit_lcnf_guarded_structure("Foo", &small, &["Repr BEq"]),
            Err(LcnfLayoutError::InvalidLeanName {
                what: "deriving",
                ..
            })
        ));
        assert!(matches!(
            emit_lcnf_guarded_structure("Foo", &small, &[""]),
            Err(LcnfLayoutError::InvalidLeanName {
                what: "deriving",
                ..
            })
        ));
        assert_eq!(
            emit_lcnf_guarded_structure("Foo", &small, &["Repr", "Repr"]),
            Err(LcnfLayoutError::DuplicateDerive {
                name: String::from("Repr")
            })
        );
    }

    #[test]
    fn split_layout_rejects_collisions_and_dependent_types() {
        let flat = vec![
            LcnfFieldSpec::new("part1", "Nat", ObjectRef),
            LcnfFieldSpec::new("n", "Nat", ObjectRef),
            LcnfFieldSpec::new("v", "Fin n", ObjectRef),
            LcnfFieldSpec::new("mk", "Nat", ObjectRef),
        ];
        // A flat structure keeps Lean's own scoping, so these fields are accepted there.
        assert!(emit_lcnf_guarded_structure("Small", &flat, &[]).is_ok());

        let wide = |extra: &[LcnfFieldSpec]| -> Vec<LcnfFieldSpec> {
            let mut fields = extra.to_vec();
            fields.extend(u64s(130));
            fields
        };
        for reserved in ["part1", "part2", "Part1", "Part2", "mk", "casesOn"] {
            let fields = wide(&[LcnfFieldSpec::new(reserved, "Nat", ObjectRef)]);
            assert_eq!(
                emit_lcnf_guarded_structure("Wide", &fields, &[]),
                Err(LcnfLayoutError::ReservedFieldName {
                    name: reserved.to_owned()
                })
            );
        }
        let dependent = wide(&flat[1..3]);
        assert_eq!(
            emit_lcnf_guarded_structure("Wide", &dependent, &[]),
            Err(LcnfLayoutError::DependentFieldType {
                field: String::from("v"),
                depends_on: String::from("n")
            })
        );
        let uses_self = wide(&[LcnfFieldSpec::new("w", "List self", ObjectRef)]);
        assert!(matches!(
            emit_lcnf_guarded_structure("Wide", &uses_self, &[]),
            Err(LcnfLayoutError::DependentFieldType { .. })
        ));
        let recursive = wide(&[LcnfFieldSpec::new("next", "Option Node", ObjectRef)]);
        assert_eq!(
            emit_lcnf_guarded_structure("Demo.Node", &recursive, &[]),
            Err(LcnfLayoutError::DependentFieldType {
                field: String::from("next"),
                depends_on: String::from("Node")
            })
        );
        let fine = wide(&[
            LcnfFieldSpec::new("part", "Nat", ObjectRef),
            LcnfFieldSpec::new("v", "Fin 3", ObjectRef),
        ]);
        assert!(emit_lcnf_guarded_structure("Wide", &fine, &[]).is_ok());
    }

    #[test]
    fn flat_structure_is_emitted_unchanged() {
        let fields = [
            LcnfFieldSpec::builtin("x", "UInt64").unwrap(),
            LcnfFieldSpec::builtin("y", "Nat").unwrap(),
            LcnfFieldSpec::builtin("ok", "Bool").unwrap(),
            LcnfFieldSpec::new("h", "x = x", Irrelevant),
        ];
        let plan = default_plan(&fields);
        assert!(plan.is_flat());
        assert_eq!(plan.field_projection_path(1), Some(vec![String::from("y")]));
        assert_eq!(
            emit_lcnf_guarded_structure("Demo.Point", &fields, &["Repr", "BEq"]).unwrap(),
            "structure Demo.Point where\n  x : UInt64\n  y : Nat\n  ok : Bool\n  h : x = x\n  deriving Repr, BEq\n"
        );
        assert_eq!(
            emit_lcnf_guarded_structure("Demo.Point", &fields, &[]).unwrap(),
            "structure Demo.Point where\n  x : UInt64\n  y : Nat\n  ok : Bool\n  h : x = x\n"
        );
        let empty = default_plan(&[]);
        assert!(empty.is_flat());
        assert_eq!(empty.ctor_counts_per_level(), [1]);
        assert_eq!(
            emit_lcnf_guarded_structure("Empty", &[], &["Inhabited"]).unwrap(),
            "structure Empty where\n  deriving Inhabited\n"
        );
        // 120 x UInt64 = 960 B fits the budget exactly and stays flat.
        assert!(default_plan(&u64s(120)).is_flat());
        assert!(default_plan(&nats(240)).is_flat());
        assert!(!default_plan(&nats(241)).is_flat());
    }

    #[test]
    fn split_structure_emits_parts_root_and_accessors() {
        let out = emit_lcnf_guarded_structure("Wide", &u64s(130), &["Inhabited"]).unwrap();
        let mut expected = String::from("structure Wide.Part1 where\n");
        for index in 0..120 {
            expected.push_str(&format!("  f{index} : UInt64\n"));
        }
        expected.push_str("  deriving Inhabited\n\nstructure Wide.Part2 where\n");
        for index in 120..130 {
            expected.push_str(&format!("  f{index} : UInt64\n"));
        }
        expected.push_str(
            "  deriving Inhabited\n\nstructure Wide where\n  part1 : Wide.Part1\n  part2 : Wide.Part2\n  deriving Inhabited\n\n",
        );
        for index in 0..130 {
            let part = if index < 120 { 1 } else { 2 };
            expected.push_str(&format!(
                "abbrev Wide.f{index} (self : Wide) : UInt64 := self.part{part}.f{index}\n"
            ));
        }
        assert_eq!(out, expected);
    }

    #[test]
    fn multi_level_structure_names_and_projection_paths() {
        let plan = plan_lcnf_ctor_layout_levels(&u64s(300), 8, 240).unwrap();
        assert_eq!(plan.ctor_lean_name("Deep", 0, 0), "Deep.Part1");
        assert_eq!(plan.ctor_lean_name("Deep", 1, 2), "Deep.Level1_Part3");
        assert_eq!(plan.ctor_lean_name("Deep", 2, 0), "Deep");
        assert_eq!(
            plan.field_projection_path(299),
            Some(vec![
                String::from("level1_part3"),
                String::from("part300"),
                String::from("f299")
            ])
        );
        let out = render_lcnf_guarded_structure("Deep", &plan, &[]).unwrap();
        assert!(out.starts_with(
            "structure Deep.Part1 where\n  f0 : UInt64\n\nstructure Deep.Part2 where\n  f1 : UInt64\n"
        ));
        assert!(out.contains(
            "\nstructure Deep.Level1_Part1 where\n  part1 : Deep.Part1\n  part2 : Deep.Part2\n"
        ));
        assert!(out.contains("  part120 : Deep.Part120\n\nstructure Deep.Level1_Part2 where\n  part121 : Deep.Part121\n"));
        assert!(out.contains(
            "\nstructure Deep where\n  level1_part1 : Deep.Level1_Part1\n  level1_part2 : Deep.Level1_Part2\n  level1_part3 : Deep.Level1_Part3\n\n"
        ));
        assert!(
            out.contains("abbrev Deep.f0 (self : Deep) : UInt64 := self.level1_part1.part1.f0\n")
        );
        assert!(out.ends_with(
            "abbrev Deep.f299 (self : Deep) : UInt64 := self.level1_part3.part300.f299\n"
        ));
        assert_eq!(out.matches("structure ").count(), 304);
        assert_eq!(out.matches("abbrev ").count(), 300);
    }

    fn owned_exprs(fields: &[LcnfFieldSpec]) -> Vec<(String, String)> {
        fields
            .iter()
            .enumerate()
            .map(|(index, field)| (field.name.clone(), index.to_string()))
            .collect()
    }

    fn borrowed(exprs: &[(String, String)]) -> Vec<(&str, &str)> {
        exprs
            .iter()
            .map(|(name, expr)| (name.as_str(), expr.as_str()))
            .collect()
    }

    #[test]
    fn ctor_expr_builds_every_level() {
        let point = [
            LcnfFieldSpec::builtin("x", "UInt64").unwrap(),
            LcnfFieldSpec::builtin("y", "Nat").unwrap(),
        ];
        let plan = default_plan(&point);
        assert_eq!(
            render_lcnf_guarded_ctor_expr("P", &[("y", "2"), ("x", " 1 ")], &plan),
            Ok(String::from("({ x := (1), y := (2) } : P)"))
        );
        assert_eq!(
            render_lcnf_guarded_ctor_expr("E", &[], &default_plan(&[])),
            Ok(String::from("({ } : E)"))
        );

        let fields = u64s(121);
        let plan = default_plan(&fields);
        let exprs = owned_exprs(&fields);
        let refs = borrowed(&exprs);
        let expr = render_lcnf_guarded_ctor_expr("T", &refs, &plan).unwrap();
        assert!(expr.starts_with("({ part1 := ({ f0 := (0), f1 := (1), "));
        assert!(expr.ends_with(
            "f119 := (119) } : T.Part1), part2 := ({ f120 := (120) } : T.Part2) } : T)"
        ));

        let deep = plan_lcnf_ctor_layout_levels(&u64s(300), 8, 240).unwrap();
        let deep_exprs = owned_exprs(deep.fields());
        let deep_expr = render_lcnf_guarded_ctor_expr("D", &borrowed(&deep_exprs), &deep).unwrap();
        assert!(deep_expr.starts_with(
            "({ level1_part1 := ({ part1 := ({ f0 := (0) } : D.Part1), part2 := ({ f1 := (1) } : D.Part2), "
        ));
        assert!(
            deep_expr
                .ends_with("part300 := ({ f299 := (299) } : D.Part300) } : D.Level1_Part3) } : D)")
        );

        assert_eq!(
            render_lcnf_guarded_ctor_expr("T", &refs[1..], &plan),
            Err(LcnfLayoutError::MissingFieldExpr {
                field: String::from("f0")
            })
        );
        let mut unknown = refs.clone();
        unknown.push(("nope", "0"));
        assert_eq!(
            render_lcnf_guarded_ctor_expr("T", &unknown, &plan),
            Err(LcnfLayoutError::UnknownFieldExpr {
                field: String::from("nope")
            })
        );
        let mut duplicate = refs.clone();
        duplicate.push(("f3", "3"));
        assert_eq!(
            render_lcnf_guarded_ctor_expr("T", &duplicate, &plan),
            Err(LcnfLayoutError::DuplicateFieldExpr {
                field: String::from("f3")
            })
        );
        for bad in ["", "  ", "1\n"] {
            let mut invalid = refs.clone();
            invalid[0] = ("f0", bad);
            assert_eq!(
                render_lcnf_guarded_ctor_expr("T", &invalid, &plan),
                Err(LcnfLayoutError::InvalidFieldExpr {
                    field: String::from("f0")
                })
            );
        }
        assert!(matches!(
            render_lcnf_guarded_ctor_expr("T.", &refs, &plan),
            Err(LcnfLayoutError::InvalidLeanName { .. })
        ));
    }

    #[test]
    fn check_ir_ctor_accepted_reports_the_first_checker_limit() {
        assert_eq!(
            check_ir_ctor_accepted(&u64s(128)),
            Ok(LcnfCtorFootprint {
                scalar_bytes: 1024,
                obj_fields: 0,
                declared_fields: 128
            })
        );
        assert_eq!(
            check_ir_ctor_accepted(&nats(256)).map(|f| f.obj_fields),
            Ok(256)
        );
        let mut both = nats(257);
        both.extend(uniform(129, "x", "UInt64", U64));
        assert_eq!(ir_ctor_violation(&both), Some(IrCtorLimit::Fields));
        let error = check_ir_ctor_accepted(&both).unwrap_err();
        assert!(error.to_string().contains("has too many fields"), "{error}");
    }

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
        assert_eq!(
            validate_mir_module_ctor_arities(MIR_MODULE_CTOR_ARITIES),
            Ok(LcnfCtorFootprint {
                scalar_bytes: 96,
                obj_fields: 12,
                declared_fields: 12
            })
        );
        let objects = [MirModuleCtorArity {
            lean_name: "Synthetic.objects",
            fields: 241,
        }];
        assert!(!mir_module_ctor_arities_fit(&objects));
        assert_eq!(
            validate_mir_module_ctor_arities(&objects),
            Err(LcnfLayoutError::MirCtorOverBudget {
                lean_name: "Synthetic.objects",
                fields: 241
            })
        );
        // 121 worst-case fields need 968 scalar bytes.
        let scalars = [MirModuleCtorArity {
            lean_name: "Synthetic.scalars",
            fields: 121,
        }];
        assert!(!mir_module_ctor_arities_fit(&scalars));
        assert!(validate_mir_module_ctor_arities(&scalars).is_err());
        let largest = [MirModuleCtorArity {
            lean_name: "Synthetic.largest",
            fields: 120,
        }];
        assert!(mir_module_ctor_arities_fit(&largest));
        assert!(validate_mir_module_ctor_arities(&largest).is_ok());
    }

    #[test]
    fn try_emit_mir_lean_module_is_byte_identical() {
        let mir = demo_answer_mir();
        let emitted = emit_mir_lean_module("Mir.Demo.answer", &mir);
        assert_eq!(
            try_emit_mir_lean_module("Mir.Demo.answer", &mir),
            Ok(emitted.clone())
        );
        // SHA-256 of the module emitted by the pre-guard emitter (base `9110fbec`).
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
        assert_eq!(table.get("MirAst.CapturedMir"), Some(&12));
        assert_eq!(table.get("MirAst.TerminatorKind.call"), Some(&5));
    }

    // Live Lean `v4.34.1` probes.

    /// One namespace of a Lean probe file and the IR-checker diagnostics the model predicts.
    struct LeanProbeCase {
        name: String,
        source: String,
        predicted: Vec<&'static str>,
    }

    impl LeanProbeCase {
        fn new(name: &str, body: &str, ctors: &[LcnfCtorFootprint]) -> Self {
            let predicted: BTreeSet<&'static str> = ctors
                .iter()
                .filter_map(|footprint| footprint.ir_violation())
                .map(IrCtorLimit::lean_diagnostic)
                .collect();
            Self {
                name: name.to_owned(),
                source: format!("namespace LcnfProbe.{name}\n{body}end LcnfProbe.{name}\n"),
                predicted: predicted.into_iter().collect(),
            }
        }
    }

    /// Removes the probe directory unless `ANNEAL_LCNF_PROBE_KEEP` is set.
    struct RemoveDirOnDrop(PathBuf);

    impl Drop for RemoveDirOnDrop {
        fn drop(&mut self) {
            if std::env::var_os("ANNEAL_LCNF_PROBE_KEEP").is_some() {
                eprintln!("kept LCNF probe directory {}", self.0.display());
            } else {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
    }

    /// A `lean` executable reporting version `4.34.1`, or `None`.
    fn lean_for_probe() -> Option<PathBuf> {
        let mut candidates: Vec<PathBuf> = Vec::new();
        if let Some(lean) = std::env::var_os("ANNEAL_LCNF_PROBE_LEAN") {
            candidates.push(PathBuf::from(lean));
        }
        if let Some(path) = std::env::var_os("PATH") {
            candidates.extend(std::env::split_paths(&path).map(|dir| dir.join("lean")));
        }
        if let Some(home) = std::env::var_os("HOME") {
            candidates.push(PathBuf::from(home).join(".elan/bin/lean"));
        }
        candidates.into_iter().find(|lean| {
            lean.is_file()
                && Command::new(lean)
                    .arg("--version")
                    .current_dir(env!("CARGO_MANIFEST_DIR"))
                    .output()
                    .is_ok_and(|output| {
                        output.status.success()
                            && String::from_utf8_lossy(&output.stdout).contains("version 4.34.1")
                    })
        })
    }

    /// Compiles `cases` in one Lean file and returns the error lines of each case, or `None`
    /// when no Lean `v4.34.1` is available (a failure when `ANNEAL_REQUIRE_LCNF_LEAN_PROBE` is
    /// set).
    fn run_lean_probe(probe: &str, cases: &[LeanProbeCase]) -> Option<Vec<Vec<String>>> {
        let Some(lean) = lean_for_probe() else {
            assert!(
                std::env::var_os("ANNEAL_REQUIRE_LCNF_LEAN_PROBE")
                    .is_none_or(|value| value.is_empty()),
                "{probe}: ANNEAL_REQUIRE_LCNF_LEAN_PROBE is set but no Lean 4.34.1 was found"
            );
            eprintln!(
                "{probe}: SKIPPED: no Lean 4.34.1 in ANNEAL_LCNF_PROBE_LEAN, on PATH, or at ~/.elan/bin/lean"
            );
            return None;
        };
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |elapsed| elapsed.as_nanos());
        let dir = std::env::temp_dir().join(format!(
            "anneal-lcnf-probe-{probe}-{}-{nanos}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).expect("probe directory");
        let _cleanup = RemoveDirOnDrop(dir.clone());

        let mut source = String::new();
        let mut ranges = Vec::with_capacity(cases.len());
        let mut line = 1;
        for case in cases {
            let lines = case.source.matches('\n').count();
            ranges.push((line, line + lines - 1));
            source.push_str(&case.source);
            source.push('\n');
            line += lines + 1;
        }
        source.push_str("#eval IO.println \"LCNF_PROBE_END\"\n");
        let path = dir.join("LcnfProbe.lean");
        std::fs::write(&path, &source).expect("probe source");

        let stdout_path = dir.join("stdout.txt");
        let stderr_path = dir.join("stderr.txt");
        let started = Instant::now();
        let mut child = Command::new(&lean)
            .arg(&path)
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .env_remove("LEAN_PATH")
            .stdin(Stdio::null())
            .stdout(Stdio::from(
                File::create(&stdout_path).expect("stdout file"),
            ))
            .stderr(Stdio::from(
                File::create(&stderr_path).expect("stderr file"),
            ))
            .spawn()
            .expect("spawn lean");
        let status = loop {
            if let Some(status) = child.try_wait().expect("wait for lean") {
                break status;
            }
            if started.elapsed() > Duration::from_secs(1200) {
                let _ = child.kill();
                panic!("{probe}: lean did not finish within 1200 s");
            }
            std::thread::sleep(Duration::from_millis(50));
        };
        let output = std::fs::read_to_string(&stdout_path).unwrap_or_default()
            + &std::fs::read_to_string(&stderr_path).unwrap_or_default();
        assert!(
            output.contains("LCNF_PROBE_END"),
            "{probe}: lean stopped early ({status}):\n{output}"
        );

        let prefix = format!("{}:", path.display());
        let mut errors = vec![Vec::new(); cases.len()];
        for text in output.lines() {
            let Some(rest) = text.strip_prefix(&prefix) else {
                continue;
            };
            let mut parts = rest.splitn(3, ':');
            let (Some(line), Some(_column), Some(message)) =
                (parts.next(), parts.next(), parts.next())
            else {
                continue;
            };
            if !message.trim_start().starts_with("error") {
                continue;
            }
            let line: usize = line.parse().expect("diagnostic line number");
            let case = ranges
                .iter()
                .position(|&(first, last)| (first..=last).contains(&line))
                .unwrap_or_else(|| panic!("{probe}: error outside every case: {text}"));
            errors[case].push(text.to_owned());
        }
        assert_eq!(
            status.success(),
            errors.iter().all(Vec::is_empty),
            "{probe}: lean exit status {status} disagrees with its diagnostics:\n{output}"
        );
        eprintln!(
            "{probe}: {} ({} cases, {} lines) compiled by {} in {:.1} s",
            if status.success() {
                "accepted"
            } else {
                "rejected"
            },
            cases.len(),
            line,
            lean.display(),
            started.elapsed().as_secs_f64()
        );
        Some(errors)
    }

    fn assert_lean_matches_model(probe: &str, cases: &[LeanProbeCase]) {
        let Some(errors) = run_lean_probe(probe, cases) else {
            return;
        };
        let mut mismatches = Vec::new();
        for (case, case_errors) in cases.iter().zip(&errors) {
            let observed: BTreeSet<&'static str> = [IrCtorLimit::Fields, IrCtorLimit::Scalar]
                .into_iter()
                .map(IrCtorLimit::lean_diagnostic)
                .filter(|diagnostic| case_errors.iter().any(|error| error.contains(diagnostic)))
                .collect();
            let observed: Vec<&'static str> = observed.into_iter().collect();
            let matches = if case.predicted.is_empty() {
                case_errors.is_empty()
            } else {
                !case_errors.is_empty() && observed == case.predicted
            };
            if !matches {
                mismatches.push(format!(
                    "{}: model {:?}, Lean {:?}: {:?}",
                    case.name,
                    case.predicted,
                    observed,
                    case_errors.iter().take(3).collect::<Vec<_>>()
                ));
            }
        }
        assert!(
            mismatches.is_empty(),
            "{probe}: Lean 4.34.1 disagrees with the LCNF model:\n{}",
            mismatches.join("\n")
        );
    }

    fn render_fields(fields: &[LcnfFieldSpec]) -> String {
        fields
            .iter()
            .map(|field| format!("  {} : {}\n", field.name, field.lean_ty))
            .collect()
    }

    /// One flat structure `W` over `fields`, without the guard.
    fn unguarded_flat_case(name: &str, fields: &[LcnfFieldSpec]) -> LeanProbeCase {
        let body = format!(
            "structure W where\n{}  deriving Inhabited\n",
            render_fields(fields)
        );
        LeanProbeCase::new(name, &body, &[LcnfCtorFootprint::of_fields(fields)])
    }

    /// `Part<j>` structures plus one wrapper `W` with one field per part, without the guard.
    fn unguarded_one_wrapper_case(name: &str, parts: &[Vec<LcnfFieldSpec>]) -> LeanProbeCase {
        let mut body = String::new();
        let mut ctors = Vec::with_capacity(parts.len() + 1);
        for (index, part) in parts.iter().enumerate() {
            body.push_str(&format!(
                "structure Part{} where\n{}  deriving Inhabited\n\n",
                index + 1,
                render_fields(part)
            ));
            ctors.push(LcnfCtorFootprint::of_fields(part));
        }
        body.push_str("structure W where\n");
        for index in 0..parts.len() {
            body.push_str(&format!("  part{} : Part{}\n", index + 1, index + 1));
        }
        body.push_str("  deriving Inhabited\n");
        ctors.push(LcnfCtorFootprint::of_kinds(lcnf_wrapper_field_kinds(parts)));
        LeanProbeCase::new(name, &body, &ctors)
    }

    /// Lean literal of field `index` for a builtin type, and whether `rfl` can check it.
    fn probe_literal(lean_ty: &str, index: usize) -> (String, bool) {
        match lean_ty {
            "Bool" => (
                String::from(if index.is_multiple_of(3) {
                    "true"
                } else {
                    "false"
                }),
                true,
            ),
            "UInt8" | "UInt16" | "UInt32" | "UInt64" | "USize" | "Nat" => {
                ((index % 250).to_string(), true)
            }
            "Int8" | "Int16" | "Int32" | "Int64" | "ISize" | "Int" => {
                (format!("-{}", index % 100), true)
            }
            "Char" => (format!("'{}'", char::from(b'a' + (index % 26) as u8)), true),
            "Float" | "Float32" => (format!("{}.5", index % 100), true),
            "String" => (format!("\"s{index}\""), true),
            "Unit" => (String::from("()"), true),
            "Prop" => (
                String::from(if index.is_multiple_of(2) {
                    "True"
                } else {
                    "False"
                }),
                true,
            ),
            "Type" => (
                String::from(if index.is_multiple_of(2) {
                    "Nat"
                } else {
                    "Bool"
                }),
                true,
            ),
            _ => (String::from("trivial"), false),
        }
    }

    /// The guarded structure `S` of `plan`, a value built with `render_lcnf_guarded_ctor_expr`,
    /// and one `rfl` example per field reading the value back through its accessor.
    fn guarded_case(name: &str, plan: &LcnfCtorLayoutPlan, derives: &[&str]) -> LeanProbeCase {
        let mut body =
            render_lcnf_guarded_structure("S", plan, derives).expect("guarded structure");
        let literals: Vec<(String, bool)> = plan
            .fields()
            .iter()
            .enumerate()
            .map(|(index, field)| probe_literal(field.lean_ty.trim(), index))
            .collect();
        let exprs: Vec<(&str, &str)> = plan
            .fields()
            .iter()
            .zip(&literals)
            .map(|(field, (literal, _))| (field.name.as_str(), literal.as_str()))
            .collect();
        let value =
            render_lcnf_guarded_ctor_expr("S", &exprs, plan).expect("constructor expression");
        body.push_str(&format!("\n@[noinline] def mkValue : S := {value}\n\n"));
        for (field, (literal, checkable)) in plan.fields().iter().zip(&literals) {
            if *checkable {
                body.push_str(&format!(
                    "example : mkValue.{} = ({literal} : {}) := rfl\n",
                    field.name,
                    field.lean_ty.trim()
                ));
            }
        }
        let ctors: Vec<LcnfCtorFootprint> = plan
            .levels()
            .iter()
            .flatten()
            .map(|ctor| ctor.footprint)
            .collect();
        LeanProbeCase::new(name, &body, &ctors)
    }

    #[test]
    fn lcnf_live_lean_probe_matches_model() {
        let deep = plan_lcnf_ctor_layout_levels(&u64s(300), 8, 240).unwrap();
        let mut proof_tail = nats(240);
        proof_tail.extend(uniform(300, "h", "True", Irrelevant));
        let mixed: Vec<LcnfFieldSpec> = (0..520)
            .map(|index| {
                LcnfFieldSpec::builtin(
                    format!("m{index}"),
                    BUILTIN_LEAN_TYPES[index % BUILTIN_LEAN_TYPES.len()],
                )
                .unwrap()
            })
            .collect();
        let small = [
            LcnfFieldSpec::builtin("x", "UInt64").unwrap(),
            LcnfFieldSpec::builtin("y", "Nat").unwrap(),
            LcnfFieldSpec::builtin("ok", "Bool").unwrap(),
            LcnfFieldSpec::builtin("name", "String").unwrap(),
        ];
        let zero_relevant = [LcnfFieldSpec::new("h", "True", Irrelevant)];
        let zero_relevant_parent: Vec<LcnfFieldKind> =
            vec![CtorReprKind::of_fields(&zero_relevant).parent_field_kind(); 300];
        let zero_relevant_body = format!(
            "structure Z : Type where\n  h : True\n  deriving Inhabited\n\nstructure W where\n{}  deriving Inhabited\n",
            (0..300)
                .map(|index| format!("  z{index} : Z\n"))
                .collect::<String>()
        );
        let cases = vec![
            // `PROTOTYPE_REPORT.md` §4.3, in order.
            unguarded_flat_case("flat_130xUInt64_1040B", &u64s(130)),
            guarded_case(
                "split_130xUInt64_960B",
                &default_plan(&u64s(130)),
                &["Inhabited"],
            ),
            unguarded_flat_case("flat_128xUInt64_1024B", &u64s(128)),
            unguarded_flat_case("flat_129xUInt64_1032B", &u64s(129)),
            unguarded_flat_case("flat_256xNat", &nats(256)),
            unguarded_flat_case("flat_257xNat", &nats(257)),
            unguarded_flat_case("flat_300xNat", &nats(300)),
            guarded_case(
                "split_300xNat_240obj",
                &default_plan(&nats(300)),
                &["Inhabited"],
            ),
            guarded_case(
                "split_121xUInt64_960B_singleton_tail",
                &default_plan(&u64s(121)),
                &["Inhabited"],
            ),
            unguarded_one_wrapper_case(
                "split_300xUInt64_cap8_one_wrapper",
                &chunk_lcnf_ctor_fields(&u64s(300), 8, 240).unwrap(),
            ),
            guarded_case("layout_300xUInt64_cap8_two_levels", &deep, &["Inhabited"]),
            // Further guard layouts.
            guarded_case(
                "declared_cap_600xBool",
                &default_plan(&uniform(600, "b", "Bool", BOOL)),
                &["Inhabited"],
            ),
            guarded_case(
                "proof_only_parts",
                &default_plan(&proof_tail),
                &["Inhabited"],
            ),
            guarded_case(
                "mixed_520_builtin_fields",
                &default_plan(&mixed),
                &["Inhabited"],
            ),
            guarded_case(
                "flat_small_all_derives",
                &default_plan(&small),
                &["Inhabited", "Repr", "BEq", "Hashable", "DecidableEq"],
            ),
            guarded_case("empty_structure", &default_plan(&[]), &["Inhabited"]),
            guarded_case("empty_structure_no_deriving", &default_plan(&[]), &[]),
            // A `Type` with no relevant field is one boxed field in its parent.
            LeanProbeCase::new(
                "zero_relevant_type_is_boxed",
                &zero_relevant_body,
                &[
                    LcnfCtorFootprint::of_fields(&zero_relevant),
                    LcnfCtorFootprint::of_kinds(zero_relevant_parent),
                ],
            ),
        ];
        assert_eq!(cases[0].predicted, [IrCtorLimit::Scalar.lean_diagnostic()]);
        assert_eq!(cases[5].predicted, [IrCtorLimit::Fields.lean_diagnostic()]);
        assert_eq!(cases[9].predicted, [IrCtorLimit::Scalar.lean_diagnostic()]);
        assert_eq!(cases[17].predicted, [IrCtorLimit::Fields.lean_diagnostic()]);
        assert!(cases[1].predicted.is_empty() && cases[10].predicted.is_empty());
        assert_lean_matches_model("lcnf_live_lean_probe_matches_model", &cases);
    }

    #[test]
    fn lcnf_live_lean_builtin_kinds_match_model() {
        let mut cases = Vec::new();
        for &lean_ty in BUILTIN_LEAN_TYPES {
            let kind = LcnfFieldKind::of_builtin_lean_ty(lean_ty).unwrap();
            let fill = |count: usize| uniform(count, "t", lean_ty, kind);
            let base = uniform(120, "u", "UInt64", U64);
            let with_base = |count: usize| -> Vec<LcnfFieldSpec> {
                let mut fields = base.clone();
                fields.extend(fill(count));
                fields
            };
            let shapes: Vec<(&str, Vec<LcnfFieldSpec>)> = match kind {
                // 960 B of `UInt64` plus `64 / bytes` fields reach exactly 1024 B.
                LcnfFieldKind::Scalar { bytes } => vec![
                    ("at_scalar_limit", with_base(64 / bytes)),
                    ("over_scalar_limit", with_base(64 / bytes + 1)),
                ],
                LcnfFieldKind::ObjectRef => vec![
                    ("at_field_limit", fill(256)),
                    ("over_field_limit", fill(257)),
                ],
                // Accepted only if the field has no scalar byte and no boxed field.
                LcnfFieldKind::Irrelevant => vec![
                    ("no_scalar_bytes", with_base(65)),
                    ("no_objects", {
                        let mut fields = nats(256);
                        fields.extend(fill(1));
                        fields
                    }),
                ],
            };
            for (shape, fields) in shapes {
                cases.push(unguarded_flat_case(&format!("{lean_ty}_{shape}"), &fields));
            }
        }
        assert_eq!(cases.len(), 2 * BUILTIN_LEAN_TYPES.len());
        assert!(cases.iter().any(|case| !case.predicted.is_empty()));
        assert_lean_matches_model("lcnf_live_lean_builtin_kinds_match_model", &cases);
    }

    #[test]
    fn lcnf_live_lean_standard_derives_scale_to_the_budget() {
        let bools = uniform(600, "b", "Bool", BOOL);
        let plan = default_plan(&bools);
        let part_sizes: Vec<usize> = plan.levels()[0]
            .iter()
            .map(|ctor| ctor.children.len())
            .collect();
        assert_eq!(part_sizes, [240, 240, 120]);
        let cases = [guarded_case(
            "derives_at_declared_cap_600xBool",
            &plan,
            &["Inhabited", "Repr", "BEq", "Hashable"],
        )];
        assert_lean_matches_model(
            "lcnf_live_lean_standard_derives_scale_to_the_budget",
            &cases,
        );
    }
}
