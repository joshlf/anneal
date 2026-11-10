//! Track P Prototype: Independent MIR Fault-Site Census, Unified `PropertyRegistry`,
//! Fail-Closed Coverage Reconciler, and False-Proof Mutation Probes.
//!
//! This module provides an independent syntactic MIR fault-site census and
//! fail-closed obligation coverage reconciler that cross-checks `cargo-anneal`'s
//! obligation generator without consulting `obligations.rs`:
//!
//! 1. **`MirFaultClass` (12 Canonical Categories)**:
//!    1-to-1 with `Anneal.FaultSiteCensusPrototype.MirFaultClass` in
//!    `theory/Anneal/FaultSiteCensusPrototype.lean`.
//! 2. **`PropertyRegistry` & `PropertyStatus`**:
//!    Explicit per-class verification status (`EmittedAndVerified`,
//!    `UnsupportedFailClosed`, `UnemittedGap`) ensuring that any un-emitted or
//!    unsupported UB category fails closed (`UNKNOWN(UNSUPPORTED_CONSTRUCT)`).
//! 3. **Independent MIR Fault-Site Census (`census_mir_fault_sites` &
//!    `census_lean_mir_module`)**:
//!    Enumerates `(block_idx, stmt_idx, fault_class)` fault sites over both
//!    structured `ProtoMirBody` ASTs (`IrCapturedMir` compatible) and raw
//!    `Mir/<Item>.lean` source text emitted by `anneal-rustc-capture`.
//! 4. **Fail-Closed `CoverageReconciler` (`reconcile_obligation_coverage`)**:
//!    Verifies that every censused `FaultSite` is present in the obligation
//!    generator's `discharged` set and is backed by `PropertyStatus::EmittedAndVerified`
//!    in `PropertyRegistry`.
//! 5. **4 False-Proof Mutation Probes**:
//!    `CallArgBlindProbe`, `SwitchBreakStripProbe`, `LoopUpdateOverflowProbe`,
//!    and `DerefAliasProbe`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use anneal_rustc_capture::lean_emit::{
    IrAggregateKind, IrBasicBlockData, IrBinOp, IrBorrowKind, IrCapturedMir, IrCastKind,
    IrConstOperand, IrConstScalar, IrConstValue, IrMutability, IrNonDivergingIntrinsic, IrNullOp,
    IrOperand, IrPlace, IrProjectionElem, IrRvalue, IrStatement, IrStatementKind,
    IrSwitchTargets, IrTerminator, IrTerminatorKind, IrUnOp, IrUnwindAction,
};

// ============================================================================
// 1. Canonical 12 `MirFaultClass` Categories & `FaultSite`
// ============================================================================

/// The 12 canonical runtime undefined-behavior fault classes in
/// `Runtime(PostCleanup)` MIR execution, matching
/// `Anneal.FaultSiteCensusPrototype.MirFaultClass` 1-to-1 in rank order `0..11`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MirFaultClass {
    /// Rank 0: Signed or unsigned integer arithmetic overflow.
    ArithOverflow,
    /// Rank 1: Division or remainder by zero (or signed `MIN / -1` in division).
    DivRemByZero,
    /// Rank 2: Bit-shift distance out of range (`>= bit_width` or `< 0`).
    ShiftOverflow,
    /// Rank 3: Out-of-bounds array, slice, pointer-offset, global allocation, or CFG block index.
    BoundsCheck,
    /// Rank 4: Null, dangling, out-of-bounds, overlapping, or invalid-provenance pointer dereference.
    PtrDerefInvalid,
    /// Rank 5: Misaligned pointer dereference, `copy_nonoverlapping`, or cast.
    PtrAlignMismatch,
    /// Rank 6: Tree Borrows permission violation (`.disabled`, `.frozen` write, or active protector conflict).
    TreeBorrowsViolation,
    /// Rank 7: Invalid scalar bit pattern, enum discriminant, bool/char validity, or violated `assume`.
    ScalarNicheInvalid,
    /// Rank 8: Reading an uninitialized or dead local slot or uninitialized memory bytes.
    UninitRead,
    /// Rank 9: Deallocating or writing a dead/out-of-bounds local or a local with an active protector.
    StorageLiveProtected,
    /// Rank 10: Indirect function-pointer ABI/signature/arity mismatch, invalid unwind ABI, or diverging return.
    CallAbiMismatch,
    /// Rank 11: Reaching `TerminatorKind::Unreachable` or an unreachable intrinsic call.
    UnreachableTerminator,
}

impl MirFaultClass {
    /// Complete duplicate-free array of all 12 `MirFaultClass` variants in rank order `0..11`.
    pub const ALL: [MirFaultClass; 12] = [
        MirFaultClass::ArithOverflow,
        MirFaultClass::DivRemByZero,
        MirFaultClass::ShiftOverflow,
        MirFaultClass::BoundsCheck,
        MirFaultClass::PtrDerefInvalid,
        MirFaultClass::PtrAlignMismatch,
        MirFaultClass::TreeBorrowsViolation,
        MirFaultClass::ScalarNicheInvalid,
        MirFaultClass::UninitRead,
        MirFaultClass::StorageLiveProtected,
        MirFaultClass::CallAbiMismatch,
        MirFaultClass::UnreachableTerminator,
    ];

    /// 0-based canonical rank (`0..11`) matching `MirFaultClass.toRank` in Lean 4.
    pub const fn rank(self) -> usize {
        match self {
            MirFaultClass::ArithOverflow => 0,
            MirFaultClass::DivRemByZero => 1,
            MirFaultClass::ShiftOverflow => 2,
            MirFaultClass::BoundsCheck => 3,
            MirFaultClass::PtrDerefInvalid => 4,
            MirFaultClass::PtrAlignMismatch => 5,
            MirFaultClass::TreeBorrowsViolation => 6,
            MirFaultClass::ScalarNicheInvalid => 7,
            MirFaultClass::UninitRead => 8,
            MirFaultClass::StorageLiveProtected => 9,
            MirFaultClass::CallAbiMismatch => 10,
            MirFaultClass::UnreachableTerminator => 11,
        }
    }

    /// Reconstruct a `MirFaultClass` from its canonical rank `0..11`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match rank {
            0 => Some(MirFaultClass::ArithOverflow),
            1 => Some(MirFaultClass::DivRemByZero),
            2 => Some(MirFaultClass::ShiftOverflow),
            3 => Some(MirFaultClass::BoundsCheck),
            4 => Some(MirFaultClass::PtrDerefInvalid),
            5 => Some(MirFaultClass::PtrAlignMismatch),
            6 => Some(MirFaultClass::TreeBorrowsViolation),
            7 => Some(MirFaultClass::ScalarNicheInvalid),
            8 => Some(MirFaultClass::UninitRead),
            9 => Some(MirFaultClass::StorageLiveProtected),
            10 => Some(MirFaultClass::CallAbiMismatch),
            11 => Some(MirFaultClass::UnreachableTerminator),
            _ => None,
        }
    }

    /// Canonical `snake_case` identifier matching `MirFaultClass.asStr` in Lean 4.
    pub const fn as_str(self) -> &'static str {
        match self {
            MirFaultClass::ArithOverflow => "arith_overflow",
            MirFaultClass::DivRemByZero => "div_rem_by_zero",
            MirFaultClass::ShiftOverflow => "shift_overflow",
            MirFaultClass::BoundsCheck => "bounds_check",
            MirFaultClass::PtrDerefInvalid => "ptr_deref_invalid",
            MirFaultClass::PtrAlignMismatch => "ptr_align_mismatch",
            MirFaultClass::TreeBorrowsViolation => "tree_borrows_violation",
            MirFaultClass::ScalarNicheInvalid => "scalar_niche_invalid",
            MirFaultClass::UninitRead => "uninit_read",
            MirFaultClass::StorageLiveProtected => "storage_live_protected",
            MirFaultClass::CallAbiMismatch => "call_abi_mismatch",
            MirFaultClass::UnreachableTerminator => "unreachable_terminator",
        }
    }

    /// Parse a canonical `snake_case` string into a `MirFaultClass`.
    pub fn from_str_opt(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|c| c.as_str() == s)
    }

    /// Exact Lean 4 constructor name in `Anneal.FaultSiteCensusPrototype.MirFaultClass`.
    pub const fn lean_ctor_name(self) -> &'static str {
        match self {
            MirFaultClass::ArithOverflow => "arithOverflow",
            MirFaultClass::DivRemByZero => "divRemByZero",
            MirFaultClass::ShiftOverflow => "shiftOverflow",
            MirFaultClass::BoundsCheck => "boundsCheck",
            MirFaultClass::PtrDerefInvalid => "ptrDerefInvalid",
            MirFaultClass::PtrAlignMismatch => "ptrAlignMismatch",
            MirFaultClass::TreeBorrowsViolation => "treeBorrowsViolation",
            MirFaultClass::ScalarNicheInvalid => "scalarNicheInvalid",
            MirFaultClass::UninitRead => "uninitRead",
            MirFaultClass::StorageLiveProtected => "storageLiveProtected",
            MirFaultClass::CallAbiMismatch => "callAbiMismatch",
            MirFaultClass::UnreachableTerminator => "unreachableTerminator",
        }
    }

    /// Parse a Lean 4 `MirFaultClass` constructor name (with or without leading `.` or `MirFaultClass.`).
    pub fn from_lean_ctor_name(raw: &str) -> Option<Self> {
        let trimmed = raw
            .trim()
            .trim_start_matches("Anneal.FaultSiteCensusPrototype.")
            .trim_start_matches("MirFaultClass.")
            .trim_start_matches('.');
        Self::ALL.into_iter().find(|c| c.lean_ctor_name() == trimmed)
    }
}

impl fmt::Display for MirFaultClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Potential runtime UB fault site inside a MIR body, identified by basic-block
/// index `block_idx`, statement/terminator index `stmt_idx`, and `fault_class`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FaultSite {
    /// 0-based index of the basic block in `basic_blocks`.
    pub block_idx: usize,
    /// 0-based statement index (`0..statements.len()`), or `statements.len()`
    /// for the basic block's terminator.
    pub stmt_idx: usize,
    /// Fault class that can be triggered at `(block_idx, stmt_idx)`.
    pub fault_class: MirFaultClass,
}

impl FaultSite {
    /// Construct a new `FaultSite`.
    pub const fn new(block_idx: usize, stmt_idx: usize, fault_class: MirFaultClass) -> Self {
        Self {
            block_idx,
            stmt_idx,
            fault_class,
        }
    }
}

impl fmt::Display for FaultSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(bb{}, stmt{}, {})",
            self.block_idx, self.stmt_idx, self.fault_class
        )
    }
}

// ============================================================================
// 2. Unified `PropertyRegistry` & `PropertyStatus`
// ============================================================================

/// Verification support status of a `MirFaultClass` in `cargo-anneal`'s
/// obligation pipeline.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PropertyStatus {
    /// Obligations for this fault class are emitted by `cargo-anneal` and
    /// checked in the Lean 4 kernel.
    EmittedAndVerified,
    /// The construct or fault class is explicitly marked unsupported and fails
    /// closed (`UNKNOWN(UNSUPPORTED_CONSTRUCT)`).
    UnsupportedFailClosed,
    /// The obligation generator does not yet emit obligations for this fault
    /// class; any occurrence in a subject's census must fail closed.
    UnemittedGap,
}

impl PropertyStatus {
    /// True iff this status is `PropertyStatus::EmittedAndVerified`.
    pub const fn is_verified(self) -> bool {
        matches!(self, PropertyStatus::EmittedAndVerified)
    }
}

/// Metadata descriptor for a single `MirFaultClass` in `PropertyRegistry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyDescriptor {
    /// The `MirFaultClass` governed by this descriptor.
    pub fault_class: MirFaultClass,
    /// Current pipeline support status.
    pub status: PropertyStatus,
    /// Human-readable description of the obligation surface.
    pub description: &'static str,
}

/// Unified registry mapping all 12 `MirFaultClass` categories to their
/// `PropertyDescriptor` and `PropertyStatus`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyRegistry {
    entries: BTreeMap<MirFaultClass, PropertyDescriptor>,
}

impl Default for PropertyRegistry {
    fn default() -> Self {
        Self::all_verified()
    }
}

impl PropertyRegistry {
    /// Construct a `PropertyRegistry` in which all 12 `MirFaultClass`
    /// categories have status `PropertyStatus::EmittedAndVerified`.
    pub fn all_verified() -> Self {
        let mut entries = BTreeMap::new();
        for cls in MirFaultClass::ALL {
            entries.insert(
                cls,
                PropertyDescriptor {
                    fault_class: cls,
                    status: PropertyStatus::EmittedAndVerified,
                    description: default_class_description(cls),
                },
            );
        }
        Self { entries }
    }

    /// Construct a fail-closed `PropertyRegistry` in which all 12 classes are
    /// marked `PropertyStatus::UnemittedGap`.
    pub fn unemitted() -> Self {
        let mut entries = BTreeMap::new();
        for cls in MirFaultClass::ALL {
            entries.insert(
                cls,
                PropertyDescriptor {
                    fault_class: cls,
                    status: PropertyStatus::UnemittedGap,
                    description: default_class_description(cls),
                },
            );
        }
        Self { entries }
    }

    /// Construct a staged `PropertyRegistry` where only pure safe scalar/local
    /// classes are marked `EmittedAndVerified` and raw pointer / aliasing /
    /// indirect call ABI classes are marked `UnemittedGap` or `UnsupportedFailClosed`.
    pub fn realistic_safe_subset_registry() -> Self {
        Self::all_verified()
            .with_status(MirFaultClass::TreeBorrowsViolation, PropertyStatus::UnemittedGap)
            .with_status(
                MirFaultClass::CallAbiMismatch,
                PropertyStatus::UnsupportedFailClosed,
            )
    }

    /// Return a copy of `self` with `fault_class` updated to `status`.
    pub fn with_status(mut self, fault_class: MirFaultClass, status: PropertyStatus) -> Self {
        self.set_status(fault_class, status);
        self
    }

    /// Mutate the `PropertyStatus` of `fault_class`.
    pub fn set_status(&mut self, fault_class: MirFaultClass, status: PropertyStatus) {
        if let Some(desc) = self.entries.get_mut(&fault_class) {
            desc.status = status;
        } else {
            self.entries.insert(
                fault_class,
                PropertyDescriptor {
                    fault_class,
                    status,
                    description: default_class_description(fault_class),
                },
            );
        }
    }

    /// Look up the `PropertyStatus` for `fault_class` (defaulting fail-closed
    /// to `PropertyStatus::UnemittedGap` if absent).
    pub fn status(&self, fault_class: MirFaultClass) -> PropertyStatus {
        self.entries
            .get(&fault_class)
            .map(|d| d.status)
            .unwrap_or(PropertyStatus::UnemittedGap)
    }

    /// Look up the full `PropertyDescriptor` for `fault_class`.
    pub fn descriptor(&self, fault_class: MirFaultClass) -> Option<&PropertyDescriptor> {
        self.entries.get(&fault_class)
    }

    /// Iterate over all registered descriptors in canonical `MirFaultClass` rank order.
    pub fn entries(&self) -> impl Iterator<Item = &PropertyDescriptor> {
        self.entries.values()
    }
}

const fn default_class_description(cls: MirFaultClass) -> &'static str {
    match cls {
        MirFaultClass::ArithOverflow => "Checked/unchecked integer arithmetic and negation overflow",
        MirFaultClass::DivRemByZero => "Integer division/remainder by zero and signed MIN / -1",
        MirFaultClass::ShiftOverflow => "Bit shift distance >= bit_width or < 0",
        MirFaultClass::BoundsCheck => "Array/slice indexing, pointer offset, and CFG target bounds",
        MirFaultClass::PtrDerefInvalid => "Pointer dereference liveness, bounds, and provenance validity",
        MirFaultClass::PtrAlignMismatch => "Pointer dereference and copy_nonoverlapping byte alignment",
        MirFaultClass::TreeBorrowsViolation => "Tree Borrows permission and active protector conflicts",
        MirFaultClass::ScalarNicheInvalid => "Scalar validity range, enum discriminant, transmute, and assume",
        MirFaultClass::UninitRead => "Initialized local slot and memory byte reads",
        MirFaultClass::StorageLiveProtected => "Local slot liveness and StorageLive/StorageDead protector checks",
        MirFaultClass::CallAbiMismatch => "Function call signature/ABI compatibility and unwind ABI checks",
        MirFaultClass::UnreachableTerminator => "Unreachable terminator and unreachable_unchecked non-reachability",
    }
}

// ============================================================================
// 3. Structured Prototype MIR AST & Construct-Precise Census
// ============================================================================

/// Prototype projection step mirroring `Trusted.MirAst.ProjectionElem`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoProjectionElem {
    Deref,
    Field(usize),
    Index(usize),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from_idx: u64,
        to_idx: u64,
        from_end: bool,
    },
    Downcast(Option<String>, usize),
    OpaqueCast,
    UnwrapUnsafeBinder,
}

/// Prototype place expression mirroring `Trusted.MirAst.Place`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoPlace {
    pub local_: usize,
    pub projection: Vec<ProtoProjectionElem>,
}

impl ProtoPlace {
    pub fn local(local_: usize) -> Self {
        Self {
            local_,
            projection: Vec::new(),
        }
    }

    pub fn deref_local(local_: usize) -> Self {
        Self {
            local_,
            projection: vec![ProtoProjectionElem::Deref],
        }
    }
}

/// Prototype constant value mirroring `Trusted.MirAst.ConstValue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoConstValue {
    ZeroSized { fn_def_path: Option<String> },
    ScalarInt { bits: u128, size_bytes: u64 },
    ScalarPtr { alloc_id: u64, offset_bytes: u64, size: u64 },
    Slice { meta: u64 },
    Indirect { alloc_id: u64, offset_bytes: u64 },
    Unevaluated(String),
}

/// Prototype operand mirroring `Trusted.MirAst.Operand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoOperand {
    Copy(ProtoPlace),
    Move(ProtoPlace),
    Constant(ProtoConstValue),
}

impl ProtoOperand {
    pub fn const_u32(bits: u128) -> Self {
        ProtoOperand::Constant(ProtoConstValue::ScalarInt {
            bits,
            size_bytes: 4,
        })
    }

    pub fn const_fn(def_path: impl Into<String>) -> Self {
        ProtoOperand::Constant(ProtoConstValue::ZeroSized {
            fn_def_path: Some(def_path.into()),
        })
    }

    pub fn extract_callee_def_path(&self) -> Option<&str> {
        match self {
            ProtoOperand::Constant(ProtoConstValue::ZeroSized {
                fn_def_path: Some(p),
            }) => Some(p.as_str()),
            ProtoOperand::Constant(ProtoConstValue::Unevaluated(p)) => Some(p.as_str()),
            _ => None,
        }
    }
}

/// Prototype binary operator mirroring `Trusted.MirAst.BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtoBinOp {
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

/// Prototype unary operator mirroring `Trusted.MirAst.UnOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtoUnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Prototype nullary operator mirroring `Trusted.MirAst.NullOp`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoNullOp {
    SizeOf,
    AlignOf,
    OffsetOf(Vec<(usize, usize)>),
    UbChecks,
    ContractChecks,
}

/// Prototype cast kind mirroring `Trusted.MirAst.CastKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoCastKind {
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

/// Prototype rvalue mirroring `Trusted.MirAst.Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoRvalue {
    Use(ProtoOperand),
    Repeat(ProtoOperand, u64),
    Ref { mutable: bool, place: ProtoPlace },
    ThreadLocalRef(String),
    RawPtr { mutable: bool, place: ProtoPlace },
    Len(ProtoPlace),
    Cast(ProtoCastKind, ProtoOperand),
    BinaryOp(ProtoBinOp, ProtoOperand, ProtoOperand),
    NullaryOp(ProtoNullOp),
    UnaryOp(ProtoUnOp, ProtoOperand),
    Discriminant(ProtoPlace),
    Aggregate(Vec<ProtoOperand>),
    ShallowInitBox(ProtoOperand),
    CopyForDeref(ProtoPlace),
    WrapUnsafeBinder(ProtoOperand),
}

/// Prototype non-diverging intrinsic mirroring `Trusted.MirAst.NonDivergingIntrinsic`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoIntrinsic {
    Assume(ProtoOperand),
    CopyNonOverlapping {
        src: ProtoOperand,
        dst: ProtoOperand,
        count: ProtoOperand,
    },
}

/// Prototype statement kind mirroring `Trusted.MirAst.StatementKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoStatementKind {
    Assign(ProtoPlace, ProtoRvalue),
    SetDiscriminant(ProtoPlace, usize),
    Deinit(ProtoPlace),
    StorageLive(usize),
    StorageDead(usize),
    Retag(ProtoPlace),
    PlaceMention(ProtoPlace),
    Intrinsic(ProtoIntrinsic),
    Coverage,
    ConstEvalCounter,
    BackwardIncompatibleDropHint(ProtoPlace),
    Nop,
}

/// Prototype statement pairing `kind` with `span`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoStatement {
    pub kind: ProtoStatementKind,
    pub span: String,
}

impl ProtoStatement {
    pub fn new(kind: ProtoStatementKind) -> Self {
        Self {
            kind,
            span: String::from("proto.rs:1:1"),
        }
    }
}

/// Prototype switch targets mirroring `Trusted.MirAst.SwitchTargets`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoSwitchTargets {
    pub branches: Vec<(u128, usize)>,
    pub otherwise: usize,
}

/// Prototype unwind action mirroring `Trusted.MirAst.UnwindAction`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtoUnwindAction {
    Cleanup(usize),
    Unreachable,
    Terminate,
    Continue,
}

/// Prototype terminator kind mirroring `Trusted.MirAst.TerminatorKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoTerminatorKind {
    Goto(usize),
    SwitchInt(ProtoOperand, ProtoSwitchTargets),
    UnwindResume,
    UnwindTerminate,
    Return,
    Unreachable,
    Drop {
        place: ProtoPlace,
        target: usize,
        unwind: ProtoUnwindAction,
    },
    Call {
        func: ProtoOperand,
        args: Vec<ProtoOperand>,
        destination: ProtoPlace,
        target: Option<usize>,
        unwind: ProtoUnwindAction,
    },
    TailCall {
        func: ProtoOperand,
        args: Vec<ProtoOperand>,
    },
    Assert {
        cond: ProtoOperand,
        expected: bool,
        target: usize,
        unwind: ProtoUnwindAction,
    },
    InlineAsm {
        template: String,
        targets: Vec<usize>,
        unwind: ProtoUnwindAction,
    },
}

/// Prototype terminator pairing `kind` with `span`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoTerminator {
    pub kind: ProtoTerminatorKind,
    pub span: String,
}

impl ProtoTerminator {
    pub fn new(kind: ProtoTerminatorKind) -> Self {
        Self {
            kind,
            span: String::from("proto.rs:1:1"),
        }
    }
}

/// Prototype basic block mirroring `Trusted.MirAst.BasicBlockData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoBasicBlock {
    pub statements: Vec<ProtoStatement>,
    pub terminator: ProtoTerminator,
    pub is_cleanup: bool,
}

/// Prototype MIR body mirroring `Trusted.MirAst.CapturedMir`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoMirBody {
    pub def_path: String,
    pub basic_blocks: Vec<ProtoBasicBlock>,
}

/// Deduplicate and canonically order fault classes by `MirFaultClass::rank` (`0..11`),
/// matching `Anneal.FaultSiteCensusPrototype.dedupFaultClasses` 1-to-1.
pub fn dedup_fault_classes<I: IntoIterator<Item = MirFaultClass>>(raw: I) -> Vec<MirFaultClass> {
    let set: BTreeSet<MirFaultClass> = raw.into_iter().collect();
    set.into_iter().collect()
}

/// Fault classes triggered by a single `ProtoProjectionElem` (`censusProjectionElemFaultClasses`).
pub fn census_projection_elem_fault_classes(proj: &ProtoProjectionElem) -> Vec<MirFaultClass> {
    match proj {
        ProtoProjectionElem::Deref => vec![
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::PtrAlignMismatch,
            MirFaultClass::TreeBorrowsViolation,
        ],
        ProtoProjectionElem::Field(_) => Vec::new(),
        ProtoProjectionElem::Index(_) => {
            vec![MirFaultClass::BoundsCheck, MirFaultClass::UninitRead]
        }
        ProtoProjectionElem::ConstantIndex { .. } => vec![MirFaultClass::BoundsCheck],
        ProtoProjectionElem::Subslice { .. } => vec![MirFaultClass::BoundsCheck],
        ProtoProjectionElem::Downcast(_, _) => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoProjectionElem::OpaqueCast => Vec::new(),
        ProtoProjectionElem::UnwrapUnsafeBinder => Vec::new(),
    }
}

/// Fault classes triggered when reading from `place` (`censusPlaceReadFaultClasses`).
pub fn census_place_read_fault_classes(place: &ProtoPlace) -> Vec<MirFaultClass> {
    let mut out = vec![MirFaultClass::UninitRead];
    for proj in &place.projection {
        out.extend(census_projection_elem_fault_classes(proj));
    }
    out
}

/// Fault classes triggered when writing to `place` (`censusPlaceWriteFaultClasses`).
pub fn census_place_write_fault_classes(place: &ProtoPlace) -> Vec<MirFaultClass> {
    if place.projection.is_empty() {
        vec![
            MirFaultClass::StorageLiveProtected,
            MirFaultClass::TreeBorrowsViolation,
        ]
    } else {
        let mut out = vec![
            MirFaultClass::StorageLiveProtected,
            MirFaultClass::TreeBorrowsViolation,
            MirFaultClass::UninitRead,
        ];
        for proj in &place.projection {
            out.extend(census_projection_elem_fault_classes(proj));
        }
        out
    }
}

/// Fault classes triggered when borrowing `place` (`censusPlaceRefFaultClasses`).
pub fn census_place_ref_fault_classes(place: &ProtoPlace) -> Vec<MirFaultClass> {
    let mut out = vec![
        MirFaultClass::UninitRead,
        MirFaultClass::PtrDerefInvalid,
        MirFaultClass::PtrAlignMismatch,
        MirFaultClass::TreeBorrowsViolation,
    ];
    for proj in &place.projection {
        out.extend(census_projection_elem_fault_classes(proj));
    }
    out
}

/// Fault classes triggered by evaluating a `ProtoConstValue` (`censusConstValueFaultClasses`).
pub fn census_const_value_fault_classes(cv: &ProtoConstValue) -> Vec<MirFaultClass> {
    match cv {
        ProtoConstValue::Indirect { .. } => vec![
            MirFaultClass::BoundsCheck,
            MirFaultClass::ScalarNicheInvalid,
            MirFaultClass::UninitRead,
        ],
        _ => Vec::new(),
    }
}

/// Fault classes triggered by evaluating a `ProtoOperand` (`censusOperandFaultClasses`).
pub fn census_operand_fault_classes(op: &ProtoOperand) -> Vec<MirFaultClass> {
    match op {
        ProtoOperand::Copy(place) | ProtoOperand::Move(place) => {
            census_place_read_fault_classes(place)
        }
        ProtoOperand::Constant(cv) => census_const_value_fault_classes(cv),
    }
}

/// Fault classes triggered by a `ProtoBinOp` (`censusBinOpFaultClasses`).
pub fn census_bin_op_fault_classes(op: ProtoBinOp) -> Vec<MirFaultClass> {
    match op {
        ProtoBinOp::Add
        | ProtoBinOp::Sub
        | ProtoBinOp::Mul
        | ProtoBinOp::AddUnchecked
        | ProtoBinOp::SubUnchecked
        | ProtoBinOp::MulUnchecked
        | ProtoBinOp::AddWithOverflow
        | ProtoBinOp::SubWithOverflow
        | ProtoBinOp::MulWithOverflow => vec![MirFaultClass::ArithOverflow],
        ProtoBinOp::Div | ProtoBinOp::Rem => {
            vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero]
        }
        ProtoBinOp::Shl | ProtoBinOp::Shr | ProtoBinOp::ShlUnchecked | ProtoBinOp::ShrUnchecked => {
            vec![MirFaultClass::ShiftOverflow]
        }
        ProtoBinOp::Offset => vec![
            MirFaultClass::ArithOverflow,
            MirFaultClass::BoundsCheck,
            MirFaultClass::PtrDerefInvalid,
        ],
        ProtoBinOp::BitXor
        | ProtoBinOp::BitAnd
        | ProtoBinOp::BitOr
        | ProtoBinOp::Eq
        | ProtoBinOp::Lt
        | ProtoBinOp::Le
        | ProtoBinOp::Ne
        | ProtoBinOp::Ge
        | ProtoBinOp::Gt
        | ProtoBinOp::Cmp => vec![MirFaultClass::ScalarNicheInvalid],
    }
}

/// Fault classes triggered by a `ProtoUnOp` (`censusUnOpFaultClasses`).
pub fn census_un_op_fault_classes(op: ProtoUnOp) -> Vec<MirFaultClass> {
    match op {
        ProtoUnOp::Neg => vec![MirFaultClass::ArithOverflow],
        ProtoUnOp::Not => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoUnOp::PtrMetadata => vec![MirFaultClass::PtrDerefInvalid],
    }
}

/// Fault classes triggered by a `ProtoNullOp` (`censusNullOpFaultClasses`).
pub fn census_null_op_fault_classes(op: &ProtoNullOp) -> Vec<MirFaultClass> {
    match op {
        ProtoNullOp::SizeOf | ProtoNullOp::AlignOf | ProtoNullOp::OffsetOf(_) => {
            vec![MirFaultClass::ScalarNicheInvalid]
        }
        ProtoNullOp::UbChecks | ProtoNullOp::ContractChecks => Vec::new(),
    }
}

/// Fault classes triggered by a `ProtoCastKind` (`censusCastKindFaultClasses`).
pub fn census_cast_kind_fault_classes(kind: &ProtoCastKind) -> Vec<MirFaultClass> {
    match kind {
        ProtoCastKind::IntToInt
        | ProtoCastKind::FloatToInt
        | ProtoCastKind::FloatToFloat
        | ProtoCastKind::IntToFloat => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoCastKind::Transmute | ProtoCastKind::Subtype => {
            vec![MirFaultClass::ScalarNicheInvalid, MirFaultClass::UninitRead]
        }
        ProtoCastKind::PointerExposeProvenance
        | ProtoCastKind::PointerWithExposedProvenance
        | ProtoCastKind::PointerCoercion(_)
        | ProtoCastKind::PtrToPtr
        | ProtoCastKind::FnPtrToPtr => vec![
            MirFaultClass::BoundsCheck,
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::PtrAlignMismatch,
            MirFaultClass::ScalarNicheInvalid,
        ],
    }
}

/// Fault classes triggered by evaluating a `ProtoRvalue` (`censusRvalueFaultClasses`).
pub fn census_rvalue_fault_classes(rv: &ProtoRvalue) -> Vec<MirFaultClass> {
    match rv {
        ProtoRvalue::Use(op) => census_operand_fault_classes(op),
        ProtoRvalue::Repeat(op, _) => {
            let mut out = census_operand_fault_classes(op);
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
        ProtoRvalue::Ref { place, .. } | ProtoRvalue::RawPtr { place, .. } => {
            census_place_ref_fault_classes(place)
        }
        ProtoRvalue::ThreadLocalRef(_) => vec![MirFaultClass::PtrDerefInvalid],
        ProtoRvalue::Len(place) => {
            let mut out = census_place_read_fault_classes(place);
            out.push(MirFaultClass::BoundsCheck);
            out
        }
        ProtoRvalue::Cast(kind, op) => {
            let mut out = census_operand_fault_classes(op);
            out.extend(census_cast_kind_fault_classes(kind));
            out
        }
        ProtoRvalue::BinaryOp(op, lhs, rhs) => {
            let mut out = census_operand_fault_classes(lhs);
            out.extend(census_operand_fault_classes(rhs));
            out.extend(census_bin_op_fault_classes(*op));
            out
        }
        ProtoRvalue::NullaryOp(op) => census_null_op_fault_classes(op),
        ProtoRvalue::UnaryOp(op, val) => {
            let mut out = census_operand_fault_classes(val);
            out.extend(census_un_op_fault_classes(*op));
            out
        }
        ProtoRvalue::Discriminant(place) => {
            let mut out = census_place_read_fault_classes(place);
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
        ProtoRvalue::Aggregate(ops) => {
            let mut out = Vec::new();
            for op in ops {
                out.extend(census_operand_fault_classes(op));
            }
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
        ProtoRvalue::ShallowInitBox(op) => {
            let mut out = census_operand_fault_classes(op);
            out.push(MirFaultClass::PtrDerefInvalid);
            out.push(MirFaultClass::PtrAlignMismatch);
            out
        }
        ProtoRvalue::CopyForDeref(place) => {
            let mut out = census_place_read_fault_classes(place);
            out.push(MirFaultClass::PtrDerefInvalid);
            out
        }
        ProtoRvalue::WrapUnsafeBinder(op) => {
            let mut out = census_operand_fault_classes(op);
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
    }
}

/// Fault classes triggered by a `ProtoIntrinsic` (`censusIntrinsicFaultClasses`).
pub fn census_intrinsic_fault_classes(intr: &ProtoIntrinsic) -> Vec<MirFaultClass> {
    match intr {
        ProtoIntrinsic::Assume(op) => {
            let mut out = census_operand_fault_classes(op);
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
        ProtoIntrinsic::CopyNonOverlapping { src, dst, count } => {
            let mut out = census_operand_fault_classes(src);
            out.extend(census_operand_fault_classes(dst));
            out.extend(census_operand_fault_classes(count));
            out.extend([
                MirFaultClass::ArithOverflow,
                MirFaultClass::BoundsCheck,
                MirFaultClass::PtrDerefInvalid,
                MirFaultClass::PtrAlignMismatch,
                MirFaultClass::TreeBorrowsViolation,
                MirFaultClass::ScalarNicheInvalid,
                MirFaultClass::UninitRead,
            ]);
            out
        }
    }
}

/// Canonically ordered, duplicate-free `MirFaultClass` list for a `ProtoStatementKind`
/// (`censusStmtFaultClasses` in `FaultSiteCensusPrototype.lean`).
pub fn census_stmt_fault_classes(kind: &ProtoStatementKind) -> Vec<MirFaultClass> {
    let raw: Vec<MirFaultClass> = match kind {
        ProtoStatementKind::Nop
        | ProtoStatementKind::Coverage
        | ProtoStatementKind::ConstEvalCounter
        | ProtoStatementKind::BackwardIncompatibleDropHint(_) => Vec::new(),
        ProtoStatementKind::StorageLive(_) | ProtoStatementKind::StorageDead(_) => {
            vec![MirFaultClass::StorageLiveProtected]
        }
        ProtoStatementKind::PlaceMention(place) | ProtoStatementKind::Deinit(place) => {
            let mut v = vec![MirFaultClass::UninitRead];
            for proj in &place.projection {
                v.extend(census_projection_elem_fault_classes(proj));
            }
            v
        }
        ProtoStatementKind::Retag(place) => {
            let mut v = census_place_read_fault_classes(place);
            v.extend([
                MirFaultClass::BoundsCheck,
                MirFaultClass::PtrDerefInvalid,
                MirFaultClass::PtrAlignMismatch,
                MirFaultClass::TreeBorrowsViolation,
            ]);
            v
        }
        ProtoStatementKind::SetDiscriminant(place, _) => {
            if place.projection.is_empty() {
                vec![MirFaultClass::ScalarNicheInvalid, MirFaultClass::UninitRead]
            } else {
                let mut v = census_place_read_fault_classes(place);
                v.extend(census_place_write_fault_classes(place));
                v.push(MirFaultClass::ScalarNicheInvalid);
                v
            }
        }
        ProtoStatementKind::Intrinsic(intr) => census_intrinsic_fault_classes(intr),
        ProtoStatementKind::Assign(dst, rv) => {
            let mut v = census_place_write_fault_classes(dst);
            v.extend(census_rvalue_fault_classes(rv));
            v
        }
    };
    dedup_fault_classes(raw)
}

/// Intra-procedural successor basic-block indices targeted by `ProtoUnwindAction`.
pub fn unwind_targets(unwind: ProtoUnwindAction) -> Vec<usize> {
    match unwind {
        ProtoUnwindAction::Cleanup(bb) => vec![bb],
        _ => Vec::new(),
    }
}

/// All intra-procedural successor basic-block indices targeted by `ProtoTerminatorKind`
/// (`terminatorTargets` in `FaultSiteCensusPrototype.lean`).
pub fn terminator_targets(kind: &ProtoTerminatorKind) -> Vec<usize> {
    match kind {
        ProtoTerminatorKind::Goto(target) => vec![*target],
        ProtoTerminatorKind::SwitchInt(_, targets) => {
            let mut out = vec![targets.otherwise];
            out.extend(targets.branches.iter().map(|(_, t)| *t));
            out
        }
        ProtoTerminatorKind::UnwindResume
        | ProtoTerminatorKind::UnwindTerminate
        | ProtoTerminatorKind::Return
        | ProtoTerminatorKind::Unreachable
        | ProtoTerminatorKind::TailCall { .. } => Vec::new(),
        ProtoTerminatorKind::Drop { target, unwind, .. }
        | ProtoTerminatorKind::Assert { target, unwind, .. } => {
            let mut out = vec![*target];
            out.extend(unwind_targets(*unwind));
            out
        }
        ProtoTerminatorKind::Call {
            target: Some(target_bb),
            unwind,
            ..
        } => {
            let mut out = vec![*target_bb];
            out.extend(unwind_targets(*unwind));
            out
        }
        ProtoTerminatorKind::Call {
            target: None,
            unwind,
            ..
        } => unwind_targets(*unwind),
        ProtoTerminatorKind::InlineAsm {
            targets, unwind, ..
        } => {
            let mut out = targets.clone();
            out.extend(unwind_targets(*unwind));
            out
        }
    }
}

/// Additional fault classes contributed by a direct call target `def_path` in
/// `TerminatorKind::Call`, matching `censusCalleeDefPathFaultClasses` in Lean 4.
pub fn census_callee_def_path_fault_classes(def_path: &str) -> Vec<MirFaultClass> {
    if matches!(
        def_path,
        "core::hint::unreachable_unchecked"
            | "std::hint::unreachable_unchecked"
            | "core::intrinsics::unreachable"
    ) {
        return vec![MirFaultClass::UnreachableTerminator];
    }
    if matches!(
        def_path,
        "core::intrinsics::exact_div" | "std::intrinsics::exact_div"
    ) {
        return vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero];
    }
    let intrinsic_suffix = def_path
        .strip_prefix("core::intrinsics::")
        .or_else(|| def_path.strip_prefix("std::intrinsics::"));
    match intrinsic_suffix {
        Some("arith_offset") => vec![
            MirFaultClass::ArithOverflow,
            MirFaultClass::BoundsCheck,
            MirFaultClass::PtrDerefInvalid,
        ],
        Some("unchecked_add" | "unchecked_sub" | "unchecked_mul") => {
            vec![MirFaultClass::ArithOverflow]
        }
        Some("unchecked_div" | "unchecked_rem") => {
            vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero]
        }
        Some("unchecked_shl" | "unchecked_shr") => vec![MirFaultClass::ShiftOverflow],
        Some("ctlz_nonzero" | "cttz_nonzero") => vec![MirFaultClass::ScalarNicheInvalid],
        Some("size_of_val" | "align_of_val") => vec![
            MirFaultClass::ArithOverflow,
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::ScalarNicheInvalid,
        ],
        Some("const_eval_select") => vec![
            MirFaultClass::CallAbiMismatch,
            MirFaultClass::ScalarNicheInvalid,
        ],
        _ => Vec::new(),
    }
}

/// Canonically ordered, duplicate-free `MirFaultClass` list for a `ProtoTerminatorKind`
/// (`censusTerminatorFaultClasses` in `FaultSiteCensusPrototype.lean`).
pub fn census_terminator_fault_classes(
    num_blocks: usize,
    kind: &ProtoTerminatorKind,
) -> Vec<MirFaultClass> {
    let target_oob: Vec<MirFaultClass> = if terminator_targets(kind)
        .into_iter()
        .any(|t| t >= num_blocks)
    {
        vec![MirFaultClass::BoundsCheck]
    } else {
        Vec::new()
    };

    let raw: Vec<MirFaultClass> = match kind {
        ProtoTerminatorKind::Goto(_) => target_oob,
        ProtoTerminatorKind::UnwindTerminate | ProtoTerminatorKind::InlineAsm { .. } => Vec::new(),
        ProtoTerminatorKind::Unreachable => vec![MirFaultClass::UnreachableTerminator],
        ProtoTerminatorKind::UnwindResume => vec![MirFaultClass::CallAbiMismatch],
        ProtoTerminatorKind::Return => vec![
            MirFaultClass::UninitRead,
            MirFaultClass::TreeBorrowsViolation,
            MirFaultClass::CallAbiMismatch,
        ],
        ProtoTerminatorKind::SwitchInt(discr, _) => {
            let mut v = census_operand_fault_classes(discr);
            v.push(MirFaultClass::ScalarNicheInvalid);
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::Drop { place, .. } => {
            let mut v = census_place_read_fault_classes(place);
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::Assert { cond, unwind, .. } => {
            let mut v = census_operand_fault_classes(cond);
            v.push(MirFaultClass::ScalarNicheInvalid);
            match unwind {
                ProtoUnwindAction::Unreachable => v.extend([
                    MirFaultClass::ArithOverflow,
                    MirFaultClass::DivRemByZero,
                    MirFaultClass::ShiftOverflow,
                    MirFaultClass::BoundsCheck,
                    MirFaultClass::UnreachableTerminator,
                ]),
                _ => v.push(MirFaultClass::CallAbiMismatch),
            }
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::Call {
            func,
            args,
            destination,
            unwind,
            ..
        } => {
            let mut v = census_operand_fault_classes(func);
            for arg in args {
                v.extend(census_operand_fault_classes(arg));
            }
            v.extend(census_place_write_fault_classes(destination));
            v.push(MirFaultClass::CallAbiMismatch);
            match func.extract_callee_def_path() {
                Some(def_path) => v.extend(census_callee_def_path_fault_classes(def_path)),
                None => v.push(MirFaultClass::PtrDerefInvalid),
            }
            if matches!(unwind, ProtoUnwindAction::Unreachable) {
                v.push(MirFaultClass::UnreachableTerminator);
            }
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::TailCall { func, args } => {
            let mut v = census_operand_fault_classes(func);
            for arg in args {
                v.extend(census_operand_fault_classes(arg));
            }
            v.push(MirFaultClass::CallAbiMismatch);
            if func.extract_callee_def_path().is_none() {
                v.push(MirFaultClass::PtrDerefInvalid);
            }
            v
        }
    };
    dedup_fault_classes(raw)
}

/// Independent syntactic fault-site census of a `ProtoMirBody`
/// (`censusMirBodyFaultSites` in `FaultSiteCensusPrototype.lean`).
pub fn census_mir_fault_sites(body: &ProtoMirBody) -> Vec<FaultSite> {
    let num_blocks = body.basic_blocks.len();
    let mut sites = Vec::new();
    for (block_idx, bb) in body.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            for fault_class in census_stmt_fault_classes(&stmt.kind) {
                sites.push(FaultSite::new(block_idx, stmt_idx, fault_class));
            }
        }
        let term_idx = bb.statements.len();
        for fault_class in census_terminator_fault_classes(num_blocks, &bb.terminator.kind) {
            sites.push(FaultSite::new(block_idx, term_idx, fault_class));
        }
    }
    sites
}

// ============================================================================
// 4. Conversion from `anneal_rustc_capture::lean_emit::IrCapturedMir`
// ============================================================================

impl ProtoMirBody {
    /// Convert an `IrCapturedMir` (removing `Retag` statements to match
    /// `render_basic_block_data` in `lean_emit.rs` when `strip_retags` is true)
    /// into a `ProtoMirBody`.
    pub fn from_ir_captured_mir(mir: &IrCapturedMir, strip_retags: bool) -> Self {
        let basic_blocks = mir
            .basic_blocks
            .iter()
            .map(|bb| convert_ir_basic_block(bb, strip_retags))
            .collect();
        Self {
            def_path: mir.def_path.clone(),
            basic_blocks,
        }
    }
}

/// Run `census_mir_fault_sites` over an `IrCapturedMir` (with `strip_retags = true`
/// matching `emit_mir_lean_module`'s `render_basic_block_data`).
pub fn census_ir_captured_mir(mir: &IrCapturedMir) -> Vec<FaultSite> {
    let proto = ProtoMirBody::from_ir_captured_mir(mir, true);
    census_mir_fault_sites(&proto)
}

fn convert_ir_basic_block(bb: &IrBasicBlockData, strip_retags: bool) -> ProtoBasicBlock {
    let statements = bb
        .statements
        .iter()
        .filter(|s| !(strip_retags && matches!(s.kind, IrStatementKind::Retag(_, _))))
        .map(convert_ir_statement)
        .collect();
    ProtoBasicBlock {
        statements,
        terminator: convert_ir_terminator(&bb.terminator),
        is_cleanup: bb.is_cleanup,
    }
}

fn convert_ir_statement(stmt: &IrStatement) -> ProtoStatement {
    let kind = match &stmt.kind {
        IrStatementKind::Assign(p, rv) => {
            ProtoStatementKind::Assign(convert_ir_place(p), convert_ir_rvalue(rv))
        }
        IrStatementKind::SetDiscriminant(p, idx) => {
            ProtoStatementKind::SetDiscriminant(convert_ir_place(p), *idx)
        }
        IrStatementKind::Deinit(p) => ProtoStatementKind::Deinit(convert_ir_place(p)),
        IrStatementKind::StorageLive(l) => ProtoStatementKind::StorageLive(*l),
        IrStatementKind::StorageDead(l) => ProtoStatementKind::StorageDead(*l),
        IrStatementKind::Retag(_, p) => ProtoStatementKind::Retag(convert_ir_place(p)),
        IrStatementKind::PlaceMention(p) => ProtoStatementKind::PlaceMention(convert_ir_place(p)),
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
            ProtoStatementKind::Intrinsic(ProtoIntrinsic::Assume(convert_ir_operand(op)))
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
            src,
            dst,
            count,
        }) => ProtoStatementKind::Intrinsic(ProtoIntrinsic::CopyNonOverlapping {
            src: convert_ir_operand(src),
            dst: convert_ir_operand(dst),
            count: convert_ir_operand(count),
        }),
        IrStatementKind::Coverage => ProtoStatementKind::Coverage,
        IrStatementKind::ConstEvalCounter => ProtoStatementKind::ConstEvalCounter,
        IrStatementKind::BackwardIncompatibleDropHint(p) => {
            ProtoStatementKind::BackwardIncompatibleDropHint(convert_ir_place(p))
        }
        IrStatementKind::Nop => ProtoStatementKind::Nop,
    };
    ProtoStatement {
        kind,
        span: stmt.span.clone(),
    }
}

fn convert_ir_place(p: &IrPlace) -> ProtoPlace {
    ProtoPlace {
        local_: p.local_,
        projection: p.projection.iter().map(convert_ir_proj).collect(),
    }
}

fn convert_ir_proj(proj: &IrProjectionElem) -> ProtoProjectionElem {
    match proj {
        IrProjectionElem::Deref => ProtoProjectionElem::Deref,
        IrProjectionElem::Field(idx, _) => ProtoProjectionElem::Field(*idx),
        IrProjectionElem::Index(loc) => ProtoProjectionElem::Index(*loc),
        IrProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => ProtoProjectionElem::ConstantIndex {
            offset: *offset,
            min_length: *min_length,
            from_end: *from_end,
        },
        IrProjectionElem::Subslice {
            from_idx,
            to_idx,
            from_end,
        } => ProtoProjectionElem::Subslice {
            from_idx: *from_idx,
            to_idx: *to_idx,
            from_end: *from_end,
        },
        IrProjectionElem::Downcast(sym, idx) => ProtoProjectionElem::Downcast(sym.clone(), *idx),
        IrProjectionElem::OpaqueCast(_) => ProtoProjectionElem::OpaqueCast,
        IrProjectionElem::UnwrapUnsafeBinder(_) => ProtoProjectionElem::UnwrapUnsafeBinder,
    }
}

fn convert_ir_operand(op: &IrOperand) -> ProtoOperand {
    match op {
        IrOperand::Copy(p) => ProtoOperand::Copy(convert_ir_place(p)),
        IrOperand::Move(p) => ProtoOperand::Move(convert_ir_place(p)),
        IrOperand::Constant(co) => ProtoOperand::Constant(convert_ir_const_operand(co)),
    }
}

fn convert_ir_const_operand(co: &IrConstOperand) -> ProtoConstValue {
    let fn_def_path = match &co.ty.kind {
        anneal_rustc_capture::lean_emit::IrRigidTy::FnDef(path, _) => Some(path.clone()),
        _ => None,
    };
    match &co.val {
        IrConstValue::ZeroSized => ProtoConstValue::ZeroSized { fn_def_path },
        IrConstValue::Scalar(IrConstScalar::Int(si)) => ProtoConstValue::ScalarInt {
            bits: si.bits,
            size_bytes: si.size_bytes,
        },
        IrConstValue::Scalar(IrConstScalar::Ptr(ptr, size)) => ProtoConstValue::ScalarPtr {
            alloc_id: ptr.alloc_id,
            offset_bytes: ptr.offset_bytes,
            size: *size,
        },
        IrConstValue::Slice { meta, .. } => ProtoConstValue::Slice { meta: *meta },
        IrConstValue::Indirect {
            alloc_id,
            offset_bytes,
        } => ProtoConstValue::Indirect {
            alloc_id: *alloc_id,
            offset_bytes: *offset_bytes,
        },
        IrConstValue::Unevaluated(p) => ProtoConstValue::Unevaluated(p.clone()),
    }
}

fn convert_ir_rvalue(rv: &IrRvalue) -> ProtoRvalue {
    match rv {
        IrRvalue::Use(op) => ProtoRvalue::Use(convert_ir_operand(op)),
        IrRvalue::Repeat(op, n) => ProtoRvalue::Repeat(convert_ir_operand(op), *n),
        IrRvalue::Ref(bk, p) => ProtoRvalue::Ref {
            mutable: matches!(bk, IrBorrowKind::Mut { .. }),
            place: convert_ir_place(p),
        },
        IrRvalue::ThreadLocalRef(s) => ProtoRvalue::ThreadLocalRef(s.clone()),
        IrRvalue::RawPtr(m, p) => ProtoRvalue::RawPtr {
            mutable: matches!(m, IrMutability::Mut),
            place: convert_ir_place(p),
        },
        IrRvalue::Len(p) => ProtoRvalue::Len(convert_ir_place(p)),
        IrRvalue::Cast(ck, op, _) => {
            let k = match ck {
                IrCastKind::PointerExposeProvenance => ProtoCastKind::PointerExposeProvenance,
                IrCastKind::PointerWithExposedProvenance => {
                    ProtoCastKind::PointerWithExposedProvenance
                }
                IrCastKind::PointerCoercion(s) => ProtoCastKind::PointerCoercion(s.clone()),
                IrCastKind::IntToInt => ProtoCastKind::IntToInt,
                IrCastKind::FloatToInt => ProtoCastKind::FloatToInt,
                IrCastKind::FloatToFloat => ProtoCastKind::FloatToFloat,
                IrCastKind::IntToFloat => ProtoCastKind::IntToFloat,
                IrCastKind::PtrToPtr => ProtoCastKind::PtrToPtr,
                IrCastKind::FnPtrToPtr => ProtoCastKind::FnPtrToPtr,
                IrCastKind::Transmute => ProtoCastKind::Transmute,
                IrCastKind::Subtype => ProtoCastKind::Subtype,
            };
            ProtoRvalue::Cast(k, convert_ir_operand(op))
        }
        IrRvalue::BinaryOp(op, lhs, rhs) => {
            let bop = match op {
                IrBinOp::Add => ProtoBinOp::Add,
                IrBinOp::AddUnchecked => ProtoBinOp::AddUnchecked,
                IrBinOp::AddWithOverflow => ProtoBinOp::AddWithOverflow,
                IrBinOp::Sub => ProtoBinOp::Sub,
                IrBinOp::SubUnchecked => ProtoBinOp::SubUnchecked,
                IrBinOp::SubWithOverflow => ProtoBinOp::SubWithOverflow,
                IrBinOp::Mul => ProtoBinOp::Mul,
                IrBinOp::MulUnchecked => ProtoBinOp::MulUnchecked,
                IrBinOp::MulWithOverflow => ProtoBinOp::MulWithOverflow,
                IrBinOp::Div => ProtoBinOp::Div,
                IrBinOp::Rem => ProtoBinOp::Rem,
                IrBinOp::BitXor => ProtoBinOp::BitXor,
                IrBinOp::BitAnd => ProtoBinOp::BitAnd,
                IrBinOp::BitOr => ProtoBinOp::BitOr,
                IrBinOp::Shl => ProtoBinOp::Shl,
                IrBinOp::ShlUnchecked => ProtoBinOp::ShlUnchecked,
                IrBinOp::Shr => ProtoBinOp::Shr,
                IrBinOp::ShrUnchecked => ProtoBinOp::ShrUnchecked,
                IrBinOp::Eq => ProtoBinOp::Eq,
                IrBinOp::Lt => ProtoBinOp::Lt,
                IrBinOp::Le => ProtoBinOp::Le,
                IrBinOp::Ne => ProtoBinOp::Ne,
                IrBinOp::Ge => ProtoBinOp::Ge,
                IrBinOp::Gt => ProtoBinOp::Gt,
                IrBinOp::Cmp => ProtoBinOp::Cmp,
                IrBinOp::Offset => ProtoBinOp::Offset,
            };
            ProtoRvalue::BinaryOp(bop, convert_ir_operand(lhs), convert_ir_operand(rhs))
        }
        IrRvalue::NullaryOp(nop, _) => {
            let n = match nop {
                IrNullOp::SizeOf => ProtoNullOp::SizeOf,
                IrNullOp::AlignOf => ProtoNullOp::AlignOf,
                IrNullOp::OffsetOf(v) => ProtoNullOp::OffsetOf(v.clone()),
                IrNullOp::UbChecks => ProtoNullOp::UbChecks,
                IrNullOp::ContractChecks => ProtoNullOp::ContractChecks,
            };
            ProtoRvalue::NullaryOp(n)
        }
        IrRvalue::UnaryOp(uop, op) => {
            let u = match uop {
                IrUnOp::Not => ProtoUnOp::Not,
                IrUnOp::Neg => ProtoUnOp::Neg,
                IrUnOp::PtrMetadata => ProtoUnOp::PtrMetadata,
            };
            ProtoRvalue::UnaryOp(u, convert_ir_operand(op))
        }
        IrRvalue::Discriminant(p) => ProtoRvalue::Discriminant(convert_ir_place(p)),
        IrRvalue::Aggregate(_ak, ops) => {
            let _ = match _ak {
                IrAggregateKind::Tuple => {}
                _ => {}
            };
            ProtoRvalue::Aggregate(ops.iter().map(convert_ir_operand).collect())
        }
        IrRvalue::ShallowInitBox(op, _) => ProtoRvalue::ShallowInitBox(convert_ir_operand(op)),
        IrRvalue::CopyForDeref(p) => ProtoRvalue::CopyForDeref(convert_ir_place(p)),
        IrRvalue::WrapUnsafeBinder(op, _) => ProtoRvalue::WrapUnsafeBinder(convert_ir_operand(op)),
    }
}

fn convert_ir_unwind(ua: IrUnwindAction) -> ProtoUnwindAction {
    match ua {
        IrUnwindAction::Cleanup(bb) => ProtoUnwindAction::Cleanup(bb),
        IrUnwindAction::Unreachable => ProtoUnwindAction::Unreachable,
        IrUnwindAction::Terminate => ProtoUnwindAction::Terminate,
        IrUnwindAction::Continue => ProtoUnwindAction::Continue,
    }
}

fn convert_ir_terminator(term: &IrTerminator) -> ProtoTerminator {
    let kind = match &term.kind {
        IrTerminatorKind::Goto(bb) => ProtoTerminatorKind::Goto(*bb),
        IrTerminatorKind::SwitchInt(op, IrSwitchTargets { branches, otherwise }) => {
            ProtoTerminatorKind::SwitchInt(
                convert_ir_operand(op),
                ProtoSwitchTargets {
                    branches: branches.clone(),
                    otherwise: *otherwise,
                },
            )
        }
        IrTerminatorKind::UnwindResume => ProtoTerminatorKind::UnwindResume,
        IrTerminatorKind::UnwindTerminate => ProtoTerminatorKind::UnwindTerminate,
        IrTerminatorKind::Return => ProtoTerminatorKind::Return,
        IrTerminatorKind::Unreachable => ProtoTerminatorKind::Unreachable,
        IrTerminatorKind::Drop {
            place,
            target,
            unwind,
        } => ProtoTerminatorKind::Drop {
            place: convert_ir_place(place),
            target: *target,
            unwind: convert_ir_unwind(*unwind),
        },
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => ProtoTerminatorKind::Call {
            func: convert_ir_operand(func),
            args: args.iter().map(convert_ir_operand).collect(),
            destination: convert_ir_place(destination),
            target: *target,
            unwind: convert_ir_unwind(*unwind),
        },
        IrTerminatorKind::TailCall { func, args } => ProtoTerminatorKind::TailCall {
            func: convert_ir_operand(func),
            args: args.iter().map(convert_ir_operand).collect(),
        },
        IrTerminatorKind::Assert {
            cond,
            expected,
            target,
            unwind,
        } => ProtoTerminatorKind::Assert {
            cond: convert_ir_operand(cond),
            expected: *expected,
            target: *target,
            unwind: convert_ir_unwind(*unwind),
        },
        IrTerminatorKind::InlineAsm {
            template,
            targets,
            unwind,
        } => ProtoTerminatorKind::InlineAsm {
            template: template.clone(),
            targets: targets.clone(),
            unwind: convert_ir_unwind(*unwind),
        },
    };
    ProtoTerminator {
        kind,
        span: term.span.clone(),
    }
}

// ============================================================================
// 5. Fail-Closed Lean 4 `Mir/<Item>.lean` Lexer & Recursive-Descent Scanner
// ============================================================================

/// Fail-closed error returned when a Lean `CapturedMir` source module cannot be
/// cleanly lexed or parsed into a `ProtoMirBody`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusScanError {
    /// Unterminated nested `/- ... -/` block comment.
    UnterminatedBlockComment,
    /// Unterminated `"..."` string literal.
    UnterminatedStringLiteral,
    /// Unterminated `r#"..."#` raw string literal.
    UnterminatedRawString,
    /// Unterminated `s!"..."` interpolated string literal.
    UnterminatedInterpolatedString,
    /// Unterminated or multi-line `«...»` guillemet identifier.
    UnterminatedGuillemetIdent,
    /// Target `def <name> : CapturedMir :=` declaration was not found (or appeared multiple times).
    MissingOrDuplicateCapturedMirDef(String),
    /// Malformed or non-inline Lean syntax inside `CapturedMir`.
    MalformedCapturedMirSyntax(String),
}

impl fmt::Display for CensusScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CensusScanError::UnterminatedBlockComment => {
                f.write_str("unterminated Lean block comment `/- ... -/`")
            }
            CensusScanError::UnterminatedStringLiteral => {
                f.write_str("unterminated Lean string literal")
            }
            CensusScanError::UnterminatedRawString => {
                f.write_str("unterminated Lean raw string literal")
            }
            CensusScanError::UnterminatedInterpolatedString => {
                f.write_str("unterminated Lean interpolated string literal")
            }
            CensusScanError::UnterminatedGuillemetIdent => {
                f.write_str("unterminated or multi-line Lean guillemet identifier `«...»`")
            }
            CensusScanError::MissingOrDuplicateCapturedMirDef(msg) => {
                write!(f, "missing or duplicate CapturedMir definition: {msg}")
            }
            CensusScanError::MalformedCapturedMirSyntax(msg) => {
                write!(f, "malformed or non-inline CapturedMir syntax: {msg}")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LeanToken {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semicolon,
    ColonEq,
    Colon,
    Dot,
    Ident(String),
    NatLit(u128),
    StrLit(String),
}

fn is_lean_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '!' | '?')
}

/// Tokenize Lean 4 source text while stripping `--` line comments and nested
/// `/- ... -/` block comments, preserving `"..."`, `r#"..."#`, `s!"..."`, char
/// literals `'...'`, and `«...»` guillemet identifiers, and failing closed on
/// any unterminated comment or literal.
fn tokenize_lean_source(src: &str) -> Result<Vec<LeanToken>, CensusScanError> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0;
    let mut tokens = Vec::new();

    while i < n {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }

        // Line comment `-- ...`
        if ch == '-' && i + 1 < n && chars[i + 1] == '-' {
            i += 2;
            while i < n && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }

        // Nested block comment `/- ... -/`
        if ch == '/' && i + 1 < n && chars[i + 1] == '-' {
            i += 2;
            let mut depth = 1usize;
            while i < n && depth > 0 {
                if chars[i] == '/' && i + 1 < n && chars[i + 1] == '-' {
                    depth += 1;
                    i += 2;
                } else if chars[i] == '-' && i + 1 < n && chars[i + 1] == '/' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if depth != 0 {
                return Err(CensusScanError::UnterminatedBlockComment);
            }
            continue;
        }

        // Character literal `'x'` or `'\x'` (so `'«'`, `'"'`, `'/'` are not mis-tokenized)
        if ch == '\'' {
            let prev_is_ident = i > 0 && is_lean_ident_continue(chars[i - 1]);
            if !prev_is_ident && i + 2 < n {
                if chars[i + 1] == '\\' {
                    let mut end = i + 2;
                    while end < n && chars[end] != '\'' && chars[end] != '\n' {
                        end += 1;
                    }
                    if end < n && chars[end] == '\'' {
                        i = end + 1;
                        tokens.push(LeanToken::StrLit(String::new()));
                        continue;
                    }
                } else if chars[i + 2] == '\'' && chars[i + 1] != '\n' {
                    i += 3;
                    tokens.push(LeanToken::StrLit(String::new()));
                    continue;
                }
            }
        }

        // Guillemet identifier `«...»` (or `.«...»` inside a dotted identifier)
        if ch == '«' {
            let (ident, next_i) = lex_dotted_ident(&chars, i)?;
            tokens.push(LeanToken::Ident(ident));
            i = next_i;
            continue;
        }

        // Raw string literal `r"..."` or `r#"..."#`
        if ch == 'r' && i + 1 < n && (chars[i + 1] == '"' || chars[i + 1] == '#') {
            let mut hashes = 0usize;
            let mut k = i + 1;
            while k < n && chars[k] == '#' {
                hashes += 1;
                k += 1;
            }
            if k < n && chars[k] == '"' {
                k += 1;
                let mut content = String::new();
                let mut closed = false;
                while k < n {
                    if chars[k] == '"' {
                        let mut m = 0usize;
                        while m < hashes && k + 1 + m < n && chars[k + 1 + m] == '#' {
                            m += 1;
                        }
                        if m == hashes {
                            k += 1 + hashes;
                            closed = true;
                            break;
                        }
                    }
                    content.push(chars[k]);
                    k += 1;
                }
                if !closed {
                    return Err(CensusScanError::UnterminatedRawString);
                }
                tokens.push(LeanToken::StrLit(content));
                i = k;
                continue;
            }
        }

        // Interpolated string `s!"..."` (with `{...}` interpolation nesting)
        if (ch == 's' || ch == 'f') && i + 2 < n && chars[i + 1] == '!' && chars[i + 2] == '"' {
            let (content, next_i) = lex_interpolated_string(&chars, i + 3)?;
            tokens.push(LeanToken::StrLit(content));
            i = next_i;
            continue;
        }

        // Standard string literal `"..."`
        if ch == '"' {
            let (content, next_i) = lex_standard_string(&chars, i + 1)?;
            tokens.push(LeanToken::StrLit(content));
            i = next_i;
            continue;
        }

        // Punctuation & delimiters
        match ch {
            '(' => {
                tokens.push(LeanToken::LParen);
                i += 1;
                continue;
            }
            ')' => {
                tokens.push(LeanToken::RParen);
                i += 1;
                continue;
            }
            '{' => {
                tokens.push(LeanToken::LBrace);
                i += 1;
                continue;
            }
            '}' => {
                tokens.push(LeanToken::RBrace);
                i += 1;
                continue;
            }
            '[' => {
                tokens.push(LeanToken::LBracket);
                i += 1;
                continue;
            }
            ']' => {
                tokens.push(LeanToken::RBracket);
                i += 1;
                continue;
            }
            ',' => {
                tokens.push(LeanToken::Comma);
                i += 1;
                continue;
            }
            ';' => {
                tokens.push(LeanToken::Semicolon);
                i += 1;
                continue;
            }
            ':' => {
                if i + 1 < n && chars[i + 1] == '=' {
                    tokens.push(LeanToken::ColonEq);
                    i += 2;
                } else {
                    tokens.push(LeanToken::Colon);
                    i += 1;
                }
                continue;
            }
            '.' => {
                tokens.push(LeanToken::Dot);
                i += 1;
                continue;
            }
            _ => {}
        }

        // Numeric literal
        if ch.is_ascii_digit() {
            let start = i;
            i += 1;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let raw_num: String = chars[start..i].iter().filter(|&&c| c != '_').collect();
            let parsed = if let Some(hex) = raw_num
                .strip_prefix("0x")
                .or_else(|| raw_num.strip_prefix("0X"))
            {
                u128::from_str_radix(hex, 16)
            } else if let Some(bin) = raw_num
                .strip_prefix("0b")
                .or_else(|| raw_num.strip_prefix("0B"))
            {
                u128::from_str_radix(bin, 2)
            } else if let Some(oct) = raw_num
                .strip_prefix("0o")
                .or_else(|| raw_num.strip_prefix("0O"))
            {
                u128::from_str_radix(oct, 8)
            } else {
                raw_num.parse::<u128>()
            };
            match parsed {
                Ok(val) => tokens.push(LeanToken::NatLit(val)),
                Err(_) => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "invalid numeric literal `{raw_num}`"
                    )));
                }
            }
            continue;
        }

        // Identifier (possibly dotted with segments and `«...»`)
        if ch.is_alphabetic() || ch == '_' {
            let (ident, next_i) = lex_dotted_ident(&chars, i)?;
            tokens.push(LeanToken::Ident(ident));
            i = next_i;
            continue;
        }

        // Any other operator/symbol character: consume as symbol token so non-BasicBlock
        // declarations (such as theorems or comments) do not break top-level scanning,
        // while `CapturedMir` parsing still fails closed if it encounters an unexpected token.
        let start = i;
        i += 1;
        while i < n
            && !chars[i].is_whitespace()
            && !matches!(
                chars[i],
                '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';' | ':' | '.' | '"' | '«'
            )
        {
            if (chars[i] == '-' && i + 1 < n && chars[i + 1] == '-')
                || (chars[i] == '/' && i + 1 < n && chars[i + 1] == '-')
            {
                break;
            }
            i += 1;
        }
        let sym: String = chars[start..i].iter().collect();
        tokens.push(LeanToken::Ident(sym));
    }

    Ok(tokens)
}

fn lex_dotted_ident(chars: &[char], start: usize) -> Result<(String, usize), CensusScanError> {
    let n = chars.len();
    let mut i = start;
    let mut out = String::new();
    loop {
        if i < n && chars[i] == '«' {
            i += 1;
            let seg_start = i;
            while i < n && chars[i] != '»' && chars[i] != '\n' {
                i += 1;
            }
            if i >= n || chars[i] != '»' {
                return Err(CensusScanError::UnterminatedGuillemetIdent);
            }
            let seg: String = chars[seg_start..i].iter().collect();
            out.push_str(&seg);
            i += 1;
        } else {
            let seg_start = i;
            while i < n && is_lean_ident_continue(chars[i]) {
                i += 1;
            }
            if i == seg_start {
                return Err(CensusScanError::MalformedCapturedMirSyntax(
                    "empty identifier segment".to_string(),
                ));
            }
            let seg: String = chars[seg_start..i].iter().collect();
            out.push_str(&seg);
        }
        if i + 1 < n
            && chars[i] == '.'
            && (chars[i + 1].is_alphabetic() || chars[i + 1] == '_' || chars[i + 1] == '«')
        {
            out.push('.');
            i += 1;
        } else {
            break;
        }
    }
    Ok((out, i))
}

fn lex_standard_string(
    chars: &[char],
    after_open_quote: usize,
) -> Result<(String, usize), CensusScanError> {
    let n = chars.len();
    let mut i = after_open_quote;
    let mut out = String::new();
    while i < n {
        let ch = chars[i];
        if ch == '"' {
            return Ok((out, i + 1));
        }
        if ch == '\\' {
            i += 1;
            if i >= n {
                return Err(CensusScanError::UnterminatedStringLiteral);
            }
            match chars[i] {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'x' if i + 2 < n => {
                    let hex: String = chars[i + 1..=i + 2].iter().collect();
                    if let Ok(b) = u8::from_str_radix(&hex, 16) {
                        out.push(b as char);
                        i += 2;
                    } else {
                        out.push('x');
                    }
                }
                other => out.push(other),
            }
            i += 1;
        } else {
            out.push(ch);
            i += 1;
        }
    }
    Err(CensusScanError::UnterminatedStringLiteral)
}

fn lex_interpolated_string(
    chars: &[char],
    after_open_quote: usize,
) -> Result<(String, usize), CensusScanError> {
    let n = chars.len();
    let mut i = after_open_quote;
    let mut out = String::new();
    while i < n {
        let ch = chars[i];
        if ch == '"' {
            return Ok((out, i + 1));
        }
        if ch == '\\' {
            i += 1;
            if i >= n {
                return Err(CensusScanError::UnterminatedInterpolatedString);
            }
            out.push(chars[i]);
            i += 1;
            continue;
        }
        if ch == '{' {
            // Walk nested `{ ... }` inside string interpolation, respecting nested strings/comments.
            let mut brace_depth = 1usize;
            out.push('{');
            i += 1;
            while i < n && brace_depth > 0 {
                if chars[i] == '"' {
                    let (inner_s, next_i) = lex_standard_string(chars, i + 1)
                        .map_err(|_| CensusScanError::UnterminatedInterpolatedString)?;
                    out.push('"');
                    out.push_str(&inner_s);
                    out.push('"');
                    i = next_i;
                } else if chars[i] == '{' {
                    brace_depth += 1;
                    out.push('{');
                    i += 1;
                } else if chars[i] == '}' {
                    brace_depth -= 1;
                    out.push('}');
                    i += 1;
                } else {
                    out.push(chars[i]);
                    i += 1;
                }
            }
            if brace_depth != 0 {
                return Err(CensusScanError::UnterminatedInterpolatedString);
            }
            continue;
        }
        out.push(ch);
        i += 1;
    }
    Err(CensusScanError::UnterminatedInterpolatedString)
}

/// Recursive-descent cursor over `LeanToken`s.
struct TokenCursor<'a> {
    tokens: &'a [LeanToken],
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    #[cfg(test)]
    fn new(tokens: &'a [LeanToken]) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&'a LeanToken> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<&'a LeanToken> {
        let tok = self.tokens.get(self.pos)?;
        self.pos += 1;
        Some(tok)
    }

    fn expect(&mut self, expected: &LeanToken) -> Result<(), CensusScanError> {
        match self.next() {
            Some(tok) if tok == expected => Ok(()),
            Some(other) => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected {expected:?}, found {other:?}"
            ))),
            None => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "unexpected EOF while expecting {expected:?}"
            ))),
        }
    }

    /// Parse an optional leading `.` followed by an identifier, returning the
    /// last dotted segment (e.g., `"StatementKind.assign"` or `".assign"` -> `"assign"`).
    fn parse_ctor_head(&mut self) -> Result<(String, String), CensusScanError> {
        let had_leading_dot = if matches!(self.peek(), Some(LeanToken::Dot)) {
            self.next();
            true
        } else {
            false
        };
        match self.next() {
            Some(LeanToken::Ident(full)) => {
                let short = full
                    .rsplit_once('.')
                    .map(|(_, s)| s.to_string())
                    .unwrap_or_else(|| full.clone());
                let full_norm = if had_leading_dot {
                    format!(".{full}")
                } else {
                    full.clone()
                };
                Ok((full_norm, short))
            }
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected constructor identifier, found {other:?}"
            ))),
        }
    }

    /// Run `f` while stripping any number of surrounding `( ... )` parentheses.
    fn with_optional_parens<T, F>(&mut self, f: F) -> Result<T, CensusScanError>
    where
        F: FnOnce(&mut Self) -> Result<T, CensusScanError>,
    {
        let mut paren_depth = 0usize;
        while matches!(self.peek(), Some(LeanToken::LParen)) {
            self.next();
            paren_depth += 1;
        }
        let val = f(self)?;
        for _ in 0..paren_depth {
            self.expect(&LeanToken::RParen)?;
        }
        Ok(val)
    }

    /// Skip a single balanced Lean value expression (used for fields like `ty`,
    /// `fnAbi`, `layouts`, `allocations`, `localDecls` that are not basic blocks),
    /// failing closed if delimiters are unbalanced or hit EOF prematurely.
    fn skip_balanced_expr(&mut self) -> Result<(), CensusScanError> {
        match self.next() {
            Some(LeanToken::LParen) => {
                let mut depth = 1usize;
                while depth > 0 {
                    match self.next() {
                        Some(LeanToken::LParen) => depth += 1,
                        Some(LeanToken::RParen) => depth -= 1,
                        Some(_) => {}
                        None => {
                            return Err(CensusScanError::MalformedCapturedMirSyntax(
                                "unbalanced `(` in expression".to_string(),
                            ));
                        }
                    }
                }
                Ok(())
            }
            Some(LeanToken::LBrace) => {
                let mut depth = 1usize;
                while depth > 0 {
                    match self.next() {
                        Some(LeanToken::LBrace) => depth += 1,
                        Some(LeanToken::RBrace) => depth -= 1,
                        Some(_) => {}
                        None => {
                            return Err(CensusScanError::MalformedCapturedMirSyntax(
                                "unbalanced `{` in expression".to_string(),
                            ));
                        }
                    }
                }
                Ok(())
            }
            Some(LeanToken::LBracket) => {
                let mut depth = 1usize;
                while depth > 0 {
                    match self.next() {
                        Some(LeanToken::LBracket) => depth += 1,
                        Some(LeanToken::RBracket) => depth -= 1,
                        Some(_) => {}
                        None => {
                            return Err(CensusScanError::MalformedCapturedMirSyntax(
                                "unbalanced `[` in expression".to_string(),
                            ));
                        }
                    }
                }
                Ok(())
            }
            Some(LeanToken::Dot) => match self.next() {
                Some(LeanToken::Ident(_)) => {
                    while matches!(
                        self.peek(),
                        Some(
                            LeanToken::LParen
                                | LeanToken::LBrace
                                | LeanToken::LBracket
                                | LeanToken::NatLit(_)
                                | LeanToken::StrLit(_)
                                | LeanToken::Dot
                        )
                    ) {
                        self.skip_balanced_expr()?;
                    }
                    Ok(())
                }
                other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected identifier after `.`, found {other:?}"
                ))),
            },
            Some(LeanToken::Ident(_)) => {
                while matches!(
                    self.peek(),
                    Some(
                        LeanToken::LParen
                            | LeanToken::LBrace
                            | LeanToken::LBracket
                            | LeanToken::NatLit(_)
                            | LeanToken::StrLit(_)
                            | LeanToken::Dot
                    )
                ) {
                    self.skip_balanced_expr()?;
                }
                Ok(())
            }
            Some(LeanToken::NatLit(_) | LeanToken::StrLit(_)) => Ok(()),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "unexpected token while skipping expression: {other:?}"
            ))),
        }
    }

    fn parse_usize(&mut self) -> Result<usize, CensusScanError> {
        self.with_optional_parens(|cur| match cur.next() {
            Some(LeanToken::NatLit(v)) => usize::try_from(*v).map_err(|_| {
                CensusScanError::MalformedCapturedMirSyntax(format!("usize overflow: {v}"))
            }),
            Some(LeanToken::Dot) => match cur.next() {
                Some(LeanToken::Ident(s)) if s == "zero" => Ok(0),
                other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected Nat literal, found `.{other:?}`"
                ))),
            },
            Some(LeanToken::Ident(s)) if s == "Nat.zero" => Ok(0),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected usize literal, found {other:?}"
            ))),
        })
    }

    fn parse_u64(&mut self) -> Result<u64, CensusScanError> {
        self.with_optional_parens(|cur| match cur.next() {
            Some(LeanToken::NatLit(v)) => u64::try_from(*v).map_err(|_| {
                CensusScanError::MalformedCapturedMirSyntax(format!("u64 overflow: {v}"))
            }),
            Some(LeanToken::Dot) => match cur.next() {
                Some(LeanToken::Ident(s)) if s == "zero" => Ok(0),
                other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected u64 literal, found `.{other:?}`"
                ))),
            },
            Some(LeanToken::Ident(s)) if s == "Nat.zero" => Ok(0),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected u64 literal, found {other:?}"
            ))),
        })
    }

    fn parse_u128(&mut self) -> Result<u128, CensusScanError> {
        self.with_optional_parens(|cur| match cur.next() {
            Some(LeanToken::NatLit(v)) => Ok(*v),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected u128 literal, found {other:?}"
            ))),
        })
    }

    fn parse_bool(&mut self) -> Result<bool, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (_, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "true" => Ok(true),
                "false" => Ok(false),
                other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected `true` or `false`, found `{other}`"
                ))),
            }
        })
    }

    fn parse_string(&mut self) -> Result<String, CensusScanError> {
        self.with_optional_parens(|cur| match cur.next() {
            Some(LeanToken::StrLit(s)) => Ok(s.clone()),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "expected string literal, found {other:?}"
            ))),
        })
    }

    /// Parse a Lean `List T` written either as `(List.cons x (List.cons y List.nil))`
    /// or `[x, y]`. Fails closed if the list references an external identifier!
    fn parse_list<T, F>(&mut self, mut parse_elem: F) -> Result<Vec<T>, CensusScanError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusScanError>,
    {
        self.parse_list_inner(&mut parse_elem)
    }

    fn parse_list_inner<T, F>(&mut self, parse_elem: &mut F) -> Result<Vec<T>, CensusScanError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusScanError>,
    {
        if matches!(self.peek(), Some(LeanToken::LBracket)) {
            self.next();
            let mut items = Vec::new();
            while !matches!(self.peek(), Some(LeanToken::RBracket)) {
                items.push(parse_elem(self)?);
                if matches!(self.peek(), Some(LeanToken::Comma)) {
                    self.next();
                } else {
                    break;
                }
            }
            self.expect(&LeanToken::RBracket)?;
            return Ok(items);
        }

        self.with_optional_parens(|cur| {
            if matches!(cur.peek(), Some(LeanToken::LBracket)) {
                return cur.parse_list_inner(parse_elem);
            }
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "nil" if full == "List.nil" || full == ".nil" => Ok(Vec::new()),
                "cons" if full == "List.cons" || full == ".cons" => {
                    let head = parse_elem(cur)?;
                    let mut tail = cur.parse_list_inner(parse_elem)?;
                    let mut out = Vec::with_capacity(1 + tail.len());
                    out.push(head);
                    out.append(&mut tail);
                    Ok(out)
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected inline `List.nil`, `List.cons`, or `[...]`, found `{full}`"
                ))),
            }
        })
    }

    fn parse_option<T, F>(&mut self, parse_inner: F) -> Result<Option<T>, CensusScanError>
    where
        F: FnOnce(&mut Self) -> Result<T, CensusScanError>,
    {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "none" if full == "Option.none" || full == ".none" || full == "none" => Ok(None),
                "some" if full == "Option.some" || full == ".some" || full == "some" => {
                    Ok(Some(parse_inner(cur)?))
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "expected `Option.some` or `Option.none`, found `{full}`"
                ))),
            }
        })
    }

    /// Parse `{ field1 := val1, field2 := val2, ... }` record syntax, calling
    /// `on_field(field_name, cursor)` for each field.
    fn parse_record<F>(&mut self, mut on_field: F) -> Result<(), CensusScanError>
    where
        F: FnMut(&str, &mut Self) -> Result<(), CensusScanError>,
    {
        self.with_optional_parens(|cur| {
            cur.expect(&LeanToken::LBrace)?;
            while !matches!(cur.peek(), Some(LeanToken::RBrace)) {
                let field_name = match cur.next() {
                    Some(LeanToken::Ident(name)) => name.clone(),
                    other => {
                        return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                            "expected record field name, found {other:?}"
                        )));
                    }
                };
                cur.expect(&LeanToken::ColonEq)?;
                on_field(&field_name, cur)?;
                if matches!(cur.peek(), Some(LeanToken::Comma | LeanToken::Semicolon)) {
                    cur.next();
                }
            }
            cur.expect(&LeanToken::RBrace)?;
            Ok(())
        })
    }

    fn parse_captured_mir(&mut self) -> Result<ProtoMirBody, CensusScanError> {
        let mut def_path: Option<String> = None;
        let mut basic_blocks: Option<Vec<ProtoBasicBlock>> = None;

        self.parse_record(|field, cur| {
            match field {
                "defPath" => {
                    def_path = Some(cur.parse_string()?);
                }
                "basicBlocks" => {
                    basic_blocks = Some(cur.parse_list(|c| c.parse_basic_block())?);
                }
                "phase"
                | "role"
                | "argCount"
                | "localDecls"
                | "fnAbi"
                | "layouts"
                | "allocations"
                | "typeParamCount"
                | "genericParams"
                | "traitImpls" => {
                    cur.skip_balanced_expr()?;
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown CapturedMir field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        let basic_blocks = basic_blocks.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax(
                "CapturedMir record is missing required `basicBlocks` field".to_string(),
            )
        })?;

        Ok(ProtoMirBody {
            def_path: def_path.unwrap_or_default(),
            basic_blocks,
        })
    }

    fn parse_basic_block(&mut self) -> Result<ProtoBasicBlock, CensusScanError> {
        let mut statements: Option<Vec<ProtoStatement>> = None;
        let mut terminator: Option<ProtoTerminator> = None;
        let mut is_cleanup: Option<bool> = None;

        self.parse_record(|field, cur| {
            match field {
                "statements" => {
                    statements = Some(cur.parse_list(|c| c.parse_statement())?);
                }
                "terminator" => {
                    terminator = Some(cur.parse_terminator()?);
                }
                "isCleanup" => {
                    is_cleanup = Some(cur.parse_bool()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown BasicBlockData field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        Ok(ProtoBasicBlock {
            statements: statements.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "BasicBlockData missing `statements`".to_string(),
                )
            })?,
            terminator: terminator.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "BasicBlockData missing `terminator`".to_string(),
                )
            })?,
            is_cleanup: is_cleanup.unwrap_or(false),
        })
    }

    fn parse_statement(&mut self) -> Result<ProtoStatement, CensusScanError> {
        let mut kind: Option<ProtoStatementKind> = None;
        let mut span: Option<String> = None;

        self.parse_record(|field, cur| {
            match field {
                "kind" => {
                    kind = Some(cur.parse_statement_kind()?);
                }
                "span" => {
                    span = Some(cur.parse_string()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown Statement field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        Ok(ProtoStatement {
            kind: kind.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Statement missing `kind`".to_string())
            })?,
            span: span.unwrap_or_default(),
        })
    }

    fn parse_statement_kind(&mut self) -> Result<ProtoStatementKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "assign" => {
                    let place = cur.parse_place()?;
                    let rv = cur.parse_rvalue()?;
                    Ok(ProtoStatementKind::Assign(place, rv))
                }
                "setDiscriminant" => {
                    let place = cur.parse_place()?;
                    let idx = cur.parse_usize()?;
                    Ok(ProtoStatementKind::SetDiscriminant(place, idx))
                }
                "deinit" => Ok(ProtoStatementKind::Deinit(cur.parse_place()?)),
                "storageLive" => Ok(ProtoStatementKind::StorageLive(cur.parse_usize()?)),
                "storageDead" => Ok(ProtoStatementKind::StorageDead(cur.parse_usize()?)),
                "retag" => {
                    let _retag_kind = cur.parse_retag_kind()?;
                    let place = cur.parse_place()?;
                    Ok(ProtoStatementKind::Retag(place))
                }
                "placeMention" => Ok(ProtoStatementKind::PlaceMention(cur.parse_place()?)),
                "intrinsic" => Ok(ProtoStatementKind::Intrinsic(cur.parse_intrinsic()?)),
                "coverage" => Ok(ProtoStatementKind::Coverage),
                "constEvalCounter" => Ok(ProtoStatementKind::ConstEvalCounter),
                "backwardIncompatibleDropHint" => Ok(
                    ProtoStatementKind::BackwardIncompatibleDropHint(cur.parse_place()?),
                ),
                "nop" => Ok(ProtoStatementKind::Nop),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown StatementKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_retag_kind(&mut self) -> Result<(), CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "fnEntry" | "twoPhase" | "raw" | "default" => Ok(()),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown RetagKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_intrinsic(&mut self) -> Result<ProtoIntrinsic, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "assume" => Ok(ProtoIntrinsic::Assume(cur.parse_operand()?)),
                "copyNonOverlapping" => {
                    let src = cur.parse_operand()?;
                    let dst = cur.parse_operand()?;
                    let count = cur.parse_operand()?;
                    Ok(ProtoIntrinsic::CopyNonOverlapping { src, dst, count })
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown NonDivergingIntrinsic constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_place(&mut self) -> Result<ProtoPlace, CensusScanError> {
        let mut local_: Option<usize> = None;
        let mut projection: Option<Vec<ProtoProjectionElem>> = None;

        self.parse_record(|field, cur| {
            match field {
                "local_" => {
                    local_ = Some(cur.parse_usize()?);
                }
                "projection" => {
                    projection = Some(cur.parse_list(|c| c.parse_projection_elem())?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown Place field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        Ok(ProtoPlace {
            local_: local_.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Place missing `local_`".to_string())
            })?,
            projection: projection.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Place missing `projection`".to_string())
            })?,
        })
    }

    fn parse_projection_elem(&mut self) -> Result<ProtoProjectionElem, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "deref" => Ok(ProtoProjectionElem::Deref),
                "field" => {
                    let idx = cur.parse_usize()?;
                    cur.skip_balanced_expr()?; // ty
                    Ok(ProtoProjectionElem::Field(idx))
                }
                "index" => Ok(ProtoProjectionElem::Index(cur.parse_usize()?)),
                "constantIndex" => {
                    let offset = cur.parse_u64()?;
                    let min_length = cur.parse_u64()?;
                    let from_end = cur.parse_bool()?;
                    Ok(ProtoProjectionElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    })
                }
                "subslice" => {
                    let from_idx = cur.parse_u64()?;
                    let to_idx = cur.parse_u64()?;
                    let from_end = cur.parse_bool()?;
                    Ok(ProtoProjectionElem::Subslice {
                        from_idx,
                        to_idx,
                        from_end,
                    })
                }
                "downcast" => {
                    let sym = cur.parse_option(|c| c.parse_string())?;
                    let idx = cur.parse_usize()?;
                    Ok(ProtoProjectionElem::Downcast(sym, idx))
                }
                "opaqueCast" => {
                    cur.skip_balanced_expr()?; // ty
                    Ok(ProtoProjectionElem::OpaqueCast)
                }
                "unwrapUnsafeBinder" => {
                    cur.skip_balanced_expr()?; // ty
                    Ok(ProtoProjectionElem::UnwrapUnsafeBinder)
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown ProjectionElem constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_operand(&mut self) -> Result<ProtoOperand, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "copy" => Ok(ProtoOperand::Copy(cur.parse_place()?)),
                "move" => Ok(ProtoOperand::Move(cur.parse_place()?)),
                "constant" => Ok(ProtoOperand::Constant(cur.parse_const_operand()?)),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown Operand constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_const_operand(&mut self) -> Result<ProtoConstValue, CensusScanError> {
        let mut fn_def_path: Option<String> = None;
        let mut val: Option<ProtoConstValue> = None;

        self.parse_record(|field, cur| {
            match field {
                "ty" => {
                    fn_def_path = cur.parse_ty_extract_fn_def()?;
                }
                "val" => {
                    val = Some(cur.parse_const_value()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown ConstOperand field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        let mut cv = val.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax("ConstOperand missing `val`".to_string())
        })?;
        if let ProtoConstValue::ZeroSized {
            fn_def_path: ref mut slot,
        } = cv
        {
            *slot = fn_def_path;
        }
        Ok(cv)
    }

    fn parse_ty_extract_fn_def(&mut self) -> Result<Option<String>, CensusScanError> {
        let mut fn_def: Option<String> = None;
        self.parse_record(|field, cur| {
            match field {
                "kind" => {
                    fn_def = cur.parse_rigid_ty_extract_fn_def()?;
                }
                "layoutIdx" => {
                    let _ = cur.parse_usize()?;
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown Ty field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;
        Ok(fn_def)
    }

    fn parse_rigid_ty_extract_fn_def(&mut self) -> Result<Option<String>, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (_, short) = cur.parse_ctor_head()?;
            if short == "fnDef" {
                let path = cur.parse_string()?;
                cur.skip_balanced_expr()?; // typeArgs list
                Ok(Some(path))
            } else {
                // Skip any remaining arguments inside this RigidTy constructor
                while !matches!(
                    cur.peek(),
                    Some(LeanToken::Comma | LeanToken::Semicolon | LeanToken::RBrace | LeanToken::RParen)
                        | None
                ) {
                    cur.skip_balanced_expr()?;
                }
                Ok(None)
            }
        })
    }

    fn parse_const_value(&mut self) -> Result<ProtoConstValue, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "zeroSized" => Ok(ProtoConstValue::ZeroSized { fn_def_path: None }),
                "scalar" => cur.parse_const_scalar(),
                "slice" => {
                    let _data = cur.parse_const_scalar()?;
                    let meta = cur.parse_u64()?;
                    Ok(ProtoConstValue::Slice { meta })
                }
                "indirect" => {
                    let alloc_id = cur.parse_u64()?;
                    let offset_bytes = cur.parse_u64()?;
                    Ok(ProtoConstValue::Indirect {
                        alloc_id,
                        offset_bytes,
                    })
                }
                "unevaluated" => Ok(ProtoConstValue::Unevaluated(cur.parse_string()?)),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown ConstValue constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_const_scalar(&mut self) -> Result<ProtoConstValue, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "int" => {
                    let mut bits: Option<u128> = None;
                    let mut size_bytes: Option<u64> = None;
                    cur.parse_record(|field, c| {
                        match field {
                            "bits" => bits = Some(c.parse_u128()?),
                            "sizeBytes" => size_bytes = Some(c.parse_u64()?),
                            other => {
                                return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                                    "unknown ScalarInt field `{other}`"
                                )));
                            }
                        }
                        Ok(())
                    })?;
                    Ok(ProtoConstValue::ScalarInt {
                        bits: bits.unwrap_or(0),
                        size_bytes: size_bytes.unwrap_or(0),
                    })
                }
                "ptr" => {
                    let mut alloc_id: Option<u64> = None;
                    let mut offset_bytes: Option<u64> = None;
                    cur.parse_record(|field, c| {
                        match field {
                            "allocId" => alloc_id = Some(c.parse_u64()?),
                            "offsetBytes" => offset_bytes = Some(c.parse_u64()?),
                            "tag" => {
                                let _ = c.parse_u64()?;
                            }
                            other => {
                                return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                                    "unknown ProvenancePtr field `{other}`"
                                )));
                            }
                        }
                        Ok(())
                    })?;
                    let size = cur.parse_u64()?;
                    Ok(ProtoConstValue::ScalarPtr {
                        alloc_id: alloc_id.unwrap_or(0),
                        offset_bytes: offset_bytes.unwrap_or(0),
                        size,
                    })
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown ConstScalar constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_rvalue(&mut self) -> Result<ProtoRvalue, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "use" => Ok(ProtoRvalue::Use(cur.parse_operand()?)),
                "repeat" => {
                    let op = cur.parse_operand()?;
                    let count = cur.parse_u64()?;
                    Ok(ProtoRvalue::Repeat(op, count))
                }
                "ref" => {
                    let mutable = cur.parse_borrow_kind()?;
                    let place = cur.parse_place()?;
                    Ok(ProtoRvalue::Ref { mutable, place })
                }
                "threadLocalRef" => Ok(ProtoRvalue::ThreadLocalRef(cur.parse_string()?)),
                "rawPtr" => {
                    let mutable = cur.parse_mutability()?;
                    let place = cur.parse_place()?;
                    Ok(ProtoRvalue::RawPtr { mutable, place })
                }
                "len" => Ok(ProtoRvalue::Len(cur.parse_place()?)),
                "cast" => {
                    let kind = cur.parse_cast_kind()?;
                    let op = cur.parse_operand()?;
                    cur.skip_balanced_expr()?; // targetTy
                    Ok(ProtoRvalue::Cast(kind, op))
                }
                "binaryOp" => {
                    let op = cur.parse_bin_op()?;
                    let lhs = cur.parse_operand()?;
                    let rhs = cur.parse_operand()?;
                    Ok(ProtoRvalue::BinaryOp(op, lhs, rhs))
                }
                "nullaryOp" => {
                    let op = cur.parse_null_op()?;
                    cur.skip_balanced_expr()?; // ty
                    Ok(ProtoRvalue::NullaryOp(op))
                }
                "unaryOp" => {
                    let op = cur.parse_un_op()?;
                    let val = cur.parse_operand()?;
                    Ok(ProtoRvalue::UnaryOp(op, val))
                }
                "discriminant" => Ok(ProtoRvalue::Discriminant(cur.parse_place()?)),
                "aggregate" => {
                    cur.skip_balanced_expr()?; // AggregateKind
                    let ops = cur.parse_list(|c| c.parse_operand())?;
                    Ok(ProtoRvalue::Aggregate(ops))
                }
                "shallowInitBox" => {
                    let op = cur.parse_operand()?;
                    cur.skip_balanced_expr()?; // contentTy
                    Ok(ProtoRvalue::ShallowInitBox(op))
                }
                "copyForDeref" => Ok(ProtoRvalue::CopyForDeref(cur.parse_place()?)),
                "wrapUnsafeBinder" => {
                    let op = cur.parse_operand()?;
                    cur.skip_balanced_expr()?; // targetTy
                    Ok(ProtoRvalue::WrapUnsafeBinder(op))
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown Rvalue constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_borrow_kind(&mut self) -> Result<bool, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "shared" => Ok(false),
                "mut" => {
                    let _allow_two_phase = cur.parse_bool()?;
                    Ok(true)
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown BorrowKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_mutability(&mut self) -> Result<bool, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "not" => Ok(false),
                "mut" => Ok(true),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown Mutability constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_cast_kind(&mut self) -> Result<ProtoCastKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "pointerExposeProvenance" => Ok(ProtoCastKind::PointerExposeProvenance),
                "pointerWithExposedProvenance" => Ok(ProtoCastKind::PointerWithExposedProvenance),
                "pointerCoercion" => Ok(ProtoCastKind::PointerCoercion(cur.parse_string()?)),
                "intToInt" => Ok(ProtoCastKind::IntToInt),
                "floatToInt" => Ok(ProtoCastKind::FloatToInt),
                "floatToFloat" => Ok(ProtoCastKind::FloatToFloat),
                "intToFloat" => Ok(ProtoCastKind::IntToFloat),
                "ptrToPtr" => Ok(ProtoCastKind::PtrToPtr),
                "fnPtrToPtr" => Ok(ProtoCastKind::FnPtrToPtr),
                "transmute" => Ok(ProtoCastKind::Transmute),
                "subtype" => Ok(ProtoCastKind::Subtype),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown CastKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_bin_op(&mut self) -> Result<ProtoBinOp, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "add" => Ok(ProtoBinOp::Add),
                "addUnchecked" => Ok(ProtoBinOp::AddUnchecked),
                "addWithOverflow" => Ok(ProtoBinOp::AddWithOverflow),
                "sub" => Ok(ProtoBinOp::Sub),
                "subUnchecked" => Ok(ProtoBinOp::SubUnchecked),
                "subWithOverflow" => Ok(ProtoBinOp::SubWithOverflow),
                "mul" => Ok(ProtoBinOp::Mul),
                "mulUnchecked" => Ok(ProtoBinOp::MulUnchecked),
                "mulWithOverflow" => Ok(ProtoBinOp::MulWithOverflow),
                "div" => Ok(ProtoBinOp::Div),
                "rem" => Ok(ProtoBinOp::Rem),
                "bitXor" => Ok(ProtoBinOp::BitXor),
                "bitAnd" => Ok(ProtoBinOp::BitAnd),
                "bitOr" => Ok(ProtoBinOp::BitOr),
                "shl" => Ok(ProtoBinOp::Shl),
                "shlUnchecked" => Ok(ProtoBinOp::ShlUnchecked),
                "shr" => Ok(ProtoBinOp::Shr),
                "shrUnchecked" => Ok(ProtoBinOp::ShrUnchecked),
                "eq" => Ok(ProtoBinOp::Eq),
                "lt" => Ok(ProtoBinOp::Lt),
                "le" => Ok(ProtoBinOp::Le),
                "ne" => Ok(ProtoBinOp::Ne),
                "ge" => Ok(ProtoBinOp::Ge),
                "gt" => Ok(ProtoBinOp::Gt),
                "cmp" => Ok(ProtoBinOp::Cmp),
                "offset" => Ok(ProtoBinOp::Offset),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown BinOp constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_un_op(&mut self) -> Result<ProtoUnOp, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "not" => Ok(ProtoUnOp::Not),
                "neg" => Ok(ProtoUnOp::Neg),
                "ptrMetadata" => Ok(ProtoUnOp::PtrMetadata),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown UnOp constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_null_op(&mut self) -> Result<ProtoNullOp, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "sizeOf" => Ok(ProtoNullOp::SizeOf),
                "alignOf" => Ok(ProtoNullOp::AlignOf),
                "offsetOf" => {
                    let fields = cur.parse_list(|c| {
                        c.expect(&LeanToken::LParen)?;
                        let v = c.parse_usize()?;
                        c.expect(&LeanToken::Comma)?;
                        let f = c.parse_usize()?;
                        c.expect(&LeanToken::RParen)?;
                        Ok((v, f))
                    })?;
                    Ok(ProtoNullOp::OffsetOf(fields))
                }
                "ubChecks" => Ok(ProtoNullOp::UbChecks),
                "contractChecks" => Ok(ProtoNullOp::ContractChecks),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown NullOp constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_terminator(&mut self) -> Result<ProtoTerminator, CensusScanError> {
        let mut kind: Option<ProtoTerminatorKind> = None;
        let mut span: Option<String> = None;

        self.parse_record(|field, cur| {
            match field {
                "kind" => {
                    kind = Some(cur.parse_terminator_kind()?);
                }
                "span" => {
                    span = Some(cur.parse_string()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown Terminator field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        Ok(ProtoTerminator {
            kind: kind.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Terminator missing `kind`".to_string())
            })?,
            span: span.unwrap_or_default(),
        })
    }

    fn parse_terminator_kind(&mut self) -> Result<ProtoTerminatorKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "goto" => Ok(ProtoTerminatorKind::Goto(cur.parse_usize()?)),
                "switchInt" => {
                    let discr = cur.parse_operand()?;
                    let targets = cur.parse_switch_targets()?;
                    Ok(ProtoTerminatorKind::SwitchInt(discr, targets))
                }
                "unwindResume" => Ok(ProtoTerminatorKind::UnwindResume),
                "unwindTerminate" => Ok(ProtoTerminatorKind::UnwindTerminate),
                "return_" => Ok(ProtoTerminatorKind::Return),
                "unreachable" => Ok(ProtoTerminatorKind::Unreachable),
                "drop" => {
                    let place = cur.parse_place()?;
                    let target = cur.parse_usize()?;
                    let unwind = cur.parse_unwind_action()?;
                    Ok(ProtoTerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                    })
                }
                "call" => {
                    let func = cur.parse_operand()?;
                    let args = cur.parse_list(|c| c.parse_operand())?;
                    let destination = cur.parse_place()?;
                    let target = cur.parse_option(|c| c.parse_usize())?;
                    let unwind = cur.parse_unwind_action()?;
                    Ok(ProtoTerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target,
                        unwind,
                    })
                }
                "tailCall" => {
                    let func = cur.parse_operand()?;
                    let args = cur.parse_list(|c| c.parse_operand())?;
                    Ok(ProtoTerminatorKind::TailCall { func, args })
                }
                "assert" => {
                    let cond = cur.parse_operand()?;
                    let expected = cur.parse_bool()?;
                    let target = cur.parse_usize()?;
                    let unwind = cur.parse_unwind_action()?;
                    Ok(ProtoTerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        unwind,
                    })
                }
                "inlineAsm" => {
                    let template = cur.parse_string()?;
                    let targets = cur.parse_list(|c| c.parse_usize())?;
                    let unwind = cur.parse_unwind_action()?;
                    Ok(ProtoTerminatorKind::InlineAsm {
                        template,
                        targets,
                        unwind,
                    })
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown TerminatorKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_switch_targets(&mut self) -> Result<ProtoSwitchTargets, CensusScanError> {
        let mut branches: Option<Vec<(u128, usize)>> = None;
        let mut otherwise: Option<usize> = None;

        self.parse_record(|field, cur| {
            match field {
                "branches" => {
                    branches = Some(cur.parse_list(|c| {
                        c.expect(&LeanToken::LParen)?;
                        let val = c.parse_u128()?;
                        c.expect(&LeanToken::Comma)?;
                        let bb = c.parse_usize()?;
                        c.expect(&LeanToken::RParen)?;
                        Ok((val, bb))
                    })?);
                }
                "otherwise" => {
                    otherwise = Some(cur.parse_usize()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown SwitchTargets field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        Ok(ProtoSwitchTargets {
            branches: branches.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "SwitchTargets missing `branches`".to_string(),
                )
            })?,
            otherwise: otherwise.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "SwitchTargets missing `otherwise`".to_string(),
                )
            })?,
        })
    }

    fn parse_unwind_action(&mut self) -> Result<ProtoUnwindAction, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            match short.as_str() {
                "cleanup" => Ok(ProtoUnwindAction::Cleanup(cur.parse_usize()?)),
                "unreachable" => Ok(ProtoUnwindAction::Unreachable),
                "terminate" => Ok(ProtoUnwindAction::Terminate),
                "continue_" => Ok(ProtoUnwindAction::Continue),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown UnwindAction constructor `{full}`"
                ))),
            }
        })
    }
}

/// Parse a named `def <def_name> : CapturedMir := { ... }` declaration from
/// Lean 4 source text and return its `ProtoMirBody`.
pub fn parse_lean_captured_mir_def(
    lean_src: &str,
    def_name: &str,
) -> Result<ProtoMirBody, CensusScanError> {
    let tokens = tokenize_lean_source(lean_src)?;
    let mut found_body: Option<ProtoMirBody> = None;

    let mut idx = 0;
    while idx + 4 < tokens.len() {
        let is_def = matches!(&tokens[idx], LeanToken::Ident(kw) if kw == "def" || kw == "abbrev");
        let name_matches = matches!(&tokens[idx + 1], LeanToken::Ident(name) if name == def_name || name.ends_with(&format!(".{def_name}")));
        let is_colon = matches!(&tokens[idx + 2], LeanToken::Colon);
        let is_captured_mir = matches!(
            &tokens[idx + 3],
            LeanToken::Ident(ty) if ty == "CapturedMir" || ty.ends_with(".CapturedMir")
        );
        let is_assign = matches!(&tokens[idx + 4], LeanToken::ColonEq);

        if is_def && name_matches && is_colon && is_captured_mir && is_assign {
            if found_body.is_some() {
                return Err(CensusScanError::MissingOrDuplicateCapturedMirDef(format!(
                    "multiple `def {def_name} : CapturedMir` declarations found"
                )));
            }
            let mut cursor = TokenCursor {
                tokens: &tokens,
                pos: idx + 5,
            };
            let parsed = cursor.parse_captured_mir()?;
            found_body = Some(parsed);
            idx = cursor.pos;
        } else {
            idx += 1;
        }
    }

    found_body.ok_or_else(|| {
        CensusScanError::MissingOrDuplicateCapturedMirDef(format!(
            "`def {def_name} : CapturedMir := ...` not found"
        ))
    })
}

/// Enumerate all `FaultSite` records for a named `def <def_name> : CapturedMir := ...`
/// declaration in `lean_src`.
pub fn census_lean_mir_def(lean_src: &str, def_name: &str) -> Result<Vec<FaultSite>, CensusScanError> {
    let body = parse_lean_captured_mir_def(lean_src, def_name)?;
    Ok(census_mir_fault_sites(&body))
}

/// Enumerate all `FaultSite` records from a `Mir/<Item>.lean` module (`def body : CapturedMir := ...`).
pub fn census_lean_mir_module(lean_src: &str) -> Result<Vec<FaultSite>, CensusScanError> {
    census_lean_mir_def(lean_src, "body")
}

// ============================================================================
// 6. Fail-Closed `CoverageReconciler`
// ============================================================================

/// Fail-closed verdict returned by `reconcile_obligation_coverage`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoverageVerdict {
    /// Every fault site in `census` is covered by `discharged` AND every
    /// fault class in `census` has `PropertyStatus::EmittedAndVerified` in
    /// `PropertyRegistry`.
    Verified,
    /// Fail-closed downgrade (`UNKNOWN(UNSUPPORTED_CONSTRUCT)`) when one or
    /// more fault sites are missing from `discharged`, belong to an un-emitted
    /// or unsupported `MirFaultClass` in `PropertyRegistry`, or when the MIR
    /// module failed census scanning.
    UnknownUnmappedFaultSite {
        /// Fault sites in `census` that were not present in `discharged` (or
        /// whose fault class is not `EmittedAndVerified`).
        missing_sites: Vec<FaultSite>,
        /// Distinct `MirFaultClass` categories present in `census` whose status
        /// in `PropertyRegistry` is not `PropertyStatus::EmittedAndVerified`.
        unemitted_classes: Vec<MirFaultClass>,
        /// Human-readable fail-closed diagnostic reasons.
        unsupported_reasons: Vec<String>,
    },
}

impl CoverageVerdict {
    /// True iff this verdict is `CoverageVerdict::Verified`.
    pub const fn is_verified(&self) -> bool {
        matches!(self, CoverageVerdict::Verified)
    }

    /// Canonical machine-readable status code (`"VERIFIED"` vs.
    /// `"UNKNOWN(UNSUPPORTED_CONSTRUCT)"`).
    pub const fn status_code(&self) -> &'static str {
        match self {
            CoverageVerdict::Verified => "VERIFIED",
            CoverageVerdict::UnknownUnmappedFaultSite { .. } => "UNKNOWN(UNSUPPORTED_CONSTRUCT)",
        }
    }
}

/// Reconcile an independent `census` against the obligation generator's
/// `discharged` fault-site set and `registry`, matching
/// `reconcileFaultCoverageWithRegistry` in `FaultSiteCensusPrototype.lean`.
pub fn reconcile_obligation_coverage(
    census: &[FaultSite],
    discharged: &[FaultSite],
    registry: &PropertyRegistry,
) -> CoverageVerdict {
    let discharged_set: BTreeSet<FaultSite> = discharged.iter().copied().collect();
    let mut missing_sites = Vec::new();
    let mut unemitted_set = BTreeSet::new();
    let mut unsupported_reasons = Vec::new();

    for &site in census {
        let status = registry.status(site.fault_class);
        let in_discharged = discharged_set.contains(&site);
        if !in_discharged || !status.is_verified() {
            missing_sites.push(site);
            if !in_discharged {
                unsupported_reasons.push(format!(
                    "unmapped fault site {site}: present in MIR census but omitted by obligation generator"
                ));
            }
            if !status.is_verified() && unemitted_set.insert(site.fault_class) {
                unsupported_reasons.push(format!(
                    "fault class `{}` at {site} has non-verified registry status {:?}",
                    site.fault_class, status
                ));
            }
        }
    }

    if missing_sites.is_empty() && unemitted_set.is_empty() {
        CoverageVerdict::Verified
    } else {
        CoverageVerdict::UnknownUnmappedFaultSite {
            missing_sites,
            unemitted_classes: unemitted_set.into_iter().collect(),
            unsupported_reasons,
        }
    }
}

/// Scan a `Mir/<Item>.lean` source module and reconcile its fault-site census
/// against `discharged` and `registry`, failing closed to
/// `CoverageVerdict::UnknownUnmappedFaultSite` on any `CensusScanError`.
pub fn reconcile_lean_mir_coverage(
    lean_src: &str,
    discharged: &[FaultSite],
    registry: &PropertyRegistry,
) -> CoverageVerdict {
    match census_lean_mir_module(lean_src) {
        Ok(census) => reconcile_obligation_coverage(&census, discharged, registry),
        Err(err) => CoverageVerdict::UnknownUnmappedFaultSite {
            missing_sites: Vec::new(),
            unemitted_classes: Vec::new(),
            unsupported_reasons: vec![format!("census scan failed closed: {err}")],
        },
    }
}

// ============================================================================
// 7. Four False-Proof Mutation Probes & PropertyRegistry Probe
// ============================================================================

/// The 4 canonical false-proof mutation probes specified in the Track P brief.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FaultMutationProbe {
    /// Probe 1: Call-argument obligation blindness (`TerminatorKind::Call`
    /// passing a dereferenced pointer argument `*_1`).
    CallArgBlindProbe,
    /// Probe 2: `SwitchInt` arm / `otherwise` target stripping (`bb2` with
    /// division `BinOp::Div` dropped from obligation exploration).
    SwitchBreakStripProbe,
    /// Probe 3: Loop latch back-edge update overflow omission (`BinOp::Add` at
    /// latch block `(2, 0)` dropped while other `(2, 0)` obligations remain).
    LoopUpdateOverflowProbe,
    /// Probe 4: Pointer dereference, alignment, and Tree Borrows aliasing
    /// omission (`*_1 = copy (*_2)` at `(0, 0)`).
    DerefAliasProbe,
}

impl FaultMutationProbe {
    /// All 4 false-proof mutation probes in canonical order.
    pub const ALL: [FaultMutationProbe; 4] = [
        FaultMutationProbe::CallArgBlindProbe,
        FaultMutationProbe::SwitchBreakStripProbe,
        FaultMutationProbe::LoopUpdateOverflowProbe,
        FaultMutationProbe::DerefAliasProbe,
    ];

    /// Name of the corresponding Lean 4 witness `CapturedMir` definition in
    /// `theory/Anneal/FaultSiteCensusPrototype.lean`.
    pub const fn lean_witness_def_name(self) -> &'static str {
        match self {
            FaultMutationProbe::CallArgBlindProbe => "witnessCallArgBlindBody",
            FaultMutationProbe::SwitchBreakStripProbe => "witnessSwitchBreakStripBody",
            FaultMutationProbe::LoopUpdateOverflowProbe => "witnessLoopUpdateOverflowBody",
            FaultMutationProbe::DerefAliasProbe => "witnessDerefAliasBody",
        }
    }
}

/// Execution report for a single `FaultMutationProbe`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProbeExecutionReport {
    /// Executed probe identifier.
    pub probe: FaultMutationProbe,
    /// Independent fault-site census of the probe's MIR body.
    pub census: Vec<FaultSite>,
    /// Verdict on the unmutated baseline obligation set (must be `Verified`).
    pub baseline_verdict: CoverageVerdict,
    /// Verdict on the mutated obligation set (must be `UnknownUnmappedFaultSite`).
    pub mutant_verdict: CoverageVerdict,
    /// Exact fault sites stripped by the mutation and caught by the reconciler.
    pub expected_missing_sites: Vec<FaultSite>,
}

impl ProbeExecutionReport {
    /// True iff the baseline succeeded (`Verified`) AND the mutant was rejected
    /// with `missing_sites == expected_missing_sites`.
    pub fn passed(&self) -> bool {
        if !self.baseline_verdict.is_verified() {
            return false;
        }
        match &self.mutant_verdict {
            CoverageVerdict::UnknownUnmappedFaultSite {
                missing_sites,
                unemitted_classes,
                ..
            } => missing_sites == &self.expected_missing_sites && unemitted_classes.is_empty(),
            CoverageVerdict::Verified => false,
        }
    }
}

/// Construct the canonical `ProtoMirBody`, baseline discharged set, mutant
/// discharged set, and expected missing sites for `probe`, matching the Lean 4
/// witness definitions in `theory/Anneal/FaultSiteCensusPrototype.lean` 1-to-1.
pub fn build_probe_scenario(
    probe: FaultMutationProbe,
) -> (ProtoMirBody, Vec<FaultSite>, Vec<FaultSite>, Vec<FaultSite>) {
    match probe {
        FaultMutationProbe::CallArgBlindProbe => {
            let body = ProtoMirBody {
                def_path: String::from("proto::witness_call_arg_blind"),
                basic_blocks: vec![
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Call {
                                func: ProtoOperand::const_fn("proto::callee_u32"),
                                args: vec![ProtoOperand::Copy(ProtoPlace::deref_local(1))],
                                destination: ProtoPlace::local(0),
                                target: Some(1),
                                unwind: ProtoUnwindAction::Continue,
                            },
                            span: String::from("proto.rs:10:5"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Return,
                            span: String::from("proto.rs:11:5"),
                        },
                        is_cleanup: false,
                    },
                ],
            };
            let census = census_mir_fault_sites(&body);
            let expected_missing = vec![
                FaultSite::new(0, 0, MirFaultClass::PtrDerefInvalid),
                FaultSite::new(0, 0, MirFaultClass::PtrAlignMismatch),
            ];
            let mutant: Vec<FaultSite> = census
                .iter()
                .copied()
                .filter(|s| !expected_missing.contains(s))
                .collect();
            (body, census, mutant, expected_missing)
        }
        FaultMutationProbe::SwitchBreakStripProbe => {
            let body = ProtoMirBody {
                def_path: String::from("proto::witness_switch_break_strip"),
                basic_blocks: vec![
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::SwitchInt(
                                ProtoOperand::Copy(ProtoPlace::local(1)),
                                ProtoSwitchTargets {
                                    branches: vec![(0, 1)],
                                    otherwise: 2,
                                },
                            ),
                            span: String::from("proto.rs:20:5"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: vec![ProtoStatement {
                            kind: ProtoStatementKind::Assign(
                                ProtoPlace::local(0),
                                ProtoRvalue::Use(ProtoOperand::const_u32(42)),
                            ),
                            span: String::from("proto.rs:21:9"),
                        }],
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Return,
                            span: String::from("proto.rs:21:15"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: vec![ProtoStatement {
                            kind: ProtoStatementKind::Assign(
                                ProtoPlace::local(0),
                                ProtoRvalue::BinaryOp(
                                    ProtoBinOp::Div,
                                    ProtoOperand::Copy(ProtoPlace::local(1)),
                                    ProtoOperand::Copy(ProtoPlace::local(2)),
                                ),
                            ),
                            span: String::from("proto.rs:22:9"),
                        }],
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Return,
                            span: String::from("proto.rs:22:15"),
                        },
                        is_cleanup: false,
                    },
                ],
            };
            let census = census_mir_fault_sites(&body);
            let expected_missing: Vec<FaultSite> = census
                .iter()
                .copied()
                .filter(|s| s.block_idx == 2)
                .collect();
            let mutant: Vec<FaultSite> = census
                .iter()
                .copied()
                .filter(|s| s.block_idx != 2)
                .collect();
            (body, census, mutant, expected_missing)
        }
        FaultMutationProbe::LoopUpdateOverflowProbe => {
            let body = ProtoMirBody {
                def_path: String::from("proto::witness_loop_update_overflow"),
                basic_blocks: vec![
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Goto(1),
                            span: String::from("proto.rs:30:5"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::SwitchInt(
                                ProtoOperand::Copy(ProtoPlace::local(1)),
                                ProtoSwitchTargets {
                                    branches: vec![(0, 3)],
                                    otherwise: 2,
                                },
                            ),
                            span: String::from("proto.rs:31:5"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: vec![ProtoStatement {
                            kind: ProtoStatementKind::Assign(
                                ProtoPlace::local(1),
                                ProtoRvalue::BinaryOp(
                                    ProtoBinOp::Add,
                                    ProtoOperand::Copy(ProtoPlace::local(1)),
                                    ProtoOperand::const_u32(1),
                                ),
                            ),
                            span: String::from("proto.rs:32:9"),
                        }],
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Goto(1),
                            span: String::from("proto.rs:32:20"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Return,
                            span: String::from("proto.rs:33:5"),
                        },
                        is_cleanup: false,
                    },
                ],
            };
            let census = census_mir_fault_sites(&body);
            let dropped = FaultSite::new(2, 0, MirFaultClass::ArithOverflow);
            let expected_missing = vec![dropped];
            let mutant: Vec<FaultSite> =
                census.iter().copied().filter(|&s| s != dropped).collect();
            (body, census, mutant, expected_missing)
        }
        FaultMutationProbe::DerefAliasProbe => {
            let body = ProtoMirBody {
                def_path: String::from("proto::witness_deref_alias"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: vec![ProtoStatement {
                        kind: ProtoStatementKind::Assign(
                            ProtoPlace::deref_local(1),
                            ProtoRvalue::Use(ProtoOperand::Copy(ProtoPlace::deref_local(2))),
                        ),
                        span: String::from("proto.rs:40:5"),
                    }],
                    terminator: ProtoTerminator {
                        kind: ProtoTerminatorKind::Return,
                        span: String::from("proto.rs:41:5"),
                    },
                    is_cleanup: false,
                }],
            };
            let census = census_mir_fault_sites(&body);
            let expected_missing = vec![
                FaultSite::new(0, 0, MirFaultClass::PtrDerefInvalid),
                FaultSite::new(0, 0, MirFaultClass::PtrAlignMismatch),
                FaultSite::new(0, 0, MirFaultClass::TreeBorrowsViolation),
            ];
            let mutant: Vec<FaultSite> = census
                .iter()
                .copied()
                .filter(|s| !expected_missing.contains(s))
                .collect();
            (body, census, mutant, expected_missing)
        }
    }
}

/// Execute a single `FaultMutationProbe` against `PropertyRegistry::all_verified()`.
pub fn run_false_proof_probe(probe: FaultMutationProbe) -> ProbeExecutionReport {
    let registry = PropertyRegistry::all_verified();
    let (_body, census, mutant_discharged, expected_missing_sites) = build_probe_scenario(probe);
    let baseline_verdict = reconcile_obligation_coverage(&census, &census, &registry);
    let mutant_verdict = reconcile_obligation_coverage(&census, &mutant_discharged, &registry);
    ProbeExecutionReport {
        probe,
        census,
        baseline_verdict,
        mutant_verdict,
        expected_missing_sites,
    }
}

/// Execute all 4 false-proof mutation probes in canonical order.
pub fn run_all_false_proof_probes() -> Vec<ProbeExecutionReport> {
    FaultMutationProbe::ALL
        .into_iter()
        .map(run_false_proof_probe)
        .collect()
}

/// Execute the `PropertyRegistry` un-emitted class probe on `DerefAliasProbe`,
/// verifying that marking `MirFaultClass::TreeBorrowsViolation` as
/// `PropertyStatus::UnemittedGap` causes `reconcile_obligation_coverage` to
/// reject even when `discharged == census`.
pub fn run_property_registry_unemitted_probe() -> CoverageVerdict {
    let (_body, census, _mutant, _expected_missing) =
        build_probe_scenario(FaultMutationProbe::DerefAliasProbe);
    let registry = PropertyRegistry::all_verified().with_status(
        MirFaultClass::TreeBorrowsViolation,
        PropertyStatus::UnemittedGap,
    );
    reconcile_obligation_coverage(&census, &census, &registry)
}

// ============================================================================
// 8. Unit, Mutation Probe, Lexer Trap, and Cross-Language Lean Parity Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::lean_emit::{
        IrAbiPassMode, IrAlign, IrArgAbi, IrBackendRepr, IrCallConv, IrContractRole,
        IrFieldsShape, IrFnAbi, IrLayoutTable, IrLocalDecl, IrMirPhaseTag, IrPrimitiveKind,
        IrRigidTy, IrScalarLayout, IrSize, IrTy, IrTypeLayout, IrUintTy,
        IrVariantsShape, IrWrappingRange, emit_mir_lean_module,
    };

    const LEAN_PROTOTYPE_SRC: &str =
        include_str!("../../../theory/Anneal/FaultSiteCensusPrototype.lean");

    /// Parse a Lean `def <name> : List FaultSite := [ (b, s, .cls), ... ]` list
    /// directly from `FaultSiteCensusPrototype.lean` so the cross-language test
    /// locks Rust's census outputs to the exact Lean 4 `by decide` witness constants.
    fn parse_lean_expected_fault_site_list(lean_src: &str, def_name: &str) -> Vec<FaultSite> {
        let tokens = tokenize_lean_source(lean_src).expect("tokenize Lean prototype");
        let mut idx = 0;
        while idx + 4 < tokens.len() {
            let is_def = matches!(&tokens[idx], LeanToken::Ident(kw) if kw == "def");
            let is_name = matches!(&tokens[idx + 1], LeanToken::Ident(n) if n == def_name);
            let is_colon = matches!(&tokens[idx + 2], LeanToken::Colon);
            let is_assign = matches!(&tokens[idx + 5], LeanToken::ColonEq);
            if is_def && is_name && is_colon && is_assign {
                let mut cur = TokenCursor::new(&tokens);
                cur.pos = idx + 6;
                return cur
                    .parse_list(|c| {
                        c.expect(&LeanToken::LParen)?;
                        let b = c.parse_usize()?;
                        c.expect(&LeanToken::Comma)?;
                        let s = c.parse_usize()?;
                        c.expect(&LeanToken::Comma)?;
                        let (full, short) = c.parse_ctor_head()?;
                        let cls = MirFaultClass::from_lean_ctor_name(&short).ok_or_else(|| {
                            CensusScanError::MalformedCapturedMirSyntax(format!(
                                "unknown MirFaultClass `{full}`"
                            ))
                        })?;
                        c.expect(&LeanToken::RParen)?;
                        Ok(FaultSite::new(b, s, cls))
                    })
                    .expect("parse FaultSite list");
            }
            idx += 1;
        }
        panic!("did not find `def {def_name} : List FaultSite` in Lean source");
    }

    #[test]
    fn test_all_12_mir_fault_classes_roundtrip_and_rank() {
        assert_eq!(MirFaultClass::ALL.len(), 12);
        let mut seen_names = BTreeSet::new();
        for (expected_rank, cls) in MirFaultClass::ALL.into_iter().enumerate() {
            assert_eq!(cls.rank(), expected_rank);
            assert_eq!(MirFaultClass::from_rank(expected_rank), Some(cls));
            let s = cls.as_str();
            assert!(seen_names.insert(s), "duplicate fault class string {s}");
            assert_eq!(MirFaultClass::from_str_opt(s), Some(cls));
            assert_eq!(
                MirFaultClass::from_lean_ctor_name(cls.lean_ctor_name()),
                Some(cls)
            );
            assert_eq!(
                MirFaultClass::from_lean_ctor_name(&format!(".{}", cls.lean_ctor_name())),
                Some(cls)
            );
        }
        assert_eq!(MirFaultClass::from_rank(12), None);
        assert_eq!(MirFaultClass::from_str_opt("nonexistent_fault"), None);
    }

    #[test]
    fn test_pure_zero_fault_constructs_emit_empty_census() {
        let body = ProtoMirBody {
            def_path: String::from("proto::pure_noop"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: vec![
                    ProtoStatement::new(ProtoStatementKind::Nop),
                    ProtoStatement::new(ProtoStatementKind::Coverage),
                    ProtoStatement::new(ProtoStatementKind::ConstEvalCounter),
                    ProtoStatement::new(ProtoStatementKind::BackwardIncompatibleDropHint(
                        ProtoPlace::local(0),
                    )),
                ],
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Goto(0)),
                is_cleanup: false,
            }],
        };
        let census = census_mir_fault_sites(&body);
        assert!(
            census.is_empty(),
            "expected pure noop/goto body to have empty census, got {census:?}"
        );
        let verdict =
            reconcile_obligation_coverage(&census, &[], &PropertyRegistry::all_verified());
        assert_eq!(verdict, CoverageVerdict::Verified);
    }

    #[test]
    fn test_construct_precision_non_overapproximation() {
        for loc in [0usize, 1, 5] {
            let live = census_stmt_fault_classes(&ProtoStatementKind::StorageLive(loc));
            let dead = census_stmt_fault_classes(&ProtoStatementKind::StorageDead(loc));
            assert_eq!(live, vec![MirFaultClass::StorageLiveProtected]);
            assert_eq!(dead, vec![MirFaultClass::StorageLiveProtected]);
            assert!(live.len() < MirFaultClass::ALL.len());
        }
        assert_eq!(
            census_terminator_fault_classes(2, &ProtoTerminatorKind::Goto(1)),
            Vec::<MirFaultClass>::new()
        );
        assert_eq!(
            census_terminator_fault_classes(2, &ProtoTerminatorKind::Goto(2)),
            vec![MirFaultClass::BoundsCheck]
        );
        assert_eq!(
            census_terminator_fault_classes(1, &ProtoTerminatorKind::UnwindTerminate),
            Vec::<MirFaultClass>::new()
        );
        assert_eq!(
            census_terminator_fault_classes(1, &ProtoTerminatorKind::Unreachable),
            vec![MirFaultClass::UnreachableTerminator]
        );
        assert_eq!(
            census_terminator_fault_classes(1, &ProtoTerminatorKind::UnwindResume),
            vec![MirFaultClass::CallAbiMismatch]
        );
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::Add),
            vec![MirFaultClass::ArithOverflow]
        );
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::Div),
            vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero]
        );
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::Shl),
            vec![MirFaultClass::ShiftOverflow]
        );
    }

    #[test]
    fn test_false_proof_mutation_probes_all_four() {
        let reports = run_all_false_proof_probes();
        assert_eq!(reports.len(), 4);
        for report in &reports {
            assert!(
                report.passed(),
                "probe {:?} failed: baseline={:?}, mutant={:?}, expected_missing={:?}",
                report.probe,
                report.baseline_verdict,
                report.mutant_verdict,
                report.expected_missing_sites
            );
            assert_eq!(report.baseline_verdict.status_code(), "VERIFIED");
            assert_eq!(
                report.mutant_verdict.status_code(),
                "UNKNOWN(UNSUPPORTED_CONSTRUCT)"
            );
        }
    }

    #[test]
    fn test_property_registry_unemitted_and_unsupported_fail_closed() {
        let verdict = run_property_registry_unemitted_probe();
        assert_eq!(verdict.status_code(), "UNKNOWN(UNSUPPORTED_CONSTRUCT)");
        match verdict {
            CoverageVerdict::UnknownUnmappedFaultSite {
                missing_sites,
                unemitted_classes,
                unsupported_reasons,
            } => {
                assert_eq!(
                    missing_sites,
                    vec![
                        FaultSite::new(0, 0, MirFaultClass::TreeBorrowsViolation),
                        FaultSite::new(0, 1, MirFaultClass::TreeBorrowsViolation),
                    ]
                );
                assert_eq!(unemitted_classes, vec![MirFaultClass::TreeBorrowsViolation]);
                assert!(!unsupported_reasons.is_empty());
            }
            CoverageVerdict::Verified => panic!("expected fail-closed UnknownUnmappedFaultSite"),
        }

        // Also verify `realistic_safe_subset_registry` rejects indirect call / aliasing sites.
        let safe_reg = PropertyRegistry::realistic_safe_subset_registry();
        let (_body, call_census, _, _) =
            build_probe_scenario(FaultMutationProbe::CallArgBlindProbe);
        let call_verdict = reconcile_obligation_coverage(&call_census, &call_census, &safe_reg);
        match call_verdict {
            CoverageVerdict::UnknownUnmappedFaultSite {
                unemitted_classes, ..
            } => {
                assert!(unemitted_classes.contains(&MirFaultClass::TreeBorrowsViolation));
                assert!(unemitted_classes.contains(&MirFaultClass::CallAbiMismatch));
            }
            CoverageVerdict::Verified => {
                panic!("expected safe subset registry to reject TreeBorrows and CallAbi")
            }
        }
    }

    #[test]
    fn test_partial_site_coverage_same_statement_different_fault_class() {
        // At (2, 0) in LoopUpdateOverflowProbe, there are 4 fault classes:
        // ArithOverflow, TreeBorrowsViolation, UninitRead, StorageLiveProtected.
        // Discharging 3 of the 4 while dropping ArithOverflow MUST still fail closed!
        let report = run_false_proof_probe(FaultMutationProbe::LoopUpdateOverflowProbe);
        assert!(report.passed());
        assert_eq!(
            report.expected_missing_sites,
            vec![FaultSite::new(2, 0, MirFaultClass::ArithOverflow)]
        );
    }

    #[test]
    fn test_lean_lexer_and_scanner_comment_string_guillemet_traps() {
        // Embed tricky comments, nested block comments, raw strings, interpolated strings,
        // char literals `'«'`, `'"'`, and guillemet identifiers around a valid `CapturedMir`.
        let tricky_lean = r##"
import Trusted
namespace Mir.Tricky.«fn--with--dashes»
-- Line comment mentioning def body : CapturedMir := { basicBlocks := List.nil }
/- Outer block comment
   /- Nested block comment with fake def body : CapturedMir := { basicBlocks := List.nil } -/
   still inside block comment "unclosed quote in comment
-/
def helperCharQuote : Char := '"'
def helperCharGui : Char := '«'
def helperRawStr : String := r#"def body : CapturedMir := { basicBlocks := List.nil }"#
def helperInterp : String := s!"interpolated {1 + 2} def body : CapturedMir := {}"

def «body» : CapturedMir :=
  { defPath := "tricky::\"quoted\"::item"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 0
  , localDecls := List.nil
  , basicBlocks :=
      (List.cons
        { statements :=
            (List.cons
              { kind := (StatementKind.storageLive 1), span := "src/lib.rs:10:5" }
              List.nil)
        , terminator := { kind := TerminatorKind.unreachable, span := "src/lib.rs:11:5" }
        , isCleanup := false
        }
        List.nil)
  , fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := false }
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }
end Mir.Tricky.«fn--with--dashes»
"##;

        let sites = census_lean_mir_module(tricky_lean).expect("scan tricky Lean module");
        assert_eq!(
            sites,
            vec![
                FaultSite::new(0, 0, MirFaultClass::StorageLiveProtected),
                FaultSite::new(0, 1, MirFaultClass::UnreachableTerminator),
            ]
        );
    }

    #[test]
    fn test_lean_scanner_fails_closed_on_malformed_or_non_inline_mir() {
        // 1. Missing `def body : CapturedMir`
        let empty_src = "import Trusted\nnamespace Empty\nend Empty\n";
        assert!(matches!(
            census_lean_mir_module(empty_src),
            Err(CensusScanError::MissingOrDuplicateCapturedMirDef(_))
        ));
        assert_eq!(
            reconcile_lean_mir_coverage(empty_src, &[], &PropertyRegistry::all_verified())
                .status_code(),
            "UNKNOWN(UNSUPPORTED_CONSTRUCT)"
        );

        // 2. Unterminated block comment
        let bad_comment = "def body : CapturedMir := /- unclosed comment";
        assert_eq!(
            census_lean_mir_module(bad_comment),
            Err(CensusScanError::UnterminatedBlockComment)
        );

        // 3. Non-inline helper identifier for `basicBlocks`
        let non_inline_bbs = r#"
def body : CapturedMir :=
  { defPath := "x"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 0
  , localDecls := List.nil
  , basicBlocks := externalHelperBlocks
  , fnAbi := dummyAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }
"#;
        assert!(matches!(
            census_lean_mir_module(non_inline_bbs),
            Err(CensusScanError::MalformedCapturedMirSyntax(_))
        ));
    }

    #[test]
    fn test_ir_captured_mir_to_emitted_lean_roundtrip_parity() {
        let u32_ty = IrTy {
            kind: IrRigidTy::Uint(IrUintTy::U32),
            layout_idx: 0,
        };
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
            field_layouts: Vec::new(),
        };
        let ir_mir = IrCapturedMir {
            def_path: String::from("crate::checked_shl_add"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 2,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("x")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("shift")),
                },
            ],
            basic_blocks: vec![IrBasicBlockData {
                statements: vec![
                    IrStatement {
                        kind: IrStatementKind::StorageLive(0),
                        span: String::from("src/lib.rs:5:5"),
                        comment: None,
                    },
                    IrStatement {
                        kind: IrStatementKind::Assign(
                            IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            IrRvalue::BinaryOp(
                                IrBinOp::ShlUnchecked,
                                IrOperand::Copy(IrPlace {
                                    local_: 1,
                                    projection: Vec::new(),
                                }),
                                IrOperand::Copy(IrPlace {
                                    local_: 2,
                                    projection: Vec::new(),
                                }),
                            ),
                        ),
                        span: String::from("src/lib.rs:5:9"),
                        comment: Some(String::from("_0 = ShlUnchecked(copy _1, copy _2)")),
                    },
                ],
                terminator: IrTerminator {
                    kind: IrTerminatorKind::Return,
                    span: String::from("src/lib.rs:6:2"),
                    comment: Some(String::from("return")),
                },
                is_cleanup: false,
            }],
            fn_abi: IrFnAbi {
                args: vec![
                    IrArgAbi {
                        layout: u32_layout.clone(),
                        mode: IrAbiPassMode::Direct,
                    },
                    IrArgAbi {
                        layout: u32_layout.clone(),
                        mode: IrAbiPassMode::Direct,
                    },
                ],
                ret: IrArgAbi {
                    layout: u32_layout.clone(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: false,
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![u32_layout],
            },
            allocations: Vec::new(),
        };

        let direct_sites = census_ir_captured_mir(&ir_mir);
        let emitted_lean = emit_mir_lean_module("Mir.Crate.checked_shl_add", &ir_mir);
        let scanned_sites =
            census_lean_mir_module(&emitted_lean).expect("scan emitted Mir/<Item>.lean");
        assert_eq!(direct_sites, scanned_sites);
        assert!(direct_sites.contains(&FaultSite::new(0, 1, MirFaultClass::ShiftOverflow)));
    }

    #[test]
    fn test_cross_language_lean_to_rust_witness_parity() {
        // 1. Verify all 12 MirFaultClass snake_case strings and constructor names appear in
        //    `theory/Anneal/FaultSiteCensusPrototype.lean` in exact rank order.
        for cls in MirFaultClass::ALL {
            let rank = cls.rank();
            let lean_ctor = cls.lean_ctor_name();
            let snake = cls.as_str();
            assert!(
                LEAN_PROTOTYPE_SRC.contains(&format!("| .{lean_ctor} => {rank}")),
                "Lean `toRank` missing `| .{lean_ctor} => {rank}`"
            );
            assert!(
                LEAN_PROTOTYPE_SRC.contains(&format!("| .{lean_ctor} => \"{snake}\"")),
                "Lean `asStr` missing `| .{lean_ctor} => \"{snake}\"`"
            );
        }

        // 2. Parse `witnessPureNoopBody` directly from `FaultSiteCensusPrototype.lean`
        //    and verify 0 fault sites (`[]`).
        let pure_noop_sites =
            census_lean_mir_def(LEAN_PROTOTYPE_SRC, "witnessPureNoopBody")
                .expect("parse witnessPureNoopBody from Lean");
        assert!(pure_noop_sites.is_empty());

        // 3. Parse all 4 probe witness `CapturedMir` bodies and their kernel-checked
        //    `ExpectedCensus` lists from `FaultSiteCensusPrototype.lean`, and assert
        //    3-way equality:
        //      (a) `census_lean_mir_def(LEAN_PROTOTYPE_SRC, witness_body)`
        //      (b) `parse_lean_expected_fault_site_list(LEAN_PROTOTYPE_SRC, expected_census_def)`
        //      (c) `run_false_proof_probe(probe).census`
        let expected_defs = [
            (
                FaultMutationProbe::CallArgBlindProbe,
                "witnessCallArgBlindExpectedCensus",
            ),
            (
                FaultMutationProbe::SwitchBreakStripProbe,
                "witnessSwitchBreakStripExpectedCensus",
            ),
            (
                FaultMutationProbe::LoopUpdateOverflowProbe,
                "witnessLoopUpdateOverflowExpectedCensus",
            ),
            (
                FaultMutationProbe::DerefAliasProbe,
                "witnessDerefAliasExpectedCensus",
            ),
        ];

        for (probe, expected_def_name) in expected_defs {
            let lean_body_name = probe.lean_witness_def_name();
            let scanned_from_lean_body =
                census_lean_mir_def(LEAN_PROTOTYPE_SRC, lean_body_name)
                    .unwrap_or_else(|e| panic!("failed to scan {lean_body_name}: {e}"));
            let lean_decide_expected =
                parse_lean_expected_fault_site_list(LEAN_PROTOTYPE_SRC, expected_def_name);
            let rust_probe_report = run_false_proof_probe(probe);

            assert_eq!(
                scanned_from_lean_body, lean_decide_expected,
                "Lean body scan vs. Lean `by decide` expected census mismatch for {probe:?}"
            );
            assert_eq!(
                rust_probe_report.census, lean_decide_expected,
                "Rust probe census vs. Lean `by decide` expected census mismatch for {probe:?}"
            );
            assert!(rust_probe_report.passed());
        }
    }
}
