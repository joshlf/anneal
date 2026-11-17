//! Track P Prototype: Independent MIR Fault-Site Census, Unified `PropertyRegistry`,
//! Fail-Closed Coverage Reconciler, and False-Proof Mutation Probes.
//!
//! This module provides an independent syntactic MIR fault-site census and
//! fail-closed obligation coverage reconciler that cross-checks `cargo-anneal`'s
//! obligation generator without consulting `obligations.rs`:
//!
//! 1. **`MirFaultClass` (12 Canonical Categories)**:
//!    1-to-1 with `Anneal.FaultSiteCensus.MirFaultClass` in
//!    `theory/Anneal/FaultSiteCensus.lean`.
//! 2. **`PropertyRegistry` & `PropertyStatus`**:
//!    Explicit per-class verification status (`EmittedAndVerified`,
//!    `UnsupportedFailClosed`, `UnemittedGap`) ensuring that any un-emitted or
//!    unsupported UB category fails closed (`UNKNOWN(UNMAPPED_FAULT_SITE)`).
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
    IrOperand, IrPlace, IrProjectionElem, IrRvalue, IrStatement, IrStatementKind, IrSwitchTargets,
    IrTerminator, IrTerminatorKind, IrUnOp, IrUnwindAction,
};

// ============================================================================
// 1. Canonical 12 `MirFaultClass` Categories & `FaultSite`
// ============================================================================

/// The 12 canonical runtime undefined-behavior fault classes in
/// `Runtime(PostCleanup)` MIR execution, matching
/// `Anneal.FaultSiteCensus.MirFaultClass` 1-to-1 in rank order `0..11`.
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

    /// Exact Lean 4 constructor name in `Anneal.FaultSiteCensus.MirFaultClass`.
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
            .trim_start_matches("Anneal.FaultSiteCensus.")
            .trim_start_matches("MirFaultClass.")
            .trim_start_matches('.');
        Self::ALL
            .into_iter()
            .find(|c| c.lean_ctor_name() == trimmed)
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
    /// closed (`UNKNOWN(UNMAPPED_FAULT_SITE)`).
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
            .with_status(
                MirFaultClass::TreeBorrowsViolation,
                PropertyStatus::UnemittedGap,
            )
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

    /// `[adv ep1-B1]` One-line registry summary for `agent-context`: how many of the
    /// 12 `MirFaultClass`es are `EmittedAndVerified`, plus every non-verified class
    /// with its status (absent classes report the fail-closed `UnemittedGap`).
    pub fn summary_line(&self) -> String {
        let total = MirFaultClass::ALL.len();
        let not_verified: Vec<String> = MirFaultClass::ALL
            .into_iter()
            .filter(|cls| !self.status(*cls).is_verified())
            .map(|cls| format!("{}={:?}", cls.as_str(), self.status(cls)))
            .collect();
        let verified = total - not_verified.len();
        if not_verified.is_empty() {
            format!("{verified}/{total} MirFaultClass EmittedAndVerified")
        } else {
            format!(
                "{verified}/{total} MirFaultClass EmittedAndVerified; not verified (fail-closed): {}",
                not_verified.join(", ")
            )
        }
    }
}

const fn default_class_description(cls: MirFaultClass) -> &'static str {
    match cls {
        MirFaultClass::ArithOverflow => {
            "Checked/unchecked integer arithmetic and negation overflow"
        }
        MirFaultClass::DivRemByZero => "Integer division/remainder by zero and signed MIN / -1",
        MirFaultClass::ShiftOverflow => "Bit shift distance >= bit_width or < 0",
        MirFaultClass::BoundsCheck => "Array/slice indexing, pointer offset, and CFG target bounds",
        MirFaultClass::PtrDerefInvalid => {
            "Pointer dereference liveness, bounds, and provenance validity"
        }
        MirFaultClass::PtrAlignMismatch => {
            "Pointer dereference and copy_nonoverlapping byte alignment"
        }
        MirFaultClass::TreeBorrowsViolation => {
            "Tree Borrows permission and active protector conflicts"
        }
        MirFaultClass::ScalarNicheInvalid => {
            "Scalar validity range, enum discriminant, transmute, and assume"
        }
        MirFaultClass::UninitRead => "Initialized local slot and memory byte reads",
        MirFaultClass::StorageLiveProtected => {
            "Local slot liveness and StorageLive/StorageDead protector checks"
        }
        MirFaultClass::CallAbiMismatch => {
            "Function call signature/ABI compatibility and unwind ABI checks"
        }
        MirFaultClass::UnreachableTerminator => {
            "Unreachable terminator and unreachable_unchecked non-reachability"
        }
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
    ZeroSized {
        fn_def_path: Option<String>,
    },
    ScalarInt {
        bits: u128,
        size_bytes: u64,
    },
    ScalarPtr {
        alloc_id: u64,
        offset_bytes: u64,
        size: u64,
    },
    Slice {
        meta: u64,
    },
    Indirect {
        alloc_id: u64,
        offset_bytes: u64,
    },
    Unevaluated(String),
    /// `[adv A4]` Constant operand whose `ConstOperand.ty.kind` is `RigidTy.param`,
    /// preserved so `ProtoOperand::has_no_param_const_ty` and
    /// `ProtoMirBody::has_no_param_call_const` mirror Lean's
    /// `operandHasNoParamConstTy` / `bodyHasNoParamCallConst` 1-to-1.
    ParamTypedConst(Box<ProtoConstValue>),
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
            ProtoOperand::Constant(ProtoConstValue::ParamTypedConst(inner)) => match inner.as_ref()
            {
                ProtoConstValue::Unevaluated(p) => Some(p.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    /// `[adv A4]` `true` iff `self` is not a constant operand with a `RigidTy.param` type,
    /// mirroring `Anneal.FaultSiteCensus.operandHasNoParamConstTy` 1-to-1.
    pub fn has_no_param_const_ty(&self) -> bool {
        !matches!(
            self,
            ProtoOperand::Constant(ProtoConstValue::ParamTypedConst(_))
        )
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

/// Prototype aggregate kind mirroring `Trusted.MirAst.AggregateKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoAggregateKind {
    Array,
    Tuple,
    Adt(String, usize, Option<usize>),
    Closure(String),
    Coroutine(String),
    RawPtr(bool),
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
    Aggregate(ProtoAggregateKind, Vec<ProtoOperand>),
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

impl ProtoMirBody {
    /// `[adv A4]` `true` iff no `Call` or `TailCall` terminator in `self` has a `func`
    /// constant operand with a `RigidTy.param` type, mirroring
    /// `Anneal.FaultSiteCensus.bodyHasNoParamCallConst` 1-to-1.
    pub fn has_no_param_call_const(&self) -> bool {
        self.basic_blocks
            .iter()
            .all(|bb| match &bb.terminator.kind {
                ProtoTerminatorKind::Call { func, .. }
                | ProtoTerminatorKind::TailCall { func, .. } => func.has_no_param_const_ty(),
                _ => true,
            })
    }

    /// `[adv ep1-B3]` `true` iff `self.basic_blocks` is non-empty and every syntactic
    /// successor block index in every basic block's terminator is
    /// `< self.basic_blocks.len()`, mirroring `Anneal.FaultSiteCensus.cfgTargetsInBounds`
    /// 1-to-1.
    pub fn cfg_targets_in_bounds(&self) -> bool {
        let num_blocks = self.basic_blocks.len();
        num_blocks > 0
            && self.basic_blocks.iter().all(|bb| {
                terminator_targets(&bb.terminator.kind)
                    .into_iter()
                    .all(|t| t < num_blocks)
            })
    }
}

/// `[adv ep1-B3]` Parsed `Trusted.MirAst.ContractRole` tag from a `CapturedMir` record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoContractRole {
    Subject,
    Model,
    Requires(String),
    Ensures(String),
    ExternalSpec(String),
}

/// `[adv ep1-B3]` Parsed `Trusted.MirAst.TraitImplEntry` record from `CapturedMir.traitImpls`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoTraitImplEntry {
    pub trait_method_def_path: String,
    pub impl_path: String,
}

/// `[adv ep1-B3]` Strictly scanned `Mir/<Item>.lean` `CapturedMir` body together with its
/// `ContractRole` and `traitImpls` table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedMirModuleMetadata {
    pub body: ProtoMirBody,
    pub role: ProtoContractRole,
    pub trait_impls: Vec<ProtoTraitImplEntry>,
}

/// Deduplicate and canonically order fault classes by `MirFaultClass::rank` (`0..11`),
/// matching `Anneal.FaultSiteCensus.dedupFaultClasses` 1-to-1.
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
///
/// `[adv B1]`: only places whose projection starts with `Deref` inspect pointer
/// provenance, permissions, and bounds; every other borrow can only fault on a
/// missing/dead root local or an uninitialized `Index` local (`[UninitRead]`).
pub fn census_place_ref_fault_classes(place: &ProtoPlace) -> Vec<MirFaultClass> {
    if !matches!(place.projection.first(), Some(ProtoProjectionElem::Deref)) {
        if place
            .projection
            .iter()
            .any(|p| matches!(p, ProtoProjectionElem::Subslice { .. }))
        {
            return vec![
                MirFaultClass::UninitRead,
                MirFaultClass::BoundsCheck,
                MirFaultClass::PtrAlignMismatch,
            ];
        }
        return vec![MirFaultClass::UninitRead];
    }
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
        ProtoConstValue::ParamTypedConst(inner) => census_const_value_fault_classes(inner),
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

/// Fault classes triggered by an operand whose loaded value is re-validated by
/// `validateLoadedValue` (`censusLoadedOperandFaultClasses`): `Copy`/`Move` of a
/// `bool` place holding a scalar other than `0`/`1` is `.ub`.
pub fn census_loaded_operand_fault_classes(op: &ProtoOperand) -> Vec<MirFaultClass> {
    match op {
        ProtoOperand::Copy(place) | ProtoOperand::Move(place) => {
            let mut out = census_place_read_fault_classes(place);
            out.push(MirFaultClass::ScalarNicheInvalid);
            out
        }
        ProtoOperand::Constant(cv) => census_const_value_fault_classes(cv),
    }
}

/// Fault classes triggered by a `ProtoBinOp` (`censusBinOpFaultClasses`).
pub fn census_bin_op_fault_classes(op: ProtoBinOp) -> Vec<MirFaultClass> {
    // `[adv B1]` precision (kernel-checked in Lean by `censusBinOpFaultClasses_exact`):
    // wrapping, overflow-flagged, masked-shift, bitwise, and comparison operators
    // never make `evalScalarBinOp` return `.ub`.
    match op {
        ProtoBinOp::AddUnchecked | ProtoBinOp::SubUnchecked | ProtoBinOp::MulUnchecked => {
            vec![MirFaultClass::ArithOverflow]
        }
        ProtoBinOp::Div | ProtoBinOp::Rem => {
            vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero]
        }
        ProtoBinOp::ShlUnchecked | ProtoBinOp::ShrUnchecked => vec![MirFaultClass::ShiftOverflow],
        ProtoBinOp::Offset => vec![
            MirFaultClass::ArithOverflow,
            MirFaultClass::BoundsCheck,
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::TreeBorrowsViolation,
        ],
        ProtoBinOp::Add
        | ProtoBinOp::Sub
        | ProtoBinOp::Mul
        | ProtoBinOp::AddWithOverflow
        | ProtoBinOp::SubWithOverflow
        | ProtoBinOp::MulWithOverflow
        | ProtoBinOp::Shl
        | ProtoBinOp::Shr
        | ProtoBinOp::BitXor
        | ProtoBinOp::BitAnd
        | ProtoBinOp::BitOr
        | ProtoBinOp::Eq
        | ProtoBinOp::Lt
        | ProtoBinOp::Le
        | ProtoBinOp::Ne
        | ProtoBinOp::Ge
        | ProtoBinOp::Gt
        | ProtoBinOp::Cmp => Vec::new(),
    }
}

/// Fault classes triggered by a `ProtoUnOp` (`censusUnOpFaultClasses`).
pub fn census_un_op_fault_classes(op: ProtoUnOp) -> Vec<MirFaultClass> {
    match op {
        ProtoUnOp::Neg => Vec::new(),
        ProtoUnOp::Not => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoUnOp::PtrMetadata => vec![MirFaultClass::PtrDerefInvalid],
    }
}

/// Fault classes triggered by a `ProtoNullOp` (`censusNullOpFaultClasses`).
pub fn census_null_op_fault_classes(op: &ProtoNullOp) -> Vec<MirFaultClass> {
    // `[adv B1]`: `evalRvalue` has no `NullaryOp` arm (`.unsupported`, never `.ub`).
    match op {
        ProtoNullOp::SizeOf
        | ProtoNullOp::AlignOf
        | ProtoNullOp::OffsetOf(_)
        | ProtoNullOp::UbChecks
        | ProtoNullOp::ContractChecks => Vec::new(),
    }
}

/// `[adv A1]` Fault classes triggered by a `ProtoProjectionElem` inside
/// `readProjectedValue` (used by projected `Deinit` and `Drop`), matching
/// `censusReadProjectedFaultClasses` in `FaultSiteCensus.lean`.
pub fn census_read_projected_fault_classes(proj: &ProtoProjectionElem) -> Vec<MirFaultClass> {
    match proj {
        ProtoProjectionElem::Deref
        | ProtoProjectionElem::Field(_)
        | ProtoProjectionElem::OpaqueCast
        | ProtoProjectionElem::UnwrapUnsafeBinder => Vec::new(),
        ProtoProjectionElem::Downcast(_, _) => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoProjectionElem::Subslice { .. } => vec![MirFaultClass::BoundsCheck],
        ProtoProjectionElem::Index(_) | ProtoProjectionElem::ConstantIndex { .. } => vec![
            MirFaultClass::BoundsCheck,
            MirFaultClass::ScalarNicheInvalid,
            MirFaultClass::UninitRead,
        ],
    }
}

/// Fault classes triggered by a `ProtoCastKind` (`censusCastKindFaultClasses`).
///
/// `[adv ep1-B1]`: `MutToConstPointer`, `PointerExposeProvenance`, and
/// `PointerWithExposedProvenance` have their own `.ub` edges in `evalRvalue`
/// (ill-shaped operands / pointer-width mismatches), pinned in Lean by
/// `evalRvalue_cast_ub_cause` and `evalRvalue_cast_own_ub_witnesses`.
pub fn census_cast_kind_fault_classes(kind: &ProtoCastKind) -> Vec<MirFaultClass> {
    match kind {
        ProtoCastKind::IntToInt
        | ProtoCastKind::FloatToInt
        | ProtoCastKind::FloatToFloat
        | ProtoCastKind::IntToFloat => Vec::new(),
        ProtoCastKind::PointerExposeProvenance => {
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        }
        ProtoCastKind::PointerWithExposedProvenance => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoCastKind::Transmute | ProtoCastKind::Subtype => {
            vec![MirFaultClass::ScalarNicheInvalid, MirFaultClass::UninitRead]
        }
        ProtoCastKind::PointerCoercion(coercion) if coercion == "MutToConstPointer" => {
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        }
        ProtoCastKind::PointerCoercion(coercion)
            if coercion == "Unsize" || coercion == "ArrayToPointer" =>
        {
            vec![
                MirFaultClass::BoundsCheck,
                MirFaultClass::PtrDerefInvalid,
                MirFaultClass::PtrAlignMismatch,
                MirFaultClass::TreeBorrowsViolation,
                MirFaultClass::ScalarNicheInvalid,
            ]
        }
        ProtoCastKind::PtrToPtr => vec![
            MirFaultClass::BoundsCheck,
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::PtrAlignMismatch,
            MirFaultClass::TreeBorrowsViolation,
            MirFaultClass::ScalarNicheInvalid,
        ],
        ProtoCastKind::PointerCoercion(_) | ProtoCastKind::FnPtrToPtr => vec![
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::ScalarNicheInvalid,
            MirFaultClass::CallAbiMismatch,
        ],
    }
}

/// True for the cast kinds that `evalRvalue` never evaluates (`castKindUnevaluated`).
///
/// Every `CastKind` (including IEEE-754 float casts, evaluated by
/// `evalFloatCastRvalue`) has an `evalRvalue` arm, so this is constantly `false`.
pub const fn cast_kind_unevaluated(_kind: &ProtoCastKind) -> bool {
    false
}

/// `[adv A1]` True for `ProtoAggregateKind`s that `evalRvalue` never evaluates
/// (`aggregateKindUnevaluated` in Lean).
pub const fn aggregate_kind_unevaluated(kind: &ProtoAggregateKind) -> bool {
    matches!(kind, ProtoAggregateKind::Coroutine(_))
}

/// `[adv ep1-B1]` Fault classes an evaluated aggregate can trigger beyond its
/// operands (`censusAggregateKindFaultClasses` in Lean, pinned by
/// `evalRvalue_aggregate_ub_cause`): union construction (`Adt(_, _, Some(_))`)
/// can fail the active-field overlay, and `RawPtr` validates pointer/metadata
/// widths and thin/wide shape.
pub fn census_aggregate_kind_fault_classes(kind: &ProtoAggregateKind) -> Vec<MirFaultClass> {
    match kind {
        ProtoAggregateKind::Adt(_, _, Some(_)) => vec![MirFaultClass::ScalarNicheInvalid],
        ProtoAggregateKind::RawPtr(_) => {
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        }
        ProtoAggregateKind::Array
        | ProtoAggregateKind::Tuple
        | ProtoAggregateKind::Adt(_, _, None)
        | ProtoAggregateKind::Closure(_)
        | ProtoAggregateKind::Coroutine(_) => Vec::new(),
    }
}

/// `[adv A1]` True for `ProtoRvalue` forms that `evalRvalue` never evaluates
/// (`rvalueUnevaluated` in Lean).
pub const fn rvalue_unevaluated(rv: &ProtoRvalue) -> bool {
    match rv {
        ProtoRvalue::ThreadLocalRef(_)
        | ProtoRvalue::NullaryOp(_)
        | ProtoRvalue::ShallowInitBox(_) => true,
        ProtoRvalue::Cast(kind, _) => cast_kind_unevaluated(kind),
        ProtoRvalue::Aggregate(kind, _) => aggregate_kind_unevaluated(kind),
        _ => false,
    }
}

/// Fault classes triggered by evaluating a `ProtoRvalue` (`censusRvalueFaultClasses`).
pub fn census_rvalue_fault_classes(rv: &ProtoRvalue) -> Vec<MirFaultClass> {
    match rv {
        ProtoRvalue::Use(op) => census_loaded_operand_fault_classes(op),
        ProtoRvalue::Repeat(op, _) => census_operand_fault_classes(op),
        ProtoRvalue::Ref { place, .. } | ProtoRvalue::RawPtr { place, .. } => {
            census_place_ref_fault_classes(place)
        }
        ProtoRvalue::ThreadLocalRef(_) => Vec::new(),
        ProtoRvalue::Len(place) => {
            let mut out = census_place_read_fault_classes(place);
            out.push(MirFaultClass::BoundsCheck);
            out
        }
        ProtoRvalue::Cast(kind, op) => {
            if cast_kind_unevaluated(kind) {
                return Vec::new();
            }
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
        ProtoRvalue::Aggregate(kind, ops) => {
            if aggregate_kind_unevaluated(kind) {
                return Vec::new();
            }
            let mut out = Vec::new();
            for op in ops {
                out.extend(census_operand_fault_classes(op));
            }
            out.extend(census_aggregate_kind_fault_classes(kind));
            out
        }
        ProtoRvalue::ShallowInitBox(_) => Vec::new(),
        ProtoRvalue::CopyForDeref(place) => census_place_read_fault_classes(place),
        ProtoRvalue::WrapUnsafeBinder(op) => census_loaded_operand_fault_classes(op),
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
/// (`censusStmtFaultClasses` in `FaultSiteCensus.lean`).
pub fn census_stmt_fault_classes(kind: &ProtoStatementKind) -> Vec<MirFaultClass> {
    let raw: Vec<MirFaultClass> = match kind {
        ProtoStatementKind::Nop
        | ProtoStatementKind::Coverage
        | ProtoStatementKind::ConstEvalCounter
        | ProtoStatementKind::BackwardIncompatibleDropHint(_) => Vec::new(),
        ProtoStatementKind::StorageLive(_) | ProtoStatementKind::StorageDead(_) => {
            vec![MirFaultClass::StorageLiveProtected]
        }
        ProtoStatementKind::PlaceMention(_) => vec![MirFaultClass::UninitRead],
        ProtoStatementKind::Deinit(place) => {
            if place.projection.is_empty() {
                vec![MirFaultClass::StorageLiveProtected]
            } else {
                let mut v = vec![MirFaultClass::UninitRead];
                for proj in &place.projection {
                    v.extend(census_read_projected_fault_classes(proj));
                }
                v
            }
        }
        ProtoStatementKind::Retag(place) => {
            let mut v = census_place_read_fault_classes(place);
            v.extend([
                MirFaultClass::BoundsCheck,
                MirFaultClass::PtrDerefInvalid,
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
            if rvalue_unevaluated(rv) {
                Vec::new()
            } else {
                let mut v = census_place_write_fault_classes(dst);
                v.extend(census_rvalue_fault_classes(rv));
                v
            }
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
/// (`terminatorTargets` in `FaultSiteCensus.lean`).
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
    if def_path == "core::intrinsics::exact_div" {
        return vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero];
    }
    // `[adv B1]` / `[adv A1]` parity fix: `Trusted.MirSemantics.classifyRustIntrinsic?`
    // and `isDirectExactDivTarget` only recognize `core::intrinsics::*`; `std::intrinsics::*`
    // paths are ordinary callees and contribute no intrinsic fault classes.
    let intrinsic_suffix = def_path.strip_prefix("core::intrinsics::");
    match intrinsic_suffix {
        Some("arith_offset") => vec![
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::ScalarNicheInvalid,
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
            MirFaultClass::ArithOverflow,
            MirFaultClass::DivRemByZero,
            MirFaultClass::ShiftOverflow,
            MirFaultClass::PtrDerefInvalid,
            MirFaultClass::ScalarNicheInvalid,
            MirFaultClass::CallAbiMismatch,
            MirFaultClass::UnreachableTerminator,
        ],
        _ => Vec::new(),
    }
}

/// Canonically ordered, duplicate-free `MirFaultClass` list for a `ProtoTerminatorKind`
/// (`censusTerminatorFaultClasses` in `FaultSiteCensus.lean`).
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
            let mut v = if place.projection.is_empty() {
                vec![MirFaultClass::StorageLiveProtected]
            } else {
                let mut p = vec![MirFaultClass::UninitRead];
                for proj in &place.projection {
                    p.extend(census_read_projected_fault_classes(proj));
                }
                p
            };
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::Assert { cond, unwind, .. } => {
            let mut v = census_operand_fault_classes(cond);
            v.push(MirFaultClass::ScalarNicheInvalid);
            // `[adv B1]`: only `Unreachable` (immediate `.ub`) and `Continue`
            // (propagation through a caller with `returnUnwind = .unreachable`)
            // unwind edges can fault; `Cleanup`/`Terminate` never do.
            match unwind {
                ProtoUnwindAction::Unreachable => v.push(MirFaultClass::UnreachableTerminator),
                ProtoUnwindAction::Continue => v.push(MirFaultClass::CallAbiMismatch),
                ProtoUnwindAction::Cleanup(_) | ProtoUnwindAction::Terminate => {}
            }
            v.extend(target_oob);
            v
        }
        ProtoTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            let mut v = census_operand_fault_classes(func);
            for arg in args {
                v.extend(census_operand_fault_classes(arg));
            }
            if target.is_some() {
                v.extend(census_place_write_fault_classes(destination));
            }
            v.push(MirFaultClass::CallAbiMismatch);
            match func.extract_callee_def_path() {
                Some(def_path) => {
                    if target.is_some() {
                        v.extend(census_callee_def_path_fault_classes(def_path));
                    } else if matches!(
                        def_path,
                        "core::hint::unreachable_unchecked"
                            | "std::hint::unreachable_unchecked"
                            | "core::intrinsics::unreachable"
                    ) {
                        v.push(MirFaultClass::UnreachableTerminator);
                    }
                }
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
            v.extend([
                MirFaultClass::TreeBorrowsViolation,
                MirFaultClass::UninitRead,
                MirFaultClass::StorageLiveProtected,
                MirFaultClass::CallAbiMismatch,
            ]);
            if func.extract_callee_def_path().is_none() {
                v.push(MirFaultClass::PtrDerefInvalid);
            }
            v
        }
    };
    dedup_fault_classes(raw)
}

/// Independent syntactic fault-site census of a `ProtoMirBody`
/// (`censusMirBodyFaultSites` in `FaultSiteCensus.lean`).
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
    let is_type_param = matches!(
        &co.ty.kind,
        anneal_rustc_capture::lean_emit::IrRigidTy::Param { .. }
    );
    let inner = match &co.val {
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
    };
    if is_type_param {
        ProtoConstValue::ParamTypedConst(Box::new(inner))
    } else {
        inner
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
        IrRvalue::Aggregate(ak, ops) => {
            let kind = match ak {
                IrAggregateKind::Array(_) => ProtoAggregateKind::Array,
                IrAggregateKind::Tuple => ProtoAggregateKind::Tuple,
                IrAggregateKind::Adt(def_id, variant_idx, active_field) => {
                    ProtoAggregateKind::Adt(def_id.clone(), *variant_idx, *active_field)
                }
                IrAggregateKind::Closure(def_id) => ProtoAggregateKind::Closure(def_id.clone()),
                IrAggregateKind::Coroutine(def_id) => ProtoAggregateKind::Coroutine(def_id.clone()),
                IrAggregateKind::RawPtr(_, m) => {
                    ProtoAggregateKind::RawPtr(matches!(m, IrMutability::Mut))
                }
            };
            ProtoRvalue::Aggregate(kind, ops.iter().map(convert_ir_operand).collect())
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
        IrTerminatorKind::SwitchInt(
            op,
            IrSwitchTargets {
                branches,
                otherwise,
            },
        ) => ProtoTerminatorKind::SwitchInt(
            convert_ir_operand(op),
            ProtoSwitchTargets {
                branches: branches.clone(),
                otherwise: *otherwise,
            },
        ),
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
    CharLit(char),
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

        // `[adv A1]` Character literal `'x'` or `'\x'` (including `'\''`):
        // lexed as `LeanToken::CharLit(char)` so `parse_string` rejects `'a'` instead
        // of reading it as `""`, and `'\''` advances past the closing quote.
        if ch == '\'' {
            if let Some((lit_ch, next_i)) = lex_char_literal(&chars, i)? {
                tokens.push(LeanToken::CharLit(lit_ch));
                i = next_i;
                continue;
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
        if let Some((content, next_i)) = lex_raw_string(&chars, i)? {
            tokens.push(LeanToken::StrLit(content));
            i = next_i;
            continue;
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
            // `[adv B1]`: every `<ident>!"..."` (`s!`, `m!`, `f!`, user `foo!` macros) is
            // an interpolated string in Lean; lexing it as a plain string would let a
            // `{"..."}` interpolation leak string contents into the token stream.
            if ident.ends_with('!') && next_i < n && chars[next_i] == '"' {
                let (content, after) = lex_interpolated_string(&chars, next_i + 1)?;
                tokens.push(LeanToken::StrLit(content));
                i = after;
                continue;
            }
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

/// Decode one Lean 4 string escape starting right after the backslash at
/// `chars[i]` (`Lean.Parser.quotedCharCoreFn`): `\\`, `\"`, `\'`, `\n`, `\r`,
/// `\t`, `\xHH` (exactly 2 hex digits), `\uHHHH` (exactly 4 hex digits), a
/// string gap (`\` + newline + skipped whitespace), and `\{` inside interpolated
/// strings only. Any other escape fails closed (`[adv B1]`): silently mangling an
/// unknown escape could change a callee `DefPath` (for example
/// `"core::intrinsics::unreach\u0061ble"`) and hide its fault classes.
fn lex_string_escape(
    chars: &[char],
    i: usize,
    out: &mut String,
    interpolated: bool,
) -> Result<usize, CensusScanError> {
    let n = chars.len();
    let bad = |what: &str| {
        CensusScanError::MalformedCapturedMirSyntax(format!("invalid Lean string escape {what}"))
    };
    if i >= n {
        return Err(CensusScanError::UnterminatedStringLiteral);
    }
    let hex_digits = |start: usize, count: usize| -> Result<u32, CensusScanError> {
        if start + count > n
            || !chars[start..start + count]
                .iter()
                .all(|c| c.is_ascii_hexdigit())
        {
            return Err(bad("(expected hex digits)"));
        }
        let hex: String = chars[start..start + count].iter().collect();
        u32::from_str_radix(&hex, 16).map_err(|_| bad("(hex overflow)"))
    };
    match chars[i] {
        '\\' => out.push('\\'),
        '"' => out.push('"'),
        '\'' => out.push('\''),
        'n' => out.push('\n'),
        'r' => out.push('\r'),
        't' => out.push('\t'),
        'x' => {
            let code = hex_digits(i + 1, 2)?;
            out.push(char::from_u32(code).ok_or_else(|| bad("(invalid \\x code point)"))?);
            return Ok(i + 3);
        }
        'u' => {
            let code = hex_digits(i + 1, 4)?;
            out.push(char::from_u32(code).ok_or_else(|| bad("(invalid \\u code point)"))?);
            return Ok(i + 5);
        }
        '\n' => {
            let mut j = i + 1;
            while j < n && chars[j].is_whitespace() {
                j += 1;
            }
            return Ok(j);
        }
        '{' if interpolated => out.push('{'),
        other => return Err(bad(&format!("`\\{other}`"))),
    }
    Ok(i + 1)
}

/// `[adv A1]` Lex a Lean character literal `'c'` or `'\...'` starting at `open_quote`
/// (`chars[open_quote] == '\''`). Properly decodes `'\''`, `'\"'`, `'\\'`, `'\xHH'`,
/// and `'\uHHHH'` via `lex_string_escape` so `'\''` never terminates prematurely at
/// the escaped quote.
fn lex_char_literal(
    chars: &[char],
    open_quote: usize,
) -> Result<Option<(char, usize)>, CensusScanError> {
    let n = chars.len();
    let prev_is_ident = open_quote > 0 && is_lean_ident_continue(chars[open_quote - 1]);
    if prev_is_ident || open_quote + 2 >= n {
        return Ok(None);
    }
    if chars[open_quote + 1] == '\\' {
        let mut decoded = String::new();
        let after_esc = lex_string_escape(chars, open_quote + 2, &mut decoded, false)?;
        let mut ch_iter = decoded.chars();
        let Some(ch) = ch_iter.next() else {
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "empty character literal escape".to_string(),
            ));
        };
        if ch_iter.next().is_some() || after_esc >= n || chars[after_esc] != '\'' {
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "unterminated escaped character literal".to_string(),
            ));
        }
        return Ok(Some((ch, after_esc + 1)));
    }
    if chars[open_quote + 2] == '\''
        && chars[open_quote + 1] != '\''
        && chars[open_quote + 1] != '\n'
    {
        return Ok(Some((chars[open_quote + 1], open_quote + 3)));
    }
    Ok(None)
}

/// `[adv A1]` Lex a Lean raw string literal `r"..."` or `r#"..."#` starting at `start`.
fn lex_raw_string(
    chars: &[char],
    start: usize,
) -> Result<Option<(String, usize)>, CensusScanError> {
    let n = chars.len();
    let prev_is_ident = start > 0 && is_lean_ident_continue(chars[start - 1]);
    if prev_is_ident
        || start + 1 >= n
        || chars[start] != 'r'
        || (chars[start + 1] != '"' && chars[start + 1] != '#')
    {
        return Ok(None);
    }
    let mut hashes = 0usize;
    let mut k = start + 1;
    while k < n && chars[k] == '#' {
        hashes += 1;
        k += 1;
    }
    if k >= n || chars[k] != '"' {
        return Ok(None);
    }
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
    Ok(Some((content, k)))
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
            i = lex_string_escape(chars, i + 1, &mut out, false)?;
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
            i = lex_string_escape(chars, i + 1, &mut out, true).map_err(|e| match e {
                CensusScanError::UnterminatedStringLiteral => {
                    CensusScanError::UnterminatedInterpolatedString
                }
                other => other,
            })?;
            continue;
        }
        if ch == '{' {
            // Walk nested `{ ... }` inside string interpolation, respecting nested
            // strings, raw strings, nested `<ident>!"..."` interpolations, character
            // literals `'...'`, and `«...»` guillemet identifiers (`[adv A1]`).
            let mut brace_depth = 1usize;
            out.push('{');
            i += 1;
            while i < n && brace_depth > 0 {
                // `[adv B1]`: a `--` or `/-` comment inside an interpolated term would
                // swallow the closing `}`/`"` in Lean but not here; fail closed.
                if (chars[i] == '-' && i + 1 < n && chars[i + 1] == '-')
                    || (chars[i] == '/' && i + 1 < n && chars[i + 1] == '-')
                {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(
                        "comment inside string interpolation".to_string(),
                    ));
                }
                if chars[i] == '\'' {
                    if let Some((lit_ch, next_i)) = lex_char_literal(chars, i)? {
                        out.push('\'');
                        out.push(lit_ch);
                        out.push('\'');
                        i = next_i;
                        continue;
                    }
                }
                if chars[i] == '«' {
                    let (ident, next_i) = lex_dotted_ident(chars, i)?;
                    out.push('«');
                    out.push_str(&ident);
                    out.push('»');
                    i = next_i;
                    continue;
                }
                if let Some((raw_s, next_i)) = lex_raw_string(chars, i)? {
                    out.push('"');
                    out.push_str(&raw_s);
                    out.push('"');
                    i = next_i;
                    continue;
                }
                if chars[i].is_alphabetic() || chars[i] == '_' {
                    let (ident, next_i) = lex_dotted_ident(chars, i)?;
                    out.push_str(&ident);
                    if ident.ends_with('!') && next_i < n && chars[next_i] == '"' {
                        let (inner_interp, after_interp) =
                            lex_interpolated_string(chars, next_i + 1)?;
                        out.push('"');
                        out.push_str(&inner_interp);
                        out.push('"');
                        i = after_interp;
                    } else {
                        i = next_i;
                    }
                    continue;
                }
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

/// Lean namespaces under which `Trusted` MIR AST constructors may be fully qualified.
/// `[adv B2]`: pinned to the `V2026_06_01` dialect that the census and
/// `Trusted.MirSemantics` are defined over; a `Trusted.Rustc.V2026_08_01.MirAst`
/// constructor has a different type and different semantics.
const MIR_AST_NAMESPACES: [&str; 4] = [
    "MirAst",
    "Trusted.MirAst",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "_root_.Trusted.Rustc.V2026_06_01.MirAst",
];

/// `[adv B2]` Exact namespaces a strict `Mir/<Item>.lean` module may `open`: the
/// four opened by `anneal-rustc-capture`'s `render_mir_module_header`, plus the
/// default-dialect aliases. Opening any other namespace (another MIR dialect, or a
/// namespace that could contribute look-alike `TerminatorKind.*` declarations)
/// fails closed.
const STRICT_MODULE_OPENS: [&str; 6] = [
    "Trusted.Rustc.V2026_06_01.Layout",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "Trusted.Rustc.V2026_06_01.MirSemantics",
    "Trusted.VerificationResult",
    "Trusted.MirAst",
    "Trusted.MirSemantics",
];

/// `[adv A3]` Exact module paths a strict `Mir/<Item>.lean` module may `import`:
/// `Trusted` or the `V2026_06_01` dialect modules re-exported by `Trusted`.
/// Rejects `import Trusted.Evil` and foreign dialects such as
/// `import Trusted.Rustc.V2026_08_01.MirAst`.
const STRICT_MODULE_IMPORTS: [&str; 9] = [
    "Trusted",
    "Trusted.MirAst",
    "Trusted.MirSemantics",
    "Trusted.VerificationResult",
    "Trusted.Rustc.V2026_06_01.Layout",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "Trusted.Rustc.V2026_06_01.MirSemantics",
    "Trusted.Rustc.V2026_06_01",
    "Trusted.Rustc",
];

/// `[adv A3]` True iff `ty` is `CapturedMir` or `<ns>.CapturedMir` for a dialect-pinned
/// namespace `<ns>` in `MIR_AST_NAMESPACES` (rejecting `Evil.CapturedMir` and
/// `Trusted.Rustc.V2026_08_01.MirAst.CapturedMir`).
fn is_valid_captured_mir_type(ty: &str) -> bool {
    ty == "CapturedMir"
        || MIR_AST_NAMESPACES
            .iter()
            .any(|ns| ty.strip_prefix(ns).and_then(|r| r.strip_prefix('.')) == Some("CapturedMir"))
}

/// `Trusted` MIR AST type names whose constructors or fields the scanner
/// interprets. Strict module scanning rejects any declaration or namespace that
/// reuses one of these names, because a local `def TerminatorKind.goto` would
/// shadow the real constructor for every `TerminatorKind.goto` written in the module.
const MIR_AST_TYPE_NAMES: [&str; 62] = [
    "AggregateKind",
    "BasicBlockData",
    "BinOp",
    "Bool",
    "BorrowKind",
    "CapturedMir",
    "CastKind",
    "ConstOperand",
    "ConstScalar",
    "ConstValue",
    "ContractRole",
    "CrateClaim",
    "CrateVerificationResult",
    "ItemProof",
    "ItemSpec",
    "List",
    "LocalDecl",
    "MirCallContract",
    "MirPhaseTag",
    "ModularItemProof",
    "ModularItemSpec",
    "ModularVerificationClaim",
    "ModularVerificationResult",
    "Mutability",
    "Nat",
    "NonDivergingIntrinsic",
    "NullOp",
    "Operand",
    "Option",
    "Place",
    "ProjectionElem",
    "ProvenancePtr",
    "RetagKind",
    "RigidTy",
    "Rvalue",
    "ScalarInt",
    "Statement",
    "StatementKind",
    "StatefulEquivClaim",
    "StatefulEquivItemProof",
    "StatefulEquivItemSpec",
    "StatefulEquivVerificationResult",
    "StatefulItemProof",
    "StatefulItemSpec",
    "StatefulVerificationClaim",
    "StatefulVerificationResult",
    "SwitchTargets",
    "Terminator",
    "TerminatorKind",
    "TotalItemProof",
    "TotalItemSpec",
    "TotalVerificationClaim",
    "TotalVerificationResult",
    "Ty",
    "UbExceptionClaim",
    "UbExceptionItemProof",
    "UbExceptionItemSpec",
    "UbExceptionVerificationResult",
    "UnOp",
    "UnwindAction",
    "VerificationClaim",
    "VerificationResult",
];

/// `[adv B1]`: validate that the constructor head `full` (whose last segment is
/// `short`) denotes constructor `short` of `type_name`: either leading-dot syntax
/// (`.short`, resolved against the expected type) or `type_name.short`, optionally
/// under a known `Trusted` MIR AST namespace. Bare heads (`goto 1`) and foreign
/// qualifiers (`Evil.goto 1`) may resolve to arbitrary non-inline user definitions
/// in Lean, so they fail closed instead of being read as the constructor.
fn check_ctor_qualifier(full: &str, short: &str, type_name: &str) -> Result<(), CensusScanError> {
    if full.strip_prefix('.') == Some(short) {
        return Ok(());
    }
    let qualified = format!("{type_name}.{short}");
    if full == qualified
        || MIR_AST_NAMESPACES
            .iter()
            .any(|ns| full.strip_prefix(ns).and_then(|r| r.strip_prefix('.')) == Some(&qualified))
    {
        return Ok(());
    }
    Err(CensusScanError::MalformedCapturedMirSyntax(format!(
        "constructor head `{full}` is not a `{type_name}` constructor \
         (expected `.{short}` or `{type_name}.{short}`)"
    )))
}

/// True for tokens that can begin a new top-level Lean command, used to verify
/// that nothing (such as `|> mutate` or `.withBlocks evil`) is applied to a parsed
/// `CapturedMir` record before the next declaration.
fn is_lean_command_start(tok: &LeanToken) -> bool {
    match tok {
        LeanToken::Ident(kw) => {
            kw.starts_with('#')
                || kw.starts_with('@')
                || matches!(
                    kw.as_str(),
                    "def"
                        | "theorem"
                        | "lemma"
                        | "abbrev"
                        | "example"
                        | "instance"
                        | "structure"
                        | "inductive"
                        | "class"
                        | "opaque"
                        | "axiom"
                        | "namespace"
                        | "end"
                        | "section"
                        | "open"
                        | "import"
                        | "export"
                        | "set_option"
                        | "attribute"
                        | "local"
                        | "scoped"
                        | "private"
                        | "protected"
                        | "noncomputable"
                        | "partial"
                        | "unsafe"
                        | "mutual"
                        | "variable"
                        | "universe"
                        | "macro"
                        | "macro_rules"
                        | "syntax"
                        | "notation"
                        | "elab"
                        | "deriving"
                )
        }
        _ => false,
    }
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
                                | LeanToken::CharLit(_)
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
                            | LeanToken::CharLit(_)
                            | LeanToken::Dot
                    )
                ) {
                    self.skip_balanced_expr()?;
                }
                Ok(())
            }
            Some(LeanToken::NatLit(_) | LeanToken::StrLit(_) | LeanToken::CharLit(_)) => Ok(()),
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "unexpected token while skipping expression: {other:?}"
            ))),
        }
    }

    /// Skip a single atomic Lean term (a balanced `(...)`, `{...}`, or `[...]`, a
    /// `.ctor` / identifier atom, or a literal) without consuming subsequent
    /// sibling arguments in an outer application such as `List.cons head tail`.
    fn skip_atomic_expr(&mut self) -> Result<(), CensusScanError> {
        match self.peek() {
            Some(LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket) => {
                self.skip_balanced_expr()
            }
            Some(LeanToken::Dot) => {
                self.next();
                match self.next() {
                    Some(LeanToken::Ident(_)) => Ok(()),
                    other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "expected identifier after `.`, found {other:?}"
                    ))),
                }
            }
            Some(
                LeanToken::Ident(_)
                | LeanToken::NatLit(_)
                | LeanToken::StrLit(_)
                | LeanToken::CharLit(_),
            ) => {
                self.next();
                Ok(())
            }
            other => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                "unexpected token while skipping atomic expression: {other:?}"
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
            let (full, short) = cur.parse_ctor_head()?;
            if full != short {
                check_ctor_qualifier(&full, &short, "Bool")?;
            }
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
            let mut seen_fields: BTreeSet<String> = BTreeSet::new();
            while !matches!(cur.peek(), Some(LeanToken::RBrace)) {
                let field_name = match cur.next() {
                    Some(LeanToken::Ident(name)) => name.clone(),
                    other => {
                        return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                            "expected record field name, found {other:?}"
                        )));
                    }
                };
                // `[adv B1]`: Lean rejects duplicate structure-instance fields; never
                // let a later `basicBlocks := ...` silently replace an earlier one.
                if !seen_fields.insert(field_name.clone()) {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "duplicate record field `{field_name}`"
                    )));
                }
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

    fn parse_captured_mir_metadata(&mut self) -> Result<ParsedMirModuleMetadata, CensusScanError> {
        let mut def_path: Option<String> = None;
        let mut has_phase = false;
        let mut role: Option<ProtoContractRole> = None;
        let mut has_arg_count = false;
        let mut has_local_decls = false;
        let mut basic_blocks: Option<Vec<ProtoBasicBlock>> = None;
        let mut has_fn_abi = false;
        let mut has_layouts = false;
        let mut has_allocations = false;
        let mut trait_impls: Vec<ProtoTraitImplEntry> = Vec::new();

        self.parse_record(|field, cur| {
            match field {
                "defPath" => {
                    def_path = Some(cur.parse_string()?);
                }
                "phase" => {
                    cur.parse_mir_phase_tag()?;
                    has_phase = true;
                }
                "role" => {
                    role = Some(cur.parse_contract_role()?);
                }
                "argCount" => {
                    let _ = cur.parse_usize()?;
                    has_arg_count = true;
                }
                "localDecls" => {
                    let _ = cur.parse_list(|c| c.skip_atomic_expr())?;
                    has_local_decls = true;
                }
                "basicBlocks" => {
                    basic_blocks = Some(cur.parse_list(|c| c.parse_basic_block())?);
                }
                "fnAbi" => {
                    cur.skip_balanced_expr()?;
                    has_fn_abi = true;
                }
                "layouts" => {
                    cur.skip_balanced_expr()?;
                    has_layouts = true;
                }
                "allocations" => {
                    let _ = cur.parse_list(|c| c.skip_atomic_expr())?;
                    has_allocations = true;
                }
                "typeParamCount" => {
                    let _ = cur.parse_usize()?;
                }
                "genericParams" => {
                    let _ = cur.parse_list(|c| c.skip_atomic_expr())?;
                }
                "traitImpls" => {
                    trait_impls = cur.parse_list(|c| c.parse_trait_impl_entry())?;
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown CapturedMir field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;

        let def_path = def_path.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax(
                "CapturedMir record is missing required `defPath` field".to_string(),
            )
        })?;
        let role = role.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax(
                "CapturedMir record is missing required `role` field".to_string(),
            )
        })?;
        for (present, name) in [
            (has_phase, "phase"),
            (has_arg_count, "argCount"),
            (has_local_decls, "localDecls"),
            (has_fn_abi, "fnAbi"),
            (has_layouts, "layouts"),
            (has_allocations, "allocations"),
        ] {
            if !present {
                return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "CapturedMir record is missing required `{name}` field"
                )));
            }
        }
        let basic_blocks = basic_blocks.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax(
                "CapturedMir record is missing required `basicBlocks` field".to_string(),
            )
        })?;

        Ok(ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path,
                basic_blocks,
            },
            role,
            trait_impls,
        })
    }

    fn parse_mir_phase_tag(&mut self) -> Result<(), CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "MirPhaseTag")?;
            match short.as_str() {
                "runtimePostCleanup" | "runtimeOptimized" => Ok(()),
                "other" => {
                    let _ = cur.parse_string()?;
                    Ok(())
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown MirPhaseTag constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_contract_role(&mut self) -> Result<ProtoContractRole, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "ContractRole")?;
            // `[adv ep1-B1]` / `[adv ep1-B3]`: exactly the `Trusted.MirAst.ContractRole`
            // constructors (`subject`, `model`, and the mandatory `DefPath`-carrying
            // `requires` / `ensures` / `externalSpec`).
            match short.as_str() {
                "subject" => Ok(ProtoContractRole::Subject),
                "model" => Ok(ProtoContractRole::Model),
                "requires" => Ok(ProtoContractRole::Requires(cur.parse_string()?)),
                "ensures" => Ok(ProtoContractRole::Ensures(cur.parse_string()?)),
                "externalSpec" => Ok(ProtoContractRole::ExternalSpec(cur.parse_string()?)),
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown ContractRole constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_trait_impl_entry(&mut self) -> Result<ProtoTraitImplEntry, CensusScanError> {
        let mut trait_method_def_path: Option<String> = None;
        let mut impl_path: Option<String> = None;
        self.parse_record(|field, cur| {
            match field {
                "traitRef" => {
                    let mut def_path: Option<String> = None;
                    let mut has_args = false;
                    cur.parse_record(|tr_field, tr_cur| {
                        match tr_field {
                            "defPath" => {
                                def_path = Some(tr_cur.parse_string()?);
                            }
                            "args" => {
                                let _ = tr_cur.parse_list(|c| c.skip_atomic_expr())?;
                                has_args = true;
                            }
                            other => {
                                return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                                    "unknown TraitRef field `{other}`"
                                )));
                            }
                        }
                        Ok(())
                    })?;
                    if !has_args {
                        return Err(CensusScanError::MalformedCapturedMirSyntax(
                            "TraitRef missing `args` field".to_string(),
                        ));
                    }
                    trait_method_def_path = Some(def_path.ok_or_else(|| {
                        CensusScanError::MalformedCapturedMirSyntax(
                            "TraitRef missing `defPath` field".to_string(),
                        )
                    })?);
                }
                "implPath" => {
                    impl_path = Some(cur.parse_string()?);
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown TraitImplEntry field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;
        Ok(ProtoTraitImplEntry {
            trait_method_def_path: trait_method_def_path.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "TraitImplEntry missing `traitRef` field".to_string(),
                )
            })?,
            impl_path: impl_path.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "TraitImplEntry missing `implPath` field".to_string(),
                )
            })?,
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
            is_cleanup: is_cleanup.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax(
                    "BasicBlockData missing `isCleanup`".to_string(),
                )
            })?,
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
            span: span.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Statement missing `span`".to_string())
            })?,
        })
    }

    fn parse_statement_kind(&mut self) -> Result<ProtoStatementKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "StatementKind")?;
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
            check_ctor_qualifier(&full, &short, "RetagKind")?;
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
            check_ctor_qualifier(&full, &short, "NonDivergingIntrinsic")?;
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
                CensusScanError::MalformedCapturedMirSyntax(
                    "Place missing `projection`".to_string(),
                )
            })?,
        })
    }

    fn parse_projection_elem(&mut self) -> Result<ProtoProjectionElem, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "ProjectionElem")?;
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
            check_ctor_qualifier(&full, &short, "Operand")?;
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
        let mut has_ty = false;
        let mut fn_def_path: Option<String> = None;
        let mut is_type_param = false;
        let mut val: Option<ProtoConstValue> = None;

        self.parse_record(|field, cur| {
            match field {
                "ty" => {
                    let (fn_def, is_param) = cur.parse_ty_extract_fn_def()?;
                    fn_def_path = fn_def;
                    is_type_param = is_param;
                    has_ty = true;
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

        if !has_ty {
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "ConstOperand missing `ty`".to_string(),
            ));
        }
        let mut cv = val.ok_or_else(|| {
            CensusScanError::MalformedCapturedMirSyntax("ConstOperand missing `val`".to_string())
        })?;
        if let ProtoConstValue::ZeroSized {
            fn_def_path: ref mut slot,
        } = cv
        {
            *slot = fn_def_path;
        } else if fn_def_path.is_some() {
            // `[adv B1]`: `extractCalleeDefPath?` takes the callee from an
            // `RigidTy.fnDef` type before looking at the value, which
            // `ProtoConstValue` can only represent for zero-sized function items.
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "`RigidTy.fnDef`-typed constant with a non-zero-sized value".to_string(),
            ));
        }
        if is_type_param {
            Ok(ProtoConstValue::ParamTypedConst(Box::new(cv)))
        } else {
            Ok(cv)
        }
    }

    fn parse_ty_extract_fn_def(&mut self) -> Result<(Option<String>, bool), CensusScanError> {
        let mut has_kind = false;
        let mut has_layout_idx = false;
        let mut fn_def: Option<String> = None;
        let mut is_type_param = false;
        self.parse_record(|field, cur| {
            match field {
                "kind" => {
                    let (fd, is_param) = cur.parse_rigid_ty_extract_fn_def()?;
                    fn_def = fd;
                    is_type_param = is_param;
                    has_kind = true;
                }
                "layoutIdx" => {
                    let _ = cur.parse_usize()?;
                    has_layout_idx = true;
                }
                other => {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unknown Ty field `{other}`"
                    )));
                }
            }
            Ok(())
        })?;
        if !has_kind {
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "Ty missing `kind`".to_string(),
            ));
        }
        if !has_layout_idx {
            return Err(CensusScanError::MalformedCapturedMirSyntax(
                "Ty missing `layoutIdx`".to_string(),
            ));
        }
        Ok((fn_def, is_type_param))
    }

    fn parse_rigid_ty_extract_fn_def(&mut self) -> Result<(Option<String>, bool), CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "RigidTy")?;
            if short == "fnDef" {
                let path = cur.parse_string()?;
                let _ = cur.parse_list(|c| c.skip_atomic_expr())?; // typeArgs list
                Ok((Some(path), false))
            } else {
                let is_param = short == "param";
                // Skip any remaining arguments inside this RigidTy constructor
                while !matches!(
                    cur.peek(),
                    Some(
                        LeanToken::Comma
                            | LeanToken::Semicolon
                            | LeanToken::RBrace
                            | LeanToken::RParen
                    ) | None
                ) {
                    cur.skip_balanced_expr()?;
                }
                Ok((None, is_param))
            }
        })
    }

    fn parse_const_value(&mut self) -> Result<ProtoConstValue, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "ConstValue")?;
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
            check_ctor_qualifier(&full, &short, "ConstScalar")?;
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
                        bits: bits.ok_or_else(|| {
                            CensusScanError::MalformedCapturedMirSyntax(
                                "ScalarInt missing `bits`".to_string(),
                            )
                        })?,
                        size_bytes: size_bytes.ok_or_else(|| {
                            CensusScanError::MalformedCapturedMirSyntax(
                                "ScalarInt missing `sizeBytes`".to_string(),
                            )
                        })?,
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
                        alloc_id: alloc_id.ok_or_else(|| {
                            CensusScanError::MalformedCapturedMirSyntax(
                                "ProvenancePtr missing `allocId`".to_string(),
                            )
                        })?,
                        offset_bytes: offset_bytes.ok_or_else(|| {
                            CensusScanError::MalformedCapturedMirSyntax(
                                "ProvenancePtr missing `offsetBytes`".to_string(),
                            )
                        })?,
                        size,
                    })
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown ConstScalar constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_aggregate_kind(&mut self) -> Result<ProtoAggregateKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "AggregateKind")?;
            match short.as_str() {
                "array" => {
                    cur.skip_balanced_expr()?; // elemTy
                    Ok(ProtoAggregateKind::Array)
                }
                "tuple" => Ok(ProtoAggregateKind::Tuple),
                "adt" => {
                    let def_id = cur.parse_string()?;
                    let variant_idx = cur.parse_usize()?;
                    let active_field = cur.parse_option(|c| c.parse_usize())?;
                    Ok(ProtoAggregateKind::Adt(def_id, variant_idx, active_field))
                }
                "closure" => Ok(ProtoAggregateKind::Closure(cur.parse_string()?)),
                "coroutine" => Ok(ProtoAggregateKind::Coroutine(cur.parse_string()?)),
                "rawPtr" => {
                    cur.skip_balanced_expr()?; // pointeeTy
                    let mutable = cur.parse_mutability()?;
                    Ok(ProtoAggregateKind::RawPtr(mutable))
                }
                _ => Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                    "unknown AggregateKind constructor `{full}`"
                ))),
            }
        })
    }

    fn parse_rvalue(&mut self) -> Result<ProtoRvalue, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "Rvalue")?;
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
                    let kind = cur.parse_aggregate_kind()?;
                    let ops = cur.parse_list(|c| c.parse_operand())?;
                    Ok(ProtoRvalue::Aggregate(kind, ops))
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
            check_ctor_qualifier(&full, &short, "BorrowKind")?;
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
            check_ctor_qualifier(&full, &short, "Mutability")?;
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
            check_ctor_qualifier(&full, &short, "CastKind")?;
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
            check_ctor_qualifier(&full, &short, "BinOp")?;
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
            check_ctor_qualifier(&full, &short, "UnOp")?;
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
            check_ctor_qualifier(&full, &short, "NullOp")?;
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
            span: span.ok_or_else(|| {
                CensusScanError::MalformedCapturedMirSyntax("Terminator missing `span`".to_string())
            })?,
        })
    }

    fn parse_terminator_kind(&mut self) -> Result<ProtoTerminatorKind, CensusScanError> {
        self.with_optional_parens(|cur| {
            let (full, short) = cur.parse_ctor_head()?;
            check_ctor_qualifier(&full, &short, "TerminatorKind")?;
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
            check_ctor_qualifier(&full, &short, "UnwindAction")?;
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
    parse_lean_captured_mir_def_metadata(lean_src, def_name).map(|m| m.body)
}

fn parse_lean_captured_mir_def_metadata(
    lean_src: &str,
    def_name: &str,
) -> Result<ParsedMirModuleMetadata, CensusScanError> {
    let tokens = tokenize_lean_source(lean_src)?;
    let mut found_body: Option<ParsedMirModuleMetadata> = None;

    let mut idx = 0;
    let mut delim_depth = 0isize;
    while idx + 4 < tokens.len() {
        match &tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                delim_depth += 1;
                idx += 1;
                continue;
            }
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                delim_depth -= 1;
                idx += 1;
                continue;
            }
            _ => {}
        }
        let is_def = delim_depth == 0
            && matches!(&tokens[idx], LeanToken::Ident(kw) if kw == "def" || kw == "abbrev");
        let name_matches = matches!(&tokens[idx + 1], LeanToken::Ident(name) if name == def_name || name.ends_with(&format!(".{def_name}")));
        let is_colon = matches!(&tokens[idx + 2], LeanToken::Colon);
        let is_captured_mir =
            matches!(&tokens[idx + 3], LeanToken::Ident(ty) if is_valid_captured_mir_type(ty));
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
            let parsed = cursor.parse_captured_mir_metadata()?;
            // `[adv B1]`: the record must be the *entire* definition body. Anything
            // applied to it (`|> mutate`, `.withBlocks evil`, `++ extra`) would change
            // the elaborated `CapturedMir` in Lean while being ignored here.
            if let Some(tok) = cursor.peek() {
                if !is_lean_command_start(tok) {
                    return Err(CensusScanError::MalformedCapturedMirSyntax(format!(
                        "unexpected token {tok:?} after `def {def_name} : CapturedMir` record"
                    )));
                }
            }
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
pub fn census_lean_mir_def(
    lean_src: &str,
    def_name: &str,
) -> Result<Vec<FaultSite>, CensusScanError> {
    let body = parse_lean_captured_mir_def(lean_src, def_name)?;
    Ok(census_mir_fault_sites(&body))
}

/// True when any dotted segment of `name` reuses a `Trusted` MIR AST type name.
fn shadows_mir_ast_name(name: &str) -> bool {
    name.split('.').any(|seg| MIR_AST_TYPE_NAMES.contains(&seg))
}

/// Strict `[adv B1]` / `[adv A1]` / `[adv A2]` grammar check for an `anneal-rustc-capture`
/// `Mir/<Item>.lean` module: only `import Trusted*`, balanced `namespace`/`section`/`end`,
/// `open Trusted*` lists, `set_option`, and `def <name> : <type> := <single balanced term>`
/// commands are accepted, no declaration or namespace may reuse a MIR AST type name
/// (constructor shadowing), every `namespace`/`section` must be closed by a matching
/// `end <name>` before EOF, and exactly one bare `def body : CapturedMir := { ... }`
/// must exist directly inside the module's single top-level `namespace` (rejecting both
/// qualified `def Sub.body` and nested `namespace Sub def body ... end Sub`).
fn check_strict_mir_module_grammar<'a>(tokens: &'a [LeanToken]) -> Result<(), CensusScanError> {
    let malformed = |msg: String| CensusScanError::MalformedCapturedMirSyntax(msg);
    let ident_at = |i: usize| -> Option<&'a str> {
        match tokens.get(i) {
            Some(LeanToken::Ident(s)) => Some(s.as_str()),
            _ => None,
        }
    };
    let mut scope_stack: Vec<(&'a str, &'a str)> = Vec::new();
    let mut top_level_namespaces = 0usize;
    let mut body_defs = 0usize;
    let mut i = 0usize;
    while i < tokens.len() {
        let Some(kw) = ident_at(i) else {
            return Err(malformed(format!(
                "unexpected top-level token {:?} in strict Mir module",
                tokens[i]
            )));
        };
        match kw {
            "import" => {
                let imp =
                    ident_at(i + 1).ok_or_else(|| malformed("`import` without module".into()))?;
                if !STRICT_MODULE_IMPORTS.contains(&imp) {
                    return Err(malformed(format!(
                        "unsupported `import {imp}` in strict Mir module (only `Trusted` / `V2026_06_01` allowed)"
                    )));
                }
                i += 2;
            }
            "namespace" | "section" => {
                let Some(name) = ident_at(i + 1) else {
                    return Err(malformed(format!("`{kw}` without an explicit scope name")));
                };
                if is_lean_command_start(&tokens[i + 1]) {
                    return Err(malformed(format!("`{kw}` without an explicit scope name")));
                }
                if shadows_mir_ast_name(name) {
                    return Err(malformed(format!(
                        "namespace `{name}` shadows a MIR AST type name"
                    )));
                }
                if kw == "namespace" && scope_stack.is_empty() {
                    if top_level_namespaces >= 1 {
                        return Err(malformed(format!(
                            "multiple top-level `namespace` blocks (`{name}`) in strict Mir module"
                        )));
                    }
                    top_level_namespaces += 1;
                }
                scope_stack.push((kw, name));
                i += 2;
            }
            "end" => {
                let Some(name) = ident_at(i + 1) else {
                    return Err(malformed("`end` without an explicit scope name".into()));
                };
                if is_lean_command_start(&tokens[i + 1]) {
                    return Err(malformed("`end` without an explicit scope name".into()));
                }
                match scope_stack.pop() {
                    Some((_, open_name)) if open_name == name => {}
                    Some((open_kw, open_name)) => {
                        return Err(malformed(format!(
                            "mismatched `end {name}` for open `{open_kw} {open_name}`"
                        )));
                    }
                    None => {
                        return Err(malformed(format!(
                            "unmatched `end {name}` with no open namespace or section"
                        )));
                    }
                }
                i += 2;
            }
            "open" => {
                i += 1;
                let mut count = 0usize;
                while let Some(name) = ident_at(i) {
                    if is_lean_command_start(&tokens[i]) {
                        break;
                    }
                    if matches!(name, "renaming" | "hiding" | "in" | "scoped") {
                        return Err(malformed(format!("`open ... {name}` is not supported")));
                    }
                    if !STRICT_MODULE_OPENS.contains(&name) {
                        return Err(malformed(format!(
                            "unsupported `open {name}` in strict Mir module (only `Trusted` namespaces allowed)"
                        )));
                    }
                    count += 1;
                    i += 1;
                }
                if count == 0 {
                    return Err(malformed("`open` without namespaces".into()));
                }
            }
            "set_option" => {
                ident_at(i + 1).ok_or_else(|| malformed("`set_option` without name".into()))?;
                match tokens.get(i + 2) {
                    Some(
                        LeanToken::Ident(_)
                        | LeanToken::NatLit(_)
                        | LeanToken::StrLit(_)
                        | LeanToken::CharLit(_),
                    ) => {}
                    other => {
                        return Err(malformed(format!("`set_option` with value {other:?}")));
                    }
                }
                i += 3;
            }
            "def" => {
                let name = ident_at(i + 1)
                    .ok_or_else(|| malformed("`def` without a plain identifier name".into()))?;
                if shadows_mir_ast_name(name) || is_lean_command_start(&tokens[i + 1]) {
                    return Err(malformed(format!(
                        "declaration `{name}` shadows a MIR AST name or keyword"
                    )));
                }
                if name.ends_with(".body") {
                    return Err(malformed(format!(
                        "qualified `def {name}` is not allowed in strict Mir module (expected bare `def body`)"
                    )));
                }
                if tokens.get(i + 2) != Some(&LeanToken::Colon) {
                    return Err(malformed(format!(
                        "`def {name}` must carry an explicit `: <type>` ascription"
                    )));
                }
                let is_body = name == "body";
                let mut j = i + 3;
                let ty_start = j;
                let mut depth = 0isize;
                while j < tokens.len() {
                    match &tokens[j] {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => depth -= 1,
                        LeanToken::ColonEq if depth == 0 => break,
                        tok if depth == 0 && is_lean_command_start(tok) => {
                            return Err(malformed(format!("`def {name}` has no `:=` body")));
                        }
                        _ => {}
                    }
                    j += 1;
                }
                if j >= tokens.len() {
                    return Err(malformed(format!("`def {name}` has no `:=` body")));
                }
                if is_body {
                    if scope_stack.len() != 1 || scope_stack[0].0 != "namespace" {
                        return Err(malformed(
                            "`def body : CapturedMir` must appear directly inside the module's single top-level `namespace`".into(),
                        ));
                    }
                    let ty_ok = j == ty_start + 1
                        && matches!(&tokens[ty_start], LeanToken::Ident(ty)
                            if is_valid_captured_mir_type(ty));
                    if !ty_ok {
                        return Err(malformed(format!(
                            "`def {name}` must be ascribed `: CapturedMir` (in `V2026_06_01` dialect)"
                        )));
                    }
                    body_defs += 1;
                }
                let mut cursor = TokenCursor { tokens, pos: j + 1 };
                cursor.skip_balanced_expr()?;
                if !is_body {
                    // Strings in a skipped definition are never parsed, so a Lean
                    // interpolation (`throwError "{"..."}"`, `m!"..."`, `panic!"..."`)
                    // there could desynchronize the token stream; the emitter never
                    // produces braces in such strings or `!`-macros, so fail closed.
                    for tok in &tokens[i + 3..cursor.pos] {
                        match tok {
                            LeanToken::StrLit(lit) if lit.contains('{') || lit.contains('}') => {
                                return Err(malformed(format!(
                                    "brace-carrying string in skipped `def {name}`"
                                )));
                            }
                            LeanToken::Ident(id) if id.ends_with('!') => {
                                return Err(malformed(format!(
                                    "macro invocation `{id}` in skipped `def {name}`"
                                )));
                            }
                            _ => {}
                        }
                    }
                }
                if let Some(tok) = cursor.peek() {
                    if !is_lean_command_start(tok) {
                        return Err(malformed(format!(
                            "unexpected token {tok:?} after the value of `def {name}`"
                        )));
                    }
                }
                i = cursor.pos;
            }
            other => {
                return Err(malformed(format!(
                    "unsupported top-level command `{other}` in strict Mir module"
                )));
            }
        }
    }
    if let Some((open_kw, open_name)) = scope_stack.last() {
        return Err(malformed(format!(
            "unclosed `{open_kw} {open_name}` at end of strict Mir module"
        )));
    }
    if body_defs != 1 {
        return Err(CensusScanError::MissingOrDuplicateCapturedMirDef(format!(
            "expected exactly one `def body : CapturedMir`, found {body_defs}"
        )));
    }
    Ok(())
}

/// Enumerate all `FaultSite` records from an `anneal-rustc-capture`
/// `Mir/<Item>.lean` module (`def body : CapturedMir := ...`), first enforcing the
/// strict module grammar (`check_strict_mir_module_grammar`).
pub fn census_lean_mir_module(lean_src: &str) -> Result<Vec<FaultSite>, CensusScanError> {
    let body = parse_lean_mir_module_body_strict(lean_src)?;
    Ok(census_mir_fault_sites(&body))
}

/// `[adv ep1-B1]` Parse the unique `def body : CapturedMir` of an
/// `anneal-rustc-capture` `Mir/<Item>.lean` module *after* enforcing the strict
/// module grammar (`check_strict_mir_module_grammar`): exactly the body that
/// `census_lean_mir_module` censuses. Verify-time and scaffold-time coverage
/// reconciliation must use this entry point rather than the lenient
/// `parse_lean_captured_mir_def`, which would accept a module whose other
/// commands (constructor shadowing, extra namespaces, macros) make Lean elaborate
/// a different `CapturedMir` than the one scanned here.
pub fn parse_lean_mir_module_body_strict(lean_src: &str) -> Result<ProtoMirBody, CensusScanError> {
    parse_lean_mir_module_metadata_strict(lean_src).map(|m| m.body)
}

/// `[adv ep1-B3]` Parse the unique `def body : CapturedMir` together with its
/// `ContractRole` and `traitImpls` table after enforcing `check_strict_mir_module_grammar`.
pub fn parse_lean_mir_module_metadata_strict(
    lean_src: &str,
) -> Result<ParsedMirModuleMetadata, CensusScanError> {
    let tokens = tokenize_lean_source(lean_src)?;
    check_strict_mir_module_grammar(&tokens)?;
    parse_lean_captured_mir_def_metadata(lean_src, "body")
}

/// `[adv ep1-B3]` Structured `externalSpecCallContract` binding declared in a generated
/// `Obligations/<Item>.lean` module (`def <def_ident> : MirCallContract :=
/// externalSpecCallContract "<target_def_path>" Mir.<sidecar_mir_suffix>.body ...`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternalSpecContractLink {
    pub def_ident: String,
    pub target_def_path: String,
    pub sidecar_mir_suffix: String,
}

/// `[adv ep1-B1]` / `[adv ep1-A1]` / `[adv ep1-A2]` / `[adv ep1-B3]` Callee links and claim
/// bindings declared by a generated `Obligations/<Item>.lean` module, scanned with the
/// comment- and string-aware Lean lexer so that text inside `--` / `/- ... -/`
/// comments or string literals can never add a link or spoof a claim binding.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ObligationsCalleeLinks {
    /// Target `DefPath`s bound by `externalSpecCallContract "<target>" ...`.
    pub external_spec_targets: Vec<String>,
    /// `[adv ep1-B3]` Structured `def <ident> : MirCallContract := externalSpecCallContract ...`
    /// definitions in the module.
    pub external_spec_contracts: Vec<ExternalSpecContractLink>,
    /// `[adv ep1-B3]` Any `externalSpecCallContract` token not bound as the head of a
    /// canonical `def <ident> : MirCallContract := externalSpecCallContract "<target>" Mir.<sidecar>.body ...`.
    pub unlinked_external_spec_errors: Vec<String>,
    /// `[adv ep1-B3]` Contract identifiers referenced via `<ident>.holdsOn` (including
    /// resolution of `abbrev defaultExternalCallContract : MirCallContract := <ident>`).
    pub referenced_external_contract_idents: Vec<String>,
    /// `[adv ep1-B3]` `<Suffix>` module suffixes of `import Mir.<Suffix>` commands.
    pub imported_mir_suffixes: Vec<String>,
    /// `<Callee>` module suffixes of `import Obligations.<Callee>` commands.
    pub imported_obligation_suffixes: Vec<String>,
    /// `[adv ep1-A2]` `<Callee>` module suffixes referenced via
    /// `Obligations.<Callee>.defaultCallContract` (or `.defaultCallContract.holdsOn`).
    pub referenced_callee_contracts: Vec<String>,
    /// Every dotted identifier of the form `Mir.<Item>.body` (or a projection of it,
    /// such as `Mir.<Item>.body.instantiate`) referenced by the module, reported as
    /// the `<Item>` suffix.
    pub referenced_mir_bodies: Vec<String>,
    /// `[adv ep1-A1]` Every `<Item>` suffix bound to an exact `body := Mir.<Item>.body`
    /// (or `Mir.<Item>.body.instantiate typeArgs`) or `implBody := Mir.<Item>.body`
    /// field inside a claim record literal.
    pub claim_mir_bodies: Vec<String>,
    /// `[adv ep1-A1]` / `[adv ep1-A2]` Any non-`Mir.<Item>.body` token sequence assigned
    /// to `body := ...` or `implBody := ...` inside a claim record literal (must be
    /// empty for a valid generated Obligations module).
    pub non_mir_claim_bodies: Vec<String>,
    /// `[adv ep1-A1]` / `[adv ep1-A2]` Every RHS expression bound to `callees := ...`,
    /// `implCallees := ...`, or `specCallees := ...` inside a claim record literal
    /// (every entry must be `"defaultCallees"` with no trailing tokens).
    pub claim_callees_bindings: Vec<String>,
    /// `[adv ep1-A2]` / `[adv ep1-B3]` Expected callee-table field count implied by
    /// `body :=` (+1) and `implBody :=` (+2, for `implCallees` and `specCallees` on
    /// `StatefulEquivClaim`).
    pub claim_body_field_count: usize,
    /// `[adv ep1-A2]` / `[adv ep1-B3]` Total number of `callees :=`, `implCallees :=`,
    /// and `specCallees :=` claim field bindings.
    pub claim_callees_field_count: usize,
    /// `[adv ep1-A3]` Number of top-level `instance ... defaultModularSpec : ModularItemSpec ...`
    /// declarations in the module (must be `1` in a canonical `Obligations/<Item>.lean`).
    pub default_modular_spec_count: usize,
    /// `[adv ep1-B4]` Target `defId` string literal carried by `defaultModularSpec :
    /// ModularItemSpec "<defId>"` when present.
    pub default_modular_spec_def_id: Option<String>,
    /// `[adv ep1-A3]` Structural/grammar errors inside `defaultModularSpec` (missing
    /// `envAssumed :=` field or non-canonical `envAssumed` expression).
    pub default_modular_spec_errors: Vec<String>,
    /// `[adv ep1-A3]` Resolved `defaultExternalCallContract` alias target identifier when
    /// `abbrev defaultExternalCallContract : MirCallContract := <ident>` is present.
    pub default_external_contract_alias: Option<String>,
    /// `[adv ep1-A3]` Optional `<Ref>` module suffix bound by `instance rustEquivSpec :
    /// StatefulEquivItemSpec ... := refineEquivSpec Mir.<Ref>.body ...` in `Obligations/<Item>.lean`.
    pub rust_equiv_spec_body_suffix: Option<String>,
    /// `[adv ep1-B4]` Target `defId` string literal carried by `rustEquivSpec :
    /// StatefulEquivItemSpec "<defId>"` when present.
    pub rust_equiv_spec_def_id: Option<String>,
    /// `[adv ep1-A3]` Errors from malformed or duplicate `StatefulEquivItemSpec` instances
    /// in `Obligations/<Item>.lean`.
    pub equiv_spec_errors: Vec<String>,
    /// `[adv ep1-B4]` Target `defPath` string literal bound by `def defaultCallContract :
    /// MirCallContract where pre req := And (req.defPath = "<defPath>") ...` when present.
    pub default_call_contract_def_path: Option<String>,
    /// `[adv ep1-A4]` Count of canonical `instance (priority := low) defaultSpec` declarations.
    pub default_spec_count: usize,
    /// `[adv ep1-A4]` Count of canonical `instance (priority := low) defaultTotalSpec` declarations.
    pub default_total_spec_count: usize,
    /// `[adv ep1-A4]` True when `Obligations/<Item>.lean` imports `Specs.<Item>` or declares
    /// `instance legacySpec` overriding `defaultSpec` inside the `Obligations` module.
    pub has_legacy_spec_override: bool,
    /// `[adv ep1-B4]` Errors from malformed, shadowed, or duplicate `defaultCallContract` or
    /// unexpected specification instances in `Obligations/<Item>.lean`.
    pub contract_integrity_errors: Vec<String>,
}

/// `[adv ep1-B4]` Recognize any Lean qualification of the 6 `Trusted.VerificationResult`
/// specification typeclasses (`ItemSpec`, `VerificationResult.ItemSpec`,
/// `Trusted.VerificationResult.ItemSpec`, `_root_.Trusted.VerificationResult.ItemSpec`, etc.).
fn canonical_spec_class_name(ident: &str) -> Option<&'static str> {
    let s = ident.strip_prefix("_root_.").unwrap_or(ident);
    let s = s.strip_prefix("Trusted.").unwrap_or(s);
    let s = s.strip_prefix("VerificationResult.").unwrap_or(s);
    match s {
        "ItemSpec" => Some("ItemSpec"),
        "StatefulItemSpec" => Some("StatefulItemSpec"),
        "TotalItemSpec" => Some("TotalItemSpec"),
        "StatefulEquivItemSpec" => Some("StatefulEquivItemSpec"),
        "ModularItemSpec" => Some("ModularItemSpec"),
        "UbExceptionItemSpec" => Some("UbExceptionItemSpec"),
        _ => None,
    }
}

/// `[adv ep1-B4]` Recognize any Lean qualification of the 6 `Trusted.VerificationResult`
/// fallback proof typeclasses (`ItemProof`, `ModularItemProof`, etc.).
fn canonical_proof_class_name(ident: &str) -> Option<&'static str> {
    let s = ident.strip_prefix("_root_.").unwrap_or(ident);
    let s = s.strip_prefix("Trusted.").unwrap_or(s);
    let s = s.strip_prefix("VerificationResult.").unwrap_or(s);
    match s {
        "ItemProof" => Some("ItemProof"),
        "StatefulItemProof" => Some("StatefulItemProof"),
        "TotalItemProof" => Some("TotalItemProof"),
        "StatefulEquivItemProof" => Some("StatefulEquivItemProof"),
        "ModularItemProof" => Some("ModularItemProof"),
        "UbExceptionItemProof" => Some("UbExceptionItemProof"),
        _ => None,
    }
}

/// `[adv ep1-B4]` True iff `ident` names (bare or qualified) one of the `Obligations`
/// `refine*Spec` constructors.
fn is_refine_spec_helper_ident(ident: &str) -> bool {
    let short = ident.rsplit_once('.').map(|(_, s)| s).unwrap_or(ident);
    matches!(
        short,
        "refineSpec"
            | "refineStatefulSpec"
            | "refineSafeSpec"
            | "refineSafeStatefulSpec"
            | "refineTotalSpec"
            | "refineEquivSpec"
            | "refineModularSpec"
            | "refineUbExceptionSpec"
    )
}

/// `[adv ep1-B4]` Detect `@[... instance ...]` or `@[... default_instance ...]` attributes
/// anywhere in `tokens` (which register typeclass instances on `def`/`abbrev` without a
/// top-level `instance` keyword, while leaving `@[reducible, simp]` and
/// `@[instance_reducible]` permitted).
fn detect_instance_attribute(tokens: &[LeanToken]) -> Option<String> {
    let mut i = 0usize;
    while i + 2 < tokens.len() {
        if matches!(&tokens[i], LeanToken::Ident(at) if at == "@")
            && tokens[i + 1] == LeanToken::LBracket
        {
            let mut depth = 1isize;
            let mut j = i + 2;
            while j < tokens.len() && depth > 0 {
                match &tokens[j] {
                    LeanToken::LBracket => depth += 1,
                    LeanToken::RBracket => depth -= 1,
                    LeanToken::Ident(attr) if attr == "instance" || attr == "default_instance" => {
                        return Some(attr.clone());
                    }
                    _ => {}
                }
                j += 1;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    None
}

fn is_allowed_specs_import(module: &str) -> bool {
    module == "Init"
        || module.starts_with("Init.")
        || module == "Std"
        || module.starts_with("Std.")
        || module == "Trusted"
        || module.starts_with("Trusted.")
        || module == "Anneal"
        || module.starts_with("Anneal.")
        || module.starts_with("Mir.")
        || module.starts_with("Obligations.")
        || module.starts_with("Specs.")
}

fn is_allowed_aux_import(module: &str) -> bool {
    is_allowed_specs_import(module)
        || module.starts_with("Proof.")
        || module.starts_with("Assumptions.")
}

fn strip_enclosing_parens(mut slice: &[LeanToken]) -> &[LeanToken] {
    while slice.len() >= 2
        && slice.first() == Some(&LeanToken::LParen)
        && slice.last() == Some(&LeanToken::RParen)
    {
        let mut bal = 0isize;
        let mut enclosed = true;
        for (pos, tok) in slice.iter().enumerate() {
            match tok {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => bal += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => bal -= 1,
                _ => {}
            }
            if bal <= 0 && pos + 1 < slice.len() {
                enclosed = false;
                break;
            }
        }
        if enclosed && bal == 0 {
            slice = &slice[1..slice.len() - 1];
        } else {
            break;
        }
    }
    slice
}

fn take_one_balanced_lean_arg(slice: &[LeanToken]) -> Option<(&[LeanToken], &[LeanToken])> {
    let first = slice.first()?;
    match first {
        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
            let mut bal = 0isize;
            for (idx, tok) in slice.iter().enumerate() {
                match tok {
                    LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => bal += 1,
                    LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                        bal -= 1;
                        if bal == 0 {
                            return Some((&slice[..=idx], &slice[idx + 1..]));
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        LeanToken::Ident(_) | LeanToken::StrLit(_) | LeanToken::NatLit(_) => {
            Some((&slice[..1], &slice[1..]))
        }
        _ => None,
    }
}

fn take_exact_n_balanced_args(mut slice: &[LeanToken], n: usize) -> Option<Vec<&[LeanToken]>> {
    let mut args = Vec::with_capacity(n);
    for _ in 0..n {
        let (arg, rest) = take_one_balanced_lean_arg(slice)?;
        args.push(arg);
        slice = rest;
    }
    slice.is_empty().then_some(args)
}

fn parse_env_assumed_conjuncts(
    expr: &[LeanToken],
    binder: &str,
    out: &mut Vec<String>,
) -> Result<(), String> {
    let expr = strip_enclosing_parens(expr);
    if expr.is_empty() {
        return Err("empty clause in `envAssumed`".to_string());
    }
    // Check for top-level infix `∧` first.
    let mut depth = 0isize;
    for (idx, tok) in expr.iter().enumerate() {
        match tok {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            LeanToken::Ident(op) if depth == 0 && op == "∧" => {
                parse_env_assumed_conjuncts(&expr[..idx], binder, out)?;
                parse_env_assumed_conjuncts(&expr[idx + 1..], binder, out)?;
                return Ok(());
            }
            _ => {}
        }
    }
    // Prefix `And <lhs> <rhs>`.
    if let Some(LeanToken::Ident(head)) = expr.first()
        && head == "And"
    {
        let Some((lhs, after_lhs)) = take_one_balanced_lean_arg(&expr[1..]) else {
            return Err("malformed `And` LHS in `envAssumed`".to_string());
        };
        let Some((rhs, rem)) = take_one_balanced_lean_arg(after_lhs) else {
            return Err("malformed `And` RHS in `envAssumed`".to_string());
        };
        if !rem.is_empty() {
            return Err(format!("trailing tokens `{rem:?}` after `And` in `envAssumed`"));
        }
        parse_env_assumed_conjuncts(lhs, binder, out)?;
        parse_env_assumed_conjuncts(rhs, binder, out)?;
        return Ok(());
    }
    match expr {
        [LeanToken::Ident(holds_ident), LeanToken::Ident(arg)] if arg == binder => {
            if holds_ident == "defaultModularSpec.envAssumed"
                || holds_ident.ends_with(".defaultModularSpec.envAssumed")
            {
                if !out.iter().any(|x| x == holds_ident) {
                    out.push(holds_ident.clone());
                }
                return Ok(());
            }
            let Some(stem) = holds_ident.strip_suffix(".holdsOn").filter(|s| !s.is_empty()) else {
                return Err(format!(
                    "expected `<contract>.holdsOn {binder}` in `envAssumed`, found `{holds_ident} {arg}`"
                ));
            };
            if !out.iter().any(|x| x == stem) {
                out.push(stem.to_string());
            }
            Ok(())
        }
        [LeanToken::Ident(holds_fn), LeanToken::Ident(contract_ident), LeanToken::Ident(arg)]
            if (holds_fn == "MirCallContract.holdsOn"
                || holds_fn == "Trusted.VerificationResult.MirCallContract.holdsOn")
                && arg == binder =>
        {
            if !out.iter().any(|x| x == contract_ident) {
                out.push(contract_ident.clone());
            }
            Ok(())
        }
        other => Err(format!(
            "unsupported or non-canonical `envAssumed` clause `{other:?}`"
        )),
    }
}

/// `[adv ep1-A3]` Parse an `envAssumed := <expr>` token slice, accepting only:
/// 1. `fun _ => True` (no assumed external contracts),
/// 2. `<contract>.holdsOn` or `<prefix>.defaultModularSpec.envAssumed` (single contract /
///    default modular environment delegation), or
/// 3. `fun h => <And / ∧ conjunction of (<contract>.holdsOn h | <prefix>.defaultModularSpec.envAssumed h)>`.
///
/// Rejects vacuous disjunctions (`True ∨ ...`), implications, `let` bindings, or
/// arbitrary terms so an unverified contract identifier can never be smuggled in.
fn parse_env_assumed_holds_on_stems(env_rhs: &[LeanToken]) -> Result<Vec<String>, String> {
    let env_rhs = strip_enclosing_parens(env_rhs);
    match env_rhs {
        [LeanToken::Ident(holds_ident)] => {
            if holds_ident == "defaultModularSpec.envAssumed"
                || holds_ident.ends_with(".defaultModularSpec.envAssumed")
            {
                return Ok(vec![holds_ident.clone()]);
            }
            let Some(stem) = holds_ident.strip_suffix(".holdsOn").filter(|s| !s.is_empty()) else {
                return Err(format!(
                    "expected `<contract>.holdsOn` in `envAssumed`, found `{holds_ident}`"
                ));
            };
            Ok(vec![stem.to_string()])
        }
        [LeanToken::Ident(holds_fn), LeanToken::Ident(contract_ident)]
            if holds_fn == "MirCallContract.holdsOn"
                || holds_fn == "Trusted.VerificationResult.MirCallContract.holdsOn" =>
        {
            Ok(vec![contract_ident.clone()])
        }
        [LeanToken::Ident(fun_kw), LeanToken::Ident(binder), LeanToken::Ident(arrow), body @ ..]
            if (fun_kw == "fun" || fun_kw == "λ") && (arrow == "=>" || arrow == "↦") =>
        {
            let body = strip_enclosing_parens(body);
            if matches!(body, [LeanToken::Ident(t)] if t == "True") {
                return Ok(Vec::new());
            }
            if binder == "_" {
                return Err(
                    "`envAssumed := fun _ => ...` may only have body `True`".to_string()
                );
            }
            let mut stems = Vec::new();
            parse_env_assumed_conjuncts(body, binder, &mut stems)?;
            Ok(stems)
        }
        other => Err(format!(
            "non-canonical `envAssumed` expression `{other:?}`"
        )),
    }
}

/// `[adv ep1-B1]` / `[adv ep1-A1]` / `[adv ep1-A2]` / `[adv ep1-B3]` / `[adv ep1-A3]` Scan a
/// generated `Obligations/<Item>.lean` module for its callee links and claim bindings (see
/// [`ObligationsCalleeLinks`]), failing closed on any lexer error.
pub fn scan_obligations_callee_links(
    ob_text: &str,
) -> Result<ObligationsCalleeLinks, CensusScanError> {
    let tokens = tokenize_lean_source(ob_text)?;
    let mut links = ObligationsCalleeLinks::default();
    let push_unique = |out: &mut Vec<String>, s: &str| {
        if !s.is_empty() && !out.iter().any(|x| x == s) {
            out.push(s.to_string());
        }
    };
    fn extract_mir_item(ident: &str) -> Option<&str> {
        let rest = ident.strip_prefix("Mir.")?;
        rest.strip_suffix(".body")
            .or_else(|| rest.rsplit_once(".body.").map(|(item, _)| item))
            .filter(|s| !s.is_empty())
    }
    fn extract_callee_contract(stem: &str) -> Option<&str> {
        let rest = stem.strip_prefix("Obligations.")?;
        rest.strip_suffix(".defaultCallContract")
            .filter(|s| !s.is_empty())
    }
    let find_field_rhs_end = |start: usize| -> usize {
        let mut depth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if depth == 0 {
                if matches!(tokens[k], LeanToken::Comma | LeanToken::RBrace)
                    || is_lean_command_start(&tokens[k])
                {
                    break;
                }
                if k > start
                    && matches!(tokens.get(k), Some(LeanToken::Ident(_)))
                    && tokens.get(k + 1) == Some(&LeanToken::ColonEq)
                {
                    break;
                }
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };
    let find_command_end = |start: usize| -> usize {
        let mut depth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if depth == 0 && k > start && is_lean_command_start(&tokens[k]) {
                break;
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };

    let mut linked_ext_contract_positions: BTreeSet<usize> = BTreeSet::new();
    let mut default_ext_alias_target: Option<String> = None;
    let mut raw_holds_on_stems: Vec<String> = Vec::new();
    let mut top_depth = 0isize;
    for idx in 0..tokens.len() {
        let cur_depth = top_depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => top_depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                top_depth = (top_depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            continue;
        }
        if matches!(tokens.get(idx), Some(LeanToken::Ident(kw)) if kw == "instance") {
            let cmd_end = find_command_end(idx + 1);
            let cmd_slice = &tokens[idx..cmd_end];
            let mut header_end = cmd_slice.len();
            let mut h_depth = 0isize;
            for (h_pos, t) in cmd_slice.iter().enumerate() {
                if h_depth == 0
                    && (*t == LeanToken::ColonEq
                        || matches!(t, LeanToken::Ident(w) if w == "where"))
                {
                    header_end = h_pos;
                    break;
                }
                match t {
                    LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => h_depth += 1,
                    LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                        h_depth = (h_depth - 1).max(0);
                    }
                    _ => {}
                }
            }
            let header = &cmd_slice[..header_end];
            let is_default_modular = header
                .iter()
                .any(|t| matches!(t, LeanToken::Ident(n) if n == "defaultModularSpec"));
            let mut spec_cls_opt: Option<(&'static str, Option<String>)> = None;
            for (h_pos, t) in header.iter().enumerate() {
                if let LeanToken::Ident(n) = t
                    && let Some(cls) = canonical_spec_class_name(n)
                {
                    let def_id = match header.get(h_pos + 1) {
                        Some(LeanToken::StrLit(s)) => Some(s.clone()),
                        _ => None,
                    };
                    spec_cls_opt = Some((cls, def_id));
                    break;
                }
            }
            let is_modular_ty = matches!(spec_cls_opt, Some(("ModularItemSpec", _)));
            let is_equiv_ty = matches!(spec_cls_opt, Some(("StatefulEquivItemSpec", _)));
            let is_item_spec_ty = matches!(spec_cls_opt, Some(("ItemSpec", _)));
            let is_total_spec_ty = matches!(spec_cls_opt, Some(("TotalItemSpec", _)));
            let is_default_spec = header
                .iter()
                .any(|t| matches!(t, LeanToken::Ident(n) if n == "defaultSpec"));
            let is_default_total_spec = header
                .iter()
                .any(|t| matches!(t, LeanToken::Ident(n) if n == "defaultTotalSpec"));
            let is_rust_safe_total_spec = header
                .iter()
                .any(|t| matches!(t, LeanToken::Ident(n) if n == "rustSafeTotalSpec"));
            let is_legacy_spec = header
                .iter()
                .any(|t| matches!(t, LeanToken::Ident(n) if n == "legacySpec"));
            if is_legacy_spec {
                links.has_legacy_spec_override = true;
            }
            if let Some((cls, ref opt_did)) = spec_cls_opt {
                const ALLOWED_OB_SPEC_INSTANCES: &[&str] = &[
                    "defaultSpec",
                    "defaultStatefulSpec",
                    "defaultTotalSpec",
                    "defaultModularSpec",
                    "defaultUbExceptionSpec",
                    "rustSafeTotalSpec",
                    "rustSafeTotalStatefulSpec",
                    "rustEquivSpec",
                    "legacySpec",
                ];
                let has_allowed_name = header.iter().any(|t| {
                    matches!(t, LeanToken::Ident(n) if ALLOWED_OB_SPEC_INSTANCES.contains(&n.as_str()))
                });
                if !has_allowed_name {
                    links.contract_integrity_errors.push(format!(
                        "unexpected `{cls}` instance in Obligations module"
                    ));
                }
                if opt_did.is_none() {
                    links.contract_integrity_errors.push(format!(
                        "`{cls}` instance in Obligations module omits explicit `\"<defId>\"` target"
                    ));
                }
            }
            if is_default_spec || (is_item_spec_ty && !is_rust_safe_total_spec && !is_legacy_spec) {
                links.default_spec_count += 1;
                let body_tokens = cmd_slice.get(header_end + 1..).unwrap_or(&[]);
                let has_nested_where = body_tokens
                    .iter()
                    .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"));
                let pre_ok = body_tokens.windows(2).any(|w| {
                    matches!(w, [LeanToken::Ident(p), LeanToken::ColonEq] if p == "pre")
                }) && body_tokens
                    .iter()
                    .any(|t| matches!(t, LeanToken::Ident(dp) if dp == "defaultPre"));
                let post_ok = body_tokens.windows(3).any(|w| {
                    matches!(
                        w,
                        [LeanToken::Ident(p), LeanToken::ColonEq, LeanToken::Ident(dp)]
                            if p == "post" && dp == "defaultPost"
                    )
                }) && body_tokens.last() == Some(&LeanToken::Ident("defaultPost".to_string()));
                if !is_default_spec
                    || !is_item_spec_ty
                    || !matches!(cmd_slice.get(header_end), Some(LeanToken::Ident(w)) if w == "where")
                    || has_nested_where
                    || !pre_ok
                    || !post_ok
                {
                    links.contract_integrity_errors.push(
                        "malformed or tampered `defaultSpec` instance in Obligations module"
                            .to_string(),
                    );
                }
            }
            if is_rust_safe_total_spec {
                let rhs = strip_enclosing_parens(cmd_slice.get(header_end + 1..).unwrap_or(&[]));
                let safe_ok = cmd_slice.get(header_end) == Some(&LeanToken::ColonEq)
                    && matches!(rhs.first(), Some(LeanToken::Ident(fn_id)) if fn_id == "refineSafeSpec")
                    && take_exact_n_balanced_args(rhs.get(1..).unwrap_or(&[]), 3).is_some_and(
                        |args3| {
                            let dom = strip_enclosing_parens(args3[0]);
                            let ep = strip_enclosing_parens(args3[1]);
                            let eq = strip_enclosing_parens(args3[2]);
                            dom.iter().any(|t| matches!(t, LeanToken::Ident(id) if id.ends_with(".body.argCount")))
                                && matches!(
                                    ep,
                                    [LeanToken::Ident(f), LeanToken::Ident(u), LeanToken::Ident(ar), LeanToken::Ident(tr)]
                                        if f == "fun" && u == "_" && ar == "=>" && tr == "True"
                                )
                                && matches!(
                                    eq,
                                    [LeanToken::Ident(f), LeanToken::Ident(u1), LeanToken::Ident(u2), LeanToken::Ident(ar), LeanToken::Ident(tr)]
                                        if f == "fun" && u1 == "_" && u2 == "_" && ar == "=>" && tr == "True"
                                )
                        },
                    );
                if !safe_ok {
                    links.contract_integrity_errors.push(
                        "malformed or tampered `rustSafeTotalSpec` instance in Obligations module"
                            .to_string(),
                    );
                }
            }
            if is_default_total_spec || is_total_spec_ty {
                links.default_total_spec_count += 1;
                let body_tokens = cmd_slice.get(header_end + 1..).unwrap_or(&[]);
                let has_nested_where = body_tokens
                    .iter()
                    .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"));
                let pre_ok = body_tokens
                    .iter()
                    .any(|t| matches!(t, LeanToken::Ident(dp) if dp == "defaultPre"))
                    && body_tokens
                        .iter()
                        .any(|t| matches!(t, LeanToken::Ident(im) if im.ends_with("initMachineState")));
                let post_tail = body_tokens.len() >= 9
                    && matches!(
                        &body_tokens[body_tokens.len() - 9..],
                        [
                            LeanToken::Ident(post_kw),
                            LeanToken::ColonEq,
                            LeanToken::Ident(fun_kw),
                            LeanToken::Ident(a1),
                            LeanToken::Ident(_),
                            LeanToken::Ident(r1),
                            LeanToken::Ident(_),
                            LeanToken::Ident(arr),
                            LeanToken::Ident(dp),
                        ] if post_kw == "post" && fun_kw == "fun" && a1 == "args" && r1 == "ret" && arr == "=>" && dp == "defaultPost"
                    );
                let post_ok = post_tail
                    || (body_tokens.len() >= 11
                        && matches!(
                            &body_tokens[body_tokens.len() - 11..],
                            [
                                LeanToken::Ident(post_kw),
                                LeanToken::ColonEq,
                                LeanToken::Ident(fun_kw),
                                LeanToken::Ident(a1),
                                LeanToken::Ident(_),
                                LeanToken::Ident(r1),
                                LeanToken::Ident(_),
                                LeanToken::Ident(arr),
                                LeanToken::Ident(dp),
                                LeanToken::Ident(a2),
                                LeanToken::Ident(r2),
                            ] if post_kw == "post"
                                && fun_kw == "fun"
                                && a1 == "args"
                                && r1 == "ret"
                                && arr == "=>"
                                && dp == "defaultPost"
                                && a2 == "args"
                                && r2 == "ret"
                        ));
                if !is_default_total_spec
                    || !is_total_spec_ty
                    || !matches!(cmd_slice.get(header_end), Some(LeanToken::Ident(w)) if w == "where")
                    || has_nested_where
                    || !pre_ok
                    || !post_ok
                {
                    links.contract_integrity_errors.push(
                        "malformed or tampered `defaultTotalSpec` instance in Obligations module"
                            .to_string(),
                    );
                }
            }
            if is_default_modular || is_modular_ty {
                links.default_modular_spec_count += 1;
                if let Some(("ModularItemSpec", Some(ref did))) = spec_cls_opt {
                    links.default_modular_spec_def_id = Some(did.clone());
                }
                if !is_default_modular || !is_modular_ty || spec_cls_opt.as_ref().and_then(|(_, d)| d.as_ref()).is_none() {
                    links.default_modular_spec_errors.push(
                        "unexpected `ModularItemSpec` / `defaultModularSpec` instance header in Obligations module"
                            .to_string(),
                    );
                } else if matches!(cmd_slice.get(header_end), Some(LeanToken::Ident(w)) if w == "where") {
                    let body_tokens = &cmd_slice[header_end + 1..];
                    if body_tokens
                        .iter()
                        .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"))
                    {
                        links.default_modular_spec_errors.push(
                            "nested `where` clause is forbidden inside `defaultModularSpec`".to_string(),
                        );
                    } else {
                        let mut env_count = 0usize;
                        let mut b_idx = 0usize;
                        let mut b_depth = 0isize;
                        while b_idx < body_tokens.len() {
                            if b_depth == 0
                                && matches!(body_tokens.get(b_idx), Some(LeanToken::Ident(f)) if f == "envAssumed")
                            {
                                env_count += 1;
                                if body_tokens.get(b_idx + 1) != Some(&LeanToken::ColonEq) {
                                    links.default_modular_spec_errors.push(
                                        "`defaultModularSpec.envAssumed` must use `envAssumed := ...` without binders"
                                            .to_string(),
                                    );
                                } else {
                                    let rhs_start = idx + header_end + 1 + b_idx + 2;
                                    let mut rhs_end = find_field_rhs_end(rhs_start);
                                    let mut scan_k = rhs_start;
                                    let mut scan_d = 0isize;
                                    while scan_k < rhs_end {
                                        if scan_d == 0
                                            && scan_k > rhs_start
                                            && matches!(
                                                tokens.get(scan_k),
                                                Some(LeanToken::Ident(fnm)) if fnm == "pre" || fnm == "post" || fnm == "envAssumed"
                                            )
                                        {
                                            rhs_end = scan_k;
                                            break;
                                        }
                                        match tokens[scan_k] {
                                            LeanToken::LParen
                                            | LeanToken::LBrace
                                            | LeanToken::LBracket => scan_d += 1,
                                            LeanToken::RParen
                                            | LeanToken::RBrace
                                            | LeanToken::RBracket => {
                                                scan_d = (scan_d - 1).max(0);
                                            }
                                            _ => {}
                                        }
                                        scan_k += 1;
                                    }
                                    match parse_env_assumed_holds_on_stems(&tokens[rhs_start..rhs_end])
                                    {
                                        Ok(stems) => {
                                            for st in stems {
                                                push_unique(&mut raw_holds_on_stems, &st);
                                            }
                                        }
                                        Err(err) => links.default_modular_spec_errors.push(format!(
                                            "invalid `defaultModularSpec.envAssumed`: {err}"
                                        )),
                                    }
                                }
                            }
                            match body_tokens[b_idx] {
                                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                    b_depth += 1;
                                }
                                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                    b_depth = (b_depth - 1).max(0);
                                }
                                _ => {}
                            }
                            b_idx += 1;
                        }
                        if env_count != 1 {
                            links.default_modular_spec_errors.push(format!(
                                "`defaultModularSpec` must bind `envAssumed :=` once (found {env_count})"
                            ));
                        }
                    }
                } else {
                    links.default_modular_spec_errors.push(
                        "`defaultModularSpec` must be declared with `where envAssumed := ...`"
                            .to_string(),
                    );
                }
            }
            if is_equiv_ty {
                if let Some(("StatefulEquivItemSpec", Some(ref did))) = spec_cls_opt {
                    links.rust_equiv_spec_def_id = Some(did.clone());
                }
                if links.rust_equiv_spec_body_suffix.is_some() {
                    links.equiv_spec_errors.push(
                        "multiple `StatefulEquivItemSpec` instances in Obligations module"
                            .to_string(),
                    );
                } else if cmd_slice.get(header_end) == Some(&LeanToken::ColonEq) {
                    let rhs = strip_enclosing_parens(&cmd_slice[header_end + 1..]);
                    match (rhs.first(), take_exact_n_balanced_args(rhs.get(1..).unwrap_or(&[]), 3)) {
                        (Some(LeanToken::Ident(fn_id)), Some(args3))
                            if (fn_id == "refineEquivSpec"
                                || fn_id.ends_with(".refineEquivSpec")) =>
                        {
                            let mir_arg = strip_enclosing_parens(args3[0]);
                            if let [LeanToken::Ident(mir_ref)] = mir_arg
                                && let Some(ref_suffix) = mir_ref
                                    .strip_prefix("Mir.")
                                    .and_then(|s| s.strip_suffix(".body"))
                                    .filter(|s| !s.is_empty())
                            {
                                links.rust_equiv_spec_body_suffix = Some(ref_suffix.to_string());
                            } else {
                                links.equiv_spec_errors.push(format!(
                                    "`StatefulEquivItemSpec` binds non-`Mir.<Ref>.body` reference `{mir_arg:?}`"
                                ));
                            }
                        }
                        _ => {
                            links.equiv_spec_errors.push(
                                "`StatefulEquivItemSpec` instance in Obligations module must use `refineEquivSpec Mir.<Ref>.body <pre> <post>` with exact 3 arguments"
                                    .to_string(),
                            );
                        }
                    }
                } else {
                    links.equiv_spec_errors.push(
                        "`StatefulEquivItemSpec` instance in Obligations module must use `:= refineEquivSpec Mir.<Ref>.body ...`"
                            .to_string(),
                    );
                }
            }
        }
        if let (
            Some(LeanToken::Ident(kw)),
            Some(LeanToken::Ident(def_ident)),
            Some(LeanToken::Colon),
            Some(LeanToken::Ident(ty)),
            Some(LeanToken::Ident(where_kw)),
        ) = (
            tokens.get(idx),
            tokens.get(idx + 1),
            tokens.get(idx + 2),
            tokens.get(idx + 3),
            tokens.get(idx + 4),
        ) {
            let is_mir_call_contract = ty == "MirCallContract"
                || ty == "Trusted.VerificationResult.MirCallContract"
                || ty == "_root_.Trusted.VerificationResult.MirCallContract"
                || ty == "VerificationResult.MirCallContract";
            if kw == "def" && def_ident == "defaultCallContract" && is_mir_call_contract && where_kw == "where" {
                let cmd_end = find_command_end(idx + 1);
                let slice = &tokens[idx + 5..cmd_end];
                let has_nested_where = slice
                    .iter()
                    .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"));
                let post_ok = !has_nested_where
                    && slice.windows(4).any(|w| {
                        matches!(
                            w,
                            [
                                LeanToken::Ident(post_kw),
                                LeanToken::Ident(req_kw),
                                LeanToken::Ident(ans_kw),
                                LeanToken::ColonEq,
                            ] if post_kw == "post" && req_kw == "req" && ans_kw == "ans"
                        )
                    })
                    && slice.windows(3).any(|w| {
                        matches!(
                            w,
                            [
                                LeanToken::Ident(dp),
                                LeanToken::Ident(ra),
                                LeanToken::Ident(rv),
                            ] if dp == "defaultPost" && ra == "req.args" && rv == "retVal"
                        )
                    })
                    && slice.iter().any(|t| {
                        matches!(
                            t,
                            LeanToken::Ident(rm)
                                if rm == "Trusted.VerificationResult.retMatchesCalleeReturnTy"
                                    || rm == "retMatchesCalleeReturnTy"
                        )
                    });
                // Canonical form: `pre req := And (req.defPath = "<def_id>") (defaultPre req.args) post req ans := ...`
                let extracted = if post_ok
                    && slice.len() >= 13
                    && matches!(slice.first(), Some(LeanToken::Ident(p)) if p == "pre")
                    && matches!(slice.get(1), Some(LeanToken::Ident(r)) if r == "req")
                    && slice.get(2) == Some(&LeanToken::ColonEq)
                    && matches!(slice.get(3), Some(LeanToken::Ident(a)) if a == "And")
                    && slice.get(4) == Some(&LeanToken::LParen)
                    && matches!(slice.get(5), Some(LeanToken::Ident(dp)) if dp == "req.defPath")
                    && matches!(slice.get(6), Some(LeanToken::Ident(eq)) if eq == "=")
                    && let Some(LeanToken::StrLit(did)) = slice.get(7)
                    && slice.get(8) == Some(&LeanToken::RParen)
                    && slice.get(9) == Some(&LeanToken::LParen)
                    && matches!(slice.get(10), Some(LeanToken::Ident(dpre)) if dpre == "defaultPre")
                    && matches!(slice.get(11), Some(LeanToken::Ident(rargs)) if rargs == "req.args")
                    && slice.get(12) == Some(&LeanToken::RParen)
                {
                    Some(did.clone())
                } else {
                    None
                };
                match extracted {
                    Some(did) => {
                        if links.default_call_contract_def_path.is_some() {
                            links.contract_integrity_errors.push(
                                "duplicate `def defaultCallContract` in Obligations module".to_string(),
                            );
                        } else {
                            links.default_call_contract_def_path = Some(did);
                        }
                    }
                    None => {
                        links.contract_integrity_errors.push(
                            "malformed `def defaultCallContract` precondition in Obligations module".to_string(),
                        );
                    }
                }
            }
        }
        if let (
            Some(LeanToken::Ident(kw)),
            Some(LeanToken::Ident(def_ident)),
            Some(LeanToken::Colon),
            Some(LeanToken::Ident(ty)),
            Some(LeanToken::ColonEq),
        ) = (
            tokens.get(idx),
            tokens.get(idx + 1),
            tokens.get(idx + 2),
            tokens.get(idx + 3),
            tokens.get(idx + 4),
        ) {
            let is_mir_call_contract = ty == "MirCallContract"
                || ty == "Trusted.VerificationResult.MirCallContract"
                || ty == "_root_.Trusted.VerificationResult.MirCallContract"
                || ty == "VerificationResult.MirCallContract";
            if kw == "def" && def_ident == "defaultCallContract" {
                links.contract_integrity_errors.push(
                    "`def defaultCallContract` in Obligations module must use canonical `where pre req := And (req.defPath = ...) ...`"
                        .to_string(),
                );
            } else if kw == "def"
                && is_mir_call_contract
                && matches!(tokens.get(idx + 5), Some(LeanToken::Ident(fn_id)) if fn_id == "externalSpecCallContract")
                && let Some(LeanToken::StrLit(target)) = tokens.get(idx + 6)
                && let Some(LeanToken::Ident(sidecar_expr)) = tokens.get(idx + 7)
                && let Some(sidecar_suffix) = sidecar_expr
                    .strip_prefix("Mir.")
                    .and_then(|s| s.strip_suffix(".body"))
                    .filter(|s| !s.is_empty())
            {
                let cmd_end = find_command_end(idx + 1);
                if take_exact_n_balanced_args(&tokens[idx + 6..cmd_end], 4).is_some() {
                    linked_ext_contract_positions.insert(idx + 5);
                    links.external_spec_contracts.push(ExternalSpecContractLink {
                        def_ident: def_ident.clone(),
                        target_def_path: target.clone(),
                        sidecar_mir_suffix: sidecar_suffix.to_string(),
                    });
                }
            } else if kw == "abbrev"
                && def_ident == "defaultExternalCallContract"
                && is_mir_call_contract
                && let Some(LeanToken::Ident(alias_target)) = tokens.get(idx + 5)
            {
                let cmd_end = find_command_end(idx + 1);
                if cmd_end == idx + 6 {
                    default_ext_alias_target = Some(alias_target.clone());
                    links.default_external_contract_alias = Some(alias_target.clone());
                } else {
                    links.default_modular_spec_errors.push(format!(
                        "`abbrev defaultExternalCallContract` has unexpected trailing tokens `{:?}`",
                        &tokens[idx + 6..cmd_end]
                    ));
                }
            }
        }
    }

    for (idx, tok) in tokens.iter().enumerate() {
        let LeanToken::Ident(ident) = tok else {
            continue;
        };
        if ident == "externalSpecCallContract" {
            if let Some(LeanToken::StrLit(target)) = tokens.get(idx + 1) {
                push_unique(&mut links.external_spec_targets, target);
            }
            if !linked_ext_contract_positions.contains(&idx) {
                links.unlinked_external_spec_errors.push(format!(
                    "unlinked or malformed `externalSpecCallContract` expression near {:?}",
                    tokens.get(idx + 1)
                ));
            }
        }
        match (ident.as_str(), tokens.get(idx + 1)) {
            ("import", Some(LeanToken::Ident(module))) => {
                if let Some(suffix) = module.strip_prefix("Obligations.") {
                    push_unique(&mut links.imported_obligation_suffixes, suffix);
                } else if let Some(suffix) = module.strip_prefix("Mir.") {
                    push_unique(&mut links.imported_mir_suffixes, suffix);
                } else if module.starts_with("Specs.") {
                    links.has_legacy_spec_override = true;
                }
            }
            ("body" | "implBody", Some(LeanToken::ColonEq)) => {
                links.claim_body_field_count += if ident == "implBody" { 2 } else { 1 };
                let end = find_field_rhs_end(idx + 2);
                let rhs_slice = &tokens[idx + 2..end];
                match rhs_slice {
                    [LeanToken::Ident(rhs)] => {
                        if let Some(item) =
                            rhs.strip_prefix("Mir.").and_then(|r| r.strip_suffix(".body"))
                            && !item.is_empty()
                        {
                            push_unique(&mut links.claim_mir_bodies, item);
                        } else {
                            push_unique(&mut links.non_mir_claim_bodies, rhs);
                        }
                    }
                    [LeanToken::Ident(rhs), LeanToken::Ident(arg)] if arg == "typeArgs" => {
                        if let Some(item) = rhs
                            .strip_prefix("Mir.")
                            .and_then(|r| r.strip_suffix(".body.instantiate"))
                            && !item.is_empty()
                        {
                            push_unique(&mut links.claim_mir_bodies, item);
                        } else {
                            push_unique(
                                &mut links.non_mir_claim_bodies,
                                &format!("{rhs} {arg}"),
                            );
                        }
                    }
                    other => {
                        push_unique(&mut links.non_mir_claim_bodies, &format!("{other:?}"));
                    }
                }
            }
            ("callees" | "implCallees" | "specCallees", Some(LeanToken::ColonEq)) => {
                links.claim_callees_field_count += 1;
                let end = find_field_rhs_end(idx + 2);
                let rhs_slice = &tokens[idx + 2..end];
                match rhs_slice {
                    [LeanToken::Ident(rhs)] => {
                        push_unique(&mut links.claim_callees_bindings, rhs);
                    }
                    [LeanToken::Dot, LeanToken::Ident(rhs)] => {
                        push_unique(&mut links.claim_callees_bindings, &format!(".{rhs}"));
                    }
                    other => {
                        push_unique(&mut links.claim_callees_bindings, &format!("{other:?}"));
                    }
                }
            }
            _ => {}
        }
        if let Some(item) = extract_mir_item(ident) {
            push_unique(&mut links.referenced_mir_bodies, item);
        }
    }
    for stem in raw_holds_on_stems {
        if let Some(callee) = extract_callee_contract(&stem) {
            push_unique(&mut links.referenced_callee_contracts, callee);
        } else if stem == "defaultExternalCallContract" {
            if let Some(ref target_ident) = default_ext_alias_target {
                push_unique(&mut links.referenced_external_contract_idents, target_ident);
            } else {
                links.default_modular_spec_errors.push(
                    "`defaultModularSpec.envAssumed` references `defaultExternalCallContract.holdsOn` without an `abbrev defaultExternalCallContract` alias"
                        .to_string(),
                );
            }
        } else if !stem.contains('.') {
            push_unique(&mut links.referenced_external_contract_idents, &stem);
        } else {
            links.default_modular_spec_errors.push(format!(
                "`defaultModularSpec.envAssumed` references unexpected qualified contract `{stem}.holdsOn`"
            ));
        }
    }
    Ok(links)
}

/// `[adv ep1-B3]` Verify that a generated `Obligations/<Item>.lean` module defines every
/// canonical monomorphic, equivalence, instantiated (`*For`), and polymorphic (`poly*`)
/// claim for `subject_suffix` with exact `{ ... }` record syntax (no positional
/// `Claim.mk` / `⟨...⟩` constructors, no `{ ... with ... }` record updates, no missing or
/// shadowed claim declarations, and exact `Mir.<subject_suffix>.body` + `defaultCallees`
/// bindings on every claim).
pub fn validate_obligations_canonical_claims(
    ob_text: &str,
    subject_suffix: &str,
) -> Result<(), String> {
    validate_obligations_canonical_claims_for_def_path(ob_text, subject_suffix, None)
}

/// `[adv ep1-B4]` Variant of [`validate_obligations_canonical_claims`] that additionally
/// pins every `defaultCallContract`, `defaultModularSpec`, `rustEquivSpec`, and canonical
/// claim typeclass binder in `Obligations/<subject_suffix>.lean` to `expected_def_path`.
pub fn validate_obligations_canonical_claims_for_def_path(
    ob_text: &str,
    subject_suffix: &str,
    expected_def_path: Option<&str>,
) -> Result<(), String> {
    const CANONICAL_NAMES: &[&str] = &[
        "claim",
        "statefulClaim",
        "totalClaim",
        "equivClaim",
        "modularClaim",
        "ubExceptionClaim",
        "claimFor",
        "statefulClaimFor",
        "totalClaimFor",
        "modularClaimFor",
        "ubExceptionClaimFor",
        "polyClaim",
        "polyStatefulClaim",
        "polyTotalClaim",
        "polyModularClaim",
        "polyUbExceptionClaim",
    ];
    const RESERVED_HELPER_DEFS: &[&str] = &[
        "defaultCallContract",
        "polyCertificate",
        "refineEquivSpec",
        "refineModularSpec",
    ];
    let tokens = tokenize_lean_source(ob_text)
        .map_err(|err| format!("failed to tokenize Obligations module for {subject_suffix}: {err}"))?;
    if let Some(attr) = detect_instance_attribute(&tokens) {
        return Err(format!(
            "disallowed `@[{attr}]` attribute in Obligations module for {subject_suffix}"
        ));
    }
    let expected_ns = format!("Obligations.{subject_suffix}");
    let mut ns_opens = 0usize;
    let mut ns_closes = 0usize;
    let mut claim_defs: BTreeMap<String, Vec<LeanToken>> = BTreeMap::new();
    let mut claim_sigs: BTreeMap<String, Vec<LeanToken>> = BTreeMap::new();
    let mut helper_cmds: BTreeMap<String, Vec<LeanToken>> = BTreeMap::new();

    let mut idx = 0usize;
    let mut depth = 0isize;
    while idx < tokens.len() {
        let cur_depth = depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            idx += 1;
            continue;
        }
        let LeanToken::Ident(kw) = &tokens[idx] else {
            idx += 1;
            continue;
        };
        match kw.as_str() {
            "import" => {
                let Some(LeanToken::Ident(module)) = tokens.get(idx + 1) else {
                    return Err(format!(
                        "malformed `import` command in Obligations module for {subject_suffix}"
                    ));
                };
                let allowed = module == "Init"
                    || module.starts_with("Init.")
                    || module == "Trusted"
                    || module.starts_with("Trusted.")
                    || module.starts_with("Mir.")
                    || module.starts_with("Obligations.")
                    || module == &format!("Specs.{subject_suffix}");
                if !allowed {
                    return Err(format!(
                        "disallowed `import {module}` in Obligations module for {subject_suffix}"
                    ));
                }
            }
            "namespace" => {
                match tokens.get(idx + 1) {
                    Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_opens += 1,
                    other => {
                        return Err(format!(
                            "unexpected `namespace {other:?}` in Obligations module for {subject_suffix}"
                        ));
                    }
                }
            }
            "end" => {
                match tokens.get(idx + 1) {
                    Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_closes += 1,
                    other => {
                        return Err(format!(
                            "unexpected `end {other:?}` in Obligations module for {subject_suffix}"
                        ));
                    }
                }
            }
            "axiom" | "opaque" | "macro" | "macro_rules" | "syntax" | "notation" | "infix"
            | "infixl" | "infixr" | "prefix" | "postfix" | "elab" | "local" | "scoped"
            | "attribute" | "unsafe" | "partial" | "export" | "section" => {
                return Err(format!(
                    "disallowed top-level `{kw}` command in Obligations module for {subject_suffix}"
                ));
            }
            "open" => {
                let mut open_idx = idx + 1;
                let mut count = 0usize;
                while let Some(LeanToken::Ident(ns_name)) = tokens.get(open_idx) {
                    if is_lean_command_start(&tokens[open_idx]) {
                        break;
                    }
                    if matches!(ns_name.as_str(), "renaming" | "hiding" | "in" | "scoped") {
                        return Err(format!(
                            "`open ... {ns_name}` is not supported in Obligations module for {subject_suffix}"
                        ));
                    }
                    if !STRICT_MODULE_OPENS.contains(&ns_name.as_str()) {
                        return Err(format!(
                            "disallowed `open {ns_name}` in Obligations module for {subject_suffix}"
                        ));
                    }
                    count += 1;
                    open_idx += 1;
                }
                if count == 0 {
                    return Err(format!(
                        "`open` without namespaces in Obligations module for {subject_suffix}"
                    ));
                }
            }
            "private" | "protected" | "noncomputable" => {
                if let Some(LeanToken::Ident(next_name)) = tokens.get(idx + 2)
                    && (CANONICAL_NAMES.contains(&next_name.as_str())
                        || RESERVED_HELPER_DEFS.contains(&next_name.as_str())
                        || next_name == "defaultModularSpec"
                        || next_name == "externalSpecCallContract")
                {
                    return Err(format!(
                        "`{kw}` modifier on canonical `{next_name}` in Obligations module for {subject_suffix}"
                    ));
                }
            }
            "abbrev" | "theorem" | "lemma" | "instance" | "structure" | "inductive" | "class" => {
                if let Some(LeanToken::Ident(name)) = tokens.get(idx + 1)
                    && (CANONICAL_NAMES.contains(&name.as_str())
                        || RESERVED_HELPER_DEFS.contains(&name.as_str())
                        || name == "externalSpecCallContract"
                        || (kw != "instance" && name == "defaultModularSpec"))
                {
                    return Err(format!(
                        "canonical `{name}` shadowed as `{kw}` in Obligations module for {subject_suffix}"
                    ));
                }
            }
            "def" => {
                if matches!(
                    tokens.get(idx + 1),
                    Some(LeanToken::Ident(n))
                        if n == "defaultModularSpec" || n == "externalSpecCallContract"
                ) {
                    return Err(format!(
                        "reserved identifier {:?} shadowed as `def` in Obligations module for {subject_suffix}",
                        tokens.get(idx + 1)
                    ));
                }
                if let Some(LeanToken::Ident(name)) = tokens.get(idx + 1)
                    && RESERVED_HELPER_DEFS.contains(&name.as_str())
                {
                    if helper_cmds.contains_key(name) {
                        return Err(format!(
                            "duplicate `def {name}` in Obligations module for {subject_suffix}"
                        ));
                    }
                    let mut k = idx + 2;
                    let mut hdepth = 0isize;
                    while k < tokens.len() {
                        if hdepth == 0 && is_lean_command_start(&tokens[k]) {
                            break;
                        }
                        match tokens[k] {
                            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                hdepth += 1;
                            }
                            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                hdepth = (hdepth - 1).max(0);
                            }
                            _ => {}
                        }
                        k += 1;
                    }
                    helper_cmds.insert(name.clone(), tokens[idx + 2..k].to_vec());
                }
                if let Some(LeanToken::Ident(name)) = tokens.get(idx + 1)
                    && CANONICAL_NAMES.contains(&name.as_str())
                {
                    if claim_defs.contains_key(name) {
                        return Err(format!(
                            "duplicate `def {name}` in Obligations module for {subject_suffix}"
                        ));
                    }
                    let mut j = idx + 2;
                    let mut sig_depth = 0isize;
                    while j < tokens.len() {
                        if sig_depth == 0 {
                            if tokens[j] == LeanToken::ColonEq {
                                break;
                            }
                            if is_lean_command_start(&tokens[j]) {
                                return Err(format!(
                                    "`def {name}` has no `:=` body in Obligations module for {subject_suffix}"
                                ));
                            }
                        }
                        match tokens[j] {
                            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                sig_depth += 1;
                            }
                            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                sig_depth = (sig_depth - 1).max(0);
                            }
                            _ => {}
                        }
                        j += 1;
                    }
                    if j >= tokens.len() {
                        return Err(format!(
                            "`def {name}` has no `:=` body in Obligations module for {subject_suffix}"
                        ));
                    }
                    let rhs_start = j + 1;
                    let mut k = rhs_start;
                    let mut rhs_depth = 0isize;
                    while k < tokens.len() {
                        if rhs_depth == 0 && is_lean_command_start(&tokens[k]) {
                            break;
                        }
                        match tokens[k] {
                            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                rhs_depth += 1;
                            }
                            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                rhs_depth = (rhs_depth - 1).max(0);
                            }
                            _ => {}
                        }
                        k += 1;
                    }
                    claim_sigs.insert(name.clone(), tokens[idx + 2..j].to_vec());
                    claim_defs.insert(name.clone(), tokens[rhs_start..k].to_vec());
                }
            }
            _ => {}
        }
        idx += 1;
    }
    if ns_opens != 1 || ns_closes != 1 {
        return Err(format!(
            "Obligations module for {subject_suffix} must contain a single `namespace {expected_ns} ... end {expected_ns}` block"
        ));
    }

    let check_record_claim =
        |def_name: &str, expected_fields: &[(&str, Vec<LeanToken>)]| -> Result<(), String> {
            let rhs = claim_defs.get(def_name).ok_or_else(|| {
                format!(
                    "missing canonical `def {def_name}` in Obligations module for {subject_suffix}"
                )
            })?;
            if rhs.len() < 2
                || rhs.first() != Some(&LeanToken::LBrace)
                || rhs.last() != Some(&LeanToken::RBrace)
            {
                return Err(format!(
                    "canonical `def {def_name}` in Obligations module for {subject_suffix} must be a `{{ ... }}` record literal (positional constructors and trailing expressions are forbidden)"
                ));
            }
            let mut bal = 0isize;
            for (pos, t) in rhs.iter().enumerate() {
                match t {
                    LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => bal += 1,
                    LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => bal -= 1,
                    _ => {}
                }
                if bal <= 0 && pos + 1 < rhs.len() {
                    return Err(format!(
                        "canonical `def {def_name}` in Obligations module for {subject_suffix} has trailing tokens after closing `}}`"
                    ));
                }
            }
            if bal != 0 {
                return Err(format!(
                    "unbalanced delimiters in `def {def_name}` of Obligations module for {subject_suffix}"
                ));
            }
            let inner = &rhs[1..rhs.len() - 1];
            let mut fields: BTreeMap<String, Vec<LeanToken>> = BTreeMap::new();
            let mut p = 0usize;
            while p < inner.len() {
                let Some(LeanToken::Ident(fname)) = inner.get(p) else {
                    return Err(format!(
                        "unexpected token {:?} in record literal of `def {def_name}` for {subject_suffix}",
                        inner.get(p)
                    ));
                };
                if fname == "with" {
                    return Err(format!(
                        "struct-update `with` syntax is forbidden in `def {def_name}` for {subject_suffix}"
                    ));
                }
                if inner.get(p + 1) != Some(&LeanToken::ColonEq) {
                    return Err(format!(
                        "expected `:=` after field `{fname}` in `def {def_name}` for {subject_suffix} (struct-update syntax is forbidden)"
                    ));
                }
                let val_start = p + 2;
                let mut q = val_start;
                let mut fdepth = 0isize;
                while q < inner.len() {
                    if fdepth == 0 {
                        if matches!(inner[q], LeanToken::Comma | LeanToken::Semicolon) {
                            break;
                        }
                        if q > val_start
                            && matches!(inner.get(q), Some(LeanToken::Ident(_)))
                            && inner.get(q + 1) == Some(&LeanToken::ColonEq)
                        {
                            break;
                        }
                        if matches!(&inner[q], LeanToken::Ident(w) if w == "with") {
                            return Err(format!(
                                "struct-update `with` syntax is forbidden in `def {def_name}` for {subject_suffix}"
                            ));
                        }
                    }
                    match inner[q] {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => fdepth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                            fdepth = (fdepth - 1).max(0);
                        }
                        _ => {}
                    }
                    q += 1;
                }
                if fields.contains_key(fname) {
                    return Err(format!(
                        "duplicate field `{fname}` in `def {def_name}` for {subject_suffix}"
                    ));
                }
                fields.insert(fname.clone(), inner[val_start..q].to_vec());
                p = if matches!(inner.get(q), Some(LeanToken::Comma | LeanToken::Semicolon)) {
                    q + 1
                } else {
                    q
                };
            }
            for (req_name, req_val) in expected_fields {
                match fields.get(*req_name) {
                    Some(actual) if actual == req_val => {}
                    Some(actual) => {
                        return Err(format!(
                            "canonical `def {def_name}` in Obligations module for {subject_suffix} binds `{req_name} := {actual:?}` instead of `{req_val:?}`"
                        ));
                    }
                    None => {
                        return Err(format!(
                            "canonical `def {def_name}` in Obligations module for {subject_suffix} omits required field `{req_name}`"
                        ));
                    }
                }
            }
            Ok(())
        };

    let mir_body_tok = vec![LeanToken::Ident(format!("Mir.{subject_suffix}.body"))];
    let mir_inst_tok = vec![
        LeanToken::Ident(format!("Mir.{subject_suffix}.body.instantiate")),
        LeanToken::Ident("typeArgs".to_string()),
    ];
    let default_callees_tok = vec![LeanToken::Ident("defaultCallees".to_string())];
    let spec_env_tok = vec![LeanToken::Ident("spec.envAssumed".to_string())];
    let spec_body_tok = vec![LeanToken::Ident("spec.specBody".to_string())];

    for mono_name in [
        "claim",
        "statefulClaim",
        "totalClaim",
        "ubExceptionClaim",
    ] {
        check_record_claim(
            mono_name,
            &[
                ("body", mir_body_tok.clone()),
                ("callees", default_callees_tok.clone()),
            ],
        )?;
    }
    check_record_claim(
        "modularClaim",
        &[
            ("body", mir_body_tok.clone()),
            ("envAssumed", spec_env_tok.clone()),
            ("callees", default_callees_tok.clone()),
        ],
    )?;
    check_record_claim(
        "equivClaim",
        &[
            ("implBody", mir_body_tok),
            ("specBody", spec_body_tok),
            ("implCallees", default_callees_tok.clone()),
            ("specCallees", default_callees_tok.clone()),
        ],
    )?;
    for inst_name in [
        "claimFor",
        "statefulClaimFor",
        "totalClaimFor",
        "ubExceptionClaimFor",
    ] {
        check_record_claim(
            inst_name,
            &[
                ("body", mir_inst_tok.clone()),
                ("callees", default_callees_tok.clone()),
            ],
        )?;
    }
    check_record_claim(
        "modularClaimFor",
        &[
            ("body", mir_inst_tok),
            ("envAssumed", spec_env_tok),
            ("callees", default_callees_tok),
        ],
    )?;

    let expected_tp_count = format!("Mir.{subject_suffix}.body.typeParamCount");
    for (poly_name, cert_short, claim_for_name) in [
        ("polyClaim", "VerificationResult", "claimFor"),
        (
            "polyStatefulClaim",
            "StatefulVerificationResult",
            "statefulClaimFor",
        ),
        ("polyTotalClaim", "TotalVerificationResult", "totalClaimFor"),
        (
            "polyModularClaim",
            "ModularVerificationResult",
            "modularClaimFor",
        ),
        (
            "polyUbExceptionClaim",
            "UbExceptionVerificationResult",
            "ubExceptionClaimFor",
        ),
    ] {
        let rhs = claim_defs.get(poly_name).ok_or_else(|| {
            format!(
                "missing canonical `def {poly_name}` in Obligations module for {subject_suffix}"
            )
        })?;
        let poly_ok = match rhs.as_slice() {
            [
                LeanToken::Ident(forall_kw),
                LeanToken::LParen,
                LeanToken::Ident(ta1),
                LeanToken::Colon,
                LeanToken::Ident(ts_ty),
                LeanToken::RParen,
                LeanToken::Comma,
                LeanToken::Ident(ta_len),
                LeanToken::Ident(eq_op),
                LeanToken::Ident(mir_tp),
                LeanToken::Ident(arrow_op),
                LeanToken::Ident(cert_ty),
                LeanToken::LParen,
                LeanToken::Ident(cf_name),
                LeanToken::Ident(ta2),
                LeanToken::RParen,
            ] => {
                let short_cert = cert_ty
                    .strip_prefix("Trusted.VerificationResult.")
                    .unwrap_or(cert_ty.as_str());
                (forall_kw == "∀" || forall_kw == "forall")
                    && ta1 == "typeArgs"
                    && (ts_ty == "Trusted.MirAst.TypeSubst" || ts_ty == "TypeSubst")
                    && ta_len == "typeArgs.length"
                    && eq_op == "="
                    && mir_tp == &expected_tp_count
                    && (arrow_op == "→" || arrow_op == "->")
                    && short_cert == cert_short
                    && cf_name == claim_for_name
                    && ta2 == "typeArgs"
            }
            _ => false,
        };
        if !poly_ok {
            return Err(format!(
                "canonical `def {poly_name}` in Obligations module for {subject_suffix} does not wrap `({claim_for_name} typeArgs)` in `{cert_short}`"
            ));
        }
    }

    // `[adv ep1-B4]`: Verify `polyCertificate (P : Prop) : CrateClaim` packages `certificate := P`
    // into a non-empty `[ { identity := artifactIdentity, certificate := P } ]` list.
    let poly_cert_cmd = helper_cmds.get("polyCertificate").ok_or_else(|| {
        format!("missing canonical `def polyCertificate` in Obligations module for {subject_suffix}")
    })?;
    let poly_cert_ok = poly_cert_cmd.len() >= 21
        && poly_cert_cmd.first() == Some(&LeanToken::LParen)
        && matches!(poly_cert_cmd.get(1), Some(LeanToken::Ident(p)) if p == "P")
        && poly_cert_cmd.get(2) == Some(&LeanToken::Colon)
        && matches!(poly_cert_cmd.get(3), Some(LeanToken::Ident(pr)) if pr == "Prop")
        && poly_cert_cmd.get(4) == Some(&LeanToken::RParen)
        && poly_cert_cmd.get(5) == Some(&LeanToken::Colon)
        && matches!(
            poly_cert_cmd.get(6),
            Some(LeanToken::Ident(cc))
                if cc == "CrateClaim"
                    || cc == "Trusted.VerificationResult.CrateClaim"
                    || cc == "_root_.Trusted.VerificationResult.CrateClaim"
                    || cc == "VerificationResult.CrateClaim"
        )
        && matches!(
            &poly_cert_cmd[poly_cert_cmd.len() - 13..],
            [
                LeanToken::Ident(items_kw),
                LeanToken::ColonEq,
                LeanToken::LBracket,
                LeanToken::LBrace,
                LeanToken::Ident(id_kw),
                LeanToken::ColonEq,
                LeanToken::Ident(art_id),
                LeanToken::Comma,
                LeanToken::Ident(cert_kw),
                LeanToken::ColonEq,
                LeanToken::Ident(p_ref),
                LeanToken::RBrace,
                LeanToken::RBracket,
            ] if items_kw == "items"
                && id_kw == "identity"
                && art_id == "artifactIdentity"
                && cert_kw == "certificate"
                && p_ref == "P"
        );
    if !poly_cert_ok {
        return Err(format!(
            "canonical `def polyCertificate` in Obligations module for {subject_suffix} was altered from `items := [{{ identity := artifactIdentity, certificate := P }}]`"
        ));
    }

    // `[adv ep1-B4]`: Verify `refineEquivSpec` and `refineModularSpec` preserve their
    // `specBody := specBody` and `envAssumed := envAssumed` arguments unaltered.
    let check_refine_helper = |helper_name: &str, field_name: &str| -> Result<(), String> {
        let cmd = helper_cmds.get(helper_name).ok_or_else(|| {
            format!("missing canonical `def {helper_name}` in Obligations module for {subject_suffix}")
        })?;
        let Some(where_pos) = cmd
            .iter()
            .position(|t| matches!(t, LeanToken::Ident(w) if w == "where"))
        else {
            return Err(format!(
                "`def {helper_name}` in Obligations module for {subject_suffix} must use `where {field_name} := {field_name}`"
            ));
        };
        let body = &cmd[where_pos + 1..];
        let ok = matches!(
            body.get(..4),
            Some([
                LeanToken::Ident(lhs),
                LeanToken::ColonEq,
                LeanToken::Ident(rhs),
                LeanToken::Ident(next_field),
            ]) if lhs == field_name && rhs == field_name && (next_field == "pre" || next_field == "post")
        );
        if !ok {
            return Err(format!(
                "`def {helper_name}` in Obligations module for {subject_suffix} does not bind `{field_name} := {field_name}`"
            ));
        }
        Ok(())
    };
    check_refine_helper("refineEquivSpec", "specBody")?;
    check_refine_helper("refineModularSpec", "envAssumed")?;

    // `[adv ep1-B4]`: Verify `[spec : <*ItemSpec> "<defId>"]` binders on spec-parameterized
    // canonical claims match `expected_def_path` when supplied.
    for (claim_name, expected_cls) in [
        ("claim", "ItemSpec"),
        ("statefulClaim", "StatefulItemSpec"),
        ("totalClaim", "TotalItemSpec"),
        ("equivClaim", "StatefulEquivItemSpec"),
        ("modularClaim", "ModularItemSpec"),
        ("ubExceptionClaim", "UbExceptionItemSpec"),
        ("claimFor", "ItemSpec"),
        ("modularClaimFor", "ModularItemSpec"),
        ("ubExceptionClaimFor", "UbExceptionItemSpec"),
        ("polyClaim", "ItemSpec"),
        ("polyModularClaim", "ModularItemSpec"),
        ("polyUbExceptionClaim", "UbExceptionItemSpec"),
    ] {
        let sig = claim_sigs.get(claim_name).ok_or_else(|| {
            format!("missing signature for `def {claim_name}` in Obligations module for {subject_suffix}")
        })?;
        let expected_binder = if claim_name == "claimFor" {
            None // `claimFor` uses `spec` or `_spec`
        } else {
            Some("spec")
        };
        let binder_ok = match sig.get(..6) {
            Some([
                LeanToken::LBracket,
                LeanToken::Ident(b_name),
                LeanToken::Colon,
                LeanToken::Ident(cls_ident),
                LeanToken::StrLit(did),
                LeanToken::RBracket,
            ]) => {
                let name_ok = match expected_binder {
                    Some(exp) => b_name == exp,
                    None => b_name == "spec" || b_name == "_spec",
                };
                name_ok
                    && canonical_spec_class_name(cls_ident) == Some(expected_cls)
                    && expected_def_path.is_none_or(|exp_did| did == exp_did)
            }
            _ => false,
        };
        if !binder_ok {
            return Err(format!(
                "canonical `def {claim_name}` in Obligations module for {subject_suffix} has non-canonical `[spec : {expected_cls} \"...\"]` binder `{sig:?}`"
            ));
        }
    }

    let links = scan_obligations_callee_links(ob_text)
        .map_err(|err| format!("failed to scan Obligations module for {subject_suffix}: {err}"))?;
    if !links.imported_mir_suffixes.iter().any(|m| m == subject_suffix) {
        return Err(format!(
            "Obligations module for {subject_suffix} must `import Mir.{subject_suffix}`"
        ));
    }
    if links.default_spec_count != 1 {
        return Err(format!(
            "Obligations module for {subject_suffix} must declare exactly one `defaultSpec` instance (found {})",
            links.default_spec_count
        ));
    }
    if links.default_total_spec_count != 1 {
        return Err(format!(
            "Obligations module for {subject_suffix} must declare exactly one `defaultTotalSpec` instance (found {})",
            links.default_total_spec_count
        ));
    }
    if links.default_modular_spec_count != 1 {
        return Err(format!(
            "Obligations module for {subject_suffix} must declare exactly one `defaultModularSpec` instance (found {})",
            links.default_modular_spec_count
        ));
    }
    if !links.default_modular_spec_errors.is_empty() {
        return Err(format!(
            "Obligations module for {subject_suffix} has malformed `defaultModularSpec`: {}",
            links.default_modular_spec_errors.join("; ")
        ));
    }
    if !links.equiv_spec_errors.is_empty() {
        return Err(format!(
            "Obligations module for {subject_suffix} has malformed `StatefulEquivItemSpec`: {}",
            links.equiv_spec_errors.join("; ")
        ));
    }
    if !links.contract_integrity_errors.is_empty() {
        return Err(format!(
            "Obligations module for {subject_suffix} has contract integrity errors: {}",
            links.contract_integrity_errors.join("; ")
        ));
    }
    if links.default_call_contract_def_path.is_none() {
        return Err(format!(
            "Obligations module for {subject_suffix} is missing canonical `def defaultCallContract`"
        ));
    }
    if let Some(exp_did) = expected_def_path {
        if links.default_call_contract_def_path.as_deref() != Some(exp_did) {
            return Err(format!(
                "Obligations module for {subject_suffix} binds `defaultCallContract` to `{:?}` instead of `{exp_did}`",
                links.default_call_contract_def_path
            ));
        }
        if links.default_modular_spec_def_id.as_deref() != Some(exp_did) {
            return Err(format!(
                "Obligations module for {subject_suffix} binds `defaultModularSpec` to `{:?}` instead of `{exp_did}`",
                links.default_modular_spec_def_id
            ));
        }
        if let Some(ref eq_did) = links.rust_equiv_spec_def_id
            && eq_did != exp_did
        {
            return Err(format!(
                "Obligations module for {subject_suffix} binds `rustEquivSpec` to `{eq_did}` instead of `{exp_did}`"
            ));
        }
    }

    Ok(())
}

/// `[adv ep1-A3]` Canonical certificate surface proved by `theorem verified` in
/// `.anneal/generated/Verify/<Item>.lean`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedCertificateSurface {
    /// `VerificationResult Obligations.<Item>.claim`
    Claim,
    /// `StatefulVerificationResult Obligations.<Item>.statefulClaim`
    StatefulClaim,
    /// `TotalVerificationResult Obligations.<Item>.totalClaim`
    TotalClaim,
    /// `StatefulEquivVerificationResult Obligations.<Item>.equivClaim`
    EquivClaim,
    /// `ModularVerificationResult Obligations.<Item>.modularClaim`
    ModularClaim,
    /// `UbExceptionVerificationResult Obligations.<Item>.ubExceptionClaim`
    UbExceptionClaim,
    /// `CrateVerificationResult (Obligations.<Item>.polyCertificate Obligations.<Item>.polyClaim)`
    PolyClaim,
    /// `CrateVerificationResult (... polyStatefulClaim)`
    PolyStatefulClaim,
    /// `CrateVerificationResult (... polyTotalClaim)`
    PolyTotalClaim,
    /// `CrateVerificationResult (... polyModularClaim)`
    PolyModularClaim,
    /// `CrateVerificationResult (... polyUbExceptionClaim)`
    PolyUbExceptionClaim,
}

/// `[adv ep1-B4]` / `[adv ep1-A4]` Kind of sibling modular call contract referenced from
/// a caller's `Obligations.<Item>` or `Specs.<Item>` `ModularItemSpec.envAssumed`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SiblingModularContractKind {
    /// `Obligations.<Callee>.defaultCallContract`
    DefaultCallContract,
    /// `Obligations.<Callee>.ubExceptionClaim.callContract`
    UbExceptionCallContract,
}

impl VerifiedCertificateSurface {
    /// True iff this surface interprets unresolved calls through a modular
    /// `ExternalCallHandler` (`ModularClaim` / `PolyModularClaim`).
    pub const fn is_modular(self) -> bool {
        matches!(self, Self::ModularClaim | Self::PolyModularClaim)
    }

    /// True iff this surface proves program-to-program equivalence (`equivClaim`).
    pub const fn is_equiv(self) -> bool {
        matches!(self, Self::EquivClaim)
    }

    /// True iff this surface proves a scoped UB-exception contract (`ubExceptionClaim` / `polyUbExceptionClaim`).
    pub const fn is_ub_exception(self) -> bool {
        matches!(self, Self::UbExceptionClaim | Self::PolyUbExceptionClaim)
    }

    /// `[adv ep1-B4]` / `[adv ep1-A4]` True iff a sibling callee's `Verify.<Callee>`
    /// certificate surface backs the requested modular `MirCallContract` kind
    /// (`defaultCallContract` requires `Claim` or `TotalClaim` without overriding that
    /// surface's default spec class via `legacySpec` or `Specs.<Callee>`, while
    /// `ubExceptionClaim.callContract` requires `UbExceptionClaim`).
    pub const fn supports_sibling_modular_contract(
        self,
        kind: SiblingModularContractKind,
        callee_overrides_active_spec: bool,
    ) -> bool {
        match kind {
            SiblingModularContractKind::DefaultCallContract => {
                matches!(self, Self::Claim | Self::TotalClaim) && !callee_overrides_active_spec
            }
            SiblingModularContractKind::UbExceptionCallContract => {
                matches!(self, Self::UbExceptionClaim)
            }
        }
    }
}

/// `[adv ep1-A3]` Parsed metadata of `.anneal/generated/Verify/<Item>.lean`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedCertificateInfo {
    /// Canonical certificate surface proved by `theorem verified`.
    pub surface: VerifiedCertificateSurface,
    /// `<Suffix>` module suffixes of `import Specs.<Suffix>` commands in `Verify/<Item>.lean`.
    pub imported_specs_suffixes: Vec<String>,
    /// `<Suffix>` module suffixes of `import Proof.<Suffix>` commands in `Verify/<Item>.lean`.
    pub imported_proof_suffixes: Vec<String>,
    /// `<Suffix>` module suffixes of `import Assumptions.<Suffix>` commands in `Verify/<Item>.lean`.
    pub imported_assumptions_suffixes: Vec<String>,
}

/// `[adv ep1-B3]` / `[adv ep1-A3]` / `[adv ep1-B4]` Inspect `.anneal/generated/Verify/<Item>.lean`,
/// verifying that it defines a single `theorem verified` inside `namespace Verify.<subject_suffix>`
/// proving one of the canonical `Obligations.<subject_suffix>` certificate types, with no
/// specification typeclass overrides (`*ItemSpec` instances, `@[instance]`, `attribute`),
/// `axiom`, `opaque`, `macro`, `elab`, `notation`, or unauthorized `import` commands.
pub fn inspect_verify_module_certificate(
    verify_text: &str,
    subject_suffix: &str,
) -> Result<VerifiedCertificateInfo, String> {
    let tokens = tokenize_lean_source(verify_text)
        .map_err(|err| format!("failed to tokenize Verify module for {subject_suffix}: {err}"))?;
    if let Some(attr) = detect_instance_attribute(&tokens) {
        return Err(format!(
            "disallowed `@[{attr}]` attribute in Verify module for {subject_suffix}"
        ));
    }
    let expected_ns = format!("Verify.{subject_suffix}");
    let mut ns_opens = 0usize;
    let mut ns_closes = 0usize;
    let mut imported_own_obligations = false;
    let mut verified_types: Vec<Vec<LeanToken>> = Vec::new();
    let mut imported_specs_suffixes: Vec<String> = Vec::new();
    let mut imported_proof_suffixes: Vec<String> = Vec::new();
    let mut imported_assumptions_suffixes: Vec<String> = Vec::new();

    const VERIFY_CERTIFICATE_TYPE_NAMES: &[&str] = &[
        "VerificationResult",
        "StatefulVerificationResult",
        "TotalVerificationResult",
        "StatefulEquivVerificationResult",
        "ModularVerificationResult",
        "UbExceptionVerificationResult",
        "CrateVerificationResult",
    ];

    let check_decl_not_shadowing = |decl_kw: &str, decl_name: &str| -> Result<(), String> {
        let last = decl_name.rsplit_once('.').map(|(_, s)| s).unwrap_or(decl_name);
        if VERIFY_CERTIFICATE_TYPE_NAMES.contains(&last)
            || canonical_spec_class_name(last).is_some()
            || canonical_proof_class_name(last).is_some()
            || decl_name.contains('.')
        {
            return Err(format!(
                "`{decl_kw} {decl_name}` shadows or escapes the certificate namespace in Verify module for {subject_suffix}"
            ));
        }
        Ok(())
    };

    let find_command_end = |start: usize| -> usize {
        let mut cdepth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if cdepth == 0 && k > start && is_lean_command_start(&tokens[k]) {
                break;
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => cdepth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    cdepth = (cdepth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };

    let mut idx = 0usize;
    let mut depth = 0isize;
    while idx < tokens.len() {
        let cur_depth = depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            idx += 1;
            continue;
        }
        let LeanToken::Ident(kw) = &tokens[idx] else {
            idx += 1;
            continue;
        };
        match kw.as_str() {
            "import" => {
                let Some(LeanToken::Ident(module)) = tokens.get(idx + 1) else {
                    return Err(format!(
                        "malformed `import` command in Verify module for {subject_suffix}"
                    ));
                };
                if let Some(spec_suf) = module.strip_prefix("Specs.") {
                    if spec_suf != subject_suffix {
                        return Err(format!(
                            "Verify module for {subject_suffix} imports foreign specification module `Specs.{spec_suf}`"
                        ));
                    }
                    if !imported_specs_suffixes.iter().any(|s| s == spec_suf) {
                        imported_specs_suffixes.push(spec_suf.to_string());
                    }
                } else if let Some(proof_suf) = module.strip_prefix("Proof.") {
                    if proof_suf != subject_suffix {
                        return Err(format!(
                            "Verify module for {subject_suffix} imports foreign proof module `Proof.{proof_suf}`"
                        ));
                    }
                    if !imported_proof_suffixes.iter().any(|s| s == proof_suf) {
                        imported_proof_suffixes.push(proof_suf.to_string());
                    }
                } else if let Some(assump_suf) = module.strip_prefix("Assumptions.") {
                    if assump_suf != subject_suffix {
                        return Err(format!(
                            "Verify module for {subject_suffix} imports foreign assumptions module `Assumptions.{assump_suf}`"
                        ));
                    }
                    if !imported_assumptions_suffixes.iter().any(|s| s == assump_suf) {
                        imported_assumptions_suffixes.push(assump_suf.to_string());
                    }
                } else {
                    if module == &format!("Obligations.{subject_suffix}") {
                        imported_own_obligations = true;
                    }
                    let allowed = module == "Init"
                        || module.starts_with("Init.")
                        || module == "Std"
                        || module.starts_with("Std.")
                        || module == "Trusted"
                        || module.starts_with("Trusted.")
                        || module == "Anneal"
                        || module.starts_with("Anneal.")
                        || module.starts_with("Mir.")
                        || module == &format!("Obligations.{subject_suffix}");
                    if !allowed {
                        return Err(format!(
                            "disallowed `import {module}` in Verify module for {subject_suffix}"
                        ));
                    }
                }
            }
            "namespace" => match tokens.get(idx + 1) {
                Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_opens += 1,
                other => {
                    return Err(format!(
                        "unexpected `namespace {other:?}` in Verify module for {subject_suffix}"
                    ));
                }
            },
            "end" => match tokens.get(idx + 1) {
                Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_closes += 1,
                other => {
                    return Err(format!(
                        "unexpected `end {other:?}` in Verify module for {subject_suffix}"
                    ));
                }
            },
            "open" => {
                let mut open_idx = idx + 1;
                let mut count = 0usize;
                while let Some(LeanToken::Ident(ns_name)) = tokens.get(open_idx) {
                    if is_lean_command_start(&tokens[open_idx]) {
                        break;
                    }
                    if matches!(ns_name.as_str(), "renaming" | "hiding" | "in" | "scoped") {
                        return Err(format!(
                            "`open ... {ns_name}` is not supported in Verify module for {subject_suffix}"
                        ));
                    }
                    if !STRICT_MODULE_OPENS.contains(&ns_name.as_str()) {
                        return Err(format!(
                            "disallowed `open {ns_name}` in Verify module for {subject_suffix}"
                        ));
                    }
                    count += 1;
                    open_idx += 1;
                }
                if count == 0 {
                    return Err(format!(
                        "`open` without namespaces in Verify module for {subject_suffix}"
                    ));
                }
            }
            "axiom" | "opaque" | "macro" | "macro_rules" | "syntax" | "notation" | "infix"
            | "infixl" | "infixr" | "prefix" | "postfix" | "elab" | "local" | "scoped"
            | "attribute" | "class" | "structure" | "inductive" | "unsafe" | "partial"
            | "export" | "section" | "private" | "protected" | "noncomputable" | "nonrec" => {
                return Err(format!(
                    "disallowed top-level `{kw}` command or modifier in Verify module for {subject_suffix}"
                ));
            }
            "def" | "abbrev" | "lemma" | "example" => {
                if let Some(LeanToken::Ident(n)) = tokens.get(idx + 1) {
                    if n == "verified" {
                        return Err(format!(
                            "`verified` declared as `{kw}` instead of `theorem` in Verify module for {subject_suffix}"
                        ));
                    }
                    check_decl_not_shadowing(kw, n)?;
                }
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok {
                        if let Some(spec_cls) = canonical_spec_class_name(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} references `{spec_cls}` inside `{kw}` declaration"
                            ));
                        }
                        if is_refine_spec_helper_ident(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} invokes specification override helper `{id}` inside `{kw}`"
                            ));
                        }
                    }
                }
            }
            "instance" => {
                if let Some(LeanToken::Ident(n)) = tokens.get(idx + 1) {
                    if n == "verified" {
                        return Err(format!(
                            "`verified` declared as `instance` instead of `theorem` in Verify module for {subject_suffix}"
                        ));
                    }
                    check_decl_not_shadowing(kw, n)?;
                }
                let cmd_end = find_command_end(idx + 1);
                let cmd_slice = &tokens[idx..cmd_end];
                let mut header_end = cmd_slice.len();
                let mut h_depth = 0isize;
                for (h_pos, t) in cmd_slice.iter().enumerate() {
                    if h_depth == 0
                        && (*t == LeanToken::ColonEq
                            || matches!(t, LeanToken::Ident(w) if w == "where"))
                    {
                        header_end = h_pos;
                        break;
                    }
                    match t {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => h_depth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                            h_depth = (h_depth - 1).max(0);
                        }
                        _ => {}
                    }
                }
                for tok in cmd_slice {
                    if let LeanToken::Ident(id) = tok {
                        if let Some(spec_cls) = canonical_spec_class_name(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} declares unauthorized `{spec_cls}` instance (specification instances must reside in `Specs.{subject_suffix}`)"
                            ));
                        }
                        if is_refine_spec_helper_ident(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} invokes specification override helper `{id}` inside `instance`"
                            ));
                        }
                    }
                }
                let header = &cmd_slice[..header_end];
                let is_proof_instance = header.iter().any(|t| {
                    matches!(t, LeanToken::Ident(id) if canonical_proof_class_name(id).is_some())
                });
                if !is_proof_instance {
                    return Err(format!(
                        "Verify module for {subject_suffix} declares non-`*ItemProof` `instance` `{header:?}`"
                    ));
                }
            }
            "theorem" => {
                if let Some(LeanToken::Ident(n)) = tokens.get(idx + 1) {
                    check_decl_not_shadowing(kw, n)?;
                }
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok {
                        if let Some(spec_cls) = canonical_spec_class_name(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} references `{spec_cls}` inside `theorem` declaration"
                            ));
                        }
                        if is_refine_spec_helper_ident(id) {
                            return Err(format!(
                                "Verify module for {subject_suffix} invokes specification override helper `{id}` inside `theorem`"
                            ));
                        }
                    }
                }
                if matches!(tokens.get(idx + 1), Some(LeanToken::Ident(n)) if n == "verified") {
                    if tokens.get(idx + 2) != Some(&LeanToken::Colon) {
                        return Err(format!(
                            "`theorem verified` in Verify module for {subject_suffix} must have an explicit `: <CertificateType> :=` signature without binders"
                        ));
                    }
                    let ty_start = idx + 3;
                    let mut j = ty_start;
                    let mut tdepth = 0isize;
                    while j < tokens.len() {
                        if tdepth == 0 {
                            if tokens[j] == LeanToken::ColonEq {
                                break;
                            }
                            if is_lean_command_start(&tokens[j]) {
                                return Err(format!(
                                    "`theorem verified` has no `:=` proof body in Verify module for {subject_suffix}"
                                ));
                            }
                        }
                        match tokens[j] {
                            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                tdepth += 1;
                            }
                            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                tdepth = (tdepth - 1).max(0);
                            }
                            _ => {}
                        }
                        j += 1;
                    }
                    if j >= tokens.len() {
                        return Err(format!(
                            "`theorem verified` has no `:=` proof body in Verify module for {subject_suffix}"
                        ));
                    }
                    verified_types.push(tokens[ty_start..j].to_vec());
                }
            }
            _ => {}
        }
        idx += 1;
    }

    if !imported_own_obligations {
        return Err(format!(
            "Verify module for {subject_suffix} must `import Obligations.{subject_suffix}`"
        ));
    }
    if ns_opens != 1 || ns_closes != 1 {
        return Err(format!(
            "Verify module for {subject_suffix} must contain a single `namespace {expected_ns} ... end {expected_ns}` block"
        ));
    }
    if verified_types.len() != 1 {
        return Err(format!(
            "Verify module for {subject_suffix} must declare exactly one `theorem verified` (found {})",
            verified_types.len()
        ));
    }
    fn strip_cert_qual(s: &str) -> &str {
        let s = s.strip_prefix("_root_.").unwrap_or(s);
        let s = s.strip_prefix("Trusted.").unwrap_or(s);
        s.strip_prefix("VerificationResult.").unwrap_or(s)
    }
    let ty_slice = &verified_types[0];
    let ob_prefix = format!("Obligations.{subject_suffix}.");
    let surface_opt = match ty_slice.as_slice() {
        [LeanToken::Ident(cert_ty), LeanToken::Ident(claim_ref)] => {
            let short_cert = strip_cert_qual(cert_ty);
            match claim_ref.strip_prefix(&ob_prefix) {
                Some("claim") if short_cert == "VerificationResult" => {
                    Some(VerifiedCertificateSurface::Claim)
                }
                Some("statefulClaim") if short_cert == "StatefulVerificationResult" => {
                    Some(VerifiedCertificateSurface::StatefulClaim)
                }
                Some("totalClaim") if short_cert == "TotalVerificationResult" => {
                    Some(VerifiedCertificateSurface::TotalClaim)
                }
                Some("equivClaim") if short_cert == "StatefulEquivVerificationResult" => {
                    Some(VerifiedCertificateSurface::EquivClaim)
                }
                Some("modularClaim") if short_cert == "ModularVerificationResult" => {
                    Some(VerifiedCertificateSurface::ModularClaim)
                }
                Some("ubExceptionClaim") if short_cert == "UbExceptionVerificationResult" => {
                    Some(VerifiedCertificateSurface::UbExceptionClaim)
                }
                _ => None,
            }
        }
        [
            LeanToken::Ident(cert_ty),
            LeanToken::LParen,
            LeanToken::Ident(poly_cert),
            LeanToken::Ident(poly_prop),
            LeanToken::RParen,
        ] => {
            let short_cert = strip_cert_qual(cert_ty);
            if short_cert == "CrateVerificationResult"
                && poly_cert == &format!("{ob_prefix}polyCertificate")
            {
                match poly_prop.strip_prefix(&ob_prefix) {
                    Some("polyClaim") => Some(VerifiedCertificateSurface::PolyClaim),
                    Some("polyStatefulClaim") => {
                        Some(VerifiedCertificateSurface::PolyStatefulClaim)
                    }
                    Some("polyTotalClaim") => Some(VerifiedCertificateSurface::PolyTotalClaim),
                    Some("polyModularClaim") => Some(VerifiedCertificateSurface::PolyModularClaim),
                    Some("polyUbExceptionClaim") => {
                        Some(VerifiedCertificateSurface::PolyUbExceptionClaim)
                    }
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    };
    let Some(surface) = surface_opt else {
        return Err(format!(
            "Verify module for {subject_suffix} proves non-canonical statement `{ty_slice:?}` instead of `Obligations.{subject_suffix}.<claim>`"
        ));
    };
    Ok(VerifiedCertificateInfo {
        surface,
        imported_specs_suffixes,
        imported_proof_suffixes,
        imported_assumptions_suffixes,
    })
}

/// `[adv ep1-B3]` Verify that `.anneal/generated/Verify/<Item>.lean` defines a single
/// `theorem verified` inside `namespace Verify.<subject_suffix>` whose statement proves
/// one of the canonical `Obligations.<subject_suffix>` certificate types (and introduces
/// no `axiom`, `opaque`, `macro`, `elab`, or `notation` commands).
pub fn validate_verify_module_certificate(
    verify_text: &str,
    subject_suffix: &str,
) -> Result<(), String> {
    inspect_verify_module_certificate(verify_text, subject_suffix).map(|_| ())
}

/// `[adv ep1-B4]` Transitive import links discovered inside an auxiliary `Proof.*` or
/// `Assumptions.*` module.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AuxiliaryModuleImports {
    /// Sibling `Specs.<Other>` suffixes (`<Other> != <subject_suffix>`) imported by this module.
    pub imported_sibling_specs: Vec<String>,
    /// `Proof.<Other>` suffixes imported by this module (for transitive cone traversal).
    pub imported_proof_suffixes: Vec<String>,
    /// `Assumptions.<Other>` suffixes imported by this module (for transitive cone traversal).
    pub imported_assumptions_suffixes: Vec<String>,
}

/// `[adv ep1-A3]` / `[adv ep1-B4]` Validate an auxiliary module (`Proof/<X>.lean` or
/// `Assumptions/<X>.lean`) in the transitive import cone of `Verify/<Item>.lean`, ensuring
/// it declares no specification typeclass instances (`*ItemSpec`, `@[instance]`, `attribute`,
/// `local`, `scoped`, `refine*Spec`, or `abbrev` class aliases) or syntax-extension commands
/// (`macro`, `elab`, `notation`), enforcing `is_allowed_aux_import` on every `import`, and
/// returning its `Specs.*`, `Proof.*`, and `Assumptions.*` imports for transitive traversal.
pub fn validate_auxiliary_module_no_spec_override(
    aux_text: &str,
    aux_label: &str,
    subject_suffix: &str,
    verify_imports_specs: bool,
) -> Result<AuxiliaryModuleImports, String> {
    let tokens = tokenize_lean_source(aux_text)
        .map_err(|err| format!("failed to tokenize {aux_label}: {err}"))?;
    if let Some(attr) = detect_instance_attribute(&tokens) {
        return Err(format!("disallowed `@[{attr}]` attribute in {aux_label}"));
    }
    let mut out = AuxiliaryModuleImports::default();
    let push_unique = |vec: &mut Vec<String>, val: &str| {
        if !val.is_empty() && !vec.iter().any(|x| x == val) {
            vec.push(val.to_string());
        }
    };
    let find_command_end = |start: usize| -> usize {
        let mut depth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if depth == 0 && k > start && is_lean_command_start(&tokens[k]) {
                break;
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };
    let mut depth = 0isize;
    for idx in 0..tokens.len() {
        let cur_depth = depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            continue;
        }
        let LeanToken::Ident(kw) = &tokens[idx] else {
            continue;
        };
        match kw.as_str() {
            "macro" | "macro_rules" | "syntax" | "notation" | "elab" | "local" | "scoped"
            | "attribute" | "class" | "unsafe" | "partial" => {
                return Err(format!("disallowed top-level `{kw}` command in {aux_label}"));
            }
            "def" | "theorem" | "lemma" => {
                if let Some(LeanToken::Ident(decl_name)) = tokens.get(idx + 1)
                    && (decl_name.starts_with("Obligations.")
                        || decl_name.starts_with("Mir.")
                        || decl_name.starts_with("Trusted."))
                {
                    return Err(format!(
                        "{aux_label} shadows reserved namespace declaration `{decl_name}`"
                    ));
                }
            }
            "structure" | "inductive" => {
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok
                        && (canonical_spec_class_name(id).is_some()
                            || is_refine_spec_helper_ident(id))
                    {
                        return Err(format!(
                            "{aux_label} references `{id}` inside `{kw}` declaration"
                        ));
                    }
                }
            }
            "import" => {
                let Some(LeanToken::Ident(module)) = tokens.get(idx + 1) else {
                    return Err(format!("malformed `import` command in {aux_label}"));
                };
                if !is_allowed_aux_import(module) {
                    return Err(format!("disallowed `import {module}` in {aux_label}"));
                }
                if let Some(spec_suf) = module.strip_prefix("Specs.") {
                    if spec_suf == subject_suffix {
                        if !verify_imports_specs {
                            return Err(format!(
                                "{aux_label} imports `Specs.{subject_suffix}`, which is not imported by `Verify.{subject_suffix}`"
                            ));
                        }
                    } else {
                        push_unique(&mut out.imported_sibling_specs, spec_suf);
                    }
                } else if let Some(proof_suf) = module.strip_prefix("Proof.") {
                    push_unique(&mut out.imported_proof_suffixes, proof_suf);
                } else if let Some(assump_suf) = module.strip_prefix("Assumptions.") {
                    push_unique(&mut out.imported_assumptions_suffixes, assump_suf);
                }
            }
            "abbrev" => {
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok
                        && let Some(spec_cls) = canonical_spec_class_name(id)
                    {
                        return Err(format!(
                            "{aux_label} aliases `{spec_cls}` via `abbrev` (specification instances must reside in `Specs.{subject_suffix}`)"
                        ));
                    }
                }
            }
            "instance" => {
                let cmd_end = find_command_end(idx + 1);
                let cmd_slice = &tokens[idx..cmd_end];
                let mut header_end = cmd_slice.len();
                let mut h_depth = 0isize;
                for (h_pos, t) in cmd_slice.iter().enumerate() {
                    if h_depth == 0
                        && (*t == LeanToken::ColonEq
                            || matches!(t, LeanToken::Ident(w) if w == "where"))
                    {
                        header_end = h_pos;
                        break;
                    }
                    match t {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => h_depth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                            h_depth = (h_depth - 1).max(0);
                        }
                        _ => {}
                    }
                }
                let header = &cmd_slice[..header_end];
                if !header.contains(&LeanToken::Colon) {
                    return Err(format!(
                        "{aux_label} declares an `instance` without an explicit `: <ClassName>` type signature"
                    ));
                }
                for tok in cmd_slice {
                    if let LeanToken::Ident(id) = tok {
                        if let Some(short) = canonical_spec_class_name(id) {
                            return Err(format!(
                                "{aux_label} declares a `{short}` specification override instance (must reside in `Specs.{subject_suffix}`)"
                            ));
                        }
                        if is_refine_spec_helper_ident(id) {
                            return Err(format!(
                                "{aux_label} invokes `{id}` inside an `instance` declaration (must reside in `Specs.{subject_suffix}`)"
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// `[adv ep1-A3]` / `[adv ep1-B4]` Verify that a sibling `Specs/<Other>.lean` module
/// transitively imported by `Proof.*`, `Assumptions.*`, or `Specs.*` obeys the strict
/// `Specs` import allowlist (`is_allowed_specs_import`), introduces no `@[instance]` /
/// `attribute` / `local` / `scoped` / `abbrev` class-alias bypasses, requires every
/// `instance` to declare an explicit `<*ItemSpec> "<def_id>"` header with
/// `def_id != subject_def_path`, and returns any further `Specs.<Next>` suffixes it
/// imports for transitive worklist closure.
pub fn validate_sibling_specs_no_subject_override(
    specs_text: &str,
    sibling_suffix: &str,
    subject_def_path: &str,
) -> Result<Vec<String>, String> {
    let tokens = tokenize_lean_source(specs_text).map_err(|err| {
        format!("failed to tokenize sibling Specs.{sibling_suffix}: {err}")
    })?;
    if let Some(attr) = detect_instance_attribute(&tokens) {
        return Err(format!(
            "disallowed `@[{attr}]` attribute in imported sibling `Specs.{sibling_suffix}`"
        ));
    }
    let mut next_specs: Vec<String> = Vec::new();
    let find_command_end = |start: usize| -> usize {
        let mut depth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if depth == 0 && k > start && is_lean_command_start(&tokens[k]) {
                break;
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };
    let mut depth = 0isize;
    for idx in 0..tokens.len() {
        let cur_depth = depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            continue;
        }
        let LeanToken::Ident(kw) = &tokens[idx] else {
            continue;
        };
        match kw.as_str() {
            "axiom" | "opaque" | "macro" | "macro_rules" | "syntax" | "notation" | "elab"
            | "local" | "scoped" | "attribute" | "class" | "unsafe" | "partial" => {
                return Err(format!(
                    "disallowed top-level `{kw}` command in imported sibling `Specs.{sibling_suffix}`"
                ));
            }
            "def" | "theorem" | "lemma" => {
                if let Some(LeanToken::Ident(decl_name)) = tokens.get(idx + 1)
                    && (decl_name.starts_with("Obligations.")
                        || decl_name.starts_with("Mir.")
                        || decl_name.starts_with("Trusted."))
                {
                    return Err(format!(
                        "imported sibling `Specs.{sibling_suffix}` shadows reserved namespace declaration `{decl_name}`"
                    ));
                }
            }
            "structure" | "inductive" => {
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok
                        && (canonical_spec_class_name(id).is_some()
                            || is_refine_spec_helper_ident(id))
                    {
                        return Err(format!(
                            "imported sibling `Specs.{sibling_suffix}` references `{id}` inside `{kw}` declaration"
                        ));
                    }
                }
            }
            "import" => {
                let Some(LeanToken::Ident(module)) = tokens.get(idx + 1) else {
                    return Err(format!(
                        "malformed `import` command in imported sibling `Specs.{sibling_suffix}`"
                    ));
                };
                if !is_allowed_specs_import(module) {
                    return Err(format!(
                        "disallowed `import {module}` in imported sibling `Specs.{sibling_suffix}`"
                    ));
                }
                if let Some(spec_suf) = module.strip_prefix("Specs.")
                    && spec_suf != sibling_suffix
                    && !next_specs.iter().any(|s| s == spec_suf)
                {
                    next_specs.push(spec_suf.to_string());
                }
            }
            "abbrev" => {
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok
                        && let Some(spec_cls) = canonical_spec_class_name(id)
                    {
                        return Err(format!(
                            "imported sibling `Specs.{sibling_suffix}` aliases `{spec_cls}` via `abbrev`"
                        ));
                    }
                }
            }
            "instance" => {
                let cmd_end = find_command_end(idx + 1);
                let cmd_slice = &tokens[idx..cmd_end];
                let mut header_end = cmd_slice.len();
                let mut h_depth = 0isize;
                for (h_pos, t) in cmd_slice.iter().enumerate() {
                    if h_depth == 0
                        && (*t == LeanToken::ColonEq
                            || matches!(t, LeanToken::Ident(w) if w == "where"))
                    {
                        header_end = h_pos;
                        break;
                    }
                    match t {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => h_depth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                            h_depth = (h_depth - 1).max(0);
                        }
                        _ => {}
                    }
                }
                let header = &cmd_slice[..header_end];
                let mut matched_spec_cls = false;
                for (h_pos, tok) in header.iter().enumerate() {
                    if let LeanToken::Ident(id) = tok
                        && let Some(short) = canonical_spec_class_name(id)
                    {
                        matched_spec_cls = true;
                        match header.get(h_pos + 1) {
                            Some(LeanToken::StrLit(def_id)) if def_id != subject_def_path => {}
                            _ => {
                                return Err(format!(
                                    "imported sibling `Specs.{sibling_suffix}` declares `{short}` overriding subject `{subject_def_path}`"
                                ));
                            }
                        }
                    }
                }
                if !matched_spec_cls {
                    return Err(format!(
                        "imported sibling `Specs.{sibling_suffix}` declares non-`*ItemSpec` `instance` `{header:?}`"
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(next_specs)
}

/// `[adv ep1-A3]` / `[adv ep1-B4]` Callee and reference-MIR links declared in an authored
/// `anneal/proofs/Specs/<Item>.lean` module.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpecsModuleLinks {
    /// Distinct `defId` string literals bound on `*ItemSpec "<defId>"` instances in
    /// `Specs/<Item>.lean` (every instance must target the subject's own `def_path`).
    pub declared_spec_def_ids: Vec<String>,
    /// Distinct canonical `*ItemSpec` class names declared as `instance`s in `Specs/<Item>.lean`.
    pub declared_spec_classes: Vec<String>,
    /// Whether `Specs/<Item>.lean` declares a `ModularItemSpec` instance overriding
    /// `Obligations.<Item>.defaultModularSpec`.
    pub has_modular_spec_instance: bool,
    /// Whether `ModularItemSpec.envAssumed` in `Specs/<Item>.lean` delegates to (or
    /// conjoins) `Obligations.<Item>.defaultModularSpec.envAssumed` (as emitted by
    /// `render_specs_template`).
    pub delegates_to_default_modular_spec_env: bool,
    /// Sibling `<Callee>` module suffixes imported via `import Obligations.<Callee>`
    /// (`<Callee> != <Item>`).
    pub imported_obligation_suffixes: Vec<String>,
    /// `<Suffix>` module suffixes imported via `import Mir.<Suffix>`.
    pub imported_mir_suffixes: Vec<String>,
    /// Sibling `<Other>` module suffixes imported via `import Specs.<Other>` (`<Other> != <Item>`).
    pub imported_specs_suffixes: Vec<String>,
    /// Sibling `<Callee>` module suffixes referenced in `ModularItemSpec.envAssumed`
    /// via `Obligations.<Callee>.{defaultCallContract,ubExceptionClaim.callContract,
    /// claim.callContract,statefulClaim.callContract,totalClaim.callContract,
    /// modularClaim.callContract}.holdsOn`.
    pub referenced_modular_callee_suffixes: Vec<String>,
    /// Exact `(callee_suffix, contract_kind)` pairs referenced in `ModularItemSpec.envAssumed`.
    pub sibling_modular_contracts: Vec<(String, SiblingModularContractKind)>,
    /// Subject-local `externalCallContract_<Sidecar>` (or `defaultExternalCallContract`)
    /// identifiers referenced in `ModularItemSpec.envAssumed`.
    pub referenced_subject_external_contract_idents: Vec<String>,
    /// Whether `Specs/<Item>.lean` declares a `StatefulEquivItemSpec` instance.
    pub has_equiv_spec_instance: bool,
    /// `<Ref>` module suffix bound as `specBody := Mir.<Ref>.body` (or via
    /// `refineEquivSpec Mir.<Ref>.body`) on `StatefulEquivItemSpec`.
    pub equiv_spec_body_suffix: Option<String>,
}

/// `[adv ep1-A3]` / `[adv ep1-B4]` Scan an authored `anneal/proofs/Specs/<Item>.lean`
/// module with the comment- and string-aware Lean lexer, enforcing `is_allowed_specs_import`
/// on every `import`, rejecting `@[instance]` / `attribute` / `local` / `scoped` / `abbrev`
/// class-alias bypasses and disallowed top-level commands (`axiom`, `opaque`, `macro`,
/// `elab`, `notation`, `unsafe`, `partial`), requiring every `instance` to declare an
/// explicit `<*ItemSpec> "<defId>"` header, extracting `ModularItemSpec.envAssumed`
/// sibling/external contract links strictly from the `ModularItemSpec` instance (with exact
/// arity on `refineModularSpec` / `refineEquivSpec`), and extracting the exact
/// `Mir.<Ref>.body` `specBody` of any `StatefulEquivItemSpec` instance.
pub fn scan_specs_module(
    specs_text: &str,
    subject_suffix: &str,
) -> Result<SpecsModuleLinks, String> {
    let tokens = tokenize_lean_source(specs_text)
        .map_err(|err| format!("failed to tokenize Specs module for {subject_suffix}: {err}"))?;
    if let Some(attr) = detect_instance_attribute(&tokens) {
        return Err(format!(
            "disallowed `@[{attr}]` attribute in Specs module for {subject_suffix}"
        ));
    }
    let mut out = SpecsModuleLinks::default();
    let expected_ns = format!("Specs.{subject_suffix}");
    let mut ns_opens = 0usize;
    let mut ns_closes = 0usize;
    let mut local_env_assumed_def: Option<Vec<LeanToken>> = None;
    let push_unique = |vec: &mut Vec<String>, val: &str| {
        if !val.is_empty() && !vec.iter().any(|x| x == val) {
            vec.push(val.to_string());
        }
    };
    let find_command_end = |start: usize| -> usize {
        let mut depth = 0isize;
        let mut k = start;
        while k < tokens.len() {
            if depth == 0 && k > start && is_lean_command_start(&tokens[k]) {
                break;
            }
            match tokens[k] {
                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            k += 1;
        }
        k
    };
    fn extract_specs_sibling_contract(stem: &str) -> Option<(&str, SiblingModularContractKind)> {
        let rest = stem.strip_prefix("Obligations.")?;
        for (suffix, kind) in [
            (
                ".defaultCallContract",
                SiblingModularContractKind::DefaultCallContract,
            ),
            (
                ".ubExceptionClaim.callContract",
                SiblingModularContractKind::UbExceptionCallContract,
            ),
        ] {
            if let Some(callee) = rest.strip_suffix(suffix)
                && !callee.is_empty()
            {
                return Some((callee, kind));
            }
        }
        None
    }

    let mut raw_modular_stems: Vec<String> = Vec::new();
    let mut depth = 0isize;
    for idx in 0..tokens.len() {
        let cur_depth = depth;
        match tokens[idx] {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            continue;
        }
        let LeanToken::Ident(kw) = &tokens[idx] else {
            continue;
        };
        match kw.as_str() {
            "axiom" | "opaque" | "macro" | "macro_rules" | "syntax" | "notation" | "elab"
            | "local" | "scoped" | "attribute" | "class" | "unsafe" | "partial" => {
                return Err(format!(
                    "disallowed top-level `{kw}` command in Specs module for {subject_suffix}"
                ));
            }
            "structure" | "inductive" => {
                let cmd_end = find_command_end(idx + 1);
                for tok in &tokens[idx..cmd_end] {
                    if let LeanToken::Ident(id) = tok
                        && (canonical_spec_class_name(id).is_some()
                            || is_refine_spec_helper_ident(id))
                    {
                        return Err(format!(
                            "Specs.{subject_suffix} references `{id}` inside `{kw}` declaration"
                        ));
                    }
                }
            }
            "namespace" => match tokens.get(idx + 1) {
                Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_opens += 1,
                other => {
                    return Err(format!(
                        "unexpected `namespace {other:?}` in Specs module for {subject_suffix}"
                    ));
                }
            },
            "end" => match tokens.get(idx + 1) {
                Some(LeanToken::Ident(ns)) if ns == &expected_ns => ns_closes += 1,
                other if ns_opens > ns_closes => {
                    return Err(format!(
                        "unexpected `end {other:?}` in Specs module for {subject_suffix}"
                    ));
                }
                _ => {}
            },
            "import" => {
                let Some(LeanToken::Ident(module)) = tokens.get(idx + 1) else {
                    return Err(format!(
                        "malformed `import` command in Specs module for {subject_suffix}"
                    ));
                };
                if !is_allowed_specs_import(module) {
                    return Err(format!(
                        "disallowed `import {module}` in Specs module for {subject_suffix}"
                    ));
                }
                if let Some(ob_suf) = module.strip_prefix("Obligations.") {
                    if ob_suf != subject_suffix {
                        push_unique(&mut out.imported_obligation_suffixes, ob_suf);
                    }
                } else if let Some(mir_suf) = module.strip_prefix("Mir.") {
                    push_unique(&mut out.imported_mir_suffixes, mir_suf);
                } else if let Some(spec_suf) = module.strip_prefix("Specs.")
                    && spec_suf != subject_suffix
                {
                    push_unique(&mut out.imported_specs_suffixes, spec_suf);
                }
            }
            "def" | "abbrev" | "theorem" | "lemma" => {
                let cmd_end = find_command_end(idx + 1);
                if kw == "abbrev" {
                    for tok in &tokens[idx..cmd_end] {
                        if let LeanToken::Ident(id) = tok
                            && let Some(spec_cls) = canonical_spec_class_name(id)
                        {
                            return Err(format!(
                                "Specs.{subject_suffix} aliases `{spec_cls}` via `abbrev`"
                            ));
                        }
                    }
                }
                if let Some(LeanToken::Ident(decl_name)) = tokens.get(idx + 1) {
                    if decl_name.starts_with("Obligations.")
                        || decl_name.starts_with("Mir.")
                        || decl_name.starts_with("Trusted.")
                        || decl_name.starts_with("externalCallContract_")
                        || decl_name == "defaultModularSpec"
                        || decl_name == "defaultExternalCallContract"
                    {
                        return Err(format!(
                            "Specs.{subject_suffix} shadows reserved contract identifier `{decl_name}`"
                        ));
                    }
                    if (kw == "def" || kw == "abbrev") && decl_name == "envAssumed" {
                        if local_env_assumed_def.is_some() {
                            return Err(format!(
                                "duplicate `def envAssumed` in Specs.{subject_suffix}"
                            ));
                        }
                        let cmd_slice = &tokens[idx..cmd_end];
                        let mut sig_end = None;
                        let mut s_depth = 0isize;
                        for (s_pos, t) in cmd_slice.iter().enumerate().skip(2) {
                            if s_depth == 0 && *t == LeanToken::ColonEq {
                                sig_end = Some(s_pos);
                                break;
                            }
                            match t {
                                LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                    s_depth += 1;
                                }
                                LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                    s_depth = (s_depth - 1).max(0);
                                }
                                _ => {}
                            }
                        }
                        let Some(colon_eq_pos) = sig_end else {
                            return Err(format!(
                                "`def envAssumed` in Specs.{subject_suffix} lacks `:=`"
                            ));
                        };
                        let sig_tokens = &cmd_slice[2..colon_eq_pos];
                        let rhs_tokens = &cmd_slice[colon_eq_pos + 1..];
                        let mut binder_name: Option<String> = None;
                        if sig_tokens.first() == Some(&LeanToken::LParen)
                            && let Some(LeanToken::Ident(b)) = sig_tokens.get(1)
                        {
                            binder_name = Some(b.clone());
                        }
                        let mut synth = Vec::new();
                        if let Some(b) = binder_name {
                            synth.push(LeanToken::Ident("fun".to_string()));
                            synth.push(LeanToken::Ident(b));
                            synth.push(LeanToken::Ident("=>".to_string()));
                            synth.extend_from_slice(rhs_tokens);
                        } else {
                            synth.extend_from_slice(rhs_tokens);
                        }
                        local_env_assumed_def = Some(synth);
                    }
                }
            }
            "instance" => {
                if let Some(LeanToken::Ident(inst_name)) = tokens.get(idx + 1)
                    && (inst_name.starts_with("Obligations.")
                        || inst_name.starts_with("Mir.")
                        || inst_name.starts_with("Trusted.")
                        || inst_name == "defaultModularSpec")
                {
                    return Err(format!(
                        "Specs.{subject_suffix} shadows reserved instance identifier `{inst_name}`"
                    ));
                }
                let cmd_end = find_command_end(idx + 1);
                let cmd_slice = &tokens[idx..cmd_end];
                let mut header_end = cmd_slice.len();
                let mut h_depth = 0isize;
                for (h_pos, t) in cmd_slice.iter().enumerate() {
                    if h_depth == 0
                        && (*t == LeanToken::ColonEq
                            || matches!(t, LeanToken::Ident(w) if w == "where"))
                    {
                        header_end = h_pos;
                        break;
                    }
                    match t {
                        LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => h_depth += 1,
                        LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                            h_depth = (h_depth - 1).max(0);
                        }
                        _ => {}
                    }
                }
                let header = &cmd_slice[..header_end];
                let mut header_spec_classes: Vec<&'static str> = Vec::new();
                for (h_pos, tok) in header.iter().enumerate() {
                    if let LeanToken::Ident(id) = tok
                        && let Some(short) = canonical_spec_class_name(id)
                    {
                        let Some(LeanToken::StrLit(def_id)) = header.get(h_pos + 1) else {
                            return Err(format!(
                                "`{short}` instance in Specs.{subject_suffix} must have an explicit string-literal `defId` immediately after `{short}`"
                            ));
                        };
                        push_unique(&mut out.declared_spec_def_ids, def_id);
                        push_unique(&mut out.declared_spec_classes, short);
                        header_spec_classes.push(short);
                    }
                }
                if header_spec_classes.len() != 1 {
                    return Err(format!(
                        "every `instance` in Specs.{subject_suffix} must declare an explicit `<*ItemSpec> \"<defId>\"` header (found {:?})",
                        header_spec_classes
                    ));
                }
                let is_modular_inst = header_spec_classes[0] == "ModularItemSpec";
                let is_equiv_inst = header_spec_classes[0] == "StatefulEquivItemSpec";
                if is_modular_inst {
                    if out.has_modular_spec_instance {
                        return Err(format!(
                            "multiple `ModularItemSpec` instances in Specs module for {subject_suffix}"
                        ));
                    }
                    out.has_modular_spec_instance = true;
                    let parse_env_with_local_def =
                        |env_slice: &[LeanToken]| -> Result<Vec<String>, String> {
                            let stripped = strip_enclosing_parens(env_slice);
                            if matches!(stripped, [LeanToken::Ident(id)] if id == "envAssumed")
                                && let Some(ref synth) = local_env_assumed_def
                            {
                                return parse_env_assumed_holds_on_stems(synth);
                            }
                            parse_env_assumed_holds_on_stems(stripped)
                        };
                    let extract_where_or_brace_env =
                        |fields_slice: &[LeanToken]| -> Result<Vec<String>, String> {
                            if fields_slice
                                .iter()
                                .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"))
                            {
                                return Err(format!(
                                    "nested `where` clause is forbidden inside `ModularItemSpec` in Specs.{subject_suffix}"
                                ));
                            }
                            let mut extracted_stems: Option<Vec<String>> = None;
                            let mut f_idx = 0usize;
                            let mut f_depth = 0isize;
                            while f_idx < fields_slice.len() {
                                if f_depth == 0
                                    && matches!(
                                        fields_slice.get(f_idx),
                                        Some(LeanToken::Ident(fnm)) if fnm == "envAssumed"
                                    )
                                {
                                    if extracted_stems.is_some() {
                                        return Err(format!(
                                            "duplicate `envAssumed` field in `ModularItemSpec` of Specs.{subject_suffix}"
                                        ));
                                    }
                                    if fields_slice.get(f_idx + 1) != Some(&LeanToken::ColonEq) {
                                        return Err(format!(
                                            "`ModularItemSpec.envAssumed` in Specs.{subject_suffix} must use `envAssumed := ...` without binders"
                                        ));
                                    }
                                    let rhs_start = f_idx + 2;
                                    let mut r_idx = rhs_start;
                                    let mut r_depth = 0isize;
                                    while r_idx < fields_slice.len() {
                                        if r_depth == 0 {
                                            if matches!(
                                                fields_slice[r_idx],
                                                LeanToken::Comma
                                                    | LeanToken::Semicolon
                                                    | LeanToken::RBrace
                                            ) {
                                                break;
                                            }
                                            if r_idx > rhs_start
                                                && matches!(
                                                    fields_slice.get(r_idx),
                                                    Some(LeanToken::Ident(next_f))
                                                        if next_f == "pre"
                                                            || next_f == "post"
                                                            || next_f == "envAssumed"
                                                            || fields_slice.get(r_idx + 1)
                                                                == Some(&LeanToken::ColonEq)
                                                )
                                            {
                                                break;
                                            }
                                        }
                                        match fields_slice[r_idx] {
                                            LeanToken::LParen
                                            | LeanToken::LBrace
                                            | LeanToken::LBracket => r_depth += 1,
                                            LeanToken::RParen
                                            | LeanToken::RBrace
                                            | LeanToken::RBracket => {
                                                r_depth = (r_depth - 1).max(0);
                                            }
                                            _ => {}
                                        }
                                        r_idx += 1;
                                    }
                                    extracted_stems = Some(parse_env_with_local_def(
                                        &fields_slice[rhs_start..r_idx],
                                    )?);
                                    f_idx = r_idx;
                                    continue;
                                }
                                match fields_slice[f_idx] {
                                    LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                        f_depth += 1;
                                    }
                                    LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                        f_depth = (f_depth - 1).max(0);
                                    }
                                    _ => {}
                                }
                                f_idx += 1;
                            }
                            extracted_stems.ok_or_else(|| {
                                format!(
                                    "`ModularItemSpec` instance in Specs.{subject_suffix} omits `envAssumed :=`"
                                )
                            })
                        };

                    let stems = match cmd_slice.get(header_end) {
                        Some(LeanToken::Ident(w)) if w == "where" => {
                            extract_where_or_brace_env(&cmd_slice[header_end + 1..])?
                        }
                        Some(LeanToken::ColonEq) => {
                            let rhs = strip_enclosing_parens(&cmd_slice[header_end + 1..]);
                            if rhs.first() == Some(&LeanToken::LBrace)
                                && rhs.last() == Some(&LeanToken::RBrace)
                            {
                                extract_where_or_brace_env(&rhs[1..rhs.len() - 1])?
                            } else if let Some(LeanToken::Ident(fn_id)) = rhs.first()
                                && (fn_id == "refineModularSpec"
                                    || *fn_id == format!("Obligations.{subject_suffix}.refineModularSpec"))
                            {
                                let Some(args) = take_exact_n_balanced_args(&rhs[1..], 3) else {
                                    return Err(format!(
                                        "`refineModularSpec` in Specs.{subject_suffix} must take exactly 3 balanced arguments without trailing tokens"
                                    ));
                                };
                                parse_env_with_local_def(args[0])?
                            } else {
                                return Err(format!(
                                    "`ModularItemSpec` instance in Specs.{subject_suffix} must use `where`, `{{ ... }}`, or `refineModularSpec`"
                                ));
                            }
                        }
                        _ => {
                            return Err(format!(
                                "malformed `ModularItemSpec` instance in Specs.{subject_suffix}"
                            ));
                        }
                    };
                    for st in stems {
                        push_unique(&mut raw_modular_stems, &st);
                    }
                }
                if is_equiv_inst {
                    if out.has_equiv_spec_instance {
                        return Err(format!(
                            "multiple `StatefulEquivItemSpec` instances in Specs module for {subject_suffix}"
                        ));
                    }
                    out.has_equiv_spec_instance = true;
                    let extract_mir_ref_from_fields =
                        |fields_slice: &[LeanToken]| -> Result<String, String> {
                            if fields_slice
                                .iter()
                                .any(|t| matches!(t, LeanToken::Ident(w) if w == "where"))
                            {
                                return Err(format!(
                                    "nested `where` clause is forbidden inside `StatefulEquivItemSpec` in Specs.{subject_suffix}"
                                ));
                            }
                            let mut extracted_ref: Option<String> = None;
                            let mut f_idx = 0usize;
                            let mut f_depth = 0isize;
                            while f_idx < fields_slice.len() {
                                if f_depth == 0
                                    && matches!(
                                        fields_slice.get(f_idx),
                                        Some(LeanToken::Ident(fnm)) if fnm == "specBody"
                                    )
                                {
                                    if extracted_ref.is_some() {
                                        return Err(format!(
                                            "duplicate `specBody` field in `StatefulEquivItemSpec` of Specs.{subject_suffix}"
                                        ));
                                    }
                                    if fields_slice.get(f_idx + 1) != Some(&LeanToken::ColonEq) {
                                        return Err(format!(
                                            "`StatefulEquivItemSpec.specBody` in Specs.{subject_suffix} must use `specBody := Mir.<Ref>.body`"
                                        ));
                                    }
                                    let rhs_start = f_idx + 2;
                                    let mut r_idx = rhs_start;
                                    let mut r_depth = 0isize;
                                    while r_idx < fields_slice.len() {
                                        if r_depth == 0 {
                                            if matches!(
                                                fields_slice[r_idx],
                                                LeanToken::Comma
                                                    | LeanToken::Semicolon
                                                    | LeanToken::RBrace
                                            ) {
                                                break;
                                            }
                                            if r_idx > rhs_start
                                                && matches!(
                                                    fields_slice.get(r_idx),
                                                    Some(LeanToken::Ident(next_f))
                                                        if next_f == "pre"
                                                            || next_f == "post"
                                                            || next_f == "specBody"
                                                            || fields_slice.get(r_idx + 1)
                                                                == Some(&LeanToken::ColonEq)
                                                )
                                            {
                                                break;
                                            }
                                        }
                                        match fields_slice[r_idx] {
                                            LeanToken::LParen
                                            | LeanToken::LBrace
                                            | LeanToken::LBracket => r_depth += 1,
                                            LeanToken::RParen
                                            | LeanToken::RBrace
                                            | LeanToken::RBracket => {
                                                r_depth = (r_depth - 1).max(0);
                                            }
                                            _ => {}
                                        }
                                        r_idx += 1;
                                    }
                                    let spec_rhs =
                                        strip_enclosing_parens(&fields_slice[rhs_start..r_idx]);
                                    if let [LeanToken::Ident(mir_ref)] = spec_rhs
                                        && let Some(ref_suf) = mir_ref
                                            .strip_prefix("Mir.")
                                            .and_then(|s| s.strip_suffix(".body"))
                                            .filter(|s| !s.is_empty())
                                    {
                                        extracted_ref = Some(ref_suf.to_string());
                                        f_idx = r_idx;
                                        continue;
                                    }
                                    return Err(format!(
                                        "`StatefulEquivItemSpec.specBody` in Specs.{subject_suffix} must be an exact `Mir.<Ref>.body` reference, found `{spec_rhs:?}`"
                                    ));
                                }
                                match fields_slice[f_idx] {
                                    LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => {
                                        f_depth += 1;
                                    }
                                    LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                                        f_depth = (f_depth - 1).max(0);
                                    }
                                    _ => {}
                                }
                                f_idx += 1;
                            }
                            extracted_ref.ok_or_else(|| {
                                format!(
                                    "`StatefulEquivItemSpec` instance in Specs.{subject_suffix} omits `specBody := Mir.<Ref>.body`"
                                )
                            })
                        };

                    let ref_suffix = match cmd_slice.get(header_end) {
                        Some(LeanToken::Ident(w)) if w == "where" => {
                            extract_mir_ref_from_fields(&cmd_slice[header_end + 1..])?
                        }
                        Some(LeanToken::ColonEq) => {
                            let rhs = strip_enclosing_parens(&cmd_slice[header_end + 1..]);
                            if rhs.first() == Some(&LeanToken::LBrace)
                                && rhs.last() == Some(&LeanToken::RBrace)
                            {
                                extract_mir_ref_from_fields(&rhs[1..rhs.len() - 1])?
                            } else if let Some(LeanToken::Ident(fn_id)) = rhs.first()
                                && (fn_id == "refineEquivSpec"
                                    || *fn_id == format!("Obligations.{subject_suffix}.refineEquivSpec"))
                            {
                                let Some(args) = take_exact_n_balanced_args(&rhs[1..], 3) else {
                                    return Err(format!(
                                        "`refineEquivSpec` in Specs.{subject_suffix} must take exactly 3 balanced arguments (`Mir.<Ref>.body`, `pre`, `post`) without trailing tokens"
                                    ));
                                };
                                match strip_enclosing_parens(args[0]) {
                                    [LeanToken::Ident(mir_ref)] => mir_ref
                                        .strip_prefix("Mir.")
                                        .and_then(|s| s.strip_suffix(".body"))
                                        .filter(|s| !s.is_empty())
                                        .map(str::to_string)
                                        .ok_or_else(|| {
                                            format!(
                                                "`refineEquivSpec` in Specs.{subject_suffix} must take `Mir.<Ref>.body` as its first argument, found `{mir_ref}`"
                                            )
                                        })?,
                                    other => {
                                        return Err(format!(
                                            "`refineEquivSpec` in Specs.{subject_suffix} must take `Mir.<Ref>.body` as its first argument, found `{other:?}`"
                                        ));
                                    }
                                }
                            } else {
                                return Err(format!(
                                    "`StatefulEquivItemSpec` instance in Specs.{subject_suffix} must use `refineEquivSpec Mir.<Ref>.body ...` or `where specBody := Mir.<Ref>.body`"
                                ));
                            }
                        }
                        _ => {
                            return Err(format!(
                                "malformed `StatefulEquivItemSpec` instance in Specs.{subject_suffix}"
                            ));
                        }
                    };
                    out.equiv_spec_body_suffix = Some(ref_suffix);
                }
            }
            _ => {}
        }
    }

    if ns_opens != ns_closes || ns_opens > 1 {
        return Err(format!(
            "Specs module for {subject_suffix} has unbalanced or repeated `namespace {expected_ns}` blocks ({ns_opens} opens, {ns_closes} closes)"
        ));
    }

    let own_ob_prefix = format!("Obligations.{subject_suffix}.");
    let own_default_mod_env = format!("Obligations.{subject_suffix}.defaultModularSpec.envAssumed");
    for stem in raw_modular_stems {
        if stem == "defaultModularSpec.envAssumed" || stem == own_default_mod_env {
            out.delegates_to_default_modular_spec_env = true;
        } else if let Some((callee, kind)) = extract_specs_sibling_contract(&stem) {
            if callee == subject_suffix {
                return Err(format!(
                    "Specs.{subject_suffix} `ModularItemSpec.envAssumed` cannot self-assume `Obligations.{subject_suffix}`'s own callContract"
                ));
            }
            if !out.imported_obligation_suffixes.iter().any(|c| c == callee) {
                return Err(format!(
                    "Specs.{subject_suffix} references `{stem}.holdsOn` without `import Obligations.{callee}`"
                ));
            }
            push_unique(&mut out.referenced_modular_callee_suffixes, callee);
            if !out
                .sibling_modular_contracts
                .iter()
                .any(|(c, k)| c == callee && *k == kind)
            {
                out.sibling_modular_contracts
                    .push((callee.to_string(), kind));
            }
        } else if let Some(local_ext) = stem.strip_prefix(&own_ob_prefix)
            && !local_ext.is_empty()
            && !local_ext.contains('.')
        {
            push_unique(&mut out.referenced_subject_external_contract_idents, local_ext);
        } else if !stem.contains('.') {
            push_unique(&mut out.referenced_subject_external_contract_idents, &stem);
        } else {
            return Err(format!(
                "Specs.{subject_suffix} `ModularItemSpec.envAssumed` references unverified contract `{stem}`"
            ));
        }
    }
    if let Some(ref ref_suf) = out.equiv_spec_body_suffix
        && ref_suf != subject_suffix
        && !out.imported_mir_suffixes.iter().any(|m| m == ref_suf)
    {
        return Err(format!(
            "Specs.{subject_suffix} binds `specBody` to `Mir.{ref_suf}.body` without `import Mir.{ref_suf}`"
        ));
    }
    Ok(out)
}

/// `[adv ep1-A1]` / `[adv ep1-B3]` Parse the `def defaultCallees : List CapturedMir := ...`
/// table of a generated `Obligations/<Item>.lean` module using the comment- and
/// string-aware Lean lexer (`tokenize_lean_source`), returning the `Mir.<Callee>` module
/// suffixes it links into `s.memory.callees`.
///
/// Comments (`-- def defaultCallees ...`, `/- ... -/`, or comments inside a multi-line
/// `[Mir.A.body, -- note\n Mir.B.body]` list) are stripped by the lexer, while missing,
/// shadowed (`abbrev defaultCallees`), or duplicate `def defaultCallees` commands,
/// malformed type signatures, entries not of the exact form `Mir.<Suffix>.body`, or
/// trailing expressions (`[] ++ [...]`, `[Mir.A.body].drop 1`, etc.) fail closed with `Err`.
pub fn parse_obligations_default_callees(ob_text: &str) -> Result<Vec<String>, String> {
    let tokens = tokenize_lean_source(ob_text)
        .map_err(|err| format!("failed to tokenize Obligations module: {err}"))?;
    let mut def_positions = Vec::new();
    let mut depth = 0isize;
    for (idx, tok) in tokens.iter().enumerate() {
        let cur_depth = depth;
        match tok {
            LeanToken::LParen | LeanToken::LBrace | LeanToken::LBracket => depth += 1,
            LeanToken::RParen | LeanToken::RBrace | LeanToken::RBracket => {
                depth = (depth - 1).max(0);
            }
            _ => {}
        }
        if cur_depth != 0 {
            continue;
        }
        if let LeanToken::Ident(kw) = tok {
            if matches!(
                kw.as_str(),
                "abbrev"
                    | "theorem"
                    | "lemma"
                    | "axiom"
                    | "opaque"
                    | "instance"
            ) && matches!(tokens.get(idx + 1), Some(LeanToken::Ident(name)) if name == "defaultCallees")
            {
                return Err(format!(
                    "`defaultCallees` declared via `{kw}` instead of `def` in Obligations module"
                ));
            }
            if matches!(kw.as_str(), "private" | "protected" | "noncomputable")
                && matches!(tokens.get(idx + 2), Some(LeanToken::Ident(name)) if name == "defaultCallees")
            {
                return Err(format!(
                    "`{kw}` modifier on `defaultCallees` in Obligations module"
                ));
            }
            if kw == "def"
                && matches!(tokens.get(idx + 1), Some(LeanToken::Ident(name)) if name == "defaultCallees")
            {
                def_positions.push(idx);
            }
        }
    }
    let Some(&pos) = def_positions.first() else {
        return Err(
            "missing `def defaultCallees : List CapturedMir :=` table in Obligations module"
                .to_string(),
        );
    };
    if def_positions.len() > 1 {
        return Err("multiple `def defaultCallees` tables in Obligations module".to_string());
    }
    let header_ok = matches!(tokens.get(pos + 2), Some(LeanToken::Colon))
        && matches!(tokens.get(pos + 3), Some(LeanToken::Ident(s)) if s == "List" || s.ends_with(".List"))
        && matches!(tokens.get(pos + 4), Some(LeanToken::Ident(s)) if s == "CapturedMir" || s.ends_with(".CapturedMir"))
        && matches!(tokens.get(pos + 5), Some(LeanToken::ColonEq));
    if !header_ok {
        return Err(
            "malformed `def defaultCallees` header (expected `def defaultCallees : List CapturedMir :=`)"
                .to_string(),
        );
    }
    let ensure_no_trailing = |after_idx: usize| -> Result<(), String> {
        if let Some(next_tok) = tokens.get(after_idx)
            && !is_lean_command_start(next_tok)
        {
            return Err(format!(
                "unexpected trailing token `{next_tok:?}` after `defaultCallees` table"
            ));
        }
        Ok(())
    };
    let val_idx = pos + 6;
    match (tokens.get(val_idx), tokens.get(val_idx + 1)) {
        (Some(LeanToken::Ident(id)), _) if id == ".nil" || id == "List.nil" => {
            ensure_no_trailing(val_idx + 1)?;
            Ok(Vec::new())
        }
        (Some(LeanToken::Dot), Some(LeanToken::Ident(id))) if id == "nil" => {
            ensure_no_trailing(val_idx + 2)?;
            Ok(Vec::new())
        }
        (Some(LeanToken::LBracket), _) => {
            if matches!(tokens.get(val_idx + 1), Some(LeanToken::RBracket)) {
                ensure_no_trailing(val_idx + 2)?;
                return Ok(Vec::new());
            }
            let mut out = Vec::new();
            let mut cur = val_idx + 1;
            loop {
                let Some(LeanToken::Ident(entry)) = tokens.get(cur) else {
                    return Err(format!(
                        "unrecognized `defaultCallees` entry `{:?}`",
                        tokens.get(cur)
                    ));
                };
                let suffix = entry
                    .strip_prefix("Mir.")
                    .and_then(|e| e.strip_suffix(".body"))
                    .filter(|s| {
                        !s.is_empty()
                            && s.chars()
                                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
                    })
                    .ok_or_else(|| format!("unrecognized `defaultCallees` entry `{entry}`"))?;
                out.push(suffix.to_string());
                cur += 1;
                match tokens.get(cur) {
                    Some(LeanToken::Comma) => {
                        cur += 1;
                    }
                    Some(LeanToken::RBracket) => break,
                    other => {
                        return Err(format!(
                            "unterminated or malformed `defaultCallees` list near `{other:?}`"
                        ));
                    }
                }
            }
            ensure_no_trailing(cur + 1)?;
            Ok(out)
        }
        (other, _) => Err(format!("unrecognized `defaultCallees` table `{other:?}`")),
    }
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
    /// Fail-closed downgrade (`UNKNOWN(UNMAPPED_FAULT_SITE)`) when one or
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
    /// `"UNKNOWN(UNMAPPED_FAULT_SITE)"`).
    pub const fn status_code(&self) -> &'static str {
        match self {
            CoverageVerdict::Verified => "VERIFIED",
            CoverageVerdict::UnknownUnmappedFaultSite { .. } => "UNKNOWN(UNMAPPED_FAULT_SITE)",
        }
    }
}

/// Reconcile an independent `census` against the obligation generator's
/// `discharged` fault-site set and `registry`, matching
/// `reconcileFaultCoverageWithRegistry` in `FaultSiteCensus.lean`.
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

/// `[adv A2]` / `[adv B3]` Per-item coverage input for multi-item / multi-callee
/// reconciliation: a subject function together with the inline callee bodies that its
/// verification harness can install as `activeCallee`. `FaultSite` coordinates
/// `(block_idx, stmt_idx, fault_class)` are body-relative, so every item is reconciled
/// against its *own* `discharged` list (`reconcileCoverageBatch` in
/// `FaultSiteCensus.lean`), and a discharged `(0, 0, cls)` in a caller can never
/// mask an unmapped `(0, 0, cls)` in a callee.
///
/// `[adv B3]`: an item carries its *body*, never a caller-supplied census. The
/// `[adv A2]` shape accepted an arbitrary `census: Vec<FaultSite>`, so an empty or stale
/// census reconciled `Verified` for a body full of fault sites; the reconciler now always
/// recomputes `census_mir_fault_sites(&body)` itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemCoverageInput {
    /// Canonical item `DefPath`; must be unique within a batch and equal `body.def_path`.
    pub def_path: String,
    /// The item's MIR body; its census is recomputed by the reconciler.
    pub body: ProtoMirBody,
    /// Discharged `FaultSite` obligations emitted for this item's body.
    pub discharged: Vec<FaultSite>,
}

impl ItemCoverageInput {
    /// Build an item labeled with the body's own `def_path`.
    pub fn from_body(body: ProtoMirBody, discharged: Vec<FaultSite>) -> Self {
        Self {
            def_path: body.def_path.clone(),
            body,
            discharged,
        }
    }

    /// `[adv B3]` Build an item from a captured `Mir/<Item>.lean` module. The module must
    /// pass the strict module grammar (`check_strict_mir_module_grammar`), and the item is
    /// labeled with the parsed `defPath`; any `CensusScanError` keeps the module out of
    /// the batch (fail-closed).
    pub fn from_lean_module(
        lean_src: &str,
        discharged: Vec<FaultSite>,
    ) -> Result<Self, CensusScanError> {
        let tokens = tokenize_lean_source(lean_src)?;
        check_strict_mir_module_grammar(&tokens)?;
        let body = parse_lean_captured_mir_def(lean_src, "body")?;
        Ok(Self::from_body(body, discharged))
    }
}

/// `[adv B3]` Callee classification for a multi-item batch.
///
/// `inline_callees` must be exactly the `callees` list handed to
/// `initMachineStateWithCallees`: those bodies can become `activeCallee`, so each needs
/// its own batch item. `external_callees` are modeled as external calls (answered by an
/// `#[external_spec]` contract) whose bodies never execute inside the machine.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CalleeClosure {
    /// `DefPath`s of bodies installed as inline callees.
    pub inline_callees: Vec<String>,
    /// `DefPath`s of callees modeled as external calls.
    pub external_callees: Vec<String>,
    /// `[adv ep1-B2]` Permit `Call` / `TailCall` terminators whose `func` is not a
    /// constant function item. `resolveCallTarget` resolves such calls at run time
    /// through `s.memory.fnPtrs` (which a stateful precondition or an external
    /// call's answer memory can populate with arbitrary targets) or through the
    /// function-item *type* of a local, neither of which this syntactic census
    /// can bound, so an unresolved indirect call is an unclosed callee. Only items
    /// whose own body is assumed rather than verified (a subject's own
    /// `#[spec(trusted)]` contract or a UB-exception claim) set this; it is never
    /// implied by the presence of unrelated inline or external callees.
    pub allow_unresolved_indirect_calls: bool,
}

/// `[adv B3]` / `[adv ep1-A3]` Sorted, duplicate-free direct callee `DefPath`s of the
/// `Call` / `TailCall` terminators in `body` (constant function-item operands only; for a
/// converging `core::intrinsics::const_eval_select` call, resolves its 3rd runtime-target
/// argument `args[2]` when constant).
pub fn direct_callee_def_paths(body: &ProtoMirBody) -> Vec<String> {
    let mut out = BTreeSet::new();
    for bb in &body.basic_blocks {
        match &bb.terminator.kind {
            ProtoTerminatorKind::Call {
                func, args, target, ..
            } => {
                if let Some(path) = func.extract_callee_def_path() {
                    if target.is_some()
                        && path == "core::intrinsics::const_eval_select"
                        && args.len() == 3
                    {
                        if let Some(rt) = args.get(2).and_then(|op| op.extract_callee_def_path()) {
                            out.insert(rt.to_string());
                        } else {
                            out.insert(path.to_string());
                        }
                    } else {
                        out.insert(path.to_string());
                    }
                }
            }
            ProtoTerminatorKind::TailCall { func, .. } => {
                if let Some(path) = func.extract_callee_def_path() {
                    out.insert(path.to_string());
                }
            }
            _ => continue,
        }
    }
    out.into_iter().collect()
}

/// `[adv A3]` / `[adv A4]` Sorted, duplicate-free `DefPath`s of function items or
/// non-capturing closures reified into function pointers via
/// `Rvalue::Cast(CastKind::PointerCoercion("ReifyFnPointer*" | "ClosureFnPointer*"), op)`
/// inside `body`. In `Trusted.MirSemantics.evalReifyFnPointer` (`Places.lean:6643`),
/// reifying a `RigidTy.fnDef` constant registers `defPath` in `s.memory.fnPtrs`, allowing
/// subsequent indirect `Call` / `TailCall` terminators to invoke `defPath`.
pub fn reified_fn_def_paths(body: &ProtoMirBody) -> Vec<String> {
    let mut out = BTreeSet::new();
    for bb in &body.basic_blocks {
        for stmt in &bb.statements {
            if let ProtoStatementKind::Assign(
                _,
                ProtoRvalue::Cast(ProtoCastKind::PointerCoercion(coercion), op),
            ) = &stmt.kind
            {
                let is_fn_ptr_coercion = coercion == "ReifyFnPointer"
                    || coercion.starts_with("ReifyFnPointer(")
                    || coercion == "ClosureFnPointer"
                    || coercion.starts_with("ClosureFnPointer(");
                if is_fn_ptr_coercion {
                    if let Some(path) = op.extract_callee_def_path() {
                        out.insert(path.to_string());
                    }
                }
            }
        }
    }
    out.into_iter().collect()
}

/// `[adv B4]` Callees that `evalTerminator` models natively on a converging `Call`
/// (`isDirectExactDivTarget` plus every non-`const_eval_select` arm of
/// `classifyRustIntrinsic?`). Pinned to the trusted Lean source by
/// `test_b4_native_callee_lists_match_trusted_semantics`.
pub const NATIVE_CONVERGING_CALL_CALLEES: [&str; 25] = [
    "core::intrinsics::exact_div",
    "core::intrinsics::ub_checks",
    "core::intrinsics::arith_offset",
    "core::intrinsics::ctlz",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::cttz",
    "core::intrinsics::cttz_nonzero",
    "core::intrinsics::ctpop",
    "core::intrinsics::bswap",
    "core::intrinsics::bitreverse",
    "core::intrinsics::wrapping_add",
    "core::intrinsics::wrapping_sub",
    "core::intrinsics::wrapping_mul",
    "core::intrinsics::saturating_add",
    "core::intrinsics::saturating_sub",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::unchecked_shr",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_sub",
    "core::intrinsics::unchecked_mul",
    "core::intrinsics::unchecked_div",
    "core::intrinsics::unchecked_rem",
    "core::intrinsics::three_way_compare",
    "core::intrinsics::size_of_val",
    "core::intrinsics::align_of_val",
];

/// `[adv B4]` Callees that `evalTerminator` models natively on a diverging `Call`
/// (`isUnreachableCallTarget`, `isAbortingPanicDefPath`, `isUnwindingPanicDefPath`).
/// Pinned to the trusted Lean source by
/// `test_b4_native_callee_lists_match_trusted_semantics`.
pub const NATIVE_DIVERGING_CALL_CALLEES: [&str; 39] = [
    "core::hint::unreachable_unchecked",
    "std::hint::unreachable_unchecked",
    "core::intrinsics::unreachable",
    "core::panicking::panic_nounwind",
    "core::panicking::panic_nounwind_fmt",
    "core::panicking::panic_nounwind_fmt::panic_impl",
    "core::panicking::panic_nounwind_nobacktrace",
    "core::panicking::panic_in_cleanup",
    "core::panicking::panic_cannot_unwind",
    "core::panicking::panic_misaligned_pointer_dereference",
    "core::panicking::panic_null_pointer_dereference",
    "core::panicking::panic_invalid_enum_construction",
    "core::intrinsics::abort",
    "core::panicking::panic",
    "core::panicking::panic_fmt",
    "core::panicking::panic_fmt::panic_impl",
    "core::panicking::const_panic_fmt",
    "core::panicking::assert_failed",
    "core::panicking::assert_failed_inner",
    "core::panicking::assert_matches_failed",
    "core::slice::index::slice_index_fail",
    "core::panicking::panic_bounds_check",
    "core::panicking::panic_explicit",
    "core::panicking::panic_display",
    "core::panicking::panic_str_2015",
    "core::panicking::unreachable_display",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::result::unwrap_failed",
    "core::panicking::panic_const::panic_const_add_overflow",
    "core::panicking::panic_const::panic_const_sub_overflow",
    "core::panicking::panic_const::panic_const_mul_overflow",
    "core::panicking::panic_const::panic_const_div_overflow",
    "core::panicking::panic_const::panic_const_rem_overflow",
    "core::panicking::panic_const::panic_const_neg_overflow",
    "core::panicking::panic_const::panic_const_shr_overflow",
    "core::panicking::panic_const::panic_const_shl_overflow",
    "core::panicking::panic_const::panic_const_div_by_zero",
    "core::panicking::panic_const::panic_const_rem_by_zero",
];

/// `[adv A3]` True iff `def_path` is natively modeled inline by `evalTerminator` on a
/// **converging** `TerminatorKind::Call` (`target = Some(targetBb)`,
/// `Terminators.lean:3119-3166`) without falling through to `MirStepNode.extCall`:
/// `core::intrinsics::exact_div` (`isDirectExactDivTarget`) and all 24 non-`const_eval_select`
/// `RustIntrinsicKind` intrinsics in `classifyRustIntrinsic?` (both the 12 faulting and
/// the 12 zero-fault intrinsics).
///
/// Note: `core::intrinsics::const_eval_select` dispatches to its 3rd argument (`called_at_rt`),
/// so it is only closed when that 3rd argument is a direct constant function item that is
/// itself classified.
pub fn is_natively_modeled_converging_call_callee(def_path: &str) -> bool {
    NATIVE_CONVERGING_CALL_CALLEES.contains(&def_path)
}

/// `[adv A3]` True iff `def_path` is natively modeled inline by `evalTerminator` on a
/// **diverging** `TerminatorKind::Call` (`target = None`, `Terminators.lean:3227-3239`)
/// without falling through to `MirStepNode.extCall`: `isUnreachableCallTarget`,
/// `isAbortingPanicDefPath`, and `isUnwindingPanicDefPath`.
pub fn is_natively_modeled_diverging_call_callee(def_path: &str) -> bool {
    NATIVE_DIVERGING_CALL_CALLEES.contains(&def_path)
}

/// `[adv A2]` Fail-closed verdict for a multi-item / multi-callee verification batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultiItemCoverageVerdict {
    /// The batch is non-empty, every item has a unique `def_path` equal to its body's,
    /// every item's recomputed census reconciled to `CoverageVerdict::Verified` against
    /// its own `discharged` list, and the `CalleeClosure` is satisfied.
    Verified,
    /// Fail-closed downgrade when any of the `Verified` conditions fails.
    UnknownUnmappedFaultSite {
        /// Per-item failures `(def_path, verdict)` for items that did not reconcile.
        failed_items: Vec<(String, CoverageVerdict)>,
        /// Aggregate human-readable diagnostic reasons across the batch.
        unsupported_reasons: Vec<String>,
    },
}

impl MultiItemCoverageVerdict {
    /// True iff every item in the batch reconciled to `Verified`.
    pub const fn is_verified(&self) -> bool {
        matches!(self, MultiItemCoverageVerdict::Verified)
    }

    /// Canonical machine-readable status code (`"VERIFIED"` vs.
    /// `"UNKNOWN(UNMAPPED_FAULT_SITE)"`).
    pub const fn status_code(&self) -> &'static str {
        match self {
            MultiItemCoverageVerdict::Verified => "VERIFIED",
            MultiItemCoverageVerdict::UnknownUnmappedFaultSite { .. } => {
                "UNKNOWN(UNMAPPED_FAULT_SITE)"
            }
        }
    }

    /// Diagnostic reasons (empty for `Verified`).
    pub fn reasons(&self) -> &[String] {
        match self {
            MultiItemCoverageVerdict::Verified => &[],
            MultiItemCoverageVerdict::UnknownUnmappedFaultSite {
                unsupported_reasons,
                ..
            } => unsupported_reasons,
        }
    }
}

/// `[adv A2]` / `[adv B3]` / `[adv A3]` Reconcile a multi-item / multi-callee
/// verification batch under `registry`. Returns `Verified` only when:
/// 1. the batch is non-empty and every `def_path` is unique and equals `body.def_path`;
/// 2. every item's census, recomputed from its body, reconciles against that item's own
///    `discharged` list (`reconcileCoverageBatch` in Lean);
/// 3. every `closure.inline_callees` entry is unique and has a batch item;
/// 4. no `DefPath` is declared both inline and external (and `external_callees` is duplicate-free);
/// 5. every `Call` / `TailCall` callee of every item is in `closure.inline_callees`,
///    in `closure.external_callees`, or natively modeled inline for that exact terminator
///    shape (`is_natively_modeled_converging_call_callee` for converging `Call`,
///    `is_natively_modeled_diverging_call_callee` for diverging `Call`, and none for
///    `TailCall`, plus runtime-target closure for `core::intrinsics::const_eval_select`); and
/// 6. every function item reified into a function pointer via `ReifyFnPointer`
///    (`reified_fn_def_paths`) is in `closure.inline_callees` or `closure.external_callees`.
pub fn reconcile_multi_item_coverage(
    items: &[ItemCoverageInput],
    closure: &CalleeClosure,
    registry: &PropertyRegistry,
) -> MultiItemCoverageVerdict {
    if items.is_empty() {
        return MultiItemCoverageVerdict::UnknownUnmappedFaultSite {
            failed_items: Vec::new(),
            unsupported_reasons: vec![
                "multi-item coverage batch is empty (at least one subject item required)"
                    .to_string(),
            ],
        };
    }

    let mut seen_paths: BTreeSet<&str> = BTreeSet::new();
    let mut failed_items = Vec::new();
    let mut unsupported_reasons = Vec::new();

    for item in items {
        if !seen_paths.insert(item.def_path.as_str()) {
            unsupported_reasons.push(format!(
                "duplicate item def_path `{}` in multi-item coverage batch",
                item.def_path
            ));
        }
        if item.def_path != item.body.def_path {
            unsupported_reasons.push(format!(
                "item label `{}` does not match its body def_path `{}`",
                item.def_path, item.body.def_path
            ));
        }
        let census = census_mir_fault_sites(&item.body);
        let verdict = reconcile_obligation_coverage(&census, &item.discharged, registry);
        if let CoverageVerdict::UnknownUnmappedFaultSite {
            unsupported_reasons: ref item_reasons,
            ..
        } = verdict
        {
            for r in item_reasons {
                unsupported_reasons.push(format!("[{}] {r}", item.def_path));
            }
            failed_items.push((item.def_path.clone(), verdict));
        }
    }

    let mut external: BTreeSet<&str> = BTreeSet::new();
    for ext in &closure.external_callees {
        if !external.insert(ext.as_str()) {
            unsupported_reasons.push(format!(
                "duplicate external callee `{ext}` in CalleeClosure"
            ));
        }
    }
    let mut inline_set: BTreeSet<&str> = BTreeSet::new();
    for callee in &closure.inline_callees {
        if !inline_set.insert(callee.as_str()) {
            unsupported_reasons.push(format!(
                "duplicate inline callee `{callee}` in CalleeClosure"
            ));
        }
        if !seen_paths.contains(callee.as_str()) {
            unsupported_reasons.push(format!(
                "inline callee `{callee}` has no batch item: its body can become \
                 `activeCallee` but its census was never reconciled"
            ));
        }
        if external.contains(callee.as_str()) {
            unsupported_reasons.push(format!(
                "callee `{callee}` is declared both inline and external"
            ));
        }
    }
    for item in items {
        if external.contains(item.def_path.as_str()) {
            unsupported_reasons.push(format!(
                "batch item `{}` is declared in `closure.external_callees` (a verified batch item cannot be treated as an uninterpreted external callee)",
                item.def_path
            ));
        }
        if !item.body.has_no_param_call_const() {
            unsupported_reasons.push(format!(
                "[{}] body contains a `Call` or `TailCall` terminator whose `func` operand is a `RigidTy.param`-typed constant (`bodyHasNoParamCallConst` violated)",
                item.def_path
            ));
        }
        if !item.body.cfg_targets_in_bounds() {
            unsupported_reasons.push(format!(
                "[{}] body violates `cfgTargetsInBounds` (empty `basicBlocks` or out-of-bounds terminator/unwind target)",
                item.def_path
            ));
        }
        for (bb_idx, bb) in item.body.basic_blocks.iter().enumerate() {
            match &bb.terminator.kind {
                ProtoTerminatorKind::Call {
                    func,
                    args,
                    target: Some(_),
                    ..
                } => {
                    if let Some(callee) = func.extract_callee_def_path() {
                        if callee == "core::intrinsics::const_eval_select" {
                            let rt_ok = if args.len() == 3 {
                                match args.get(2) {
                                    Some(rt_op) => match rt_op.extract_callee_def_path() {
                                        Some(rt) => {
                                            inline_set.contains(rt)
                                                || external.contains(rt)
                                                || is_natively_modeled_converging_call_callee(rt)
                                                || is_natively_modeled_diverging_call_callee(rt)
                                        }
                                        None => closure.allow_unresolved_indirect_calls,
                                    },
                                    None => false,
                                }
                            } else {
                                false
                            };
                            if !rt_ok {
                                unsupported_reasons.push(format!(
                                    "[{}] bb{bb_idx} `const_eval_select` runtime target is not classified in CalleeClosure",
                                    item.def_path
                                ));
                            }
                        } else {
                            let classified = inline_set.contains(callee)
                                || external.contains(callee)
                                || is_natively_modeled_converging_call_callee(callee);
                            if !classified {
                                unsupported_reasons.push(format!(
                                    "[{}] direct callee `{callee}` is neither a declared inline callee, \
                                     a declared external callee, nor a natively modeled converging-call intrinsic",
                                    item.def_path
                                ));
                            }
                        }
                    } else if !closure.allow_unresolved_indirect_calls {
                        unsupported_reasons.push(format!(
                            "[{}] bb{bb_idx} indirect call through a non-constant `func` operand has an unresolved target (runtime `fnPtrs` / fn-item-typed local) and CalleeClosure does not permit unresolved indirect calls",
                            item.def_path
                        ));
                    }
                }
                ProtoTerminatorKind::Call {
                    func, target: None, ..
                } => {
                    if let Some(callee) = func.extract_callee_def_path() {
                        let classified = inline_set.contains(callee)
                            || external.contains(callee)
                            || is_natively_modeled_diverging_call_callee(callee);
                        if !classified {
                            unsupported_reasons.push(format!(
                                "[{}] direct callee `{callee}` is neither a declared inline callee, \
                                 a declared external callee, nor a natively modeled diverging-call target",
                                item.def_path
                            ));
                        }
                    } else if !closure.allow_unresolved_indirect_calls {
                        unsupported_reasons.push(format!(
                            "[{}] bb{bb_idx} indirect diverging call through a non-constant `func` operand has an unresolved target (runtime `fnPtrs` / fn-item-typed local) and CalleeClosure does not permit unresolved indirect calls",
                            item.def_path
                        ));
                    }
                }
                ProtoTerminatorKind::TailCall { func, .. } => {
                    if let Some(callee) = func.extract_callee_def_path() {
                        let classified = inline_set.contains(callee) || external.contains(callee);
                        if !classified {
                            unsupported_reasons.push(format!(
                                "[{}] direct tail-call callee `{callee}` is neither a declared inline callee \
                                 nor a declared external callee (`evalTailCallTerminator` does not model intrinsics inline)",
                                item.def_path
                            ));
                        }
                    } else if !closure.allow_unresolved_indirect_calls {
                        unsupported_reasons.push(format!(
                            "[{}] bb{bb_idx} indirect tail call through a non-constant `func` operand has an unresolved target (runtime `fnPtrs` / fn-item-typed local) and CalleeClosure does not permit unresolved indirect calls",
                            item.def_path
                        ));
                    }
                }
                _ => {}
            }
        }
        for reified in reified_fn_def_paths(&item.body) {
            if !inline_set.contains(reified.as_str()) && !external.contains(reified.as_str()) {
                unsupported_reasons.push(format!(
                    "[{}] reified function pointer target `{reified}` (`ReifyFnPointer`) is neither \
                     a declared inline callee nor a declared external callee",
                    item.def_path
                ));
            }
        }
    }

    if failed_items.is_empty() && unsupported_reasons.is_empty() {
        MultiItemCoverageVerdict::Verified
    } else {
        MultiItemCoverageVerdict::UnknownUnmappedFaultSite {
            failed_items,
            unsupported_reasons,
        }
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
    /// `theory/Anneal/FaultSiteCensus.lean`.
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

fn place_has_deref(place: &ProtoPlace) -> bool {
    place.projection.contains(&ProtoProjectionElem::Deref)
}

fn operand_has_deref(op: &ProtoOperand) -> bool {
    matches!(op, ProtoOperand::Copy(p) | ProtoOperand::Move(p) if place_has_deref(p))
}

fn rvalue_has_deref(rv: &ProtoRvalue) -> bool {
    match rv {
        ProtoRvalue::Use(op)
        | ProtoRvalue::Repeat(op, _)
        | ProtoRvalue::Cast(_, op)
        | ProtoRvalue::UnaryOp(_, op)
        | ProtoRvalue::ShallowInitBox(op)
        | ProtoRvalue::WrapUnsafeBinder(op) => operand_has_deref(op),
        ProtoRvalue::BinaryOp(_, lhs, rhs) => operand_has_deref(lhs) || operand_has_deref(rhs),
        ProtoRvalue::Aggregate(_, ops) => ops.iter().any(operand_has_deref),
        ProtoRvalue::Ref { place, .. }
        | ProtoRvalue::RawPtr { place, .. }
        | ProtoRvalue::Len(place)
        | ProtoRvalue::Discriminant(place)
        | ProtoRvalue::CopyForDeref(place) => place_has_deref(place),
        ProtoRvalue::ThreadLocalRef(_) | ProtoRvalue::NullaryOp(_) => false,
    }
}

fn stmt_has_deref(kind: &ProtoStatementKind) -> bool {
    match kind {
        ProtoStatementKind::Assign(dst, rv) => place_has_deref(dst) || rvalue_has_deref(rv),
        ProtoStatementKind::SetDiscriminant(p, _)
        | ProtoStatementKind::Deinit(p)
        | ProtoStatementKind::Retag(p)
        | ProtoStatementKind::PlaceMention(p) => place_has_deref(p),
        ProtoStatementKind::Intrinsic(ProtoIntrinsic::Assume(op)) => operand_has_deref(op),
        ProtoStatementKind::Intrinsic(ProtoIntrinsic::CopyNonOverlapping { .. }) => true,
        _ => false,
    }
}

fn strip_deref_projections(op: &ProtoOperand) -> ProtoOperand {
    let strip = |p: &ProtoPlace| ProtoPlace {
        local_: p.local_,
        projection: p
            .projection
            .iter()
            .filter(|e| **e != ProtoProjectionElem::Deref)
            .cloned()
            .collect(),
    };
    match op {
        ProtoOperand::Copy(p) => ProtoOperand::Copy(strip(p)),
        ProtoOperand::Move(p) => ProtoOperand::Move(strip(p)),
        ProtoOperand::Constant(_) => op.clone(),
    }
}

/// `[adv B1]` Independent mock obligation emitter driving the false-proof probes.
///
/// The `[adv A0]` probes reconciled the census against *itself minus a hard-coded
/// subset*, which only exercised set difference. This walker instead models how
/// an obligation generator explores a body: it follows CFG edges from `bb0`
/// (unreachable or un-followed blocks emit nothing), treats a block with an edge to
/// an earlier-or-same block as a loop latch, and — when `mutation` is set — injects
/// one realistic emitter bug:
/// - `CallArgBlindProbe`: call arguments are treated as opaque by-value operands, so
///   their dereference projections are never checked;
/// - `SwitchBreakStripProbe`: `SwitchInt` exploration drops the `otherwise` edge;
/// - `LoopUpdateOverflowProbe`: overflow obligations are skipped in latch blocks;
/// - `DerefAliasProbe`: dereference/alignment/aliasing obligations are skipped at
///   statements that dereference a pointer.
///
/// The unmutated emitter must reconcile `Verified` against the census, and each
/// mutant must be rejected with exactly the sites pinned by the Lean witnesses.
pub fn mock_emit_obligations(
    body: &ProtoMirBody,
    mutation: Option<FaultMutationProbe>,
) -> Vec<FaultSite> {
    let num_blocks = body.basic_blocks.len();
    let mut reachable = vec![false; num_blocks];
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        if b >= num_blocks || reachable[b] {
            continue;
        }
        reachable[b] = true;
        let kind = &body.basic_blocks[b].terminator.kind;
        match (kind, mutation) {
            (
                ProtoTerminatorKind::SwitchInt(_, targets),
                Some(FaultMutationProbe::SwitchBreakStripProbe),
            ) => work.extend(targets.branches.iter().map(|&(_, t)| t)),
            _ => work.extend(terminator_targets(kind)),
        }
    }

    let mut out = Vec::new();
    for (b, bb) in body.basic_blocks.iter().enumerate() {
        if !reachable[b] {
            continue;
        }
        let is_latch = terminator_targets(&bb.terminator.kind)
            .iter()
            .any(|&t| t <= b);
        for (i, stmt) in bb.statements.iter().enumerate() {
            let mut classes = census_stmt_fault_classes(&stmt.kind);
            match mutation {
                Some(FaultMutationProbe::LoopUpdateOverflowProbe) if is_latch => {
                    classes.retain(|c| *c != MirFaultClass::ArithOverflow);
                }
                Some(FaultMutationProbe::DerefAliasProbe) if stmt_has_deref(&stmt.kind) => {
                    classes.retain(|c| {
                        !matches!(
                            c,
                            MirFaultClass::PtrDerefInvalid
                                | MirFaultClass::PtrAlignMismatch
                                | MirFaultClass::TreeBorrowsViolation
                        )
                    });
                }
                _ => {}
            }
            out.extend(classes.into_iter().map(|c| FaultSite::new(b, i, c)));
        }
        let term_idx = bb.statements.len();
        let classes = match (&bb.terminator.kind, mutation) {
            (
                ProtoTerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                },
                Some(FaultMutationProbe::CallArgBlindProbe),
            ) => census_terminator_fault_classes(
                num_blocks,
                &ProtoTerminatorKind::Call {
                    func: func.clone(),
                    args: args.iter().map(strip_deref_projections).collect(),
                    destination: destination.clone(),
                    target: *target,
                    unwind: *unwind,
                },
            ),
            (kind, _) => census_terminator_fault_classes(num_blocks, kind),
        };
        out.extend(classes.into_iter().map(|c| FaultSite::new(b, term_idx, c)));
    }
    out
}

/// Package a probe scenario: `(body, baseline emitter obligations, mutant emitter
/// obligations, expected missing sites)`.
fn emitter_scenario(
    body: ProtoMirBody,
    probe: FaultMutationProbe,
    expected_missing: Vec<FaultSite>,
) -> (ProtoMirBody, Vec<FaultSite>, Vec<FaultSite>, Vec<FaultSite>) {
    let baseline = mock_emit_obligations(&body, None);
    let mutant = mock_emit_obligations(&body, Some(probe));
    (body, baseline, mutant, expected_missing)
}

/// Construct the canonical `ProtoMirBody`, baseline emitter obligations, mutant
/// emitter obligations, and expected missing sites for `probe`, matching the Lean 4
/// witness definitions in `theory/Anneal/FaultSiteCensus.lean` 1-to-1.
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
            let expected_missing = vec![
                FaultSite::new(0, 0, MirFaultClass::PtrDerefInvalid),
                FaultSite::new(0, 0, MirFaultClass::PtrAlignMismatch),
            ];
            emitter_scenario(body, probe, expected_missing)
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
            let expected_missing = vec![
                FaultSite::new(2, 0, MirFaultClass::ArithOverflow),
                FaultSite::new(2, 0, MirFaultClass::DivRemByZero),
                FaultSite::new(2, 0, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(2, 0, MirFaultClass::UninitRead),
                FaultSite::new(2, 0, MirFaultClass::StorageLiveProtected),
                FaultSite::new(2, 1, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(2, 1, MirFaultClass::UninitRead),
                FaultSite::new(2, 1, MirFaultClass::CallAbiMismatch),
            ];
            emitter_scenario(body, probe, expected_missing)
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
                        statements: vec![
                            ProtoStatement {
                                kind: ProtoStatementKind::Assign(
                                    ProtoPlace::local(1),
                                    ProtoRvalue::BinaryOp(
                                        ProtoBinOp::AddUnchecked,
                                        ProtoOperand::Copy(ProtoPlace::local(1)),
                                        ProtoOperand::const_u32(1),
                                    ),
                                ),
                                span: String::from("proto.rs:32:9"),
                            },
                            ProtoStatement {
                                kind: ProtoStatementKind::Assign(
                                    ProtoPlace::local(0),
                                    ProtoRvalue::BinaryOp(
                                        ProtoBinOp::Add,
                                        ProtoOperand::Copy(ProtoPlace::local(0)),
                                        ProtoOperand::Copy(ProtoPlace::local(1)),
                                    ),
                                ),
                                span: String::from("proto.rs:33:9"),
                            },
                        ],
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Goto(1),
                            span: String::from("proto.rs:33:20"),
                        },
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator {
                            kind: ProtoTerminatorKind::Return,
                            span: String::from("proto.rs:34:5"),
                        },
                        is_cleanup: false,
                    },
                ],
            };
            let expected_missing = vec![FaultSite::new(2, 0, MirFaultClass::ArithOverflow)];
            emitter_scenario(body, probe, expected_missing)
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
            let expected_missing = vec![
                FaultSite::new(0, 0, MirFaultClass::PtrDerefInvalid),
                FaultSite::new(0, 0, MirFaultClass::PtrAlignMismatch),
                FaultSite::new(0, 0, MirFaultClass::TreeBorrowsViolation),
            ];
            emitter_scenario(body, probe, expected_missing)
        }
    }
}

/// Execute a single `FaultMutationProbe` against `PropertyRegistry::all_verified()`.
pub fn run_false_proof_probe(probe: FaultMutationProbe) -> ProbeExecutionReport {
    let registry = PropertyRegistry::all_verified();
    let (body, baseline_discharged, mutant_discharged, expected_missing_sites) =
        build_probe_scenario(probe);
    let census = census_mir_fault_sites(&body);
    let baseline_verdict = reconcile_obligation_coverage(&census, &baseline_discharged, &registry);
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
    let (body, _baseline, _mutant, _expected_missing) =
        build_probe_scenario(FaultMutationProbe::DerefAliasProbe);
    let census = census_mir_fault_sites(&body);
    let registry = PropertyRegistry::all_verified().with_status(
        MirFaultClass::TreeBorrowsViolation,
        PropertyStatus::UnemittedGap,
    );
    reconcile_obligation_coverage(&census, &census, &registry)
}

// ============================================================================
// 8. Unit, Mutation Probe, Lexer Trap, and Cross-Language Lean Parity Tests
// ============================================================================

/// Per-item fault-site census and obligation coverage receipt written to
/// `.anneal/generated/FaultCensus/<Item>.json` during scaffolding and
/// assembly refresh.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultCensusReceipt {
    pub def_path: String,
    pub mir_module_sha256: String,
    pub census_sites: Vec<FaultSite>,
    pub discharged_sites: Vec<FaultSite>,
    pub callee_closure: CalleeClosure,
    pub reconciliation_verdict: String,
    pub is_verified: bool,
    pub reasons: Vec<String>,
}

fn json_escape_str(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for ch in raw.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

fn render_fault_site_json(site: &FaultSite) -> String {
    format!(
        "{{\"block_idx\": {}, \"stmt_idx\": {}, \"fault_class\": \"{}\"}}",
        site.block_idx,
        site.stmt_idx,
        site.fault_class.as_str()
    )
}

impl FaultCensusReceipt {
    /// Render deterministic pretty JSON for `.anneal/generated/FaultCensus/<Item>.json`.
    pub fn to_json_string(&self) -> String {
        let census_entries: Vec<String> = self
            .census_sites
            .iter()
            .map(|s| format!("    {}", render_fault_site_json(s)))
            .collect();
        let discharged_entries: Vec<String> = self
            .discharged_sites
            .iter()
            .map(|s| format!("    {}", render_fault_site_json(s)))
            .collect();
        let inline_entries: Vec<String> = self
            .callee_closure
            .inline_callees
            .iter()
            .map(|c| format!("      \"{}\"", json_escape_str(c)))
            .collect();
        let external_entries: Vec<String> = self
            .callee_closure
            .external_callees
            .iter()
            .map(|c| format!("      \"{}\"", json_escape_str(c)))
            .collect();
        let reason_entries: Vec<String> = self
            .reasons
            .iter()
            .map(|r| format!("    \"{}\"", json_escape_str(r)))
            .collect();

        let fmt_array = |entries: &[String], indent: &str| -> String {
            if entries.is_empty() {
                "[]".to_string()
            } else {
                format!("[\n{}\n{indent}]", entries.join(",\n"))
            }
        };

        format!(
            "{{\n  \"def_path\": \"{}\",\n  \"mir_module_sha256\": \"{}\",\n  \"census_sites\": {},\n  \"discharged_sites\": {},\n  \"callee_closure\": {{\n    \"inline_callees\": {},\n    \"external_callees\": {},\n    \"allow_unresolved_indirect_calls\": {}\n  }},\n  \"reconciliation_verdict\": \"{}\",\n  \"is_verified\": {},\n  \"reasons\": {}\n}}\n",
            json_escape_str(&self.def_path),
            json_escape_str(&self.mir_module_sha256),
            fmt_array(&census_entries, "  "),
            fmt_array(&discharged_entries, "  "),
            fmt_array(&inline_entries, "    "),
            fmt_array(&external_entries, "    "),
            self.callee_closure.allow_unresolved_indirect_calls,
            json_escape_str(&self.reconciliation_verdict),
            self.is_verified,
            fmt_array(&reason_entries, "  "),
        )
    }

    /// Concise summary lines suitable for `Obligations/<Item>.lean` docstrings and
    /// `agent-context` reporting.
    pub fn summary_lines(&self) -> Vec<String> {
        let mut class_counts: BTreeMap<MirFaultClass, usize> = BTreeMap::new();
        for site in &self.census_sites {
            *class_counts.entry(site.fault_class).or_insert(0) += 1;
        }
        let breakdown = if class_counts.is_empty() {
            "none".to_string()
        } else {
            class_counts
                .into_iter()
                .map(|(cls, cnt)| format!("{}:{cnt}", cls.as_str()))
                .collect::<Vec<_>>()
                .join(", ")
        };
        vec![
            format!(
                "Fault-site census: {} site(s) ({}); obligation discharged: {} site(s); verdict: {}",
                self.census_sites.len(),
                breakdown,
                self.discharged_sites.len(),
                self.reconciliation_verdict
            ),
            format!(
                "Callee closure: {} inline ({}), {} external ({}){}",
                self.callee_closure.inline_callees.len(),
                if self.callee_closure.inline_callees.is_empty() {
                    "none".to_string()
                } else {
                    self.callee_closure.inline_callees.join(", ")
                },
                self.callee_closure.external_callees.len(),
                if self.callee_closure.external_callees.is_empty() {
                    "none".to_string()
                } else {
                    self.callee_closure.external_callees.join(", ")
                },
                if self.callee_closure.allow_unresolved_indirect_calls {
                    "; unresolved indirect calls permitted (assumed subject)"
                } else {
                    ""
                },
            ),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::lean_emit::{
        emit_mir_lean_module, IrAbiPassMode, IrAlign, IrArgAbi, IrBackendRepr, IrCallConv,
        IrContractRole, IrFieldsShape, IrFnAbi, IrLayoutTable, IrLocalDecl, IrMirPhaseTag,
        IrPrimitiveKind, IrRigidTy, IrScalarLayout, IrSize, IrTy, IrTypeLayout, IrUintTy,
        IrVariantsShape, IrWrappingRange,
    };

    const LEAN_PROTOTYPE_SRC: &str =
        include_str!("../../../theory/Anneal/FaultSiteCensus.lean");

    /// Parse a Lean `def <name> : List FaultSite := [ (b, s, .cls), ... ]` list
    /// directly from `FaultSiteCensus.lean` so the cross-language test
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
        // `[adv B1]`: wrapping/flagged/masked operators never fault in
        // `evalScalarBinOp` (`censusBinOpFaultClasses_exact` in Lean).
        for op in [
            ProtoBinOp::Add,
            ProtoBinOp::Sub,
            ProtoBinOp::Mul,
            ProtoBinOp::AddWithOverflow,
            ProtoBinOp::SubWithOverflow,
            ProtoBinOp::MulWithOverflow,
            ProtoBinOp::Shl,
            ProtoBinOp::Shr,
            ProtoBinOp::BitXor,
            ProtoBinOp::BitAnd,
            ProtoBinOp::BitOr,
            ProtoBinOp::Eq,
            ProtoBinOp::Lt,
            ProtoBinOp::Le,
            ProtoBinOp::Ne,
            ProtoBinOp::Ge,
            ProtoBinOp::Gt,
            ProtoBinOp::Cmp,
        ] {
            assert_eq!(
                census_bin_op_fault_classes(op),
                Vec::<MirFaultClass>::new(),
                "{op:?}"
            );
        }
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::AddUnchecked),
            vec![MirFaultClass::ArithOverflow]
        );
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::Div),
            vec![MirFaultClass::ArithOverflow, MirFaultClass::DivRemByZero]
        );
        assert_eq!(
            census_bin_op_fault_classes(ProtoBinOp::ShlUnchecked),
            vec![MirFaultClass::ShiftOverflow]
        );
        assert_eq!(
            census_un_op_fault_classes(ProtoUnOp::Neg),
            Vec::<MirFaultClass>::new()
        );
        // Non-dereferencing borrows only fault on a dead/missing root or index local.
        assert_eq!(
            census_place_ref_fault_classes(&ProtoPlace::local(1)),
            vec![MirFaultClass::UninitRead]
        );
        // `validateLoadedValue` makes `Use(Copy(p))` fault on invalid `bool` scalars.
        assert!(
            census_rvalue_fault_classes(&ProtoRvalue::Use(ProtoOperand::Copy(ProtoPlace::local(
                1
            ))))
            .contains(&MirFaultClass::ScalarNicheInvalid)
        );
        // `Assert` unwind edges: only `Unreachable`/`Continue` can fault.
        for (unwind, expected) in [
            (
                ProtoUnwindAction::Unreachable,
                Some(MirFaultClass::UnreachableTerminator),
            ),
            (
                ProtoUnwindAction::Continue,
                Some(MirFaultClass::CallAbiMismatch),
            ),
            (ProtoUnwindAction::Cleanup(0), None),
            (ProtoUnwindAction::Terminate, None),
        ] {
            let classes = census_terminator_fault_classes(
                1,
                &ProtoTerminatorKind::Assert {
                    cond: ProtoOperand::const_u32(1),
                    expected: true,
                    target: 0,
                    unwind,
                },
            );
            let mut want = vec![MirFaultClass::ScalarNicheInvalid];
            want.extend(expected);
            assert_eq!(dedup_fault_classes(want), classes, "{unwind:?}");
        }
        // `std::intrinsics::*` is not classified by `classifyRustIntrinsic?`.
        assert_eq!(
            census_callee_def_path_fault_classes("std::intrinsics::unchecked_add"),
            Vec::<MirFaultClass>::new()
        );
        assert_eq!(
            census_callee_def_path_fault_classes("core::intrinsics::unchecked_add"),
            vec![MirFaultClass::ArithOverflow]
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
                "UNKNOWN(UNMAPPED_FAULT_SITE)"
            );
        }
    }

    #[test]
    fn test_property_registry_unemitted_and_unsupported_fail_closed() {
        let verdict = run_property_registry_unemitted_probe();
        assert_eq!(verdict.status_code(), "UNKNOWN(UNMAPPED_FAULT_SITE)");
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
        let (call_body, _, _, _) = build_probe_scenario(FaultMutationProbe::CallArgBlindProbe);
        let call_census = census_mir_fault_sites(&call_body);
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

        let expected = vec![
            FaultSite::new(0, 0, MirFaultClass::StorageLiveProtected),
            FaultSite::new(0, 1, MirFaultClass::UnreachableTerminator),
        ];
        // The lexer neutralizes every trap for named-definition extraction ...
        let sites = census_lean_mir_def(tricky_lean, "body").expect("scan tricky Lean module");
        assert_eq!(sites, expected);
        // ... while the strict emitter-module grammar (`[adv B1]`) fails closed on the
        // brace-carrying interpolated/raw strings in the skipped `helperInterp` /
        // `helperRawStr` definitions, and accepts the same module (comments, char
        // literals, guillemets) once those non-emitter helpers are removed.
        assert!(matches!(
            census_lean_mir_module(tricky_lean),
            Err(CensusScanError::MalformedCapturedMirSyntax(_))
        ));
        let without_interp: String = tricky_lean
            .lines()
            .filter(|line| {
                !line.starts_with("def helperInterp") && !line.starts_with("def helperRawStr")
            })
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            census_lean_mir_module(&without_interp).expect("strict tricky module"),
            expected
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
            "UNKNOWN(UNMAPPED_FAULT_SITE)"
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

    /// Deterministic xorshift64* generator for the differential fuzz tests.
    struct FuzzRng(u64);

    impl FuzzRng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next_u64() % (n as u64)) as usize
        }

        fn chance(&mut self, percent: u64) -> bool {
            self.next_u64() % 100 < percent
        }

        fn pick<'b>(&mut self, items: &'b [&'b str]) -> &'b str {
            items[self.below(items.len())]
        }

        /// Pick a trap string without line breaks, for identifier-like payloads
        /// (variant names, thread-local paths) that the emitter echoes unsanitized
        /// into its `-- bbN:` summary comment lines.
        fn pick_line<'b>(&mut self, items: &'b [&'b str]) -> &'b str {
            loop {
                let s = self.pick(items);
                if !s.contains('\n') && !s.contains('\r') {
                    return s;
                }
            }
        }
    }

    /// Strings that stress the Lean lexer when the emitter embeds them in string
    /// literals (`span`, `defPath`, `debugName`, inline-asm templates) or in `--`
    /// comment lines (`comment`).
    const FUZZ_TRAP_STRINGS: [&str; 18] = [
        "src/lib.rs:1:1: 1:9",
        "quote \" inside",
        "back\\slash \\u0061 \\x41",
        "brace { open",
        "brace } close {x}",
        "line -- comment",
        "block /- open",
        "block -/ close",
        "guillemet « and »",
        "tab\tand\nnewline\r",
        "def body : CapturedMir := { basicBlocks := List.nil }",
        "s!\"{interp}\" m!\"{x}\"",
        "r#\"raw\"#",
        "char 'x' '\\''",
        "unicode λ → ∀ ✓",
        "ctrl \u{1}\u{7f}",
        "{closure#0}",
        "",
    ];

    const FUZZ_CALLEES: [&str; 14] = [
        "core::intrinsics::unreachable",
        "core::hint::unreachable_unchecked",
        "std::hint::unreachable_unchecked",
        "core::intrinsics::exact_div",
        "std::intrinsics::exact_div",
        "core::intrinsics::unchecked_add",
        "std::intrinsics::unchecked_add",
        "core::intrinsics::unchecked_shl",
        "core::intrinsics::ctlz_nonzero",
        "core::intrinsics::arith_offset",
        "core::intrinsics::const_eval_select",
        "core::intrinsics::size_of_val",
        "crate::helper::{closure#0}",
        "crate::quote\"d::fn",
    ];

    const FUZZ_COERCIONS: [&str; 7] = [
        "Unsize",
        "ArrayToPointer",
        "MutToConstPointer",
        "ReifyFnPointer",
        "ClosureFnPointer(Safe)",
        "UnsafeFnPointer",
        "weird{\"tag",
    ];

    fn fuzz_ty(rng: &mut FuzzRng, depth: usize) -> anneal_rustc_capture::lean_emit::IrTy {
        anneal_rustc_capture::lean_emit::IrTy {
            kind: fuzz_rigid_ty(rng, depth),
            layout_idx: rng.below(2),
        }
    }

    fn fuzz_rigid_ty(
        rng: &mut FuzzRng,
        depth: usize,
    ) -> anneal_rustc_capture::lean_emit::IrRigidTy {
        use anneal_rustc_capture::lean_emit::{IrIntTy, IrMutability, IrRigidTy, IrUintTy};
        let leaf = depth == 0 || rng.chance(50);
        match if leaf { rng.below(5) } else { 5 + rng.below(6) } {
            0 => IrRigidTy::Bool,
            1 => IrRigidTy::Uint(IrUintTy::U32),
            2 => IrRigidTy::Int(IrIntTy::I8),
            3 => IrRigidTy::Str,
            4 => IrRigidTy::Param {
                index: 0,
                name: rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
            },
            5 => IrRigidTy::Tuple(vec![fuzz_rigid_ty(rng, depth - 1)]),
            6 => IrRigidTy::Array(Box::new(fuzz_rigid_ty(rng, depth - 1)), rng.below(4) as u64),
            7 => IrRigidTy::Ref(IrMutability::Mut, Box::new(fuzz_rigid_ty(rng, depth - 1))),
            8 => IrRigidTy::RawPtr(IrMutability::Not, Box::new(fuzz_rigid_ty(rng, depth - 1))),
            9 => IrRigidTy::Adt(
                rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
                vec![fuzz_rigid_ty(rng, depth - 1)],
            ),
            _ => IrRigidTy::Other(rng.pick(&FUZZ_TRAP_STRINGS).to_string()),
        }
    }

    fn fuzz_place(rng: &mut FuzzRng) -> anneal_rustc_capture::lean_emit::IrPlace {
        use anneal_rustc_capture::lean_emit::{IrPlace, IrProjectionElem};
        let mut projection = Vec::new();
        for _ in 0..rng.below(4) {
            projection.push(match rng.below(8) {
                0 => IrProjectionElem::Deref,
                1 => IrProjectionElem::Field(rng.below(3), fuzz_ty(rng, 1)),
                2 => IrProjectionElem::Index(rng.below(4)),
                3 => IrProjectionElem::ConstantIndex {
                    offset: rng.below(4) as u64,
                    min_length: rng.below(5) as u64,
                    from_end: rng.chance(50),
                },
                4 => IrProjectionElem::Subslice {
                    from_idx: rng.below(3) as u64,
                    to_idx: rng.below(3) as u64,
                    from_end: rng.chance(50),
                },
                5 => IrProjectionElem::Downcast(
                    if rng.chance(50) {
                        Some(rng.pick_line(&FUZZ_TRAP_STRINGS).to_string())
                    } else {
                        None
                    },
                    rng.below(3),
                ),
                6 => IrProjectionElem::OpaqueCast(fuzz_ty(rng, 1)),
                _ => IrProjectionElem::UnwrapUnsafeBinder(fuzz_ty(rng, 1)),
            });
        }
        IrPlace {
            local_: rng.below(5),
            projection,
        }
    }

    fn fuzz_operand(rng: &mut FuzzRng) -> anneal_rustc_capture::lean_emit::IrOperand {
        use anneal_rustc_capture::lean_emit::{
            IrConstOperand, IrConstScalar, IrConstValue, IrOperand, IrProvenancePtr, IrRigidTy,
            IrScalarInt, IrTy,
        };
        match rng.below(4) {
            0 => IrOperand::Copy(fuzz_place(rng)),
            1 => IrOperand::Move(fuzz_place(rng)),
            2 => IrOperand::Constant(IrConstOperand {
                ty: IrTy {
                    kind: IrRigidTy::FnDef(
                        rng.pick(&FUZZ_CALLEES).to_string(),
                        vec![fuzz_rigid_ty(rng, 1)],
                    ),
                    layout_idx: 0,
                },
                val: IrConstValue::ZeroSized,
            }),
            _ => {
                let scalar = if rng.chance(70) {
                    IrConstScalar::Int(IrScalarInt {
                        bits: rng.next_u64() as u128,
                        size_bytes: [1, 4, 8][rng.below(3)],
                    })
                } else {
                    IrConstScalar::Ptr(
                        IrProvenancePtr {
                            alloc_id: rng.below(3) as u64,
                            offset_bytes: rng.below(9) as u64,
                        },
                        8,
                    )
                };
                let val = match rng.below(5) {
                    0 => IrConstValue::ZeroSized,
                    1 => IrConstValue::Scalar(scalar),
                    2 => IrConstValue::Slice {
                        data: scalar,
                        meta: rng.below(4) as u64,
                    },
                    3 => IrConstValue::Indirect {
                        alloc_id: rng.below(3) as u64,
                        offset_bytes: rng.below(9) as u64,
                    },
                    _ => IrConstValue::Unevaluated(rng.pick(&FUZZ_CALLEES).to_string()),
                };
                IrOperand::Constant(IrConstOperand {
                    ty: fuzz_ty(rng, 2),
                    val,
                })
            }
        }
    }

    fn fuzz_rvalue(rng: &mut FuzzRng) -> anneal_rustc_capture::lean_emit::IrRvalue {
        use anneal_rustc_capture::lean_emit::{
            IrAggregateKind, IrBinOp, IrBorrowKind, IrCastKind, IrMutability, IrNullOp, IrRvalue,
            IrUnOp,
        };
        const BIN_OPS: [IrBinOp; 26] = [
            IrBinOp::Add,
            IrBinOp::AddUnchecked,
            IrBinOp::AddWithOverflow,
            IrBinOp::Sub,
            IrBinOp::SubUnchecked,
            IrBinOp::SubWithOverflow,
            IrBinOp::Mul,
            IrBinOp::MulUnchecked,
            IrBinOp::MulWithOverflow,
            IrBinOp::Div,
            IrBinOp::Rem,
            IrBinOp::BitXor,
            IrBinOp::BitAnd,
            IrBinOp::BitOr,
            IrBinOp::Shl,
            IrBinOp::ShlUnchecked,
            IrBinOp::Shr,
            IrBinOp::ShrUnchecked,
            IrBinOp::Eq,
            IrBinOp::Lt,
            IrBinOp::Le,
            IrBinOp::Ne,
            IrBinOp::Ge,
            IrBinOp::Gt,
            IrBinOp::Cmp,
            IrBinOp::Offset,
        ];
        match rng.below(15) {
            0 => IrRvalue::Use(fuzz_operand(rng)),
            1 => IrRvalue::Repeat(fuzz_operand(rng), rng.below(4) as u64),
            2 => IrRvalue::Ref(
                if rng.chance(50) {
                    IrBorrowKind::Shared
                } else {
                    IrBorrowKind::Mut {
                        allow_two_phase: rng.chance(50),
                    }
                },
                fuzz_place(rng),
            ),
            3 => IrRvalue::ThreadLocalRef(rng.pick_line(&FUZZ_TRAP_STRINGS).to_string()),
            4 => IrRvalue::RawPtr(
                if rng.chance(50) {
                    IrMutability::Not
                } else {
                    IrMutability::Mut
                },
                fuzz_place(rng),
            ),
            5 => IrRvalue::Len(fuzz_place(rng)),
            6 => {
                let kind = match rng.below(11) {
                    0 => IrCastKind::PointerExposeProvenance,
                    1 => IrCastKind::PointerWithExposedProvenance,
                    2 => IrCastKind::PointerCoercion(rng.pick(&FUZZ_COERCIONS).to_string()),
                    3 => IrCastKind::IntToInt,
                    4 => IrCastKind::FloatToInt,
                    5 => IrCastKind::FloatToFloat,
                    6 => IrCastKind::IntToFloat,
                    7 => IrCastKind::PtrToPtr,
                    8 => IrCastKind::FnPtrToPtr,
                    9 => IrCastKind::Transmute,
                    _ => IrCastKind::Subtype,
                };
                IrRvalue::Cast(kind, fuzz_operand(rng), fuzz_ty(rng, 1))
            }
            7 => IrRvalue::BinaryOp(
                BIN_OPS[rng.below(BIN_OPS.len())],
                fuzz_operand(rng),
                fuzz_operand(rng),
            ),
            8 => IrRvalue::NullaryOp(
                match rng.below(5) {
                    0 => IrNullOp::SizeOf,
                    1 => IrNullOp::AlignOf,
                    2 => IrNullOp::OffsetOf(vec![(0, rng.below(3))]),
                    3 => IrNullOp::UbChecks,
                    _ => IrNullOp::ContractChecks,
                },
                fuzz_ty(rng, 1),
            ),
            9 => IrRvalue::UnaryOp(
                [IrUnOp::Not, IrUnOp::Neg, IrUnOp::PtrMetadata][rng.below(3)],
                fuzz_operand(rng),
            ),
            10 => IrRvalue::Discriminant(fuzz_place(rng)),
            11 => {
                let kind = match rng.below(6) {
                    0 => IrAggregateKind::Array(fuzz_ty(rng, 1)),
                    1 => IrAggregateKind::Tuple,
                    2 => IrAggregateKind::Adt(
                        rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
                        rng.below(3),
                        if rng.chance(50) {
                            Some(rng.below(3))
                        } else {
                            None
                        },
                    ),
                    3 => IrAggregateKind::Closure(rng.pick(&FUZZ_TRAP_STRINGS).to_string()),
                    4 => IrAggregateKind::Coroutine(rng.pick(&FUZZ_TRAP_STRINGS).to_string()),
                    _ => IrAggregateKind::RawPtr(
                        fuzz_ty(rng, 1),
                        if rng.chance(50) {
                            IrMutability::Not
                        } else {
                            IrMutability::Mut
                        },
                    ),
                };
                let ops = (0..rng.below(3)).map(|_| fuzz_operand(rng)).collect();
                IrRvalue::Aggregate(kind, ops)
            }
            12 => IrRvalue::ShallowInitBox(fuzz_operand(rng), fuzz_ty(rng, 1)),
            13 => IrRvalue::CopyForDeref(fuzz_place(rng)),
            _ => IrRvalue::WrapUnsafeBinder(fuzz_operand(rng), fuzz_ty(rng, 1)),
        }
    }

    fn fuzz_unwind(
        rng: &mut FuzzRng,
        num_blocks: usize,
    ) -> anneal_rustc_capture::lean_emit::IrUnwindAction {
        use anneal_rustc_capture::lean_emit::IrUnwindAction;
        match rng.below(4) {
            0 => IrUnwindAction::Cleanup(rng.below(num_blocks + 1)),
            1 => IrUnwindAction::Unreachable,
            2 => IrUnwindAction::Terminate,
            _ => IrUnwindAction::Continue,
        }
    }

    fn fuzz_captured_mir(rng: &mut FuzzRng) -> IrCapturedMir {
        use anneal_rustc_capture::lean_emit::{
            IrNonDivergingIntrinsic, IrRetagKind, IrStatement, IrStatementKind, IrSwitchTargets,
            IrTerminator, IrTerminatorKind,
        };
        let num_blocks = 1 + rng.below(4);
        // Targets may point one past the last block to exercise `targetOob`.
        let target = |rng: &mut FuzzRng| rng.below(num_blocks + 1);
        let mut basic_blocks = Vec::new();
        for _ in 0..num_blocks {
            let mut statements = Vec::new();
            for _ in 0..rng.below(4) {
                let kind = match rng.below(14) {
                    0 | 1 => IrStatementKind::Assign(fuzz_place(rng), fuzz_rvalue(rng)),
                    2 => IrStatementKind::SetDiscriminant(fuzz_place(rng), rng.below(3)),
                    3 => IrStatementKind::Deinit(fuzz_place(rng)),
                    4 => IrStatementKind::StorageLive(rng.below(5)),
                    5 => IrStatementKind::StorageDead(rng.below(5)),
                    6 => IrStatementKind::Retag(
                        match rng.below(4) {
                            0 => IrRetagKind::FnEntry,
                            1 => IrRetagKind::TwoPhase,
                            2 => IrRetagKind::Raw,
                            _ => IrRetagKind::Default,
                        },
                        fuzz_place(rng),
                    ),
                    7 => IrStatementKind::PlaceMention(fuzz_place(rng)),
                    8 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(fuzz_operand(
                        rng,
                    ))),
                    9 => IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
                        src: fuzz_operand(rng),
                        dst: fuzz_operand(rng),
                        count: fuzz_operand(rng),
                    }),
                    10 => IrStatementKind::Coverage,
                    11 => IrStatementKind::ConstEvalCounter,
                    12 => IrStatementKind::BackwardIncompatibleDropHint(fuzz_place(rng)),
                    _ => IrStatementKind::Nop,
                };
                statements.push(IrStatement {
                    kind,
                    span: rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
                    comment: if rng.chance(50) {
                        Some(rng.pick(&FUZZ_TRAP_STRINGS).to_string())
                    } else {
                        None
                    },
                });
            }
            let kind = match rng.below(11) {
                0 => IrTerminatorKind::Goto(target(rng)),
                1 => IrTerminatorKind::SwitchInt(
                    fuzz_operand(rng),
                    IrSwitchTargets {
                        branches: (0..rng.below(3))
                            .map(|v| (v as u128, target(rng)))
                            .collect(),
                        otherwise: target(rng),
                    },
                ),
                2 => IrTerminatorKind::UnwindResume,
                3 => IrTerminatorKind::UnwindTerminate,
                4 => IrTerminatorKind::Return,
                5 => IrTerminatorKind::Unreachable,
                6 => IrTerminatorKind::Drop {
                    place: fuzz_place(rng),
                    target: target(rng),
                    unwind: fuzz_unwind(rng, num_blocks),
                },
                7 => IrTerminatorKind::Call {
                    func: fuzz_operand(rng),
                    args: (0..rng.below(3)).map(|_| fuzz_operand(rng)).collect(),
                    destination: fuzz_place(rng),
                    target: if rng.chance(70) {
                        Some(target(rng))
                    } else {
                        None
                    },
                    unwind: fuzz_unwind(rng, num_blocks),
                },
                8 => IrTerminatorKind::TailCall {
                    func: fuzz_operand(rng),
                    args: (0..rng.below(3)).map(|_| fuzz_operand(rng)).collect(),
                },
                9 => IrTerminatorKind::Assert {
                    cond: fuzz_operand(rng),
                    expected: rng.chance(50),
                    target: target(rng),
                    unwind: fuzz_unwind(rng, num_blocks),
                },
                _ => IrTerminatorKind::InlineAsm {
                    template: rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
                    targets: (0..rng.below(3)).map(|_| target(rng)).collect(),
                    unwind: fuzz_unwind(rng, num_blocks),
                },
            };
            basic_blocks.push(IrBasicBlockData {
                statements,
                terminator: IrTerminator {
                    kind,
                    span: rng.pick(&FUZZ_TRAP_STRINGS).to_string(),
                    comment: if rng.chance(50) {
                        Some(rng.pick(&FUZZ_TRAP_STRINGS).to_string())
                    } else {
                        None
                    },
                },
                is_cleanup: rng.chance(20),
            });
        }
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
        IrCapturedMir {
            // The emitter interpolates `def_path` unescaped into the header's `/-! ... -/`
            // doc comment, so a path containing `-/` yields invalid Lean (which the strict
            // scanner rejects); real `rustc` paths cannot contain `/`, so stay realistic.
            def_path: rng.pick(&FUZZ_CALLEES).to_string(),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 1,
            local_decls: (0..5)
                .map(|_| IrLocalDecl {
                    mutability: anneal_rustc_capture::lean_emit::IrMutability::Mut,
                    ty: fuzz_ty(rng, 2),
                    debug_name: if rng.chance(50) {
                        Some(rng.pick(&FUZZ_TRAP_STRINGS).to_string())
                    } else {
                        None
                    },
                })
                .collect(),
            basic_blocks,
            fn_abi: IrFnAbi {
                args: vec![IrArgAbi {
                    layout: u32_layout.clone(),
                    mode: IrAbiPassMode::Direct,
                }],
                ret: IrArgAbi {
                    layout: u32_layout.clone(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: rng.chance(50),
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![u32_layout.clone(), u32_layout],
            },
            allocations: Vec::new(),
        }
    }

    #[test]
    fn test_b2_randomized_emitter_differential_parity() {
        // `[adv B2]`: for randomized `IrCapturedMir` bodies covering every IR
        // statement, terminator, rvalue, operand, constant, projection, cast,
        // aggregate, unwind, and callee shape (with lexer-trap strings in spans,
        // paths, debug names, inline-asm templates, and `--` comments), the strict
        // scanner over the *real* `emit_mir_lean_module` output must reproduce the
        // structured census exactly.
        let mut rng = FuzzRng(0x9E37_79B9_7F4A_7C15);
        let mut sites_seen = 0usize;
        let mut classes_seen: BTreeSet<MirFaultClass> = BTreeSet::new();
        for case in 0..400 {
            let ir = fuzz_captured_mir(&mut rng);
            let emitted = emit_mir_lean_module("Mir.Fuzz.item", &ir);
            let direct = census_ir_captured_mir(&ir);
            // Structural parity: the scanned body (including decoded spans, callee
            // paths, constants, projections, and aggregate kinds) must equal the
            // direct IR conversion, not merely produce the same census.
            let parsed = parse_lean_captured_mir_def(&emitted, "body")
                .unwrap_or_else(|e| panic!("case {case}: parse failed: {e}\n{emitted}"));
            assert_eq!(
                parsed,
                ProtoMirBody::from_ir_captured_mir(&ir, true),
                "case {case}: scanned ProtoMirBody diverged from IR conversion\n{emitted}"
            );
            match census_lean_mir_module(&emitted) {
                Ok(scanned) => assert_eq!(
                    scanned, direct,
                    "case {case}: emitted-Lean census diverged from IR census\n{emitted}"
                ),
                Err(err) => {
                    panic!("case {case}: strict scanner rejected emitter output: {err}\n{emitted}")
                }
            }
            sites_seen += direct.len();
            classes_seen.extend(direct.iter().map(|site| site.fault_class));
        }
        assert!(
            sites_seen > 1000,
            "fuzz corpus too small: {sites_seen} sites"
        );
        assert_eq!(
            classes_seen.len(),
            MirFaultClass::ALL.len(),
            "fuzz corpus must exercise every fault class: {classes_seen:?}"
        );
    }

    #[test]
    fn test_b2_truncated_real_modules_fail_closed() {
        // `[adv B2]` / `[adv A2]`: every proper prefix (`cut < module.trim_end().len()`)
        // of a real `rustc`-captured module must fail closed because the top-level
        // `namespace Mir.FrameTutor.<item>` is only closed by the final
        // `end Mir.FrameTutor.<item>`.
        for module in [
            include_str!(
                "../../../examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/advance_offset.lean"
            ),
            include_str!(
                "../../../examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/magic_version.lean"
            ),
        ] {
            let full = census_lean_mir_module(module).expect("full module scans");
            let trimmed_len = module.trim_end().len();
            let mut accepted = 0usize;
            for (cut, _) in module.char_indices() {
                match census_lean_mir_module(&module[..cut]) {
                    Ok(sites) => {
                        assert!(
                            cut >= trimmed_len,
                            "proper prefix ending at byte {cut} < {trimmed_len} accepted"
                        );
                        assert_eq!(sites, full, "prefix ending at byte {cut}");
                        accepted += 1;
                    }
                    Err(_) => assert!(cut < trimmed_len),
                }
            }
            assert_eq!(accepted, 1);
        }
    }

    #[test]
    fn test_b2_emitter_escape_and_comment_injection_findings() {
        use anneal_rustc_capture::lean_emit::{
            IrPlace, IrProjectionElem, IrStatement, IrStatementKind, IrTerminator, IrTerminatorKind,
        };
        let mut rng = FuzzRng(7);
        let mut ir = fuzz_captured_mir(&mut rng);
        ir.basic_blocks.truncate(1);
        ir.basic_blocks[0].terminator = IrTerminator {
            kind: IrTerminatorKind::Return,
            span: String::from("s"),
            comment: None,
        };
        let stmt = |kind, span: &str| IrStatement {
            kind,
            span: span.to_string(),
            comment: None,
        };

        // (1) `escape_lean_str` encodes a multi-byte control character such as U+0085
        //     as one `\xHH` escape per UTF-8 byte (`\xc2\x85`), which Lean decodes as
        //     two code points. The scanner must mirror Lean's decoding (not the
        //     emitter's intent); census parity is unaffected because no `DefPath`
        //     the census classifies contains control characters.
        ir.basic_blocks[0].statements = vec![stmt(IrStatementKind::Nop, "a\u{85}b")];
        let emitted = emit_mir_lean_module("Mir.Escape.item", &ir);
        assert!(emitted.contains(r"a\xc2\x85b"), "{emitted}");
        let parsed = parse_lean_captured_mir_def(&emitted, "body").expect("parse escaped span");
        assert_eq!(parsed.basic_blocks[0].statements[0].span, "a\u{c2}\u{85}b");
        assert_eq!(
            census_lean_mir_module(&emitted).expect("strict scan"),
            census_ir_captured_mir(&ir)
        );

        // (2) A `DefPath` containing `-/` closes the emitter's `/-! ... -/` header doc
        //     comment early, and (3) a newline inside a `Downcast` variant name escapes
        //     the emitter's `-- bbN:` summary comment. Both produce Lean that does not
        //     elaborate; the strict scanner must reject them rather than guess.
        let mut doc_injection = ir.clone();
        doc_injection.def_path = String::from("evil -/ def body : CapturedMir := x");
        assert!(
            census_lean_mir_module(&emit_mir_lean_module("Mir.Doc.item", &doc_injection)).is_err()
        );
        let mut line_injection = ir.clone();
        line_injection.basic_blocks[0].statements = vec![stmt(
            IrStatementKind::PlaceMention(IrPlace {
                local_: 0,
                projection: vec![IrProjectionElem::Downcast(
                    Some(String::from("V\n) evil")),
                    0,
                )],
            }),
            "s",
        )];
        assert!(
            census_lean_mir_module(&emit_mir_lean_module("Mir.Line.item", &line_injection))
                .is_err()
        );
    }

    /// `[adv B2]` Cross-language census differential harness (run manually):
    /// writes randomized emitter modules plus the Rust census to
    /// `$FAULT_CENSUS_DIFF_DIR` so the Lean `censusMirBodyFaultSites` can be
    /// evaluated on the very same bodies and compared site-for-site.
    /// `FAULT_CENSUS_DIFF_DIR=<dir> cargo test --lib dump_lean_census_differential_corpus -- --ignored`
    #[test]
    #[ignore]
    fn dump_lean_census_differential_corpus() {
        let Ok(dir) = std::env::var("FAULT_CENSUS_DIFF_DIR") else {
            return;
        };
        // One self-checking Lean file: the prototype, 400 emitted modules, and one
        // `#guard` per body asserting that the Lean census renders exactly like the
        // Rust census of the same `IrCapturedMir`. Check it with
        // `(cd examples && anneal-lean-run --mode file --concurrency 1 -- lake env lean <dir>/LeanCensusDifferential.lean)`.
        let mut rng = FuzzRng(0xD1B5_4A32_D192_ED03);
        let mut out = String::from(LEAN_PROTOTYPE_SRC.trim_end());
        out.push_str("\n\n");
        let mut guards = String::from(
            "open Anneal.FaultSiteCensus\n\n\
             def renderFuzzSites (sites : List FaultSite) : String :=\n  \
             String.intercalate \";\" (sites.map (fun s => s!\"({s.1},{s.2.1},{s.2.2.asStr})\"))\n\n",
        );
        let mut classes_seen: BTreeSet<MirFaultClass> = BTreeSet::new();
        for case in 0..400 {
            let ir = fuzz_captured_mir(&mut rng);
            let emitted = emit_mir_lean_module(&format!("Mir.Fuzz.item{case}"), &ir);
            classes_seen.extend(census_ir_captured_mir(&ir).iter().map(|s| s.fault_class));
            out.push_str(emitted.trim_start_matches("import Trusted"));
            out.push('\n');
            let rendered: Vec<String> = census_ir_captured_mir(&ir)
                .iter()
                .map(|s| {
                    format!(
                        "({},{},{})",
                        s.block_idx,
                        s.stmt_idx,
                        s.fault_class.as_str()
                    )
                })
                .collect();
            guards.push_str(&format!(
                "#guard renderFuzzSites (censusMirBodyFaultSites Mir.Fuzz.item{case}.body) == \"{}\"\n",
                rendered.join(";")
            ));
        }
        assert_eq!(
            classes_seen.len(),
            MirFaultClass::ALL.len(),
            "{classes_seen:?}"
        );
        out.push_str(&guards);
        std::fs::write(format!("{dir}/LeanCensusDifferential.lean"), out).expect("write driver");
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
        //    `theory/Anneal/FaultSiteCensus.lean` in exact rank order.
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

        // 2. Parse `witnessPureNoopBody` directly from `FaultSiteCensus.lean`
        //    and verify 0 fault sites (`[]`).
        let pure_noop_sites = census_lean_mir_def(LEAN_PROTOTYPE_SRC, "witnessPureNoopBody")
            .expect("parse witnessPureNoopBody from Lean");
        assert!(pure_noop_sites.is_empty());

        // 3. Parse all 4 probe witness `CapturedMir` bodies and their kernel-checked
        //    `ExpectedCensus` lists from `FaultSiteCensus.lean`, and assert
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
            let scanned_from_lean_body = census_lean_mir_def(LEAN_PROTOTYPE_SRC, lean_body_name)
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
            // `[adv B2]`: the brief requires `census_lean_mir_module` itself to parse the
            // witness definitions, so re-host each witness record verbatim as the `body`
            // of a canonical strict module and scan it with the strict grammar.
            let strict = census_lean_mir_module(&witness_as_strict_module(lean_body_name))
                .unwrap_or_else(|e| panic!("strict scan of {lean_body_name} failed: {e}"));
            assert_eq!(
                strict, lean_decide_expected,
                "strict module scan for {probe:?}"
            );
        }

        // 4. `[adv B1]` precision witness: the Lean `witnessWrappingArithBody` scan must
        //    match its kernel-checked expected census and carry no arithmetic, shift,
        //    niche, or pointer-dereference labels.
        let wrapping_scan = census_lean_mir_def(LEAN_PROTOTYPE_SRC, "witnessWrappingArithBody")
            .expect("parse witnessWrappingArithBody from Lean");
        let wrapping_expected = parse_lean_expected_fault_site_list(
            LEAN_PROTOTYPE_SRC,
            "witnessWrappingArithExpectedCensus",
        );
        assert_eq!(wrapping_scan, wrapping_expected);
        assert!(wrapping_scan.iter().all(|site| !matches!(
            site.fault_class,
            MirFaultClass::ArithOverflow
                | MirFaultClass::ShiftOverflow
                | MirFaultClass::ScalarNicheInvalid
                | MirFaultClass::PtrDerefInvalid
                | MirFaultClass::PtrAlignMismatch
        )));

        // 5. `[adv B1]` every probe's baseline emitter covers exactly the census and the
        //    Lean liveness certificates exist for each stripped site.
        for probe in FaultMutationProbe::ALL {
            let (body, baseline, _, _) = build_probe_scenario(probe);
            assert_eq!(census_mir_fault_sites(&body), baseline, "{probe:?}");
        }
        for live in [
            "theorem witnessCallArgBlind_call_site_live",
            "theorem witnessSwitchBreakStrip_div_site_live",
            "theorem witnessLoopUpdateOverflow_latch_site_live",
            "theorem witnessDerefAlias_deref_site_live",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(live),
                "missing Lean liveness certificate `{live}`"
            );
        }
    }

    /// Re-host the record of `def <def_name> : CapturedMir := { ... }` from
    /// `FaultSiteCensus.lean` verbatim as the `body` of a canonical strict
    /// `Mir/<Item>.lean` module.
    fn witness_as_strict_module(def_name: &str) -> String {
        let header = format!("def {def_name} : CapturedMir :=");
        let start = LEAN_PROTOTYPE_SRC
            .find(&header)
            .unwrap_or_else(|| panic!("missing `{header}`"))
            + header.len();
        let rest = &LEAN_PROTOTYPE_SRC[start..];
        let end = ["\n/--", "\n/-!", "\ndef ", "\ntheorem "]
            .iter()
            .filter_map(|marker| rest.find(marker))
            .min()
            .expect("witness record terminator");
        format!(
            "import Trusted\nnamespace Mir.Witness.item\nopen Trusted.Rustc.V2026_06_01.Layout\n\
             open Trusted.Rustc.V2026_06_01.MirAst\ndef body : CapturedMir :=\n{}\nend Mir.Witness.item\n",
            &rest[..end]
        )
    }

    /// Wrap `blocks` (a Lean `List BasicBlockData` literal) in a canonical strict
    /// `Mir/<Item>.lean` module.
    fn strict_module_with_blocks(prelude: &str, blocks: &str) -> String {
        format!(
            r#"import Trusted
namespace Mir.Probe.item
open Trusted.Rustc.V2026_06_01.MirAst
{prelude}
def body : CapturedMir :=
  {{ defPath := "probe::item"
  , phase := MirPhaseTag.runtimePostCleanup
  , role := ContractRole.subject
  , argCount := 0
  , localDecls := List.nil
  , basicBlocks := {blocks}
  , fnAbi := dummyAbi
  , layouts := emptyLayoutTable
  , allocations := List.nil
  }}
end Mir.Probe.item
"#
        )
    }

    fn single_terminator_block(term_kind: &str) -> String {
        format!(
            "[{{ statements := [], terminator := {{ kind := {term_kind}, span := \"s\" }}, isCleanup := false }}]"
        )
    }

    #[test]
    fn test_real_rustc_captured_mir_corpus_census() {
        // `[adv B1]`: run the strict scanner over real `anneal-rustc-capture` output
        // committed in the repository (separate `def layouts`, `-- bbN:` comments,
        // `/-! -/` doc comments, `def defaultClaim`, namespaces, and `open`s).
        let magic = include_str!(
            "../../../examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/magic_version.lean"
        );
        assert_eq!(
            census_lean_mir_module(magic).expect("scan magic_version"),
            vec![
                FaultSite::new(0, 0, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(0, 0, MirFaultClass::StorageLiveProtected),
                FaultSite::new(0, 1, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(0, 1, MirFaultClass::UninitRead),
                FaultSite::new(0, 1, MirFaultClass::CallAbiMismatch),
            ]
        );
        let advance = include_str!(
            "../../../examples/tutor-ch1/.anneal/generated/Mir/FrameTutor/advance_offset.lean"
        );
        assert_eq!(
            census_lean_mir_module(advance).expect("scan advance_offset"),
            vec![
                // StorageLive(_2)
                FaultSite::new(0, 0, MirFaultClass::StorageLiveProtected),
                // _2 = AddWithOverflow(copy _1, const 4_u8): flagged add never faults.
                FaultSite::new(0, 1, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(0, 1, MirFaultClass::UninitRead),
                FaultSite::new(0, 1, MirFaultClass::StorageLiveProtected),
                // assert(!move (_2.1)) -> [success: bb1, unwind continue]
                FaultSite::new(0, 2, MirFaultClass::ScalarNicheInvalid),
                FaultSite::new(0, 2, MirFaultClass::UninitRead),
                FaultSite::new(0, 2, MirFaultClass::CallAbiMismatch),
                // _0 = move (_2.0): loaded-value validation.
                FaultSite::new(1, 0, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(1, 0, MirFaultClass::ScalarNicheInvalid),
                FaultSite::new(1, 0, MirFaultClass::UninitRead),
                FaultSite::new(1, 0, MirFaultClass::StorageLiveProtected),
                // return
                FaultSite::new(1, 1, MirFaultClass::TreeBorrowsViolation),
                FaultSite::new(1, 1, MirFaultClass::UninitRead),
                FaultSite::new(1, 1, MirFaultClass::CallAbiMismatch),
            ]
        );
    }

    #[test]
    fn test_b1_lean_scanner_fail_open_regressions() {
        let unreachable_block = single_terminator_block("TerminatorKind.unreachable");
        let baseline = strict_module_with_blocks("", &unreachable_block);
        assert_eq!(
            census_lean_mir_module(&baseline).expect("baseline strict module"),
            vec![FaultSite::new(0, 0, MirFaultClass::UnreachableTerminator)]
        );

        // (a) Foreign-qualified or bare constructor heads may name arbitrary user
        //     definitions; only `.goto` / `TerminatorKind.goto` are accepted.
        for head in ["Evil.goto 0", "goto 0", "Mir.Probe.TerminatorKind.goto 0"] {
            let src = strict_module_with_blocks("", &single_terminator_block(head));
            assert!(
                matches!(
                    census_lean_mir_module(&src),
                    Err(CensusScanError::MalformedCapturedMirSyntax(_))
                ),
                "accepted constructor head `{head}`"
            );
        }
        for head in [
            ".goto 0",
            "TerminatorKind.goto 0",
            "Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.goto 0",
        ] {
            let src = strict_module_with_blocks("", &single_terminator_block(head));
            assert_eq!(
                census_lean_mir_module(&src),
                Ok(Vec::new()),
                "rejected `{head}`"
            );
        }

        // (b) Anything applied to the `CapturedMir` record fails closed, in both the
        //     strict module scanner and the lenient named-def scanner.
        let piped = baseline.replace(
            "  }}
end Mir.Probe.item",
            "  }} |> mutateBody
end Mir.Probe.item",
        );
        let piped = if piped == baseline {
            baseline.replace(
                "allocations := List.nil
  }
",
                "allocations := List.nil
  } |> mutateBody
",
            )
        } else {
            piped
        };
        assert_ne!(piped, baseline);
        assert!(census_lean_mir_module(&piped).is_err());
        assert!(census_lean_mir_def(&piped, "body").is_err());
        let dotted = baseline.replace(
            "allocations := List.nil
  }
",
            "allocations := List.nil
  }.withBlocks evil
",
        );
        assert_ne!(dotted, baseline);
        assert!(census_lean_mir_def(&dotted, "body").is_err());

        // (c) Duplicate record fields fail closed instead of last-write-wins.
        let dup = baseline.replace(
            "  , basicBlocks := ",
            "  , basicBlocks := List.nil
  , basicBlocks := ",
        );
        assert!(matches!(
            census_lean_mir_module(&dup),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("duplicate")
        ));

        // (d) Exact Lean string escapes: `\u0061` decodes to `a`, so the escaped
        //     `core::intrinsics::unreachable` callee keeps its fault class; unknown
        //     escapes fail closed.
        let call_unreachable = |path: &str| {
            single_terminator_block(&format!(
                "TerminatorKind.call (Operand.constant {{ ty := {{ kind := RigidTy.fnDef \"{path}\" List.nil, layoutIdx := 0 }}, val := ConstValue.zeroSized }}) List.nil {{ local_ := 0, projection := List.nil }} Option.none UnwindAction.continue_"
            ))
        };
        let escaped =
            strict_module_with_blocks("", &call_unreachable(r"core::intrinsics::unreach\u0061ble"));
        let escaped_sites = census_lean_mir_module(&escaped).expect("escaped callee path");
        assert!(escaped_sites.contains(&FaultSite::new(
            0,
            0,
            MirFaultClass::UnreachableTerminator
        )));
        let bad_escape =
            strict_module_with_blocks("", &call_unreachable(r"core::intrinsics::unreach\qble"));
        assert!(census_lean_mir_module(&bad_escape).is_err());
        let std_path =
            strict_module_with_blocks("", &call_unreachable("std::intrinsics::unchecked_add"));
        assert!(!census_lean_mir_module(&std_path)
            .expect("std intrinsic path")
            .iter()
            .any(|s| s.fault_class == MirFaultClass::ArithOverflow));

        // (e) A decoy `def body` hidden inside an `m!` interpolation is a string in Lean
        //     and must stay a string here; a decoy exposed through a plain-string
        //     interpolation desync (`throwError "{"...`) yields two bodies and fails.
        let decoy_interp = strict_module_with_blocks(
            "def helperMsg : String := m!\"{\"def body : CapturedMir := { basicBlocks := List.nil }\"}\"",
            &unreachable_block,
        );
        assert_eq!(
            census_lean_mir_def(&decoy_interp, "body").expect("m! decoy stays a string"),
            vec![FaultSite::new(0, 0, MirFaultClass::UnreachableTerminator)]
        );
        assert!(census_lean_mir_module(&decoy_interp).is_err());
        let decoy_plain = strict_module_with_blocks(
            "def helperErr : String := throwError \"{\"def body : CapturedMir := { basicBlocks := List.nil } -- \"}\"",
            &unreachable_block,
        );
        assert!(census_lean_mir_module(&decoy_plain).is_err());
        let spaced_macro =
            strict_module_with_blocks("def helperErr : Unit := panic! \"{\"", &unreachable_block);
        assert!(census_lean_mir_module(&spaced_macro).is_err());
        let comment_in_interp = strict_module_with_blocks(
            "def helperMsg : String := s!\"{x -- }\"\n  }\"",
            &unreachable_block,
        );
        assert!(census_lean_mir_module(&comment_in_interp).is_err());

        // (f) Syntax extensions, attributes, and non-canonical commands fail closed.
        for prelude in [
            "notation \"EVIL\" => 0",
            "macro_rules | `(x) => `(y)",
            "@[simp] theorem helper : True := trivial",
            "instance : Inhabited Nat := ⟨0⟩",
            "#eval 1",
        ] {
            let src = strict_module_with_blocks(prelude, &unreachable_block);
            assert!(
                census_lean_mir_module(&src).is_err(),
                "accepted prelude `{prelude}`"
            );
        }

        // (g) Shadowing MIR AST names in the module namespace fails closed.
        let shadow_ns = strict_module_with_blocks(
            "namespace TerminatorKind\nend TerminatorKind",
            &unreachable_block,
        );
        assert!(census_lean_mir_module(&shadow_ns).is_err());
        let shadow_def =
            strict_module_with_blocks("def TerminatorKind.goto : Nat := 0", &unreachable_block);
        assert!(census_lean_mir_module(&shadow_def).is_err());

        // (g2) `[adv B2]` Only the emitter's exact `open`s are allowed, and constructor
        //      qualifiers are pinned to the `V2026_06_01` dialect.
        let other_dialect_open =
            strict_module_with_blocks("open Trusted.Rustc.V2026_08_01.MirAst", &unreachable_block);
        assert!(census_lean_mir_module(&other_dialect_open).is_err());
        let other_dialect_ctor = strict_module_with_blocks(
            "",
            &single_terminator_block("Trusted.Rustc.V2026_08_01.MirAst.TerminatorKind.goto 0"),
        );
        assert!(census_lean_mir_module(&other_dialect_ctor).is_err());
        let foreign_open = strict_module_with_blocks("open Trusted.Evil", &unreachable_block);
        assert!(census_lean_mir_module(&foreign_open).is_err());

        // (h) A `body` with a non-canonical type ascription (invisible to a naive
        //     `def body : CapturedMir :=` matcher) fails closed.
        let hidden =
            strict_module_with_blocks("def body : (CapturedMir) := realBody", &unreachable_block);
        assert!(census_lean_mir_module(&hidden).is_err());

        // (i) `RigidTy.fnDef`-typed constants must be zero-sized function items.
        let non_zst_fn = strict_module_with_blocks(
            "",
            &single_terminator_block(
                "TerminatorKind.call (Operand.constant { ty := { kind := RigidTy.fnDef \"core::intrinsics::unreachable\" List.nil, layoutIdx := 0 }, val := ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 1 }) }) List.nil { local_ := 0, projection := List.nil } Option.none UnwindAction.continue_",
            ),
        );
        assert!(census_lean_mir_module(&non_zst_fn).is_err());
    }

    #[test]
    fn test_a1_semantic_precision_and_scanner_regressions() {
        // 1. Unevaluated Rvalues (`NullaryOp`, `ThreadLocalRef`, `ShallowInitBox`, float casts,
        //    and `AggregateKind.coroutine`) make `evalStmt (.assign dst rv)` step directly to
        //    `MirStepNode.unsupported` before inspecting `dst`, so `census_stmt_fault_classes`
        //    must emit `[]` even when `dst` is a dereferenced place `*_1`.
        for uneval_rv in [
            ProtoRvalue::NullaryOp(ProtoNullOp::SizeOf),
            ProtoRvalue::ThreadLocalRef(String::from("tls::KEY")),
            ProtoRvalue::ShallowInitBox(ProtoOperand::Copy(ProtoPlace::deref_local(2))),
            ProtoRvalue::Aggregate(
                ProtoAggregateKind::Coroutine(String::from("coro::gen")),
                vec![ProtoOperand::Copy(ProtoPlace::deref_local(2))],
            ),
        ] {
            assert!(rvalue_unevaluated(&uneval_rv), "{uneval_rv:?}");
            assert_eq!(
                census_stmt_fault_classes(&ProtoStatementKind::Assign(
                    ProtoPlace::deref_local(1),
                    uneval_rv
                )),
                Vec::<MirFaultClass>::new()
            );
        }

        // 2. `PlaceMention` only checks root/index initialization (`[UninitRead]`), never
        //    dereferencing pointers or checking bounds/alignment/Tree Borrows.
        assert_eq!(
            census_stmt_fault_classes(&ProtoStatementKind::PlaceMention(ProtoPlace::deref_local(
                1
            ))),
            vec![MirFaultClass::UninitRead]
        );

        // 3. Unprojected `Deinit` and `Drop` only check `[StorageLiveProtected]` (succeeding on
        //    `.uninit` slots); projected `Deinit`/`Drop` use `readProjectedValue`, which has no
        //    `.deref` arm (`Deref` contributes `[]`).
        assert_eq!(
            census_stmt_fault_classes(&ProtoStatementKind::Deinit(ProtoPlace::local(1))),
            vec![MirFaultClass::StorageLiveProtected]
        );
        assert_eq!(
            census_stmt_fault_classes(&ProtoStatementKind::Deinit(ProtoPlace::deref_local(1))),
            vec![MirFaultClass::UninitRead]
        );
        assert_eq!(
            census_terminator_fault_classes(
                2,
                &ProtoTerminatorKind::Drop {
                    place: ProtoPlace::local(1),
                    target: 1,
                    unwind: ProtoUnwindAction::Continue,
                }
            ),
            vec![MirFaultClass::StorageLiveProtected]
        );
        assert_eq!(
            census_terminator_fault_classes(
                2,
                &ProtoTerminatorKind::Drop {
                    place: ProtoPlace::deref_local(1),
                    target: 1,
                    unwind: ProtoUnwindAction::Continue,
                }
            ),
            vec![MirFaultClass::UninitRead]
        );

        // 4. `CastKind` precision & soundness:
        //    - `PointerCoercion("MutToConstPointer")`, `PointerExposeProvenance`, and
        //      `PointerWithExposedProvenance` have their own ill-shaped-operand `.ub`
        //      edges (`[adv ep1-B1]`, Lean `evalRvalue_cast_own_ub_witnesses`), so
        //      they must never emit `[]`; only `IntToInt` and float casts do.
        //    - `PointerCoercion("Unsize" | "ArrayToPointer")` and `PtrToPtr` include `TreeBorrowsViolation`.
        //    - `PointerCoercion("ReifyFnPointer")` and `FnPtrToPtr` include `CallAbiMismatch` and
        //      do not emit `BoundsCheck` or `PtrAlignMismatch`.
        assert_eq!(
            census_cast_kind_fault_classes(&ProtoCastKind::PointerCoercion(String::from(
                "MutToConstPointer"
            ))),
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        );
        assert_eq!(
            census_cast_kind_fault_classes(&ProtoCastKind::PointerExposeProvenance),
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        );
        assert_eq!(
            census_cast_kind_fault_classes(&ProtoCastKind::PointerWithExposedProvenance),
            vec![MirFaultClass::ScalarNicheInvalid]
        );
        for ck in [
            ProtoCastKind::IntToInt,
            ProtoCastKind::FloatToInt,
            ProtoCastKind::FloatToFloat,
            ProtoCastKind::IntToFloat,
        ] {
            assert!(census_cast_kind_fault_classes(&ck).is_empty(), "{ck:?}");
            assert!(!cast_kind_unevaluated(&ck), "{ck:?}");
        }
        assert_eq!(
            census_aggregate_kind_fault_classes(&ProtoAggregateKind::Adt(
                String::from("demo::U"),
                0,
                Some(1)
            )),
            vec![MirFaultClass::ScalarNicheInvalid]
        );
        assert_eq!(
            census_aggregate_kind_fault_classes(&ProtoAggregateKind::RawPtr(false)),
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        );
        assert!(
            census_aggregate_kind_fault_classes(&ProtoAggregateKind::Adt(
                String::from("demo::S"),
                0,
                None
            ))
            .is_empty()
        );
        // A raw-pointer aggregate of two constant operands still faults on its own
        // width/shape checks, so its rvalue census must be non-empty.
        assert_eq!(
            census_rvalue_fault_classes(&ProtoRvalue::Aggregate(
                ProtoAggregateKind::RawPtr(false),
                Vec::new()
            )),
            vec![MirFaultClass::PtrDerefInvalid, MirFaultClass::ScalarNicheInvalid]
        );
        for ck in [
            ProtoCastKind::PtrToPtr,
            ProtoCastKind::PointerCoercion(String::from("Unsize")),
            ProtoCastKind::PointerCoercion(String::from("ArrayToPointer")),
        ] {
            let classes = census_cast_kind_fault_classes(&ck);
            assert!(
                classes.contains(&MirFaultClass::TreeBorrowsViolation),
                "{ck:?}"
            );
        }
        for ck in [
            ProtoCastKind::FnPtrToPtr,
            ProtoCastKind::PointerCoercion(String::from("ReifyFnPointer")),
            ProtoCastKind::PointerCoercion(String::from("UnsafeFnPointer")),
        ] {
            let classes = census_cast_kind_fault_classes(&ck);
            assert_eq!(
                classes,
                vec![
                    MirFaultClass::PtrDerefInvalid,
                    MirFaultClass::ScalarNicheInvalid,
                    MirFaultClass::CallAbiMismatch,
                ],
                "{ck:?}"
            );
        }

        // 5. Diverging `Call` (`target = None`) never writes to `destination` and only dispatches
        //    `isUnreachableCallTarget` (not `evalDirectRustIntrinsic?`), while `TailCall`
        //    includes destination-write classes from `resumeExternalTailCall`.
        let div_call_classes = census_terminator_fault_classes(
            1,
            &ProtoTerminatorKind::Call {
                func: ProtoOperand::const_fn("core::intrinsics::unchecked_add"),
                args: Vec::new(),
                destination: ProtoPlace::deref_local(0),
                target: None,
                unwind: ProtoUnwindAction::Continue,
            },
        );
        assert_eq!(div_call_classes, vec![MirFaultClass::CallAbiMismatch]);

        let tail_call_classes = census_terminator_fault_classes(
            1,
            &ProtoTerminatorKind::TailCall {
                func: ProtoOperand::const_fn("proto::callee"),
                args: Vec::new(),
            },
        );
        assert_eq!(
            tail_call_classes,
            vec![
                MirFaultClass::TreeBorrowsViolation,
                MirFaultClass::UninitRead,
                MirFaultClass::StorageLiveProtected,
                MirFaultClass::CallAbiMismatch,
            ]
        );

        // 6. `census_callee_def_path_fault_classes`: `std::intrinsics::exact_div` is not
        //    matched by `isDirectExactDivTarget`, `arith_offset` wraps modularly, and
        //    `const_eval_select` covers all inline intrinsic fault classes.
        assert_eq!(
            census_callee_def_path_fault_classes("std::intrinsics::exact_div"),
            Vec::<MirFaultClass>::new()
        );
        assert_eq!(
            census_callee_def_path_fault_classes("core::intrinsics::arith_offset"),
            vec![
                MirFaultClass::PtrDerefInvalid,
                MirFaultClass::ScalarNicheInvalid,
            ]
        );
        let ces = census_callee_def_path_fault_classes("core::intrinsics::const_eval_select");
        assert!(ces.contains(&MirFaultClass::ArithOverflow));
        assert!(ces.contains(&MirFaultClass::DivRemByZero));
        assert!(ces.contains(&MirFaultClass::ShiftOverflow));
        assert!(ces.contains(&MirFaultClass::UnreachableTerminator));

        // 7. Lexer & scanner fail-open regressions:
        //    (a) Character literal `'a'` must not be accepted as `String` in `defPath := 'a'`,
        //        and `'\''` must not leave a trailing `'` token.
        let unreachable_block = single_terminator_block("TerminatorKind.unreachable");
        let baseline = strict_module_with_blocks("", &unreachable_block);
        let char_as_str = baseline.replace("defPath := \"probe::item\"", "defPath := 'a'");
        assert!(census_lean_mir_module(&char_as_str).is_err());

        let escaped_single_quote_helper =
            strict_module_with_blocks("def helperSq : Char := '\\''", &unreachable_block);
        assert_eq!(
            census_lean_mir_module(&escaped_single_quote_helper).expect("escaped single quote"),
            vec![FaultSite::new(0, 0, MirFaultClass::UnreachableTerminator)]
        );

        //    (b) `s!"..."` with `'\"'`, `'}'`, `r#"}"#`, nested `s!"..."`, or `«}»` inside `{...}`
        //        must not desynchronize `census_lean_mir_def` into scanning a decoy `def body`.
        let interp_traps = strict_module_with_blocks(
            r##"def helperTrap : String := s!"{if c == '"' || c == '}' then r#"}"# else s!"{"def body : CapturedMir := { basicBlocks := List.nil }"}"}""##,
            &unreachable_block,
        );
        assert_eq!(
            census_lean_mir_def(&interp_traps, "body").expect("interp traps stay inside string"),
            vec![FaultSite::new(0, 0, MirFaultClass::UnreachableTerminator)]
        );

        //    (c) `AggregateKind` constructor head is validated (`Evil.tuple` rejected).
        let evil_agg = strict_module_with_blocks(
            "",
            "[{ statements := [{ kind := StatementKind.assign { local_ := 0, projection := [] } (Rvalue.aggregate Evil.tuple []), span := \"s\" }], terminator := { kind := TerminatorKind.return_, span := \"s\" }, isCleanup := false }]",
        );
        assert!(census_lean_mir_module(&evil_agg).is_err());

        //    (d) `import EvilMod`, `open EvilNs`, and `def Sub.body : CapturedMir` are rejected.
        let evil_import = baseline.replace("import Trusted", "import EvilMod");
        assert!(census_lean_mir_module(&evil_import).is_err());
        let evil_open = strict_module_with_blocks("open EvilNs", &unreachable_block);
        assert!(census_lean_mir_module(&evil_open).is_err());
        let sub_body = baseline.replace("def body : CapturedMir", "def Sub.body : CapturedMir");
        assert!(census_lean_mir_module(&sub_body).is_err());

        //    (e) Missing required `CapturedMir` fields (`defPath`, `phase`, `allocations`) or
        //        missing `ScalarInt.bits` / `BasicBlockData.isCleanup` fail closed.
        let missing_def_path = baseline.replace("  { defPath := \"probe::item\"\n  , ", "  { ");
        assert!(census_lean_mir_module(&missing_def_path).is_err());
        let missing_is_cleanup = baseline.replace(", isCleanup := false", "");
        assert!(census_lean_mir_module(&missing_is_cleanup).is_err());
    }

    #[test]
    fn test_a2_scope_stack_const_ty_multi_item_and_fuzz_completeness() {
        let unreachable_block = single_terminator_block("TerminatorKind.unreachable");
        let baseline = strict_module_with_blocks("", &unreachable_block);

        // 1. `check_strict_mir_module_grammar` scope-stack enforcement:
        //    - Unclosed `namespace Mir.Probe.item` (missing `end Mir.Probe.item`) fails closed.
        //    - Mismatched `end Mir.Probe.wrong` fails closed.
        //    - Nested `namespace Sub def body : CapturedMir := ... end Sub` inside `Mir.Probe.item`
        //      (which defines `Mir.Probe.item.Sub.body`, not `Mir.Probe.item.body`) fails closed.
        //    - Stray `end Mir.Probe.extra` fails closed.
        let unclosed_ns = baseline
            .strip_suffix("end Mir.Probe.item\n")
            .expect("strip trailing end");
        assert!(matches!(
            census_lean_mir_module(unclosed_ns),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("unclosed")
        ));
        let mismatched_end = baseline.replace("end Mir.Probe.item", "end Mir.Probe.wrong");
        assert!(matches!(
            census_lean_mir_module(&mismatched_end),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("mismatched")
        ));
        let nested_ns_body = baseline
            .replace(
                "def body : CapturedMir :=",
                "namespace Sub\ndef body : CapturedMir :=",
            )
            .replace("end Mir.Probe.item", "end Sub\nend Mir.Probe.item");
        assert!(matches!(
            census_lean_mir_module(&nested_ns_body),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("single top-level")
        ));
        let stray_end = format!("{baseline}end Mir.Probe.extra\n");
        assert!(matches!(
            census_lean_mir_module(&stray_end),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("unmatched")
        ));

        // 2. `ConstOperand` missing `ty`, `Ty` missing `kind` or `layoutIdx`, and
        //    non-inline list identifiers for `localDecls` / `allocations` / `RigidTy.fnDef`
        //    `typeArgs` must fail closed instead of silently dropping callee `fnDef` paths.
        let call_missing_ty = strict_module_with_blocks(
            "",
            &single_terminator_block(
                "TerminatorKind.call (Operand.constant { val := ConstValue.zeroSized }) List.nil { local_ := 0, projection := List.nil } Option.none UnwindAction.continue_",
            ),
        );
        assert!(matches!(
            census_lean_mir_module(&call_missing_ty),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("ConstOperand missing `ty`")
        ));
        let call_missing_kind = strict_module_with_blocks(
            "",
            &single_terminator_block(
                "TerminatorKind.call (Operand.constant { ty := { layoutIdx := 0 }, val := ConstValue.zeroSized }) List.nil { local_ := 0, projection := List.nil } Option.none UnwindAction.continue_",
            ),
        );
        assert!(matches!(
            census_lean_mir_module(&call_missing_kind),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("Ty missing `kind`")
        ));
        let call_missing_layout_idx = strict_module_with_blocks(
            "",
            &single_terminator_block(
                "TerminatorKind.call (Operand.constant { ty := { kind := RigidTy.fnDef \"core::intrinsics::unreachable\" List.nil }, val := ConstValue.zeroSized }) List.nil { local_ := 0, projection := List.nil } Option.none UnwindAction.continue_",
            ),
        );
        assert!(matches!(
            census_lean_mir_module(&call_missing_layout_idx),
            Err(CensusScanError::MalformedCapturedMirSyntax(msg)) if msg.contains("Ty missing `layoutIdx`")
        ));
        let call_non_list_type_args = strict_module_with_blocks(
            "",
            &single_terminator_block(
                "TerminatorKind.call (Operand.constant { ty := { kind := RigidTy.fnDef \"core::intrinsics::unreachable\" externalTypeArgs, layoutIdx := 0 }, val := ConstValue.zeroSized }) List.nil { local_ := 0, projection := List.nil } Option.none UnwindAction.continue_",
            ),
        );
        assert!(census_lean_mir_module(&call_non_list_type_args).is_err());
        let non_inline_local_decls =
            baseline.replace("localDecls := List.nil", "localDecls := externalDecls");
        assert!(census_lean_mir_module(&non_inline_local_decls).is_err());
        let non_inline_allocs =
            baseline.replace("allocations := List.nil", "allocations := externalAllocs");
        assert!(census_lean_mir_module(&non_inline_allocs).is_err());

        // 3. `fuzz_captured_mir` completeness: verify that the fuzzer exercises
        //    `IrStatementKind::ConstEvalCounter`, all 4 `IrRetagKind` variants
        //    (`FnEntry`, `TwoPhase`, `Raw`, `Default`), and `IrAggregateKind::RawPtr(_, IrMutability::Mut)`.
        let mut rng = FuzzRng(0xA2A2_A2A2_5555_1234);
        let mut saw_const_eval_counter = false;
        let mut retag_kinds = [false; 4];
        let mut saw_mut_raw_ptr_agg = false;
        for _ in 0..300 {
            let ir = fuzz_captured_mir(&mut rng);
            for bb in &ir.basic_blocks {
                for stmt in &bb.statements {
                    match &stmt.kind {
                        IrStatementKind::ConstEvalCounter => saw_const_eval_counter = true,
                        IrStatementKind::Retag(rk, _) => match rk {
                            anneal_rustc_capture::lean_emit::IrRetagKind::FnEntry => {
                                retag_kinds[0] = true;
                            }
                            anneal_rustc_capture::lean_emit::IrRetagKind::TwoPhase => {
                                retag_kinds[1] = true;
                            }
                            anneal_rustc_capture::lean_emit::IrRetagKind::Raw => {
                                retag_kinds[2] = true;
                            }
                            anneal_rustc_capture::lean_emit::IrRetagKind::Default => {
                                retag_kinds[3] = true;
                            }
                        },
                        IrStatementKind::Assign(
                            _,
                            IrRvalue::Aggregate(
                                anneal_rustc_capture::lean_emit::IrAggregateKind::RawPtr(
                                    _,
                                    IrMutability::Mut,
                                ),
                                _,
                            ),
                        ) => {
                            saw_mut_raw_ptr_agg = true;
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(
            saw_const_eval_counter,
            "fuzzer must generate ConstEvalCounter"
        );
        assert_eq!(
            retag_kinds,
            [true, true, true, true],
            "fuzzer must generate all 4 RetagKind variants"
        );
        assert!(
            saw_mut_raw_ptr_agg,
            "fuzzer must generate AggregateKind::RawPtr(_, Mut)"
        );

        // 4. Multi-item / multi-callee reconciliation (`reconcile_multi_item_coverage`),
        //    `[adv B3]` API (items carry bodies; censuses are recomputed internally):
        //    - Discharging `(0, 0, StorageLiveProtected)` in the caller NEVER masks the
        //      undischarged `(0, 0, StorageLiveProtected)` of the callee.
        //    - Empty batches and duplicate `def_path` entries fail closed.
        let reg = PropertyRegistry::all_verified();
        let caller = parse_lean_captured_mir_def(LEAN_PROTOTYPE_SRC, "witnessDerefAliasBody")
            .expect("parse caller witness");
        let callee = parse_lean_captured_mir_def(LEAN_PROTOTYPE_SRC, "witnessCalleeStorageBody")
            .expect("parse callee witness");
        let caller_ok =
            ItemCoverageInput::from_body(caller.clone(), census_mir_fault_sites(&caller));
        let callee_missing = ItemCoverageInput::from_body(callee.clone(), Vec::new());
        let callee_ok =
            ItemCoverageInput::from_body(callee.clone(), census_mir_fault_sites(&callee));
        let closure = CalleeClosure::default();
        assert_eq!(
            reconcile_multi_item_coverage(&[], &closure, &reg).status_code(),
            "UNKNOWN(UNMAPPED_FAULT_SITE)"
        );
        let cross_item_mask_attempt =
            reconcile_multi_item_coverage(&[caller_ok.clone(), callee_missing], &closure, &reg);
        match cross_item_mask_attempt {
            MultiItemCoverageVerdict::UnknownUnmappedFaultSite { failed_items, .. } => {
                assert_eq!(failed_items.len(), 1);
                assert_eq!(failed_items[0].0, "proto::witness_callee_storage");
            }
            MultiItemCoverageVerdict::Verified => panic!("expected callee missing site failure"),
        }
        assert_eq!(
            reconcile_multi_item_coverage(&[caller_ok.clone(), callee_ok], &closure, &reg),
            MultiItemCoverageVerdict::Verified
        );
        assert_eq!(
            reconcile_multi_item_coverage(&[caller_ok.clone(), caller_ok], &closure, &reg)
                .status_code(),
            "UNKNOWN(UNMAPPED_FAULT_SITE)"
        );

        // 5. Verify new `[adv A2]` Lean theorems exist in `theory/Anneal/FaultSiteCensus.lean`.
        for thm in [
            "theorem evalOperand_unprojected_copy_ub_iff",
            "theorem evalOperand_unprojected_move_ub_iff",
            "theorem evalOperand_ub_implies_mem_censusOperand",
            "theorem writePlaceValue_unprojected_ub_iff",
            "theorem evalStmt_intrinsic_assume_ub_iff",
            "theorem evalTerminator_assert_cleanup_or_terminate_ub_iff",
            "theorem mirStepsIntra_preserves_validMirPc",
            "theorem initMachineState_mirStepsIntra_exposesUb_in_census",
            "theorem reconcileFaultCoverageWithRegistry_partial_site_rejected",
            "theorem reconcileFaultCoverageWithRegistry_append_verified_iff",
            "theorem reconcileFaultCoverageWithRegistry_mono",
            "theorem initMachineState_mirStepsIntra_reconciled_safety",
            "theorem initMachineState_mirStepsIntra_not_exposesUb_of_empty_census",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(thm),
                "missing `[adv A2]` Lean theorem `{thm}`"
            );
        }
    }

    #[test]
    fn test_b3_multi_item_batch_coordinate_isolation_and_callee_closure() {
        let reg = PropertyRegistry::all_verified();
        let caller = parse_lean_captured_mir_def(LEAN_PROTOTYPE_SRC, "witnessDerefAliasBody")
            .expect("parse witnessDerefAliasBody");
        let callee = parse_lean_captured_mir_def(LEAN_PROTOTYPE_SRC, "witnessCalleeStorageBody")
            .expect("parse witnessCalleeStorageBody");
        let caller_discharged = parse_lean_expected_fault_site_list(
            LEAN_PROTOTYPE_SRC,
            "witnessDerefAliasExpectedCensus",
        );
        let callee_expected = parse_lean_expected_fault_site_list(
            LEAN_PROTOTYPE_SRC,
            "witnessCalleeStorageExpectedCensus",
        );
        assert_eq!(census_mir_fault_sites(&callee), callee_expected);
        assert_eq!(
            census_lean_mir_module(&witness_as_strict_module("witnessCalleeStorageBody"))
                .expect("strict scan of witnessCalleeStorageBody"),
            callee_expected
        );
        let closure = CalleeClosure {
            inline_callees: vec![callee.def_path.clone()],
            external_callees: Vec::new(),
            allow_unresolved_indirect_calls: false,
        };
        let item = ItemCoverageInput::from_body;

        // 1. Rust mirror of `witnessCalleeMask_append_masks_batch_rejects`: every callee
        //    site collides with a caller site, so shared-list composition is `Verified`
        //    without a single callee obligation...
        assert!(callee_expected
            .iter()
            .all(|s| caller_discharged.contains(s)));
        let combined: Vec<FaultSite> = census_mir_fault_sites(&caller)
            .into_iter()
            .chain(callee_expected.iter().copied())
            .collect();
        assert_eq!(
            reconcile_obligation_coverage(&combined, &caller_discharged, &reg),
            CoverageVerdict::Verified
        );
        // ...while the per-body batch pinpoints every unmapped callee site.
        let masked = reconcile_multi_item_coverage(
            &[
                item(caller.clone(), caller_discharged.clone()),
                item(callee.clone(), Vec::new()),
            ],
            &closure,
            &reg,
        );
        match &masked {
            MultiItemCoverageVerdict::UnknownUnmappedFaultSite { failed_items, .. } => {
                assert_eq!(failed_items.len(), 1);
                assert_eq!(failed_items[0].0, "proto::witness_callee_storage");
                match &failed_items[0].1 {
                    CoverageVerdict::UnknownUnmappedFaultSite { missing_sites, .. } => {
                        assert_eq!(missing_sites, &callee_expected);
                    }
                    CoverageVerdict::Verified => panic!("callee must not verify"),
                }
            }
            MultiItemCoverageVerdict::Verified => {
                panic!("caller obligations must never mask callee sites")
            }
        }
        let full_batch = [
            item(caller.clone(), caller_discharged.clone()),
            item(callee.clone(), callee_expected.clone()),
        ];
        assert_eq!(
            reconcile_multi_item_coverage(&full_batch, &closure, &reg),
            MultiItemCoverageVerdict::Verified
        );
        // Registry gating still applies per item.
        let downgraded = PropertyRegistry::all_verified().with_status(
            MirFaultClass::StorageLiveProtected,
            PropertyStatus::UnemittedGap,
        );
        assert!(!reconcile_multi_item_coverage(&full_batch, &closure, &downgraded).is_verified());

        // 2. Census recomputation: the `[adv A2]` API accepted `census: vec![]` for any
        //    body; an item now always carries its body, so empty obligations fail.
        assert!(!reconcile_multi_item_coverage(
            &[item(caller.clone(), Vec::new())],
            &CalleeClosure::default(),
            &reg
        )
        .is_verified());

        // 3. Missing inline callee: the subject alone cannot verify while an inline callee
        //    body (which can become `activeCallee`) was never reconciled.
        let missing_callee = reconcile_multi_item_coverage(
            &[item(caller.clone(), caller_discharged.clone())],
            &closure,
            &reg,
        );
        assert!(
            missing_callee
                .reasons()
                .iter()
                .any(|r| r
                    .contains("inline callee `proto::witness_callee_storage` has no batch item"))
        );

        // 4. Mislabeled item: the label must equal the body's def_path.
        let mut mislabeled = item(callee.clone(), callee_expected.clone());
        mislabeled.def_path = String::from("proto::some_other_item");
        let mislabeled_verdict = reconcile_multi_item_coverage(
            &[item(caller.clone(), caller_discharged.clone()), mislabeled],
            &CalleeClosure::default(),
            &reg,
        );
        assert!(mislabeled_verdict
            .reasons()
            .iter()
            .any(|r| r.contains("does not match its body def_path")));

        // 5. A callee cannot be declared both inline and external.
        let contradictory = CalleeClosure {
            inline_callees: vec![callee.def_path.clone()],
            external_callees: vec![callee.def_path.clone()],
            allow_unresolved_indirect_calls: false,
        };
        assert!(!reconcile_multi_item_coverage(&full_batch, &contradictory, &reg).is_verified());

        // 6. Direct-callee classification: `witnessCallArgBlindBody` calls
        //    `proto::callee_u32`, which must be a batch item or a declared external callee.
        let call_body = parse_lean_captured_mir_def(LEAN_PROTOTYPE_SRC, "witnessCallArgBlindBody")
            .expect("parse witnessCallArgBlindBody");
        assert_eq!(
            direct_callee_def_paths(&call_body),
            vec![String::from("proto::callee_u32")]
        );
        let call_discharged = census_mir_fault_sites(&call_body);
        let call_items = [item(call_body.clone(), call_discharged.clone())];
        let unclassified =
            reconcile_multi_item_coverage(&call_items, &CalleeClosure::default(), &reg);
        assert!(unclassified
            .reasons()
            .iter()
            .any(|r| r.contains("direct callee `proto::callee_u32` is neither")));
        let external = CalleeClosure {
            inline_callees: Vec::new(),
            external_callees: vec![String::from("proto::callee_u32")],
            allow_unresolved_indirect_calls: false,
        };
        assert_eq!(
            reconcile_multi_item_coverage(&call_items, &external, &reg),
            MultiItemCoverageVerdict::Verified
        );
        // Natively modeled intrinsics need no classification.
        let intrinsic_body = ProtoMirBody {
            def_path: String::from("proto::calls_unreachable"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("core::intrinsics::unreachable"),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: None,
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        let intrinsic_census = census_mir_fault_sites(&intrinsic_body);
        assert!(intrinsic_census
            .iter()
            .any(|s| s.fault_class == MirFaultClass::UnreachableTerminator));
        assert_eq!(
            reconcile_multi_item_coverage(
                &[item(intrinsic_body, intrinsic_census)],
                &CalleeClosure::default(),
                &reg
            ),
            MultiItemCoverageVerdict::Verified
        );

        // 7. Lean-module items go through the strict grammar and are labeled with the
        //    parsed `defPath`; a module failing the grammar never enters a batch.
        let strict_src = witness_as_strict_module("witnessCalleeStorageBody");
        let lean_item = ItemCoverageInput::from_lean_module(&strict_src, callee_expected.clone())
            .expect("strict module item");
        assert_eq!(lean_item.def_path, "proto::witness_callee_storage");
        assert_eq!(lean_item.body, callee);
        let unclosed = strict_src.replace("end Mir.Witness.item", "");
        assert!(ItemCoverageInput::from_lean_module(&unclosed, Vec::new()).is_err());
        let smuggled = strict_src.replace(
            "def body : CapturedMir :=",
            "def body : CapturedMir := evil\ndef body2 : CapturedMir :=",
        );
        assert!(ItemCoverageInput::from_lean_module(&smuggled, Vec::new()).is_err());

        // 8. The kernel-checked Lean counterparts exist.
        for thm in [
            "theorem reconcileCoverageBatch_iff",
            "theorem stepMirFn_exposesUb_in_batch_discharged",
            "theorem reconcileCoverageBatch_mono",
            "theorem witnessCalleeMask_append_masks_batch_rejects",
            "theorem witnessCalleeStorage_masked_site_live",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(thm),
                "missing `[adv B3]` Lean theorem `{thm}`"
            );
        }
    }

    #[test]
    fn test_a3_callee_closure_intrinsics_dialect_and_instantiate_invariance() {
        let reg = PropertyRegistry::all_verified();
        let item = ItemCoverageInput::from_body;

        // 1. Zero-fault native `RustIntrinsicKind` intrinsics (`wrapping_add`, `ctpop`, `ub_checks`,
        //    etc.) on a converging `Call` (`target = Some(1)`) are modeled inline by
        //    `evalDirectRustIntrinsic?` in `Trusted.MirSemantics` and MUST reconcile as `Verified`
        //    under `CalleeClosure::default()`, even though `census_callee_def_path_fault_classes`
        //    returns `[]` for them!
        for zero_fault_intrinsic in [
            "core::intrinsics::ub_checks",
            "core::intrinsics::ctlz",
            "core::intrinsics::cttz",
            "core::intrinsics::ctpop",
            "core::intrinsics::bswap",
            "core::intrinsics::bitreverse",
            "core::intrinsics::wrapping_add",
            "core::intrinsics::wrapping_sub",
            "core::intrinsics::wrapping_mul",
            "core::intrinsics::saturating_add",
            "core::intrinsics::saturating_sub",
            "core::intrinsics::three_way_compare",
        ] {
            assert!(
                census_callee_def_path_fault_classes(zero_fault_intrinsic).is_empty(),
                "{zero_fault_intrinsic}"
            );
            assert!(
                is_natively_modeled_converging_call_callee(zero_fault_intrinsic),
                "{zero_fault_intrinsic}"
            );
            let body = ProtoMirBody {
                def_path: String::from("proto::calls_zero_fault_intrinsic"),
                basic_blocks: vec![
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                            func: ProtoOperand::const_fn(zero_fault_intrinsic),
                            args: Vec::new(),
                            destination: ProtoPlace::local(0),
                            target: Some(1),
                            unwind: ProtoUnwindAction::Continue,
                        }),
                        is_cleanup: false,
                    },
                    ProtoBasicBlock {
                        statements: Vec::new(),
                        terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                        is_cleanup: false,
                    },
                ],
            };
            let census = census_mir_fault_sites(&body);
            assert_eq!(
                reconcile_multi_item_coverage(&[item(body, census)], &CalleeClosure::default(), &reg),
                MultiItemCoverageVerdict::Verified,
                "zero-fault native intrinsic `{zero_fault_intrinsic}` must be accepted on converging Call"
            );
        }

        // 2. Diverging `Call` (`target = None`) to aborting/unwinding panic hooks is natively
        //    modeled in `Terminators.lean:3230-3239`, whereas a diverging `Call` to a converging-only
        //    intrinsic (`core::intrinsics::unchecked_add`) or a `TailCall` to an intrinsic falls
        //    through to `MirStepNode.extCall` and MUST fail closed unless declared external/inline!
        for panic_hook in [
            "core::panicking::panic",
            "core::panicking::panic_fmt",
            "core::panicking::panic_nounwind",
            "core::intrinsics::abort",
            "core::panicking::panic_const::panic_const_add_overflow",
        ] {
            let div_panic = ProtoMirBody {
                def_path: String::from("proto::diverging_panic"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                        func: ProtoOperand::const_fn(panic_hook),
                        args: Vec::new(),
                        destination: ProtoPlace::local(0),
                        target: None,
                        unwind: ProtoUnwindAction::Continue,
                    }),
                    is_cleanup: false,
                }],
            };
            let census = census_mir_fault_sites(&div_panic);
            assert_eq!(
                reconcile_multi_item_coverage(
                    &[item(div_panic, census)],
                    &CalleeClosure::default(),
                    &reg
                ),
                MultiItemCoverageVerdict::Verified,
                "diverging panic hook `{panic_hook}` is natively modeled"
            );
        }

        let div_unchecked_add = ProtoMirBody {
            def_path: String::from("proto::div_unchecked_add"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("core::intrinsics::unchecked_add"),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: None,
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        let div_ua_census = census_mir_fault_sites(&div_unchecked_add);
        assert!(!reconcile_multi_item_coverage(
            &[item(div_unchecked_add, div_ua_census)],
            &CalleeClosure::default(),
            &reg
        )
        .is_verified());

        let tail_call_intrinsic = ProtoMirBody {
            def_path: String::from("proto::tail_call_intrinsic"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::TailCall {
                    func: ProtoOperand::const_fn("core::intrinsics::unchecked_add"),
                    args: Vec::new(),
                }),
                is_cleanup: false,
            }],
        };
        let tc_census = census_mir_fault_sites(&tail_call_intrinsic);
        assert!(!reconcile_multi_item_coverage(
            &[item(tail_call_intrinsic, tc_census)],
            &CalleeClosure::default(),
            &reg
        )
        .is_verified());

        // 3. Direct call to a batch item (e.g. recursive self-call or a second batch item)
        //    that is NOT in `closure.inline_callees` or `closure.external_callees` MUST fail
        //    closed, because `initMachineStateWithCallees` only links `closure.inline_callees`.
        let recursive_self = ProtoMirBody {
            def_path: String::from("proto::rec_self"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("proto::rec_self"),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        let rec_census = census_mir_fault_sites(&recursive_self);
        assert!(!reconcile_multi_item_coverage(
            &[item(recursive_self.clone(), rec_census.clone())],
            &CalleeClosure::default(),
            &reg
        )
        .is_verified());
        let rec_inline = CalleeClosure {
            inline_callees: vec![String::from("proto::rec_self")],
            external_callees: Vec::new(),
            allow_unresolved_indirect_calls: false,
        };
        assert_eq!(
            reconcile_multi_item_coverage(&[item(recursive_self, rec_census)], &rec_inline, &reg),
            MultiItemCoverageVerdict::Verified
        );

        // 4. Function items reified via `CastKind::PointerCoercion("ReifyFnPointer")`
        //    (`reified_fn_def_paths`) must be classified in `CalleeClosure`.
        let reified_body = ProtoMirBody {
            def_path: String::from("proto::reifies_fn"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: vec![ProtoStatement::new(ProtoStatementKind::Assign(
                    ProtoPlace::local(1),
                    ProtoRvalue::Cast(
                        ProtoCastKind::PointerCoercion(String::from("ReifyFnPointer")),
                        ProtoOperand::const_fn("proto::hidden_target"),
                    ),
                ))],
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                is_cleanup: false,
            }],
        };
        assert_eq!(
            reified_fn_def_paths(&reified_body),
            vec![String::from("proto::hidden_target")]
        );
        let reified_census = census_mir_fault_sites(&reified_body);
        assert!(!reconcile_multi_item_coverage(
            &[item(reified_body.clone(), reified_census.clone())],
            &CalleeClosure::default(),
            &reg
        )
        .is_verified());
        let reified_ext = CalleeClosure {
            inline_callees: Vec::new(),
            external_callees: vec![String::from("proto::hidden_target")],
            allow_unresolved_indirect_calls: false,
        };
        assert_eq!(
            reconcile_multi_item_coverage(
                &[item(reified_body, reified_census)],
                &reified_ext,
                &reg
            ),
            MultiItemCoverageVerdict::Verified
        );

        // 5. Dialect pinning in `import`, `: CapturedMir` type ascription, and single top-level
        //    `namespace` enforcement in `check_strict_mir_module_grammar`.
        let unreachable_block = single_terminator_block("TerminatorKind.unreachable");
        let baseline = strict_module_with_blocks("", &unreachable_block);
        let evil_trusted_import = baseline.replace("import Trusted", "import Trusted.Evil");
        assert!(census_lean_mir_module(&evil_trusted_import).is_err());
        let wrong_dialect_import =
            baseline.replace("import Trusted", "import Trusted.Rustc.V2026_08_01.MirAst");
        assert!(census_lean_mir_module(&wrong_dialect_import).is_err());
        let evil_captured_mir_ty =
            baseline.replace("def body : CapturedMir", "def body : Evil.CapturedMir");
        assert!(census_lean_mir_module(&evil_captured_mir_ty).is_err());
        assert!(census_lean_mir_def(&evil_captured_mir_ty, "body").is_err());
        let wrong_dialect_captured_mir_ty = baseline.replace(
            "def body : CapturedMir",
            "def body : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir",
        );
        assert!(census_lean_mir_module(&wrong_dialect_captured_mir_ty).is_err());
        let two_top_namespaces = format!(
            "import Trusted\nnamespace First\nend First\n{}",
            baseline.trim_start_matches("import Trusted\n")
        );
        assert!(census_lean_mir_module(&two_top_namespaces).is_err());

        // 6. Verify all new `[adv A3]` Lean theorems exist in `theory/Anneal/FaultSiteCensus.lean`.
        for thm in [
            "theorem validMirPc_applyUnwindAction_top",
            "theorem validMirPc_resumeExternalCall",
            "theorem validMirPc_resumeExternalDivergingCall",
            "theorem resumeExternalTailCall_top_ne_running",
            "theorem validMirPc_unwindFromCallStack",
            "theorem validMirPc_resumeExternalTailCall",
            "theorem mirStepsWithExtCalls_preserves_validMirPc",
            "theorem initMachineState_mirStepsWithExtCalls_exposesUb_in_census",
            "theorem initMachineState_mirStepsWithExtCalls_reconciled_safety",
            "theorem reconcileCoverageBatch_nil",
            "theorem censusStmtFaultClasses_instantiate",
            "theorem censusTerminatorFaultClasses_instantiate",
            "theorem censusMirBodyFaultSites_instantiate",
            "theorem cfgTargetsInBounds_instantiate",
            "theorem validMirPc_instantiate_iff",
            "theorem stepMirFn_exposesUb_in_batch_discharged_instantiated",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(thm),
                "missing `[adv A3]` Lean theorem `{thm}`"
            );
        }
    }

    /// `[adv B4]` The trusted MIR semantics read by the native-callee parity test.
    const TRUSTED_TERMINATORS_SRC: &str = include_str!(
        "../../../trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean"
    );

    /// `[adv B4]` String literals compared by `stringEq` inside the body of the trusted
    /// definition `def <def_name>`.
    fn trusted_string_eq_literals(def_name: &str) -> BTreeSet<String> {
        let header = format!("def {def_name} ");
        let start = TRUSTED_TERMINATORS_SRC
            .find(&header)
            .unwrap_or_else(|| panic!("missing trusted `{header}`"))
            + header.len();
        let rest = &TRUSTED_TERMINATORS_SRC[start..];
        let end = ["\n/--", "\ndef ", "\n@[", "\ntheorem "]
            .iter()
            .filter_map(|marker| rest.find(marker))
            .min()
            .unwrap_or(rest.len());
        let body = &rest[..end];
        let mut out = BTreeSet::new();
        let mut cursor = 0;
        while let Some(pos) = body[cursor..].find("stringEq ") {
            let after = &body[cursor + pos..];
            let open = after.find('"').expect("stringEq literal");
            let close = after[open + 1..].find('"').expect("closing quote") + open + 1;
            out.insert(after[open + 1..close].to_string());
            cursor += pos + close + 1;
        }
        out
    }

    #[test]
    fn test_b4_native_callee_lists_match_trusted_semantics() {
        // `[adv B4]`: `[adv A3]` hard-coded which callees `evalTerminator` models natively.
        // A stale entry would let `reconcile_multi_item_coverage` treat an external call as
        // native (fail-open), so both lists are pinned to the trusted Lean source.
        let intrinsics = trusted_string_eq_literals("classifyRustIntrinsic?");
        assert_eq!(
            intrinsics.len(),
            25,
            "classifyRustIntrinsic? arms: {intrinsics:?}"
        );
        let exact_div = trusted_string_eq_literals("isDirectExactDivTarget");
        assert_eq!(
            exact_div,
            BTreeSet::from([String::from("core::intrinsics::exact_div")])
        );
        let mut converging: BTreeSet<String> = intrinsics
            .iter()
            .filter(|p| p.as_str() != "core::intrinsics::const_eval_select")
            .cloned()
            .collect();
        converging.extend(exact_div);
        let rust_converging: BTreeSet<String> = NATIVE_CONVERGING_CALL_CALLEES
            .iter()
            .map(|p| p.to_string())
            .collect();
        assert_eq!(rust_converging.len(), NATIVE_CONVERGING_CALL_CALLEES.len());
        assert_eq!(rust_converging, converging);

        let diverging: BTreeSet<String> = [
            "isUnreachableCallTarget",
            "isAbortingPanicDefPath",
            "isUnwindingPanicDefPath",
        ]
        .iter()
        .flat_map(|d| trusted_string_eq_literals(d))
        .collect();
        let rust_diverging: BTreeSet<String> = NATIVE_DIVERGING_CALL_CALLEES
            .iter()
            .map(|p| p.to_string())
            .collect();
        assert_eq!(rust_diverging.len(), NATIVE_DIVERGING_CALL_CALLEES.len());
        assert_eq!(rust_diverging, diverging);

        // `const_eval_select` is never native by itself, and `std::intrinsics::*` paths
        // are ordinary callees.
        assert!(!is_natively_modeled_converging_call_callee(
            "core::intrinsics::const_eval_select"
        ));
        assert!(!is_natively_modeled_converging_call_callee(
            "std::intrinsics::wrapping_add"
        ));
        assert!(!is_natively_modeled_diverging_call_callee(
            "core::intrinsics::wrapping_add"
        ));

        // The kernel-checked `[adv B4]` Lean counterparts exist.
        for thm in [
            "theorem stepMirFn_extCall_cont_preserves_validMirPc",
            "inductive MirStepsTop",
            "theorem mirStepsTop_of_mirStepsIntra",
            "theorem mirStepsTop_preserves_validMirPc",
            "theorem initMachineState_mirStepsTop_exposesUb_in_census",
            "theorem initMachineState_mirStepsTop_reconciled_safety",
            "theorem witnessExtCall_mirStepsTop_nonvacuous",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(thm),
                "missing `[adv B4]` Lean declaration `{thm}`"
            );
        }
    }

    #[test]
    fn test_a4_interproc_trace_param_call_const_and_batch_subject_external_conflict() {
        let reg = PropertyRegistry::all_verified();

        // 1. `ProtoMirBody::has_no_param_call_const` mirrors `bodyHasNoParamCallConst` 1-to-1,
        //    and `reconcile_multi_item_coverage` fails closed when a batch item has a
        //    `RigidTy.param`-typed `Call` or `TailCall` `func` constant operand.
        let param_call_body = ProtoMirBody {
            def_path: String::from("proto::generic_caller"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::Constant(ProtoConstValue::ParamTypedConst(Box::new(
                        ProtoConstValue::ZeroSized { fn_def_path: None },
                    ))),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        assert!(!param_call_body.has_no_param_call_const());
        let param_call_census = census_mir_fault_sites(&param_call_body);
        let param_verdict = reconcile_multi_item_coverage(
            &[ItemCoverageInput {
                def_path: String::from("proto::generic_caller"),
                body: param_call_body,
                discharged: param_call_census,
            }],
            &CalleeClosure::default(),
            &reg,
        );
        assert!(
            !param_verdict.is_verified()
                && param_verdict
                    .reasons()
                    .iter()
                    .any(|r| r.contains("bodyHasNoParamCallConst")),
            "expected fail-closed rejection on RigidTy.param Call func constant: {param_verdict:?}"
        );

        // 2. A batch item (e.g. recursive subject `items[0]`) declared in `closure.external_callees`
        //    while omitted from `closure.inline_callees` must be rejected fail-closed.
        let rec_body = ProtoMirBody {
            def_path: String::from("proto::recursive_subject"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("proto::recursive_subject"),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        assert!(rec_body.has_no_param_call_const());
        let rec_census = census_mir_fault_sites(&rec_body);
        let ext_subject_verdict = reconcile_multi_item_coverage(
            &[ItemCoverageInput {
                def_path: String::from("proto::recursive_subject"),
                body: rec_body.clone(),
                discharged: rec_census.clone(),
            }],
            &CalleeClosure {
                inline_callees: Vec::new(),
                external_callees: vec![String::from("proto::recursive_subject")],
                allow_unresolved_indirect_calls: false,
            },
            &reg,
        );
        assert!(
            !ext_subject_verdict.is_verified()
                && ext_subject_verdict
                    .reasons()
                    .iter()
                    .any(|r| r.contains("is declared in `closure.external_callees`")),
            "expected fail-closed rejection when batch item is in external_callees: {ext_subject_verdict:?}"
        );

        // Declaring the recursive subject in `closure.inline_callees` succeeds.
        let inline_subject_verdict = reconcile_multi_item_coverage(
            &[ItemCoverageInput {
                def_path: String::from("proto::recursive_subject"),
                body: rec_body,
                discharged: rec_census,
            }],
            &CalleeClosure {
                inline_callees: vec![String::from("proto::recursive_subject")],
                external_callees: Vec::new(),
                allow_unresolved_indirect_calls: false,
            },
            &reg,
        );
        assert!(inline_subject_verdict.is_verified());

        // 3. `reified_fn_def_paths` also captures `ClosureFnPointer` coercions.
        let closure_coercion_body = ProtoMirBody {
            def_path: String::from("proto::closure_coercer"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: vec![ProtoStatement::new(ProtoStatementKind::Assign(
                    ProtoPlace::local(0),
                    ProtoRvalue::Cast(
                        ProtoCastKind::PointerCoercion(String::from("ClosureFnPointer(Normal)")),
                        ProtoOperand::const_fn("proto::non_capturing_closure"),
                    ),
                ))],
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                is_cleanup: false,
            }],
        };
        assert_eq!(
            reified_fn_def_paths(&closure_coercion_body),
            vec![String::from("proto::non_capturing_closure")]
        );

        // 4. All `[adv A4]` Lean interprocedural multi-step trace declarations exist.
        for decl in [
            "def ValidBatchCallerFrame",
            "def ValidBatchCallStack",
            "def ValidInterprocState",
            "theorem validInterprocState_initMachineState",
            "theorem validInterprocState_unwindFromCallStack",
            "inductive MirStepsInterproc",
            "theorem mirStepsInterproc_preserves_validInterprocState",
            "theorem initMachineState_mirStepsInterproc_batch_reconciled_safety",
            "theorem witnessInterproc_call_and_return_nonvacuous",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(decl),
                "missing `[adv A4]` Lean declaration `{decl}`"
            );
        }
    }

    /// `[adv ep1-B1]` Verify-time callee links are scanned with the Lean lexer:
    /// commented-out or string-embedded `externalSpecCallContract` / `import
    /// Obligations.*` text can never add an external callee, and the scanner fails
    /// closed on lexer errors. Also pins the strict-vs-lenient MIR body parsers and
    /// the `[adv ep1-B1]` cast/aggregate census classes declared in the Lean source.
    #[test]
    fn test_ep1_b1_obligations_link_scanner_strict_body_and_cast_census_lockstep() {
        let src = "import Trusted\nimport Obligations.Crate.a\n\
                   -- import Obligations.Crate.evil\n\
                   /- externalSpecCallContract \"evil::x\"\nimport Obligations.Crate.evil2 -/\n\n\
                   def c : MirCallContract :=\n  externalSpecCallContract\n    \"crate::ext\"\n    \
                   Mir.Crate.ext_spec.body\n    (fun _ => True)\n    (fun _ _ => True)\n\n\
                   def s : String := \"externalSpecCallContract \\\"evil::y\\\"\"\n\
                   def claim := { body := Mir.Crate.item.body.instantiate t }\n";
        let links = scan_obligations_callee_links(src).expect("scan obligations");
        assert_eq!(links.external_spec_targets, vec![String::from("crate::ext")]);
        assert_eq!(links.imported_obligation_suffixes, vec![String::from("Crate.a")]);
        assert!(links.referenced_mir_bodies.iter().any(|s| s == "Crate.item"));
        assert!(links.referenced_mir_bodies.iter().any(|s| s == "Crate.ext_spec"));
        assert!(!links.referenced_mir_bodies.iter().any(|s| s.contains("evil")));
        assert!(scan_obligations_callee_links("def x := 1\n/- unterminated").is_err());

        // The strict module parser rejects constructor shadowing that the lenient
        // named-def parser cannot see.
        let module = witness_as_strict_module("witnessPureNoopBody");
        assert!(parse_lean_mir_module_body_strict(&module).is_ok());
        let shadowed = module.replacen(
            "def body : CapturedMir :=",
            "def StatementKind.nop : Nat := 0\ndef body : CapturedMir :=",
            1,
        );
        assert_ne!(shadowed, module);
        assert!(parse_lean_captured_mir_def(&shadowed, "body").is_ok());
        assert!(parse_lean_mir_module_body_strict(&shadowed).is_err());
        assert!(census_lean_mir_module(&shadowed).is_err());
        // Only real `ContractRole` constructors are accepted.
        for (role, ok) in [
            ("ContractRole.model", true),
            ("(ContractRole.requires \"demo::f\")", true),
            ("(ContractRole.externalSpec \"demo::f\")", true),
            ("ContractRole.precondition", false),
        ] {
            let with_role = module.replacen("role := ContractRole.subject", &format!("role := {role}"), 1);
            assert_ne!(with_role, module);
            assert_eq!(parse_lean_mir_module_body_strict(&with_role).is_ok(), ok, "{role}");
        }

        // Lean/Rust lockstep for the cast and aggregate classes added in this pass.
        for decl in [
            "| .pointerExposeProvenance => [.ptrDerefInvalid, .scalarNicheInvalid]",
            "| .pointerWithExposedProvenance => [.scalarNicheInvalid]",
            "| .pointerCoercion \"MutToConstPointer\" => [.ptrDerefInvalid, .scalarNicheInvalid]",
            "| .adt _ _ (some _) => [.scalarNicheInvalid]",
            "| .rawPtr _ _ => [.ptrDerefInvalid, .scalarNicheInvalid]",
            "else ops.flatMap censusOperandFaultClasses ++ censusAggregateKindFaultClasses kind",
            "theorem evalRvalue_cast_ub_cause",
            "theorem evalRvalue_aggregate_ub_cause",
            "theorem evalRvalue_cast_own_ub_witnesses",
            "theorem evalOperands_ub_implies_mem_censusOperands",
            "theorem evalRvalue_repeat_ub_iff",
            "theorem evalRvalue_unary_neg_ub_iff",
            "theorem evalRvalue_use_ub_cause",
            "theorem evalRvalue_unaryOp_ub_cause",
            "theorem evalRvalue_binaryOp_ub_cause",
            "theorem evalRvalue_ub_implies_mem_censusRvalue",
            "theorem evalStmt_assign_rvalue_ub_justified",
            "theorem evalStmt_assume_operand_ub_justified",
            "theorem evalTerminator_switchInt_discr_ub_justified",
            "theorem evalTerminator_assert_cond_ub_justified",
            "theorem evalTerminator_call_args_ub_justified",
            "theorem evalTerminator_tailCall_args_ub_justified",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(decl),
                "missing `[adv ep1-B1]` / `[adv ep1-A1]` Lean census declaration `{decl}`"
            );
        }

        // `[adv ep1-A1]` Indirect `Call` / `TailCall` through a non-constant operand
        // (e.g. a function-pointer argument `Copy(local(1))`) with an empty
        // `CalleeClosure` fails closed in `reconcile_multi_item_coverage`.
        for indirect_term in [
            ProtoTerminatorKind::Call {
                func: ProtoOperand::Copy(ProtoPlace::local(1)),
                args: Vec::new(),
                destination: ProtoPlace::local(0),
                target: Some(0),
                unwind: ProtoUnwindAction::Continue,
            },
            ProtoTerminatorKind::Call {
                func: ProtoOperand::Copy(ProtoPlace::local(1)),
                args: Vec::new(),
                destination: ProtoPlace::local(0),
                target: None,
                unwind: ProtoUnwindAction::Continue,
            },
            ProtoTerminatorKind::TailCall {
                func: ProtoOperand::Move(ProtoPlace::local(1)),
                args: Vec::new(),
            },
        ] {
            let indirect_body = ProtoMirBody {
                def_path: String::from("proto::indirect_caller"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(indirect_term),
                    is_cleanup: false,
                }],
            };
            let indirect_census = census_mir_fault_sites(&indirect_body);
            let indirect_verdict = reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(indirect_body.clone(), indirect_census.clone())],
                &CalleeClosure::default(),
                &PropertyRegistry::all_verified(),
            );
            assert!(
                !indirect_verdict.is_verified()
                    && indirect_verdict
                        .reasons()
                        .iter()
                        .any(|r| r.contains("indirect") && r.contains("CalleeClosure")),
                "expected indirect call with empty CalleeClosure to fail closed: {indirect_verdict:?}"
            );
            assert_eq!(indirect_verdict.status_code(), "UNKNOWN(UNMAPPED_FAULT_SITE)");
            // `[adv ep1-B2]`: an unrelated declared callee must NOT legitimize an
            // indirect call (its run-time target is unbounded), but an assumed
            // subject's closure (`allow_unresolved_indirect_calls`) does.
            let with_external = CalleeClosure {
                inline_callees: Vec::new(),
                external_callees: vec![String::from("proto::ext_fn_ptr_target")],
                allow_unresolved_indirect_calls: false,
            };
            assert!(
                !reconcile_multi_item_coverage(
                    &[ItemCoverageInput::from_body(indirect_body.clone(), indirect_census.clone())],
                    &with_external,
                    &PropertyRegistry::all_verified(),
                )
                .is_verified()
            );
            let assumed_closure = CalleeClosure {
                inline_callees: Vec::new(),
                external_callees: Vec::new(),
                allow_unresolved_indirect_calls: true,
            };
            assert!(
                reconcile_multi_item_coverage(
                    &[ItemCoverageInput::from_body(indirect_body.clone(), indirect_census)],
                    &assumed_closure,
                    &PropertyRegistry::all_verified(),
                )
                .is_verified()
            );
            // `build_batch_callee_closure` only grants the permission to assumed
            // subjects, and never through a sentinel external callee.
            let strict = crate::obligations::build_batch_callee_closure(
                &indirect_body,
                &[],
                &[String::from("proto::ext_fn_ptr_target")],
                false,
            );
            assert!(!strict.allow_unresolved_indirect_calls);
            assert_eq!(strict.external_callees, vec![String::from("proto::ext_fn_ptr_target")]);
            let assumed = crate::obligations::build_batch_callee_closure(&indirect_body, &[], &[], true);
            assert!(assumed.allow_unresolved_indirect_calls);
            assert!(assumed.external_callees.is_empty(), "{assumed:?}");
        }

        // `[adv ep1-A1]` Lexer-based `parse_obligations_default_callees` neutralizes
        // commented-out `def defaultCallees` tables and inline comments, while
        // `scan_obligations_callee_links` tracks `claim_mir_bodies` and
        // `claim_callees_bindings`.
        let ob_with_comment_trap = "-- def defaultCallees : List CapturedMir := [Mir.Evil.body]\n\
            def defaultCallees : List CapturedMir :=\n  [\n    -- inline comment\n    Mir.Crate.a.body,\n    Mir.Crate.b.body\n  ]\n\
            def sigPre := Mir.Crate.item.body.argCount\n\
            def claim : Claim := { body := Mir.Crate.other.body, pre := True, post := True, callees := .nil }\n";
        assert_eq!(
            parse_obligations_default_callees(ob_with_comment_trap),
            Ok(vec![String::from("Crate.a"), String::from("Crate.b")])
        );
        let trap_links = scan_obligations_callee_links(ob_with_comment_trap).expect("scan trap");
        assert!(trap_links.referenced_mir_bodies.contains(&String::from("Crate.item")));
        assert_eq!(trap_links.claim_mir_bodies, vec![String::from("Crate.other")]);
        assert_eq!(trap_links.claim_callees_bindings, vec![String::from(".nil")]);
    }

    /// `[adv ep1-B1]` The independent obligation-side emitter
    /// (`obligations::emit_obligation_fault_sites_for_body`) must agree with the
    /// census site-for-site on randomized retag-stripped bodies and on every
    /// construct whose classes changed in `[adv ep1-B1]`, so a census rule change
    /// can never silently leave the emitter behind (or vice versa).
    #[test]
    fn test_ep1_b1_obligation_emitter_matches_census_on_randomized_bodies() {
        let mut rng = FuzzRng(0x5EED_0B11_6A71_00E5);
        for case in 0..600 {
            let ir = fuzz_captured_mir(&mut rng);
            let proto = ProtoMirBody::from_ir_captured_mir(&ir, true);
            let census: BTreeSet<FaultSite> =
                census_mir_fault_sites(&proto).into_iter().collect();
            let emitted: BTreeSet<FaultSite> =
                crate::obligations::emit_obligation_fault_sites_for_body(&proto)
                    .into_iter()
                    .collect();
            assert_eq!(census, emitted, "case {case}: emitter/census divergence");
        }

        let constant_operand = || ProtoOperand::const_u32(0);
        let rvalues = vec![
            ProtoRvalue::Cast(
                ProtoCastKind::PointerCoercion(String::from("MutToConstPointer")),
                constant_operand(),
            ),
            ProtoRvalue::Cast(ProtoCastKind::PointerExposeProvenance, constant_operand()),
            ProtoRvalue::Cast(ProtoCastKind::PointerWithExposedProvenance, constant_operand()),
            ProtoRvalue::Cast(ProtoCastKind::FloatToInt, constant_operand()),
            ProtoRvalue::Aggregate(
                ProtoAggregateKind::Adt(String::from("demo::U"), 0, Some(0)),
                vec![constant_operand()],
            ),
            ProtoRvalue::Aggregate(ProtoAggregateKind::RawPtr(true), vec![constant_operand()]),
            ProtoRvalue::Aggregate(
                ProtoAggregateKind::Adt(String::from("demo::S"), 0, None),
                vec![constant_operand()],
            ),
        ];
        for rv in rvalues {
            let body = ProtoMirBody {
                def_path: String::from("demo::ep1_b1"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: vec![ProtoStatement::new(ProtoStatementKind::Assign(
                        ProtoPlace::local(0),
                        rv.clone(),
                    ))],
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                    is_cleanup: false,
                }],
            };
            let census: BTreeSet<FaultSite> = census_mir_fault_sites(&body).into_iter().collect();
            let emitted: BTreeSet<FaultSite> =
                crate::obligations::emit_obligation_fault_sites_for_body(&body)
                    .into_iter()
                    .collect();
            assert_eq!(census, emitted, "{rv:?}");
            let own_rvalue_classes: BTreeSet<MirFaultClass> = census
                .iter()
                .filter(|s| s.stmt_idx == 0)
                .map(|s| s.fault_class)
                .filter(|c| {
                    !matches!(
                        c,
                        MirFaultClass::StorageLiveProtected | MirFaultClass::TreeBorrowsViolation
                    )
                })
                .collect();
            let expect_own = !matches!(
                rv,
                ProtoRvalue::Cast(ProtoCastKind::FloatToInt, _)
                    | ProtoRvalue::Aggregate(ProtoAggregateKind::Adt(_, _, None), _)
            );
            assert_eq!(!own_rvalue_classes.is_empty(), expect_own, "{rv:?}: {census:?}");
        }
    }

    /// `[adv ep1-B3]` Regression suite for `cfgTargetsInBounds` enforcement,
    /// `parse_obligations_default_callees` missing/trailing-expression rejection,
    /// recursive subject batch assembly & closure, `TraitImplEntry` override closure,
    /// and new Lean bridge theorems.
    #[test]
    fn test_ep1_b3_cfg_bounds_recursion_default_callees_and_lean_bridges() {
        let reg = PropertyRegistry::all_verified();

        // 1. Empty-`basicBlocks` and out-of-bounds target bodies fail closed in
        //    `reconcile_multi_item_coverage` (`cfgTargetsInBounds`).
        let empty_blocks = ProtoMirBody {
            def_path: String::from("proto::empty_blocks"),
            basic_blocks: Vec::new(),
        };
        assert!(!empty_blocks.cfg_targets_in_bounds());
        assert!(census_mir_fault_sites(&empty_blocks).is_empty());
        let empty_verdict = reconcile_multi_item_coverage(
            &[ItemCoverageInput::from_body(empty_blocks, Vec::new())],
            &CalleeClosure::default(),
            &reg,
        );
        assert!(
            !empty_verdict.is_verified()
                && empty_verdict
                    .reasons()
                    .iter()
                    .any(|r| r.contains("cfgTargetsInBounds")),
            "{empty_verdict:?}"
        );

        let oob_goto = ProtoMirBody {
            def_path: String::from("proto::oob_goto"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Goto(3)),
                is_cleanup: false,
            }],
        };
        assert!(!oob_goto.cfg_targets_in_bounds());
        let oob_census = census_mir_fault_sites(&oob_goto);
        let oob_verdict = reconcile_multi_item_coverage(
            &[ItemCoverageInput::from_body(oob_goto, oob_census)],
            &CalleeClosure::default(),
            &reg,
        );
        assert!(
            !oob_verdict.is_verified()
                && oob_verdict
                    .reasons()
                    .iter()
                    .any(|r| r.contains("cfgTargetsInBounds")),
            "{oob_verdict:?}"
        );

        // 2. `parse_obligations_default_callees` rejects missing/shadowed tables and
        //    trailing expressions after `.nil` / `List.nil` / `[]` / `[...]`.
        for bad_ob in [
            "namespace Obligations.Demo.f\nend Obligations.Demo.f\n",
            "abbrev defaultCallees : List CapturedMir := [Mir.Demo.leaf.body]\n",
            "private def defaultCallees : List CapturedMir := .nil\n",
            "def defaultCallees : List CapturedMir := .nil ++ [Mir.Demo.leaf.body]\n",
            "def defaultCallees : List CapturedMir := List.nil ++ [Mir.Demo.leaf.body]\n",
            "def defaultCallees : List CapturedMir := [] ++ [Mir.Demo.leaf.body]\n",
            "def defaultCallees : List CapturedMir := [Mir.Demo.fake.body].drop 1 ++ [Mir.Demo.real.body]\n",
        ] {
            assert!(
                parse_obligations_default_callees(bad_ob).is_err(),
                "expected fail-closed error for `{bad_ob}`"
            );
        }

        // 3. Recursive subject batch assembly & closure:
        //    - Unlinked recursive subject (`callee_bodies = []`, non-assumed) fails closed.
        //    - Linked recursive subject (`callee_bodies = [rec_meta.body]`) deduplicates
        //      `items` and reconciles to `Verified`.
        //    - Assumed (`#[spec(trusted)]`) recursive subject (`callee_bodies = []`,
        //      `allow_implicit_external_callees = true`) reconciles to `Verified`.
        let rec_body = ProtoMirBody {
            def_path: String::from("demo::rec_fn"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("demo::rec_fn"),
                    args: Vec::new(),
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        let rec_meta = ParsedMirModuleMetadata {
            body: rec_body.clone(),
            role: ProtoContractRole::Subject,
            trait_impls: Vec::new(),
        };
        let unlinked_rec_closure =
            crate::obligations::build_batch_callee_closure(&rec_body, &[], &[], false);
        assert!(unlinked_rec_closure.inline_callees.is_empty());
        let (unlinked_items, unlinked_extra) =
            crate::obligations::assemble_batch_items_and_check_trait_closure(
                &rec_meta,
                &[],
                &unlinked_rec_closure,
                &BTreeSet::new(),
            );
        assert!(unlinked_extra.is_empty());
        assert!(
            !reconcile_multi_item_coverage(&unlinked_items, &unlinked_rec_closure, &reg)
                .is_verified()
        );

        let linked_rec_closure = crate::obligations::build_batch_callee_closure(
            &rec_body,
            std::slice::from_ref(&rec_body),
            &[],
            false,
        );
        assert_eq!(
            linked_rec_closure.inline_callees,
            vec![String::from("demo::rec_fn")]
        );
        let (linked_items, linked_extra) =
            crate::obligations::assemble_batch_items_and_check_trait_closure(
                &rec_meta,
                std::slice::from_ref(&rec_meta),
                &linked_rec_closure,
                &BTreeSet::new(),
            );
        assert!(linked_extra.is_empty());
        assert_eq!(linked_items.len(), 1);
        assert!(
            reconcile_multi_item_coverage(&linked_items, &linked_rec_closure, &reg).is_verified()
        );

        let assumed_rec_closure =
            crate::obligations::build_batch_callee_closure(&rec_body, &[], &[], true);
        let (assumed_items, assumed_extra) =
            crate::obligations::assemble_batch_items_and_check_trait_closure(
                &rec_meta,
                &[],
                &assumed_rec_closure,
                &BTreeSet::new(),
            );
        assert!(assumed_extra.is_empty());
        assert!(
            reconcile_multi_item_coverage(&assumed_items, &assumed_rec_closure, &reg).is_verified()
        );

        // 4. `TraitImplEntry` redirecting a called default trait method to an unlinked
        //    `implPath` fails closed.
        let trait_caller = ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path: String::from("demo::calls_trait"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                        func: ProtoOperand::const_fn("demo::MyTrait::method"),
                        args: Vec::new(),
                        destination: ProtoPlace::local(0),
                        target: Some(0),
                        unwind: ProtoUnwindAction::Continue,
                    }),
                    is_cleanup: false,
                }],
            },
            role: ProtoContractRole::Subject,
            trait_impls: vec![ProtoTraitImplEntry {
                trait_method_def_path: String::from("demo::MyTrait::method"),
                impl_path: String::from("demo::<Concrete as MyTrait>::method"),
            }],
        };
        let default_trait_callee = ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path: String::from("demo::MyTrait::method"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                    is_cleanup: false,
                }],
            },
            role: ProtoContractRole::Subject,
            trait_impls: Vec::new(),
        };
        let trait_closure = crate::obligations::build_batch_callee_closure(
            &trait_caller.body,
            std::slice::from_ref(&default_trait_callee.body),
            &[],
            false,
        );
        let (_trait_items, trait_reasons) =
            crate::obligations::assemble_batch_items_and_check_trait_closure(
                &trait_caller,
                std::slice::from_ref(&default_trait_callee),
                &trait_closure,
                &BTreeSet::new(),
            );
        assert!(
            trait_reasons
                .iter()
                .any(|r| r.contains("TraitImplEntry") && r.contains("Concrete as MyTrait")),
            "{trait_reasons:?}"
        );

        // 5. Pin `[adv ep1-B3]` Lean theorems in `FaultSiteCensus.lean` and `UnsafeObligations.lean`.
        for decl in [
            "def reconcileCoverageBatchWellFormed",
            "theorem reconcileCoverageBatchWellFormed_iff",
            "theorem initMachineState_mirStepsInterproc_wellFormed_batch_safety",
            "def witnessEmptyBlocksBody",
            "theorem witnessEmptyBlocks_ub_and_wellFormed_batch_rejects",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(decl),
                "missing `[adv ep1-B3]` Lean declaration `{decl}`"
            );
        }
        const UNSAFE_OBLIGATIONS_SRC: &str =
            include_str!("../../../theory/Anneal/UnsafeObligations.lean");
        for decl in [
            "theorem evalOperand_deref_reconciled_of_obligations",
            "theorem writePlaceValue_deref_reconciled_of_obligations",
            "theorem evalStmt_offset_reconciled_of_validSliceRange",
            "theorem evalStmt_deref_load_reconciled_of_obligations",
            "theorem evalStmt_deref_store_reconciled_of_obligations",
        ] {
            assert!(
                UNSAFE_OBLIGATIONS_SRC.contains(decl),
                "missing `[adv ep1-B3]` / `[adv ep1-A3]` UnsafeObligations bridge `{decl}`"
            );
        }
        for decl in [
            "theorem evalTerminator_call_func_ub_justified",
            "theorem evalTerminator_tailCall_func_ub_justified",
        ] {
            assert!(
                LEAN_PROTOTYPE_SRC.contains(decl),
                "missing `[adv ep1-A3]` Lean declaration `{decl}`"
            );
        }
    }

    /// `[adv ep1-A3]` Regression suite for:
    /// 1. Dead-helper `.holdsOn` spoofing outside `defaultModularSpec.envAssumed` and
    ///    vacuous disjunctions inside `defaultModularSpec.envAssumed`.
    /// 2. `scan_specs_module` parsing of authored `ModularItemSpec` (`ubExceptionClaim`
    ///    sibling contracts) and `StatefulEquivItemSpec` (`refineEquivSpec Mir.<Ref>.body`),
    ///    plus fail-closed rejection of `axiom` and dead-helper `.holdsOn` in `Specs`.
    /// 3. `const_eval_select` runtime target (`args[2]`) closure for assumed subjects
    ///    (both constant `rt` and indirect `rt`).
    /// 4. Chained `TraitImplEntry` (`TraitA::m -> TraitB::m -> Concrete::m`) closure.
    #[test]
    fn test_ep1_a3_modular_env_scoping_specs_scanner_const_eval_select_and_chained_traits() {
        // 1. Dead-helper `.holdsOn` outside `defaultModularSpec` must NOT populate
        //    `referenced_callee_contracts` or `referenced_external_contract_idents`, and
        //    `True ∨ ...` inside `defaultModularSpec.envAssumed` must record an error.
        let spoofed_dead_helper_ob = "\
            import Trusted\n\
            import Mir.Demo.caller\n\
            import Obligations.Demo.leaf\n\
            namespace Obligations.Demo.caller\n\
            def unusedHelper := Obligations.Demo.leaf.defaultCallContract.holdsOn\n\
            instance (priority := low) defaultModularSpec : ModularItemSpec \"demo::caller\" where\n\
              envAssumed := fun _ => True\n\
              pre := fun _ _ => True\n\
              post := fun _ _ _ _ => True\n\
            end Obligations.Demo.caller\n";
        let spoof_links =
            scan_obligations_callee_links(spoofed_dead_helper_ob).expect("scan spoofed");
        assert_eq!(spoof_links.default_modular_spec_count, 1);
        assert!(spoof_links.default_modular_spec_errors.is_empty());
        assert!(
            spoof_links.referenced_callee_contracts.is_empty(),
            "dead helper outside `defaultModularSpec.envAssumed` must not register callee contract: {spoof_links:?}"
        );

        let vacuous_or_ob = "\
            import Trusted\n\
            import Mir.Demo.caller\n\
            import Obligations.Demo.leaf\n\
            namespace Obligations.Demo.caller\n\
            instance (priority := low) defaultModularSpec : ModularItemSpec \"demo::caller\" where\n\
              envAssumed := fun h => True ∨ Obligations.Demo.leaf.defaultCallContract.holdsOn h\n\
              pre := fun _ _ => True\n\
              post := fun _ _ _ _ => True\n\
            end Obligations.Demo.caller\n";
        let or_links = scan_obligations_callee_links(vacuous_or_ob).expect("scan vacuous or");
        assert!(
            !or_links.default_modular_spec_errors.is_empty(),
            "expected vacuous disjunction in `defaultModularSpec.envAssumed` to fail closed: {or_links:?}"
        );

        // 2. `scan_specs_module` accepts Fuchsia/Fxfs `ubExceptionClaim.callContract.holdsOn`
        //    and `WireframeDemo` `refineEquivSpec Mir.<Ref>.body`, while rejecting `axiom`
        //    and ignoring dead helpers outside `ModularItemSpec`.
        let fuchsia_style_specs = "\
            import Trusted\n\
            import Mir.Demo.caller\n\
            import Obligations.Demo.caller\n\
            import Obligations.Demo.ub_stub\n\
            namespace Specs.Demo.caller\n\
            def deadRef := Obligations.Demo.unimported.ubExceptionClaim.callContract.holdsOn\n\
            instance : ModularItemSpec \"demo::caller\" where\n\
              envAssumed := Obligations.Demo.ub_stub.ubExceptionClaim.callContract.holdsOn\n\
              pre := fun _ _ => True\n\
              post := fun _ _ _ _ => True\n\
            end Specs.Demo.caller\n";
        let sl = scan_specs_module(fuchsia_style_specs, "Demo.caller").expect("scan specs");
        assert!(sl.has_modular_spec_instance);
        assert_eq!(
            sl.referenced_modular_callee_suffixes,
            vec![String::from("Demo.ub_stub")]
        );

        let equiv_specs = "\
            import Trusted\n\
            import Mir.Demo.safe_ref\n\
            import Mir.Demo.fast_impl\n\
            import Obligations.Demo.fast_impl\n\
            namespace Specs.Demo.fast_impl\n\
            instance : StatefulEquivItemSpec \"demo::fast_impl\" :=\n\
              Obligations.Demo.fast_impl.refineEquivSpec\n\
                Mir.Demo.safe_ref.body\n\
                (fun _ _ => True)\n\
                (fun _ _ _ _ => True)\n\
            end Specs.Demo.fast_impl\n";
        let eq_sl = scan_specs_module(equiv_specs, "Demo.fast_impl").expect("scan equiv specs");
        assert!(eq_sl.has_equiv_spec_instance);
        assert_eq!(
            eq_sl.equiv_spec_body_suffix.as_deref(),
            Some("Demo.safe_ref")
        );

        let axiom_specs = "import Trusted\naxiom cheat : False\n";
        assert!(scan_specs_module(axiom_specs, "Demo.caller").is_err());

        // 3. `const_eval_select` runtime target (`args[2]`) in `direct_callee_def_paths`
        //    and `build_batch_callee_closure` for assumed subjects.
        let ces_const_rt = ProtoMirBody {
            def_path: String::from("demo::assumed_ces"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("core::intrinsics::const_eval_select"),
                    args: vec![
                        ProtoOperand::const_u32(0),
                        ProtoOperand::const_fn("demo::ct_target"),
                        ProtoOperand::const_fn("demo::rt_target"),
                    ],
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        assert_eq!(
            direct_callee_def_paths(&ces_const_rt),
            vec![String::from("demo::rt_target")]
        );
        let ces_assumed_closure =
            crate::obligations::build_batch_callee_closure(&ces_const_rt, &[], &[], true);
        assert_eq!(
            ces_assumed_closure.external_callees,
            vec![String::from("demo::rt_target")]
        );
        let ces_census = census_mir_fault_sites(&ces_const_rt);
        assert!(
            reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(ces_const_rt.clone(), ces_census.clone())],
                &ces_assumed_closure,
                &PropertyRegistry::all_verified(),
            )
            .is_verified()
        );
        let ces_strict_closure =
            crate::obligations::build_batch_callee_closure(&ces_const_rt, &[], &[], false);
        assert!(
            !reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(ces_const_rt, ces_census)],
                &ces_strict_closure,
                &PropertyRegistry::all_verified(),
            )
            .is_verified()
        );

        // 4. Chained `TraitImplEntry` (`TraitA::m -> TraitB::m -> Concrete::m`) fails
        //    closed when `TraitB::m` is linked inline in `defaultCallees` but `Concrete::m`
        //    is missing from `CalleeClosure`.
        let chain_caller = ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path: String::from("demo::chain_caller"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                        func: ProtoOperand::const_fn("demo::TraitA::m"),
                        args: Vec::new(),
                        destination: ProtoPlace::local(0),
                        target: Some(0),
                        unwind: ProtoUnwindAction::Continue,
                    }),
                    is_cleanup: false,
                }],
            },
            role: ProtoContractRole::Subject,
            trait_impls: vec![
                ProtoTraitImplEntry {
                    trait_method_def_path: String::from("demo::TraitA::m"),
                    impl_path: String::from("demo::TraitB::m"),
                },
                ProtoTraitImplEntry {
                    trait_method_def_path: String::from("demo::TraitB::m"),
                    impl_path: String::from("demo::Concrete::m"),
                },
            ],
        };
        let trait_a_meta = ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path: String::from("demo::TraitA::m"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                    is_cleanup: false,
                }],
            },
            role: ProtoContractRole::Subject,
            trait_impls: Vec::new(),
        };
        let trait_b_meta = ParsedMirModuleMetadata {
            body: ProtoMirBody {
                def_path: String::from("demo::TraitB::m"),
                basic_blocks: vec![ProtoBasicBlock {
                    statements: Vec::new(),
                    terminator: ProtoTerminator::new(ProtoTerminatorKind::Return),
                    is_cleanup: false,
                }],
            },
            role: ProtoContractRole::Subject,
            trait_impls: Vec::new(),
        };
        let chain_callees = vec![trait_a_meta, trait_b_meta];
        let chain_bodies: Vec<ProtoMirBody> = chain_callees.iter().map(|m| m.body.clone()).collect();
        let chain_closure = crate::obligations::build_batch_callee_closure(
            &chain_caller.body,
            &chain_bodies,
            &[],
            false,
        );
        let (_chain_items, chain_reasons) =
            crate::obligations::assemble_batch_items_and_check_trait_closure(
                &chain_caller,
                &chain_callees,
                &chain_closure,
                &BTreeSet::new(),
            );
        assert!(
            chain_reasons
                .iter()
                .any(|r| r.contains("TraitImplEntry") && r.contains("demo::Concrete::m")),
            "expected chained TraitImplEntry to catch unclosed `demo::Concrete::m`: {chain_reasons:?}"
        );
    }

    /// `[adv ep1-B4]` Regression suite for:
    /// 1. Zero false positives across EVERY real `examples/*/anneal/proofs/{Specs,Proof,Assumptions}/**/*.lean`
    ///    module in the repository (`scan_specs_module` and `validate_auxiliary_module_no_spec_override`).
    /// 2. Smuggled specification overrides inside `Verify/<Item>.lean`, `@[instance]` / `attribute [instance]` /
    ///    `_root_.Trusted.VerificationResult.*` / `VerificationResult.*` / type-inferred `instance := refineModularSpec`,
    ///    `Specs -> Proof` import smuggling, and trailing `|>` after `refineModularSpec` / `refineEquivSpec`.
    /// 3. `Obligations/<Item>.lean` canonical claim & helper integrity (`equivClaim.specBody`,
    ///    `modularClaim.envAssumed`, `polyCertificate`, `refineEquivSpec`, `refineModularSpec`,
    ///    `defaultCallContract` `defPath`, and trailing `|>` after `externalSpecCallContract`).
    /// 4. `const_eval_select` 2-arg malformed arity fail-closed check + 3-arg diverging native panic
    ///    runtime target + assumed-subject `ReifyFnPointer` / `TailCall` to native intrinsics.
    #[test]
    fn test_ep1_b4_production_proofs_compat_spec_smuggling_claim_integrity_and_ces_arity() {
        fn collect_lean_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
            let Ok(entries) = std::fs::read_dir(dir) else {
                return;
            };
            for entry in entries.flatten() {
                let p = entry.path();
                if p.is_dir() {
                    collect_lean_files(&p, out);
                } else if p.extension().and_then(|e| e.to_str()) == Some("lean") {
                    out.push(p);
                }
            }
        }
        fn rel_to_suffix(root: &std::path::Path, file: &std::path::Path) -> String {
            let rel = file.strip_prefix(root).expect("relative path");
            let mut comps: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().to_string())
                .collect();
            if let Some(last) = comps.last_mut()
                && let Some(stem) = last.strip_suffix(".lean")
            {
                *last = stem.to_string();
            }
            comps.join(".")
        }

        // 1. Scan EVERY real `Specs`, `Proof`, and `Assumptions` file across `examples/*`.
        let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|p| p.parent())
            .expect("repo root");
        let examples_dir = repo_root.join("examples");
        let mut scanned_specs_count = 0usize;
        let mut scanned_aux_count = 0usize;
        for entry in std::fs::read_dir(&examples_dir)
            .expect("read examples/")
            .flatten()
        {
            let proofs_dir = entry.path().join("anneal/proofs");
            if !proofs_dir.is_dir() {
                continue;
            }
            let specs_root = proofs_dir.join("Specs");
            let mut spec_files = Vec::new();
            collect_lean_files(&specs_root, &mut spec_files);
            spec_files.sort();
            for sf in &spec_files {
                let suffix = rel_to_suffix(&specs_root, sf);
                let src = std::fs::read_to_string(sf).expect("read Specs file");
                scan_specs_module(&src, &suffix).unwrap_or_else(|err| {
                    panic!("real Specs module {} failed scan_specs_module: {err}", sf.display())
                });
                validate_sibling_specs_no_subject_override(
                    &src,
                    &suffix,
                    "__nonexistent_subject_def_path__",
                )
                .unwrap_or_else(|err| {
                    panic!(
                        "real Specs module {} failed validate_sibling_specs_no_subject_override: {err}",
                        sf.display()
                    )
                });
                scanned_specs_count += 1;
            }
            for kind_dir in ["Proof", "Assumptions"] {
                let aux_root = proofs_dir.join(kind_dir);
                let mut aux_files = Vec::new();
                collect_lean_files(&aux_root, &mut aux_files);
                aux_files.sort();
                for af in &aux_files {
                    let suffix = rel_to_suffix(&aux_root, af);
                    let src = std::fs::read_to_string(af).expect("read aux file");
                    let has_matching_specs = specs_root
                        .join(af.strip_prefix(&aux_root).expect("strip aux"))
                        .is_file();
                    validate_auxiliary_module_no_spec_override(
                        &src,
                        &format!("{kind_dir}.{suffix}"),
                        &suffix,
                        has_matching_specs,
                    )
                    .unwrap_or_else(|err| {
                        panic!(
                            "real {kind_dir} module {} failed validate_auxiliary_module_no_spec_override: {err}",
                            af.display()
                        )
                    });
                    scanned_aux_count += 1;
                }
            }
        }
        assert!(
            scanned_specs_count >= 30 && scanned_aux_count >= 30,
            "expected to scan real examples/* Specs & Proof corpus, got specs={scanned_specs_count}, aux={scanned_aux_count}"
        );

        // 2. Verify-inline, `@[instance]`, `attribute [instance]`, `_root_.*`, type-inferred `instance :=`,
        //    `Specs -> Proof` import, and trailing `|>` bypasses all fail closed.
        let inline_verify_smuggle = "\
            import Trusted\n\
            import Mir.Demo.caller\n\
            import Obligations.Demo.caller\n\
            namespace Verify.Demo.caller\n\
            instance : ModularItemSpec \"demo::caller\" where\n\
              envAssumed := fun _ => True\n\
              pre := fun _ _ => True\n\
              post := fun _ _ _ _ => True\n\
            theorem verified : Trusted.VerificationResult.ModularVerificationResult Obligations.Demo.caller.modularClaim := sorry\n\
            end Verify.Demo.caller\n";
        assert!(inspect_verify_module_certificate(inline_verify_smuggle, "Demo.caller").is_err());

        for bad_aux in [
            "import Trusted\n@[instance] def sneaked : ModularItemSpec \"demo::caller\" := sorry\n",
            "import Trusted\ndef sneaked : ModularItemSpec \"demo::caller\" := sorry\nattribute [instance] sneaked\n",
            "import Trusted\ninstance : _root_.Trusted.VerificationResult.ModularItemSpec \"demo::caller\" where\n  envAssumed := fun _ => True\n  pre := fun _ _ => True\n  post := fun _ _ _ _ => True\n",
            "import Trusted\ninstance : VerificationResult.StatefulEquivItemSpec \"demo::caller\" := sorry\n",
            "import Trusted\ninstance := Obligations.Demo.caller.refineModularSpec (fun _ => True) (fun _ _ => True) (fun _ _ _ _ => True)\n",
            "import Trusted\nabbrev EvilAlias := ModularItemSpec\ninstance : EvilAlias \"demo::caller\" := sorry\n",
        ] {
            assert!(
                validate_auxiliary_module_no_spec_override(
                    bad_aux,
                    "Proof.Demo.caller",
                    "Demo.caller",
                    false,
                )
                .is_err(),
                "expected auxiliary spec-override bypass to fail closed:\n{bad_aux}"
            );
        }

        for bad_specs in [
            "import Trusted\nimport Proof.Demo.evil\nnamespace Specs.Demo.caller\nend Specs.Demo.caller\n",
            "import Trusted\nimport Obligations.Demo.caller\nnamespace Specs.Demo.caller\n@[instance] def sneaked : ModularItemSpec \"demo::caller\" := sorry\nend Specs.Demo.caller\n",
            "import Trusted\nimport Obligations.Demo.caller\nnamespace Specs.Demo.caller\ninstance := Obligations.Demo.caller.refineModularSpec (fun _ => True) (fun _ _ => True) (fun _ _ _ _ => True)\nend Specs.Demo.caller\n",
            "import Trusted\nimport Mir.Demo.safe_ref\nimport Obligations.Demo.caller\nnamespace Specs.Demo.caller\ninstance : StatefulEquivItemSpec \"demo::caller\" :=\n  Obligations.Demo.caller.refineEquivSpec Mir.Demo.safe_ref.body (fun _ _ => True) (fun _ _ _ _ => True) |> fun s => { s with specBody := Mir.Demo.evil.body }\nend Specs.Demo.caller\n",
            "import Trusted\nimport Obligations.Demo.caller\nnamespace Specs.Demo.caller\ninstance : ModularItemSpec \"demo::caller\" :=\n  Obligations.Demo.caller.refineModularSpec (fun _ => True) (fun _ _ => True) (fun _ _ _ _ => True) |> fun s => s\nend Specs.Demo.caller\n",
        ] {
            assert!(
                scan_specs_module(bad_specs, "Demo.caller").is_err(),
                "expected malformed/bypass Specs module to fail closed:\n{bad_specs}"
            );
        }

        // 3. `Obligations/<Item>.lean` canonical claim & helper integrity checks.
        let bundles = crate::obligations::group_subject_obligations(&vec![
            anneal_rustc_capture::UnitTargetRecord {
                target: anneal_rustc_capture::CapturedTarget {
                    def_id: "demo::caller".to_string(),
                    mir_module_path: String::new(),
                    mir_module_sha256: "00".to_string(),
                },
                lean_module_name: "Mir.Demo.caller".to_string(),
                item_kind: anneal_rustc_capture::CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
        ]);
        let canon_ob = crate::obligations::render_obligations_module(&bundles[0]);
        validate_obligations_canonical_claims_for_def_path(
            &canon_ob,
            "Demo.caller",
            Some("demo::caller"),
        )
        .expect("freshly rendered canonical Obligations must pass strict def_path validation");

        for (label, needle, replacement) in [
            (
                "equivClaim specBody tampered",
                "specBody := spec.specBody",
                "specBody := Mir.Demo.caller.body",
            ),
            (
                "modularClaim envAssumed tampered",
                "envAssumed := spec.envAssumed",
                "envAssumed := fun _ => True",
            ),
            (
                "polyCertificate tampered",
                "items := [{ identity := artifactIdentity, certificate := P }]",
                "items := []",
            ),
            (
                "refineEquivSpec tampered",
                "specBody := specBody",
                "specBody := Mir.Demo.caller.body",
            ),
            (
                "refineModularSpec tampered",
                "envAssumed := envAssumed",
                "envAssumed := fun _ => True",
            ),
            (
                "defaultCallContract defPath tampered",
                "req.defPath = \"demo::caller\"",
                "req.defPath = \"demo::other\"",
            ),
            (
                "defaultModularSpec defId tampered",
                "ModularItemSpec \"demo::caller\"",
                "ModularItemSpec \"demo::other\"",
            ),
        ] {
            let mutated = canon_ob.replacen(needle, replacement, 1);
            assert_ne!(mutated, canon_ob, "mutation `{label}` did not match `{needle}`");
            assert!(
                validate_obligations_canonical_claims_for_def_path(
                    &mutated,
                    "Demo.caller",
                    Some("demo::caller"),
                )
                .is_err(),
                "expected `{label}` mutation in Obligations to fail closed"
            );
        }

        // 4. `const_eval_select` 2-arg malformed arity fails closed, 3-arg diverging panic `rt`
        //    reconciles cleanly, and assumed-subject `ReifyFnPointer` / `TailCall` to native
        //    intrinsics closes in `build_batch_callee_closure(..., true)`.
        let ces_bad_arity = ProtoMirBody {
            def_path: String::from("demo::ces_2args"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("core::intrinsics::const_eval_select"),
                    args: vec![
                        ProtoOperand::const_u32(0),
                        ProtoOperand::const_fn("core::intrinsics::wrapping_add"),
                    ],
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        assert_eq!(
            direct_callee_def_paths(&ces_bad_arity),
            vec![String::from("core::intrinsics::const_eval_select")]
        );
        let bad_arity_closure =
            crate::obligations::build_batch_callee_closure(&ces_bad_arity, &[], &[], false);
        assert!(
            !reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(
                    ces_bad_arity.clone(),
                    census_mir_fault_sites(&ces_bad_arity),
                )],
                &bad_arity_closure,
                &PropertyRegistry::all_verified(),
            )
            .is_verified(),
            "2-arg const_eval_select falls through to extCall in Terminators.lean and must fail closed"
        );

        let ces_panic_rt = ProtoMirBody {
            def_path: String::from("demo::ces_panic_rt"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: Vec::new(),
                terminator: ProtoTerminator::new(ProtoTerminatorKind::Call {
                    func: ProtoOperand::const_fn("core::intrinsics::const_eval_select"),
                    args: vec![
                        ProtoOperand::const_u32(0),
                        ProtoOperand::const_fn("demo::ct_fn"),
                        ProtoOperand::const_fn("core::panicking::panic_fmt"),
                    ],
                    destination: ProtoPlace::local(0),
                    target: Some(0),
                    unwind: ProtoUnwindAction::Continue,
                }),
                is_cleanup: false,
            }],
        };
        let panic_rt_closure =
            crate::obligations::build_batch_callee_closure(&ces_panic_rt, &[], &[], false);
        assert!(
            reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(
                    ces_panic_rt.clone(),
                    census_mir_fault_sites(&ces_panic_rt),
                )],
                &panic_rt_closure,
                &PropertyRegistry::all_verified(),
            )
            .is_verified(),
            "3-arg const_eval_select with natively modeled panic_fmt runtime target must reconcile"
        );

        let assumed_reified_intrinsic = ProtoMirBody {
            def_path: String::from("demo::assumed_reified_intrinsic"),
            basic_blocks: vec![ProtoBasicBlock {
                statements: vec![ProtoStatement::new(ProtoStatementKind::Assign(
                    ProtoPlace::local(0),
                    ProtoRvalue::Cast(
                        ProtoCastKind::PointerCoercion(String::from("ReifyFnPointer(Safe)")),
                        ProtoOperand::const_fn("core::intrinsics::ctpop"),
                    ),
                ))],
                terminator: ProtoTerminator::new(ProtoTerminatorKind::TailCall {
                    func: ProtoOperand::const_fn("core::intrinsics::wrapping_add"),
                    args: Vec::new(),
                }),
                is_cleanup: false,
            }],
        };
        let assumed_intr_closure = crate::obligations::build_batch_callee_closure(
            &assumed_reified_intrinsic,
            &[],
            &[],
            true,
        );
        assert!(
            reconcile_multi_item_coverage(
                &[ItemCoverageInput::from_body(
                    assumed_reified_intrinsic.clone(),
                    census_mir_fault_sites(&assumed_reified_intrinsic),
                )],
                &assumed_intr_closure,
                &PropertyRegistry::all_verified(),
            )
            .is_verified(),
            "assumed subject reifying or tail-calling native intrinsics must reconcile cleanly"
        );
    }
}
