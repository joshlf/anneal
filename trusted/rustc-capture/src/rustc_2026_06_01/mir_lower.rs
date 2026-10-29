//! Post-cleanup MIR body, type, constant allocation, and contract-role lowering
//! for `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`V2026_06_01`).
//!
//! This module extracts `rustc_middle::mir::Body`, `rustc_middle::ty::Ty`,
//! and `rustc_middle::mir::interpret::Allocation` into the
//! toolchain-independent `IrCapturedMir` intermediate representation emitted as
//! `Mir/<Crate>/<Item>.lean`.
//!
//! Every extraction path quotes and links to `rustc` at commit
//! `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` per `agent_docs/trusted-rust.md`.

use std::collections::{BTreeMap, BTreeSet};

use rustc_abi::{Endian, HasDataLayout, Size};
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_middle::mir::{
    AggregateKind, BasicBlockData, BinOp, Body, BorrowKind, CastKind, Const, ConstOperand,
    ConstValue, LocalDecl, MirPhase, MutBorrowKind, NonDivergingIntrinsic, Operand, Place,
    ProjectionElem, RawPtrKind, RuntimePhase, Rvalue, Statement, StatementKind, SwitchTargets,
    Terminator, TerminatorKind, UnOp, UnwindAction, VarDebugInfoContents, WithRetag,
};
use rustc_middle::ty::{FloatTy, IntTy, Mutability, ScalarInt, Ty, TyCtxt, TyKind, UintTy};
use rustc_span::DUMMY_SP;

use crate::lean_emit::{
    IrAggregateKind, IrBasicBlockData, IrBinOp, IrBorrowKind, IrCapturedAllocation, IrCapturedMir,
    IrCastKind, IrConstOperand, IrConstScalar, IrConstValue, IrContractRole, IrFloatTy, IrIntTy,
    IrLocalDecl, IrMirPhaseTag, IrMutability, IrNonDivergingIntrinsic, IrOperand, IrPlace,
    IrProjectionElem, IrProvenancePtr, IrRetagKind, IrRigidTy, IrRvalue, IrSafety, IrScalarInt,
    IrStatement, IrStatementKind, IrSwitchTargets, IrTerminator, IrTerminatorKind, IrTy, IrUintTy,
    IrUnOp, IrUnwindAction,
};
use crate::rustc_2026_06_01::layout_lower::{
    LayoutTableBuilder, extract_fn_abi_for_body, lower_align, lower_extern_abi, lower_layout_data,
};
pub use crate::rustc_2026_06_01::specs::{
    ANNEAL_EXT_SPEC_PREFIX, ANNEAL_MODEL_PREFIX, ANNEAL_TYPE_INVARIANT_DOC_MARKER,
    ANNEAL_TYPE_INVARIANT_FN_PREFIX, ANNEAL_UNSAFE_IMPL_DOC_MARKER, ANNEAL_UNSAFE_IMPL_FN_PREFIX,
    ANNEAL_UNSAFE_TRAIT_DOC_MARKER, ANODIZED_ENSURES_PREFIX, ANODIZED_QUALIFIERS_PREFIX,
    ANODIZED_REQUIRES_PREFIX, CrateContractIndex, DocSpecMarker, ItemClassification,
    extract_doc_spec_marker, parse_doc_spec_marker,
};

/// Returns the canonical crate-qualified `DefId` path for `def_id` (for
/// example, `"demo::answer"`).
pub fn canonical_def_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let raw = tcx.def_path_str(def_id);
    if def_id.is_local() {
        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        if raw.is_empty() {
            crate_name
        } else if raw.starts_with(&format!("{crate_name}::")) {
            raw
        } else {
            format!("{crate_name}::{raw}")
        }
    } else {
        raw
    }
}

/// Returns true if `local_def_id` is a user-meaningful item whose MIR body
/// should be captured (skipping synthetic anonymous constants such as array
/// length expressions and unnamed `const _: T = ...` static assertions).
///
/// The Rust Reference ("Constant items — Unnamed constant") specifies that
/// `const _: T = ...` introduces an unnamed constant:
/// <https://doc.rust-lang.org/1.98.0/reference/items/constant-items.html#unnamed-constant>
///
/// > "Unlike a normal constant, an unnamed constant cannot be referred to by
/// > name, and instead uses an underscore (`_`) in place of an identifier."
///
/// `rustc` (`compiler/rustc_hir/src/def.rs`) classifies top-level and module
/// constants as `DefKind::Const`:
///
/// >```text
/// >pub enum DefKind {
/// >    ...
/// >    Fn,
/// >    Const,
/// >    Static { safety: Safety, mutability: Mutability, nested: bool },
/// >    ...
/// >    AssocFn,
/// >    AssocConst,
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_hir/src/def.rs#L110-L150
pub fn should_capture_mir_item(tcx: TyCtxt<'_>, local_def_id: LocalDefId) -> bool {
    let def_id = local_def_id.to_def_id();
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn | DefKind::AssocConst { .. } | DefKind::Static { .. } => {
            true
        }
        DefKind::Const { .. } => {
            let def_path_str = tcx.def_path_str(def_id);
            !is_unnamed_const_def_path(&def_path_str)
        }
        _ => false,
    }
}

/// Returns `true` if `def_path_str` denotes an unnamed constant (`"_"` or a
/// path ending with `"::_"`).
pub fn is_unnamed_const_def_path(def_path_str: &str) -> bool {
    def_path_str == "_" || def_path_str.ends_with("::_")
}

/// Queries the post-cleanup runtime MIR body for functions and methods
/// (`tcx.optimized_mir`) or the CTFE MIR body for constants and statics
/// (`tcx.mir_for_ctfe`).
///
/// `rustc` (`compiler/rustc_mir_transform/src/lib.rs`) panics if
/// `optimized_mir` is queried on a `const` or `static` item, requiring
/// `mir_for_ctfe` instead:
///
/// >```text
/// >fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
/// >    tcx.ensure_done().mir_Built(did);
/// >    if tcx.is_constructor(did.to_def_id()) {
/// >        return tcx.mir_for_ctfe(did.to_def_id());
/// >    }
/// >    match tcx.hir_body_const_context(did) {
/// >        None | Some(hir::ConstContext::ConstFn) => (),
/// >        Some(other) => panic!("do not use optimized_mir for constants: {other:?}"),
/// >    }
/// >    ...
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_mir_transform/src/lib.rs#L776-L796
pub fn query_post_cleanup_mir<'tcx>(tcx: TyCtxt<'tcx>, local_def_id: LocalDefId) -> &'tcx Body<'tcx> {
    let def_id = local_def_id.to_def_id();
    if tcx.is_constructor(def_id) {
        return tcx.mir_for_ctfe(def_id);
    }
    match tcx.hir_body_const_context(local_def_id) {
        None | Some(hir::ConstContext::ConstFn) => tcx.optimized_mir(def_id),
        Some(hir::ConstContext::Const { .. } | hir::ConstContext::Static(_)) => {
            tcx.mir_for_ctfe(def_id)
        }
    }
}

/// Lowers a `rustc_middle::mir::Body` and its referenced layouts and constant
/// allocations into an `IrCapturedMir`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/mod.rs`) defines `Body` as:
///
/// >```text
/// >pub struct Body<'tcx> {
/// >    pub basic_blocks: BasicBlocks<'tcx>,
/// >    pub phase: MirPhase,
/// >    pub pass_count: usize,
/// >    pub source: MirSource<'tcx>,
/// >    pub source_scopes: IndexVec<SourceScope, SourceScopeData<'tcx>>,
/// >    pub coroutine: Option<Box<CoroutineInfo<'tcx>>>,
/// >    pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
/// >    pub user_type_annotations: ty::CanonicalUserTypeAnnotations<'tcx>,
/// >    pub arg_count: usize,
/// >    pub spread_arg: Option<Local>,
/// >    pub var_debug_info: Vec<VarDebugInfo<'tcx>>,
/// >    pub span: Span,
/// >    pub required_consts: Option<Vec<ConstOperand<'tcx>>>,
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L206-L271
pub fn lower_mir_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    role: IrContractRole,
) -> IrCapturedMir {
    let mut ctx = MirLowerCtx::new(tcx, def_id);

    let mut local_layouts = Vec::with_capacity(body.local_decls.len());
    for decl in body.local_decls.iter() {
        let layout = match tcx.layout_of(ctx.layout_builder.typing_env().as_query_input(decl.ty)) {
            Ok(tl) => lower_layout_data(&tl.layout.0),
            Err(_) => crate::rustc_2026_06_01::layout_lower::fallback_zst_layout(),
        };
        local_layouts.push(layout);
    }

    let (local_decls, basic_blocks) = ctx.lower_body_cfg(body, false);

    let fn_abi = extract_fn_abi_for_body(
        tcx,
        def_id,
        ctx.layout_builder.typing_env(),
        body.arg_count,
        &local_layouts,
    );
    for arg in &fn_abi.args {
        ctx.layout_builder.intern_ir_layout(arg.layout.clone());
    }
    ctx.layout_builder.intern_ir_layout(fn_abi.ret.layout.clone());

    let allocations = ctx.drain_allocations();
    let layouts = ctx.layout_builder.finish();

    IrCapturedMir {
        def_path: canonical_def_path(tcx, def_id),
        phase: lower_mir_phase(body.phase),
        role,
        arg_count: body.arg_count,
        local_decls,
        basic_blocks,
        fn_abi,
        layouts,
        allocations,
    }
}

fn collect_local_debug_names(body: &Body<'_>) -> BTreeMap<usize, String> {
    let mut map = BTreeMap::new();
    for vdi in &body.var_debug_info {
        if vdi.composite.is_none()
            && let VarDebugInfoContents::Place(place) = vdi.value
            && place.projection.is_empty()
        {
            map.entry(place.local.as_usize())
                .or_insert_with(|| vdi.name.to_string());
        }
    }
    map
}

/// Lowers `rustc_middle::mir::MirPhase` into `IrMirPhaseTag`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `MirPhase` and
/// `RuntimePhase` as:
///
/// >```text
/// >pub enum MirPhase {
/// >    Built,
/// >    Analysis(AnalysisPhase),
/// >    Runtime(RuntimePhase),
/// >}
/// >```
///
/// >```text
/// >pub enum RuntimePhase {
/// >    Initial = 0,
/// >    PostCleanup = 1,
/// >    Optimized = 2,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L42-L142
fn lower_mir_phase(phase: MirPhase) -> IrMirPhaseTag {
    match phase {
        MirPhase::Runtime(RuntimePhase::PostCleanup) => IrMirPhaseTag::RuntimePostCleanup,
        MirPhase::Runtime(RuntimePhase::Optimized) => IrMirPhaseTag::RuntimeOptimized,
        other => IrMirPhaseTag::Other(format!("{other:?}")),
    }
}

struct MirLowerCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    layout_builder: LayoutTableBuilder<'tcx>,
    pending_allocs: Vec<AllocId>,
    seen_allocs: BTreeSet<u64>,
}

impl<'tcx> MirLowerCtx<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            layout_builder: LayoutTableBuilder::new(tcx, def_id),
            pending_allocs: Vec::new(),
            seen_allocs: BTreeSet::new(),
        }
    }

    fn record_alloc_id(&mut self, alloc_id: AllocId) -> u64 {
        let raw_id = alloc_id.0.get();
        if self.seen_allocs.insert(raw_id) {
            self.pending_allocs.push(alloc_id);
        }
        raw_id
    }

    /// Lowers `rustc_middle::mir::LocalDecl` into `IrLocalDecl`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/mod.rs`) defines `LocalDecl` as:
    ///
    /// >```text
    /// >pub struct LocalDecl<'tcx> {
    /// >    pub mutability: Mutability,
    /// >    pub local_info: ClearCrossCrate<Box<LocalInfo<'tcx>>>,
    /// >    pub ty: Ty<'tcx>,
    /// >    pub user_ty: Option<Box<UserTypeProjections>>,
    /// >    pub source_info: SourceInfo,
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L967-L1065
    fn lower_local_decl(
        &mut self,
        decl: &LocalDecl<'tcx>,
        debug_name: Option<String>,
    ) -> IrLocalDecl {
        IrLocalDecl {
            mutability: lower_mutability(decl.mutability),
            ty: self.lower_ty(decl.ty),
            debug_name,
        }
    }

    /// Lowers `rustc_middle::ty::Ty` into `IrTy` (pairing `IrRigidTy` with its
    /// deduplicated `layout_idx`).
    ///
    /// `rustc` (`compiler/rustc_type_ir/src/ty_kind.rs`) defines `TyKind` as:
    ///
    /// >```text
    /// >pub enum TyKind<I: Interner> {
    /// >    Bool,
    /// >    Char,
    /// >    Int(IntTy),
    /// >    Uint(UintTy),
    /// >    Float(FloatTy),
    /// >    Adt(I::AdtDef, I::GenericArgs),
    /// >    Foreign(I::DefId),
    /// >    Str,
    /// >    Array(I::Ty, I::Const),
    /// >    Pat(I::Ty, I::Pat),
    /// >    Slice(I::Ty),
    /// >    RawPtr(I::Ty, Mutability),
    /// >    Ref(I::Region, I::Ty, Mutability),
    /// >    FnDef(I::DefId, I::GenericArgs),
    /// >    FnPtr(Binder<I, FnSigTys<I>>, FnHeader<I>),
    /// >    UnsafeBinder(Binder<I, I::Ty>),
    /// >    Dynamic(I::BoundExistentialPredicates, I::Region),
    /// >    Closure(I::DefId, I::GenericArgs),
    /// >    CoroutineClosure(I::DefId, I::GenericArgs),
    /// >    Coroutine(I::DefId, I::GenericArgs),
    /// >    CoroutineWitness(I::DefId, I::GenericArgs),
    /// >    Never,
    /// >    Tuple(I::Tys),
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_type_ir/src/ty_kind.rs#L102-L216
    fn lower_ty(&mut self, ty: Ty<'tcx>) -> IrTy {
        let layout_idx = self.layout_builder.intern_ty_layout(ty);
        let kind = self.lower_rigid_ty(ty);
        IrTy { kind, layout_idx }
    }

    fn lower_rigid_ty(&mut self, ty: Ty<'tcx>) -> IrRigidTy {
        match ty.kind() {
            TyKind::Bool => IrRigidTy::Bool,
            TyKind::Char => IrRigidTy::Char,
            TyKind::Int(int_ty) => IrRigidTy::Int(lower_int_ty(*int_ty)),
            TyKind::Uint(uint_ty) => IrRigidTy::Uint(lower_uint_ty(*uint_ty)),
            TyKind::Float(float_ty) => IrRigidTy::Float(lower_float_ty(*float_ty)),
            TyKind::Never => IrRigidTy::Never,
            TyKind::Str => IrRigidTy::Str,
            TyKind::Tuple(elems) => {
                IrRigidTy::Tuple(elems.iter().map(|t| self.lower_rigid_ty(t)).collect())
            }
            TyKind::Array(elem_ty, len_const) => {
                let len = len_const.try_to_target_usize(self.tcx).unwrap_or(0);
                IrRigidTy::Array(Box::new(self.lower_rigid_ty(*elem_ty)), len)
            }
            TyKind::Slice(elem_ty) => IrRigidTy::Slice(Box::new(self.lower_rigid_ty(*elem_ty))),
            TyKind::Ref(_region, pointee, mutbl) => IrRigidTy::Ref(
                lower_mutability(*mutbl),
                Box::new(self.lower_rigid_ty(*pointee)),
            ),
            TyKind::RawPtr(pointee, mutbl) => IrRigidTy::RawPtr(
                lower_mutability(*mutbl),
                Box::new(self.lower_rigid_ty(*pointee)),
            ),
            TyKind::Adt(adt_def, args) => {
                let def_path = canonical_def_path(self.tcx, adt_def.did());
                let ty_args = args
                    .types()
                    .map(|t| self.lower_rigid_ty(t))
                    .collect::<Vec<_>>();
                IrRigidTy::Adt(def_path, ty_args)
            }
            TyKind::FnDef(fn_def_id, args) => {
                let def_path = canonical_def_path(self.tcx, *fn_def_id);
                let ty_args = args
                    .types()
                    .map(|t| self.lower_rigid_ty(t))
                    .collect::<Vec<_>>();
                IrRigidTy::FnDef(def_path, ty_args)
            }
            TyKind::FnPtr(sig_tys, hdr) => {
                let bound_tys = sig_tys.skip_binder();
                let inputs = bound_tys
                    .inputs()
                    .iter()
                    .map(|t| self.lower_rigid_ty(*t))
                    .collect();
                let output = Box::new(self.lower_rigid_ty(bound_tys.output()));
                let safety = match hdr.safety() {
                    hir::Safety::Safe => IrSafety::Safe,
                    hir::Safety::Unsafe => IrSafety::Unsafe,
                };
                let conv = lower_extern_abi(hdr.abi());
                IrRigidTy::FnPtr(inputs, output, safety, conv)
            }
            TyKind::Closure(def_id, args) => {
                let def_path = canonical_def_path(self.tcx, *def_id);
                let ty_args = args
                    .types()
                    .map(|t| self.lower_rigid_ty(t))
                    .collect::<Vec<_>>();
                IrRigidTy::Closure(def_path, ty_args)
            }
            TyKind::Dynamic(preds, _) => {
                if let Some(principal_def_id) = preds.principal_def_id() {
                    IrRigidTy::Dynamic(canonical_def_path(self.tcx, principal_def_id))
                } else {
                    IrRigidTy::Dynamic(format!("{ty}"))
                }
            }
            TyKind::Foreign(def_id) => IrRigidTy::Foreign(canonical_def_path(self.tcx, *def_id)),
            _ => IrRigidTy::Other(format!("{ty}")),
        }
    }

    /// Lowers `rustc_middle::mir::Place` and `ProjectionElem` into `IrPlace`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `Place` and
    /// `ProjectionElem` as:
    ///
    /// >```text
    /// >pub struct Place<'tcx> {
    /// >    pub local: Local,
    /// >    pub projection: &'tcx List<PlaceElem<'tcx>>,
    /// >}
    /// >
    /// >pub enum ProjectionElem<V, T> {
    /// >    Deref,
    /// >    Field(FieldIdx, T),
    /// >    Index(V),
    /// >    ConstantIndex {
    /// >        offset: u64,
    /// >        min_length: u64,
    /// >        from_end: bool,
    /// >    },
    /// >    Subslice {
    /// >        from: u64,
    /// >        to: u64,
    /// >        from_end: bool,
    /// >    },
    /// >    Downcast(Option<Symbol>, VariantIdx),
    /// >    OpaqueCast(T),
    /// >    UnwrapUnsafeBinder(T),
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1183-L1279
    fn lower_place(&mut self, place: Place<'tcx>) -> IrPlace {
        let projection = place
            .projection
            .iter()
            .map(|elem| match elem {
                ProjectionElem::Deref => IrProjectionElem::Deref,
                ProjectionElem::Field(field_idx, field_ty) => {
                    IrProjectionElem::Field(field_idx.as_usize(), self.lower_ty(field_ty))
                }
                ProjectionElem::Index(local) => IrProjectionElem::Index(local.as_usize()),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => IrProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                ProjectionElem::Subslice { from, to, from_end } => IrProjectionElem::Subslice {
                    from_idx: from,
                    to_idx: to,
                    from_end,
                },
                ProjectionElem::Downcast(sym, variant_idx) => IrProjectionElem::Downcast(
                    sym.map(|s| s.to_string()),
                    variant_idx.as_usize(),
                ),
                ProjectionElem::OpaqueCast(ty) => IrProjectionElem::OpaqueCast(self.lower_ty(ty)),
                ProjectionElem::UnwrapUnsafeBinder(ty) => {
                    IrProjectionElem::UnwrapUnsafeBinder(self.lower_ty(ty))
                }
            })
            .collect();

        IrPlace {
            local_: place.local.as_usize(),
            projection,
        }
    }

    /// Lowers `rustc_middle::mir::Operand` into `IrOperand`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `Operand`
    /// as:
    ///
    /// >```text
    /// >pub enum Operand<'tcx> {
    /// >    Copy(Place<'tcx>),
    /// >    Move(Place<'tcx>),
    /// >    Constant(Box<ConstOperand<'tcx>>),
    /// >    RuntimeChecks(RuntimeChecks),
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1335
    fn lower_operand(&mut self, op: &Operand<'tcx>) -> IrOperand {
        match op {
            Operand::Copy(place) => IrOperand::Copy(self.lower_place(*place)),
            Operand::Move(place) => IrOperand::Move(self.lower_place(*place)),
            Operand::Constant(const_op) => IrOperand::Constant(self.lower_const_operand(const_op)),
            Operand::RuntimeChecks(checks) => {
                let flag = checks.value(self.tcx.sess);
                let bool_ty = self.lower_ty(self.tcx.types.bool);
                IrOperand::Constant(IrConstOperand {
                    ty: bool_ty,
                    val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                        bits: u128::from(flag),
                        size_bytes: 1,
                    })),
                })
            }
        }
    }

    /// Lowers `rustc_middle::mir::ConstOperand` and `ConstValue` into
    /// `IrConstOperand`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/consts.rs`) defines `ConstValue`
    /// as:
    ///
    /// >```text
    /// >pub enum ConstValue {
    /// >    Scalar(Scalar),
    /// >    ZeroSized,
    /// >    Slice {
    /// >        alloc_id: AllocId,
    /// >        meta: u64,
    /// >    },
    /// >    Indirect {
    /// >        alloc_id: AllocId,
    /// >        offset: Size,
    /// >    },
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L33-L71
    fn lower_const_operand(&mut self, const_op: &ConstOperand<'tcx>) -> IrConstOperand {
        let ty = self.lower_ty(const_op.const_.ty());
        let typing_env = self.layout_builder.typing_env();
        let val = match const_op.const_ {
            Const::Val(cv, _) => self.lower_const_value(cv),
            Const::Ty(_, ct) => {
                if let Ok(cv) = const_op.const_.eval(self.tcx, typing_env, const_op.span) {
                    self.lower_const_value(cv)
                } else {
                    IrConstValue::Unevaluated(format!("{ct:?}"))
                }
            }
            Const::Unevaluated(uneval, _) => {
                if let Ok(cv) = const_op.const_.eval(self.tcx, typing_env, DUMMY_SP) {
                    self.lower_const_value(cv)
                } else {
                    IrConstValue::Unevaluated(canonical_def_path(self.tcx, uneval.def))
                }
            }
        };
        IrConstOperand { ty, val }
    }

    fn lower_const_value(&mut self, cv: ConstValue) -> IrConstValue {
        match cv {
            ConstValue::ZeroSized => IrConstValue::ZeroSized,
            ConstValue::Scalar(scalar) => IrConstValue::Scalar(self.lower_const_scalar(scalar)),
            ConstValue::Slice { alloc_id, meta } => {
                let raw_id = self.record_alloc_id(alloc_id);
                let ptr_bytes = self.tcx.data_layout().pointer_size().bytes();
                let data = IrConstScalar::Ptr(
                    IrProvenancePtr {
                        alloc_id: raw_id,
                        offset_bytes: 0,
                    },
                    ptr_bytes,
                );
                IrConstValue::Slice { data, meta }
            }
            ConstValue::Indirect { alloc_id, offset } => {
                let raw_id = self.record_alloc_id(alloc_id);
                IrConstValue::Indirect {
                    alloc_id: raw_id,
                    offset_bytes: offset.bytes(),
                }
            }
        }
    }

    fn lower_const_scalar(&mut self, scalar: Scalar) -> IrConstScalar {
        match scalar {
            Scalar::Int(si) => IrConstScalar::Int(lower_scalar_int(si)),
            Scalar::Ptr(ptr, size) => {
                let (prov, offset) = ptr.prov_and_relative_offset();
                let raw_id = self.record_alloc_id(prov.alloc_id());
                IrConstScalar::Ptr(
                    IrProvenancePtr {
                        alloc_id: raw_id,
                        offset_bytes: offset.bytes(),
                    },
                    u64::from(size),
                )
            }
        }
    }

    /// Lowers `rustc_middle::mir::Rvalue` into `IrRvalue`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `Rvalue` as:
    ///
    /// >```text
    /// >pub enum Rvalue<'tcx> {
    /// >    Use(Operand<'tcx>, WithRetag),
    /// >    Repeat(Operand<'tcx>, ty::Const<'tcx>),
    /// >    Ref(Region<'tcx>, BorrowKind, Place<'tcx>),
    /// >    ThreadLocalRef(DefId),
    /// >    RawPtr(RawPtrKind, Place<'tcx>),
    /// >    Cast(CastKind, Operand<'tcx>, Ty<'tcx>),
    /// >    BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>),
    /// >    UnaryOp(UnOp, Operand<'tcx>),
    /// >    Discriminant(Place<'tcx>),
    /// >    Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>),
    /// >    CopyForDeref(Place<'tcx>),
    /// >    WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>),
    /// >    Reborrow(Ty<'tcx>, Mutability, Place<'tcx>),
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488
    fn lower_rvalue(&mut self, rv: &Rvalue<'tcx>) -> IrRvalue {
        match rv {
            Rvalue::Use(op, _with_retag) => IrRvalue::Use(self.lower_operand(op)),
            Rvalue::Repeat(op, count_const) => {
                let count = count_const.try_to_target_usize(self.tcx).unwrap_or(0);
                IrRvalue::Repeat(self.lower_operand(op), count)
            }
            Rvalue::Ref(_region, borrow_kind, place) => {
                let bk = match borrow_kind {
                    BorrowKind::Shared | BorrowKind::Fake(_) => IrBorrowKind::Shared,
                    BorrowKind::Mut { kind } => IrBorrowKind::Mut {
                        allow_two_phase: matches!(kind, MutBorrowKind::TwoPhaseBorrow),
                    },
                };
                IrRvalue::Ref(bk, self.lower_place(*place))
            }
            Rvalue::ThreadLocalRef(def_id) => {
                IrRvalue::ThreadLocalRef(canonical_def_path(self.tcx, *def_id))
            }
            Rvalue::RawPtr(raw_ptr_kind, place) => {
                let mutbl = match raw_ptr_kind {
                    RawPtrKind::Const => IrMutability::Not,
                    RawPtrKind::Mut | RawPtrKind::FakeForPtrMetadata => IrMutability::Mut,
                };
                IrRvalue::RawPtr(mutbl, self.lower_place(*place))
            }
            Rvalue::Cast(cast_kind, op, ty) => IrRvalue::Cast(
                lower_cast_kind(*cast_kind),
                self.lower_operand(op),
                self.lower_ty(*ty),
            ),
            Rvalue::BinaryOp(bin_op, operands) => IrRvalue::BinaryOp(
                lower_bin_op(*bin_op),
                self.lower_operand(&operands.0),
                self.lower_operand(&operands.1),
            ),
            Rvalue::UnaryOp(un_op, op) => {
                IrRvalue::UnaryOp(lower_un_op(*un_op), self.lower_operand(op))
            }
            Rvalue::Discriminant(place) => IrRvalue::Discriminant(self.lower_place(*place)),
            Rvalue::Aggregate(agg_kind, operands) => {
                let ir_agg = self.lower_aggregate_kind(agg_kind);
                let ir_ops = operands.iter().map(|op| self.lower_operand(op)).collect();
                IrRvalue::Aggregate(ir_agg, ir_ops)
            }
            Rvalue::CopyForDeref(place) => IrRvalue::CopyForDeref(self.lower_place(*place)),
            Rvalue::WrapUnsafeBinder(op, ty) => {
                IrRvalue::WrapUnsafeBinder(self.lower_operand(op), self.lower_ty(*ty))
            }
            Rvalue::Reborrow(_ty, mutbl, place) => {
                let bk = match mutbl {
                    Mutability::Not => IrBorrowKind::Shared,
                    Mutability::Mut => IrBorrowKind::Mut {
                        allow_two_phase: false,
                    },
                };
                IrRvalue::Ref(bk, self.lower_place(*place))
            }
        }
    }

    /// Lowers `rustc_middle::mir::AggregateKind` into `IrAggregateKind`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines
    /// `AggregateKind` as:
    ///
    /// >```text
    /// >pub enum AggregateKind<'tcx> {
    /// >    Array(Ty<'tcx>),
    /// >    Tuple,
    /// >    Adt(DefId, VariantIdx, GenericArgsRef<'tcx>, Option<UserTypeAnnotationIndex>, Option<FieldIdx>),
    /// >    Closure(DefId, GenericArgsRef<'tcx>),
    /// >    Coroutine(DefId, GenericArgsRef<'tcx>),
    /// >    CoroutineClosure(DefId, GenericArgsRef<'tcx>),
    /// >    RawPtr(Ty<'tcx>, Mutability),
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1546-L1576
    fn lower_aggregate_kind(&mut self, agg: &AggregateKind<'tcx>) -> IrAggregateKind {
        match agg {
            AggregateKind::Array(elem_ty) => IrAggregateKind::Array(self.lower_ty(*elem_ty)),
            AggregateKind::Tuple => IrAggregateKind::Tuple,
            AggregateKind::Adt(def_id, variant_idx, _args, _user_ty, active_field) => {
                IrAggregateKind::Adt(
                    canonical_def_path(self.tcx, *def_id),
                    variant_idx.as_usize(),
                    active_field.map(|f| f.as_usize()),
                )
            }
            AggregateKind::Closure(def_id, _args)
            | AggregateKind::CoroutineClosure(def_id, _args) => {
                IrAggregateKind::Closure(canonical_def_path(self.tcx, *def_id))
            }
            AggregateKind::Coroutine(def_id, _args) => {
                IrAggregateKind::Coroutine(canonical_def_path(self.tcx, *def_id))
            }
            AggregateKind::RawPtr(pointee_ty, mutbl) => {
                IrAggregateKind::RawPtr(self.lower_ty(*pointee_ty), lower_mutability(*mutbl))
            }
        }
    }

    /// Lowers `rustc_middle::mir::BasicBlockData` into `IrBasicBlockData`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/mod.rs`) defines
    /// `BasicBlockData` as:
    ///
    /// >```text
    /// >pub struct BasicBlockData<'tcx> {
    /// >    pub statements: Vec<Statement<'tcx>>,
    /// >    pub after_last_stmt_debuginfos: StmtDebugInfos<'tcx>,
    /// >    pub terminator: Option<Terminator<'tcx>>,
    /// >    pub is_cleanup: bool,
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L1319-L1342
    fn lower_basic_block(&mut self, bb: &BasicBlockData<'tcx>) -> IrBasicBlockData {
        let mut statements = Vec::with_capacity(bb.statements.len());
        for stmt in &bb.statements {
            statements.push(self.lower_statement(stmt));
            if let StatementKind::Assign(assign_box) = &stmt.kind
                && let Rvalue::Use(_, WithRetag::Yes) = &assign_box.1
            {
                let retag_place = self.lower_place(assign_box.0);
                statements.push(IrStatement {
                    kind: IrStatementKind::Retag(IrRetagKind::Default, retag_place),
                    span: format_span(self.tcx, stmt.source_info.span),
                    comment: Some(format!("Retag({:?})", assign_box.0)),
                });
            }
        }
        let terminator = match &bb.terminator {
            Some(term) => self.lower_terminator(term),
            None => IrTerminator {
                kind: IrTerminatorKind::Unreachable,
                span: String::new(),
                comment: Some(String::from("unreachable")),
            },
        };
        IrBasicBlockData {
            statements,
            terminator,
            is_cleanup: bb.is_cleanup,
        }
    }

    /// Lowers `rustc_middle::mir::Statement` and `StatementKind` into
    /// `IrStatement`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines
    /// `StatementKind` as:
    ///
    /// >```text
    /// >pub enum StatementKind<'tcx> {
    /// >    Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
    /// >    FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
    /// >    SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
    /// >    StorageLive(Local),
    /// >    StorageDead(Local),
    /// >    PlaceMention(Box<Place<'tcx>>),
    /// >    AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, ty::Variance),
    /// >    Coverage(CoverageKind),
    /// >    Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
    /// >    ConstEvalCounter,
    /// >    Nop,
    /// >    BackwardIncompatibleDropHint {
    /// >        place: Box<Place<'tcx>>,
    /// >        reason: BackwardIncompatibleDropReason,
    /// >    },
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L305-L456
    fn lower_statement(&mut self, stmt: &Statement<'tcx>) -> IrStatement {
        let kind = match &stmt.kind {
            StatementKind::Assign(assign_box) => IrStatementKind::Assign(
                self.lower_place(assign_box.0),
                self.lower_rvalue(&assign_box.1),
            ),
            StatementKind::FakeRead(fake_box) => {
                IrStatementKind::PlaceMention(self.lower_place(fake_box.1))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => IrStatementKind::SetDiscriminant(
                self.lower_place(**place),
                variant_index.as_usize(),
            ),
            StatementKind::StorageLive(local) => IrStatementKind::StorageLive(local.as_usize()),
            StatementKind::StorageDead(local) => IrStatementKind::StorageDead(local.as_usize()),
            StatementKind::PlaceMention(place) => {
                IrStatementKind::PlaceMention(self.lower_place(**place))
            }
            StatementKind::AscribeUserType(_, _) | StatementKind::Nop => IrStatementKind::Nop,
            StatementKind::Coverage(_) => IrStatementKind::Coverage,
            StatementKind::Intrinsic(ndi) => {
                let ir_ndi = match &**ndi {
                    NonDivergingIntrinsic::Assume(op) => {
                        IrNonDivergingIntrinsic::Assume(self.lower_operand(op))
                    }
                    NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                        IrNonDivergingIntrinsic::CopyNonOverlapping {
                            src: self.lower_operand(&cno.src),
                            dst: self.lower_operand(&cno.dst),
                            count: self.lower_operand(&cno.count),
                        }
                    }
                };
                IrStatementKind::Intrinsic(ir_ndi)
            }
            StatementKind::ConstEvalCounter => IrStatementKind::ConstEvalCounter,
            StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                IrStatementKind::BackwardIncompatibleDropHint(self.lower_place(**place))
            }
        };
        IrStatement {
            kind,
            span: format_span(self.tcx, stmt.source_info.span),
            comment: Some(format!("{stmt:?}")),
        }
    }

    /// Lowers `rustc_middle::mir::Terminator` and `TerminatorKind` into
    /// `IrTerminator`.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines
    /// `TerminatorKind` as:
    ///
    /// >```text
    /// >pub enum TerminatorKind<'tcx> {
    /// >    Goto { target: BasicBlock },
    /// >    SwitchInt {
    /// >        discr: Operand<'tcx>,
    /// >        targets: SwitchTargets,
    /// >    },
    /// >    UnwindResume,
    /// >    UnwindTerminate(UnwindTerminateReason),
    /// >    Return,
    /// >    Unreachable,
    /// >    Drop {
    /// >        place: Place<'tcx>,
    /// >        target: BasicBlock,
    /// >        unwind: UnwindAction,
    /// >        replace: bool,
    /// >        drop: Option<BasicBlock>,
    /// >        async_fut: Option<Local>,
    /// >    },
    /// >    Call {
    /// >        func: Operand<'tcx>,
    /// >        args: Box<[Spanned<Operand<'tcx>>]>,
    /// >        destination: Place<'tcx>,
    /// >        target: Option<BasicBlock>,
    /// >        unwind: UnwindAction,
    /// >        call_source: CallSource,
    /// >        fn_span: Span,
    /// >    },
    /// >    TailCall {
    /// >        func: Operand<'tcx>,
    /// >        args: Box<[Spanned<Operand<'tcx>>]>,
    /// >        fn_span: Span,
    /// >    },
    /// >    Assert {
    /// >        cond: Operand<'tcx>,
    /// >        expected: bool,
    /// >        msg: Box<AssertMessage<'tcx>>,
    /// >        target: BasicBlock,
    /// >        unwind: UnwindAction,
    /// >    },
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L692-L870
    fn lower_terminator(&mut self, term: &Terminator<'tcx>) -> IrTerminator {
        let kind = match &term.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | TerminatorKind::Yield { resume: target, .. } => {
                IrTerminatorKind::Goto(target.as_usize())
            }
            TerminatorKind::SwitchInt { discr, targets } => IrTerminatorKind::SwitchInt(
                self.lower_operand(discr),
                lower_switch_targets(targets),
            ),
            TerminatorKind::UnwindResume => IrTerminatorKind::UnwindResume,
            TerminatorKind::UnwindTerminate(_) => IrTerminatorKind::UnwindTerminate,
            TerminatorKind::Return | TerminatorKind::CoroutineDrop => IrTerminatorKind::Return,
            TerminatorKind::Unreachable => IrTerminatorKind::Unreachable,
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => IrTerminatorKind::Drop {
                place: self.lower_place(*place),
                target: target.as_usize(),
                unwind: lower_unwind_action(*unwind),
            },
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => IrTerminatorKind::Call {
                func: self.lower_operand(func),
                args: args.iter().map(|sp| self.lower_operand(&sp.node)).collect(),
                destination: self.lower_place(*destination),
                target: target.map(|bb| bb.as_usize()),
                unwind: lower_unwind_action(*unwind),
            },
            TerminatorKind::TailCall { func, args, .. } => IrTerminatorKind::TailCall {
                func: self.lower_operand(func),
                args: args.iter().map(|sp| self.lower_operand(&sp.node)).collect(),
            },
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => IrTerminatorKind::Assert {
                cond: self.lower_operand(cond),
                expected: *expected,
                target: target.as_usize(),
                unwind: lower_unwind_action(*unwind),
            },
            TerminatorKind::InlineAsm {
                template,
                targets,
                unwind,
                ..
            } => IrTerminatorKind::InlineAsm {
                template: format!("{template:?}"),
                targets: targets.iter().map(|bb| bb.as_usize()).collect(),
                unwind: lower_unwind_action(*unwind),
            },
        };
        IrTerminator {
            kind,
            span: format_span(self.tcx, term.source_info.span),
            comment: Some(format!("{:?}", term.kind)),
        }
    }

    /// Transitively lowers all `AllocId`s referenced by constants in this MIR
    /// body into `IrCapturedAllocation` records.
    ///
    /// `rustc` (`compiler/rustc_middle/src/mir/interpret/allocation.rs`)
    /// defines `Allocation` as:
    ///
    /// >```text
    /// >pub struct Allocation<Prov: Provenance = CtfeProvenance, Extra = (), Bytes = Box<[u8]>> {
    /// >    bytes: Bytes,
    /// >    provenance: ProvenanceMap<Prov>,
    /// >    init_mask: InitMask,
    /// >    pub align: Align,
    /// >    pub mutability: Mutability,
    /// >    pub extra: Extra,
    /// >}
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L95-L117
    fn drain_allocations(&mut self) -> Vec<IrCapturedAllocation> {
        let mut out_by_id: BTreeMap<u64, IrCapturedAllocation> = BTreeMap::new();
        let mut cursor = 0;
        while cursor < self.pending_allocs.len() {
            let alloc_id = self.pending_allocs[cursor];
            cursor += 1;
            let raw_id = alloc_id.0.get();
            if out_by_id.contains_key(&raw_id) {
                continue;
            }
            if let Some(captured) = self.extract_global_alloc(alloc_id) {
                out_by_id.insert(raw_id, captured);
            }
        }
        out_by_id.into_values().collect()
    }

    fn extract_global_alloc(&mut self, alloc_id: AllocId) -> Option<IrCapturedAllocation> {
        let raw_id = alloc_id.0.get();
        let const_alloc = match self.tcx.global_alloc(alloc_id) {
            GlobalAlloc::Memory(mem) => mem,
            GlobalAlloc::Static(def_id) => {
                if self.tcx.is_foreign_item(def_id) {
                    return None;
                }
                let val = self.tcx.eval_static_initializer(def_id).ok()?;
                val
            }
            GlobalAlloc::Function { .. } | GlobalAlloc::VTable(..) | GlobalAlloc::TypeId { .. } => {
                return None;
            }
        };

        let alloc = const_alloc.inner();
        let len = alloc.len();
        let raw_bytes = alloc.inspect_with_uninit_and_ptr_outside_interpreter(0..len);
        let init_mask = alloc.init_mask();
        let mut bytes = Vec::with_capacity(len);
        for (i, &b) in raw_bytes.iter().enumerate() {
            let is_init = init_mask
                .is_range_initialized(alloc_range(
                    Size::from_bytes(i as u64),
                    Size::from_bytes(1),
                ))
                .is_ok();
            bytes.push(if is_init { Some(b) } else { None });
        }

        let ptr_size = self.tcx.data_layout().pointer_size().bytes_usize();
        let endian = self.tcx.data_layout().endian;
        let mut relocations = Vec::with_capacity(alloc.provenance().ptrs().len());
        for &(offset, prov) in alloc.provenance().ptrs().iter() {
            let target_alloc_id = self.record_alloc_id(prov.alloc_id());
            let idx = offset.bytes_usize();
            let target_offset = if idx + ptr_size <= raw_bytes.len() {
                read_uint_bytes(endian, &raw_bytes[idx..idx + ptr_size])
            } else {
                0
            };
            relocations.push((
                offset.bytes(),
                IrProvenancePtr {
                    alloc_id: target_alloc_id,
                    offset_bytes: target_offset,
                },
            ));
        }

        Some(IrCapturedAllocation {
            alloc_id: raw_id,
            bytes,
            relocations,
            align: lower_align(alloc.align),
            mutability: lower_mutability(alloc.mutability),
        })
    }

    /// Lowers a `Body<'tcx>`'s local declarations and control-flow graph,
    /// materializes `StorageLive` statements for always-live locals, and
    /// recursively inlines `anodized::__` closure evaluation wrappers.
    ///
    /// In `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`), locals without
    /// any `StorageLive` or `StorageDead` statement in the body are implicitly
    /// allocated for the entire duration of the function:
    ///
    /// >```text
    /// >/// Some locals have no `StorageLive` or `StorageDead` statements
    /// >/// within the entire MIR body. These locals are implicitly allocated
    /// >/// for the full duration of the function. There is a convenience
    /// >/// method at `rustc_mir_dataflow::storage::always_storage_live_locals`
    /// >/// for computing these locals.
    /// >StorageLive(Local),
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L374-L382
    ///
    /// Similarly, in `rustc` (`compiler/rustc_middle/src/ty/closure.rs`),
    /// closure captures are represented as fields of the closure capture struct
    /// at argument local `_1`:
    ///
    /// >```text
    /// >/// Captures are represented using fields inside a structure.
    /// >/// This represents accessing self in the closure structure
    /// >pub const CAPTURE_STRUCT_LOCAL: mir::Local = mir::Local::arg(0);
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/closure.rs#L18-L20
    fn lower_body_cfg(
        &mut self,
        body: &Body<'tcx>,
        is_inlined_closure: bool,
    ) -> (Vec<IrLocalDecl>, Vec<IrBasicBlockData>) {
        let debug_names = collect_local_debug_names(body);
        let mut local_decls = Vec::with_capacity(body.local_decls.len());
        for (local_idx, decl) in body.local_decls.iter_enumerated() {
            local_decls.push(
                self.lower_local_decl(decl, debug_names.get(&local_idx.as_usize()).cloned()),
            );
        }

        let mut basic_blocks: Vec<IrBasicBlockData> = body
            .basic_blocks
            .iter()
            .map(|bb| self.lower_basic_block(bb))
            .collect();

        let inlined_any =
            self.inline_anodized_closure_calls(body, &mut local_decls, &mut basic_blocks);
        if is_inlined_closure || inlined_any {
            rewrite_closure_aggregates_to_tuples(&mut basic_blocks);
            strip_storage_markers(&mut basic_blocks);
            fuse_linear_goto_blocks(&mut basic_blocks);
            compact_unused_locals(body.arg_count, &mut local_decls, &mut basic_blocks);
        }

        materialize_always_live_locals(body.arg_count, local_decls.len(), &mut basic_blocks);

        (local_decls, basic_blocks)
    }

    fn inline_anodized_closure_calls(
        &mut self,
        body: &Body<'tcx>,
        local_decls: &mut Vec<IrLocalDecl>,
        basic_blocks: &mut Vec<IrBasicBlockData>,
    ) -> bool {
        let orig_bb_len = body.basic_blocks.len();
        let mut inlined_any = false;

        for bb_idx in 0..orig_bb_len {
            let Some(term) = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(bb_idx)]
                .terminator
            else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(return_bb),
                ..
            } = &term.kind
            else {
                continue;
            };
            let func_ty = func.ty(&body.local_decls, self.tcx);
            let TyKind::FnDef(callee_def_id, _) = *func_ty.kind() else {
                continue;
            };
            let callee_path = canonical_def_path(self.tcx, callee_def_id);
            let term_span = format_span(self.tcx, term.source_info.span);
            let ir_destination = self.lower_place(*destination);
            let return_bb_idx = return_bb.as_usize();

            if callee_path.ends_with("::__::coerce_input") {
                inlined_any = true;
                basic_blocks[bb_idx].statements.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        ir_destination,
                        IrRvalue::Aggregate(IrAggregateKind::Tuple, Vec::new()),
                    ),
                    span: term_span.clone(),
                    comment: None,
                });
                basic_blocks[bb_idx].terminator = IrTerminator {
                    kind: IrTerminatorKind::Goto(return_bb_idx),
                    span: term_span,
                    comment: None,
                };
                continue;
            }

            let is_eval_once = callee_path.ends_with("::__::eval_once");
            let is_eval = callee_path.ends_with("::__::eval");
            let is_apply_keep = callee_path.ends_with("::__::apply_keep");
            if !is_eval_once && !is_eval && !is_apply_keep {
                continue;
            }
            let Some(closure_arg) = args.first().map(|sp| &sp.node) else {
                continue;
            };
            let closure_ty = closure_arg.ty(&body.local_decls, self.tcx);
            let TyKind::Closure(closure_def_id, _) = *closure_ty.kind() else {
                continue;
            };

            inlined_any = true;
            let ir_closure_op = self.lower_operand(closure_arg);
            let ir_val_op = if is_apply_keep {
                args.get(1).map(|sp| self.lower_operand(&sp.node))
            } else {
                None
            };

            let closure_val_local = if is_eval_once {
                None
            } else {
                let loc = local_decls.len();
                local_decls.push(IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: self.lower_ty(closure_ty),
                    debug_name: None,
                });
                Some(loc)
            };

            let closure_body = self.tcx.optimized_mir(closure_def_id);
            let (closure_locals, mut closure_blocks) = self.lower_body_cfg(closure_body, true);
            let local_offset = local_decls.len();
            let block_offset = basic_blocks.len();
            local_decls.extend(closure_locals);

            let caller_stmts = &mut basic_blocks[bb_idx].statements;
            if let Some(cv_loc) = closure_val_local {
                caller_stmts.push(synth_storage_live(cv_loc));
            }
            for arg_idx in 0..=closure_body.arg_count {
                caller_stmts.push(synth_storage_live(local_offset + arg_idx));
            }
            if let Some(cv_loc) = closure_val_local {
                caller_stmts.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: cv_loc,
                            projection: Vec::new(),
                        },
                        IrRvalue::Use(ir_closure_op),
                    ),
                    span: term_span.clone(),
                    comment: None,
                });
                caller_stmts.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: local_offset + 1,
                            projection: Vec::new(),
                        },
                        IrRvalue::Ref(
                            IrBorrowKind::Shared,
                            IrPlace {
                                local_: cv_loc,
                                projection: Vec::new(),
                            },
                        ),
                    ),
                    span: term_span.clone(),
                    comment: None,
                });
            } else {
                caller_stmts.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: local_offset + 1,
                            projection: Vec::new(),
                        },
                        IrRvalue::Use(ir_closure_op),
                    ),
                    span: term_span.clone(),
                    comment: None,
                });
            }
            if let Some(val_op) = ir_val_op {
                caller_stmts.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: local_offset + 2,
                            projection: Vec::new(),
                        },
                        IrRvalue::Use(val_op),
                    ),
                    span: term_span.clone(),
                    comment: None,
                });
            }

            if closure_blocks.len() == 1
                && matches!(closure_blocks[0].terminator.kind, IrTerminatorKind::Return)
            {
                let mut single_bb = closure_blocks.pop().expect("single closure block");
                shift_basic_block(&mut single_bb, local_offset, 0);
                caller_stmts.append(&mut single_bb.statements);
                caller_stmts.push(IrStatement {
                    kind: IrStatementKind::Assign(
                        ir_destination,
                        IrRvalue::Use(IrOperand::Move(IrPlace {
                            local_: local_offset,
                            projection: Vec::new(),
                        })),
                    ),
                    span: single_bb.terminator.span,
                    comment: None,
                });
                basic_blocks[bb_idx].terminator = IrTerminator {
                    kind: IrTerminatorKind::Goto(return_bb_idx),
                    span: term_span,
                    comment: None,
                };
            } else {
                for cbb in &mut closure_blocks {
                    shift_basic_block(cbb, local_offset, block_offset);
                    if matches!(cbb.terminator.kind, IrTerminatorKind::Return) {
                        cbb.statements.push(IrStatement {
                            kind: IrStatementKind::Assign(
                                ir_destination.clone(),
                                IrRvalue::Use(IrOperand::Move(IrPlace {
                                    local_: local_offset,
                                    projection: Vec::new(),
                                })),
                            ),
                            span: cbb.terminator.span.clone(),
                            comment: None,
                        });
                        cbb.terminator = IrTerminator {
                            kind: IrTerminatorKind::Goto(return_bb_idx),
                            span: cbb.terminator.span.clone(),
                            comment: None,
                        };
                    }
                }
                basic_blocks[bb_idx].terminator = IrTerminator {
                    kind: IrTerminatorKind::Goto(block_offset),
                    span: term_span,
                    comment: None,
                };
                basic_blocks.extend(closure_blocks);
            }
        }

        inlined_any
    }
}

fn synth_storage_live(loc: usize) -> IrStatement {
    IrStatement {
        kind: IrStatementKind::StorageLive(loc),
        span: String::from("<dummy>"),
        comment: None,
    }
}

fn materialize_always_live_locals(
    arg_count: usize,
    local_count: usize,
    basic_blocks: &mut [IrBasicBlockData],
) {
    if basic_blocks.is_empty() || local_count <= arg_count + 1 {
        return;
    }
    let mut explicit_storage = BTreeSet::new();
    let referenced = collect_referenced_locals(basic_blocks);
    for bb in basic_blocks.iter() {
        for stmt in &bb.statements {
            if let IrStatementKind::StorageLive(loc) | IrStatementKind::StorageDead(loc) = stmt.kind
            {
                explicit_storage.insert(loc);
            }
        }
    }
    let mut prepended = Vec::new();
    for loc in (arg_count + 1)..local_count {
        if referenced.contains(&loc) && !explicit_storage.contains(&loc) {
            prepended.push(synth_storage_live(loc));
        }
    }
    if !prepended.is_empty() {
        prepended.append(&mut basic_blocks[0].statements);
        basic_blocks[0].statements = prepended;
    }
}

fn strip_storage_markers(basic_blocks: &mut [IrBasicBlockData]) {
    for bb in basic_blocks {
        bb.statements.retain(|stmt| {
            !matches!(
                stmt.kind,
                IrStatementKind::StorageLive(_) | IrStatementKind::StorageDead(_)
            )
        });
    }
}

fn record_place_locals(p: &IrPlace, used: &mut BTreeSet<usize>) {
    used.insert(p.local_);
    for proj in &p.projection {
        if let IrProjectionElem::Index(loc) = proj {
            used.insert(*loc);
        }
    }
}

fn record_op_locals(op: &IrOperand, used: &mut BTreeSet<usize>) {
    if let IrOperand::Copy(p) | IrOperand::Move(p) = op {
        record_place_locals(p, used);
    }
}

fn collect_referenced_locals(basic_blocks: &[IrBasicBlockData]) -> BTreeSet<usize> {
    let mut used = BTreeSet::new();
    for bb in basic_blocks {
        for stmt in &bb.statements {
            match &stmt.kind {
                IrStatementKind::Assign(p, rv) => {
                    record_place_locals(p, &mut used);
                    match rv {
                        IrRvalue::Use(op)
                        | IrRvalue::Repeat(op, _)
                        | IrRvalue::Cast(_, op, _)
                        | IrRvalue::UnaryOp(_, op)
                        | IrRvalue::ShallowInitBox(op, _)
                        | IrRvalue::WrapUnsafeBinder(op, _) => record_op_locals(op, &mut used),
                        IrRvalue::Ref(_, rp)
                        | IrRvalue::RawPtr(_, rp)
                        | IrRvalue::Len(rp)
                        | IrRvalue::Discriminant(rp)
                        | IrRvalue::CopyForDeref(rp) => record_place_locals(rp, &mut used),
                        IrRvalue::BinaryOp(_, lhs, rhs) => {
                            record_op_locals(lhs, &mut used);
                            record_op_locals(rhs, &mut used);
                        }
                        IrRvalue::Aggregate(_, ops) => {
                            for op in ops {
                                record_op_locals(op, &mut used);
                            }
                        }
                        IrRvalue::ThreadLocalRef(_) | IrRvalue::NullaryOp(_, _) => {}
                    }
                }
                IrStatementKind::SetDiscriminant(p, _)
                | IrStatementKind::Deinit(p)
                | IrStatementKind::Retag(_, p)
                | IrStatementKind::PlaceMention(p)
                | IrStatementKind::BackwardIncompatibleDropHint(p) => {
                    record_place_locals(p, &mut used);
                }
                IrStatementKind::StorageLive(loc) | IrStatementKind::StorageDead(loc) => {
                    used.insert(*loc);
                }
                IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
                    record_op_locals(op, &mut used);
                }
                IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
                    src,
                    dst,
                    count,
                }) => {
                    record_op_locals(src, &mut used);
                    record_op_locals(dst, &mut used);
                    record_op_locals(count, &mut used);
                }
                IrStatementKind::Coverage
                | IrStatementKind::ConstEvalCounter
                | IrStatementKind::Nop => {}
            }
        }
        match &bb.terminator.kind {
            IrTerminatorKind::SwitchInt(op, _) | IrTerminatorKind::Assert { cond: op, .. } => {
                record_op_locals(op, &mut used);
            }
            IrTerminatorKind::Drop { place, .. } => record_place_locals(place, &mut used),
            IrTerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                record_op_locals(func, &mut used);
                for arg in args {
                    record_op_locals(arg, &mut used);
                }
                record_place_locals(destination, &mut used);
            }
            IrTerminatorKind::TailCall { func, args } => {
                record_op_locals(func, &mut used);
                for arg in args {
                    record_op_locals(arg, &mut used);
                }
            }
            IrTerminatorKind::Goto(_)
            | IrTerminatorKind::UnwindResume
            | IrTerminatorKind::UnwindTerminate
            | IrTerminatorKind::Return
            | IrTerminatorKind::Unreachable
            | IrTerminatorKind::InlineAsm { .. } => {}
        }
    }
    used
}

fn compact_unused_locals(
    arg_count: usize,
    local_decls: &mut Vec<IrLocalDecl>,
    basic_blocks: &mut [IrBasicBlockData],
) {
    let referenced = collect_referenced_locals(basic_blocks);
    let mut remap = vec![0usize; local_decls.len()];
    let mut new_decls = Vec::with_capacity(local_decls.len());
    for (idx, decl) in local_decls.drain(..).enumerate() {
        if idx <= arg_count || referenced.contains(&idx) {
            remap[idx] = new_decls.len();
            new_decls.push(decl);
        }
    }
    *local_decls = new_decls;

    let remap_place = |p: &mut IrPlace| {
        p.local_ = remap[p.local_];
        for proj in &mut p.projection {
            if let IrProjectionElem::Index(loc) = proj {
                *loc = remap[*loc];
            }
        }
    };
    let remap_op = |op: &mut IrOperand| {
        if let IrOperand::Copy(p) | IrOperand::Move(p) = op {
            remap_place(p);
        }
    };
    for bb in basic_blocks {
        for stmt in &mut bb.statements {
            match &mut stmt.kind {
                IrStatementKind::Assign(p, rv) => {
                    remap_place(p);
                    match rv {
                        IrRvalue::Use(op)
                        | IrRvalue::Repeat(op, _)
                        | IrRvalue::Cast(_, op, _)
                        | IrRvalue::UnaryOp(_, op)
                        | IrRvalue::ShallowInitBox(op, _)
                        | IrRvalue::WrapUnsafeBinder(op, _) => remap_op(op),
                        IrRvalue::Ref(_, rp)
                        | IrRvalue::RawPtr(_, rp)
                        | IrRvalue::Len(rp)
                        | IrRvalue::Discriminant(rp)
                        | IrRvalue::CopyForDeref(rp) => remap_place(rp),
                        IrRvalue::BinaryOp(_, lhs, rhs) => {
                            remap_op(lhs);
                            remap_op(rhs);
                        }
                        IrRvalue::Aggregate(_, ops) => {
                            for op in ops {
                                remap_op(op);
                            }
                        }
                        IrRvalue::ThreadLocalRef(_) | IrRvalue::NullaryOp(_, _) => {}
                    }
                }
                IrStatementKind::SetDiscriminant(p, _)
                | IrStatementKind::Deinit(p)
                | IrStatementKind::Retag(_, p)
                | IrStatementKind::PlaceMention(p)
                | IrStatementKind::BackwardIncompatibleDropHint(p) => remap_place(p),
                IrStatementKind::StorageLive(loc) | IrStatementKind::StorageDead(loc) => {
                    *loc = remap[*loc];
                }
                IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => remap_op(op),
                IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
                    src,
                    dst,
                    count,
                }) => {
                    remap_op(src);
                    remap_op(dst);
                    remap_op(count);
                }
                IrStatementKind::Coverage
                | IrStatementKind::ConstEvalCounter
                | IrStatementKind::Nop => {}
            }
        }
        match &mut bb.terminator.kind {
            IrTerminatorKind::SwitchInt(op, _) | IrTerminatorKind::Assert { cond: op, .. } => {
                remap_op(op);
            }
            IrTerminatorKind::Drop { place, .. } => remap_place(place),
            IrTerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                remap_op(func);
                for arg in args {
                    remap_op(arg);
                }
                remap_place(destination);
            }
            IrTerminatorKind::TailCall { func, args } => {
                remap_op(func);
                for arg in args {
                    remap_op(arg);
                }
            }
            IrTerminatorKind::Goto(_)
            | IrTerminatorKind::UnwindResume
            | IrTerminatorKind::UnwindTerminate
            | IrTerminatorKind::Return
            | IrTerminatorKind::Unreachable
            | IrTerminatorKind::InlineAsm { .. } => {}
        }
    }
}

fn terminator_successors(kind: &IrTerminatorKind) -> Vec<usize> {
    let mut succs = Vec::new();
    let push_unwind = |succs: &mut Vec<usize>, unwind: &IrUnwindAction| {
        if let IrUnwindAction::Cleanup(bb) = unwind {
            succs.push(*bb);
        }
    };
    match kind {
        IrTerminatorKind::Goto(target) => succs.push(*target),
        IrTerminatorKind::SwitchInt(_, targets) => {
            for (_, target) in &targets.branches {
                succs.push(*target);
            }
            succs.push(targets.otherwise);
        }
        IrTerminatorKind::Drop { target, unwind, .. }
        | IrTerminatorKind::Assert { target, unwind, .. } => {
            succs.push(*target);
            push_unwind(&mut succs, unwind);
        }
        IrTerminatorKind::Call { target, unwind, .. } => {
            if let Some(target_bb) = target {
                succs.push(*target_bb);
            }
            push_unwind(&mut succs, unwind);
        }
        IrTerminatorKind::InlineAsm {
            targets, unwind, ..
        } => {
            succs.extend(targets.iter().copied());
            push_unwind(&mut succs, unwind);
        }
        IrTerminatorKind::UnwindResume
        | IrTerminatorKind::UnwindTerminate
        | IrTerminatorKind::Return
        | IrTerminatorKind::Unreachable
        | IrTerminatorKind::TailCall { .. } => {}
    }
    succs
}

fn fuse_linear_goto_blocks(basic_blocks: &mut Vec<IrBasicBlockData>) {
    if basic_blocks.len() <= 1 {
        return;
    }
    loop {
        let mut in_degree = vec![0usize; basic_blocks.len()];
        in_degree[0] = 2;
        for bb in basic_blocks.iter() {
            for succ in terminator_successors(&bb.terminator.kind) {
                if succ < in_degree.len() {
                    in_degree[succ] += 1;
                }
            }
        }
        let mut merged = false;
        for idx in 0..basic_blocks.len() {
            if let IrTerminatorKind::Goto(target) = basic_blocks[idx].terminator.kind
                && target < basic_blocks.len()
                && target != idx
                && in_degree[target] == 1
                && basic_blocks[idx].is_cleanup == basic_blocks[target].is_cleanup
            {
                let mut target_stmts = std::mem::take(&mut basic_blocks[target].statements);
                let target_term = basic_blocks[target].terminator.clone();
                basic_blocks[idx].statements.append(&mut target_stmts);
                basic_blocks[idx].terminator = target_term;
                basic_blocks[target].terminator = IrTerminator {
                    kind: IrTerminatorKind::Unreachable,
                    span: String::new(),
                    comment: None,
                };
                merged = true;
                break;
            }
        }
        if !merged {
            break;
        }
    }

    let mut reachable = BTreeSet::new();
    let mut stack = vec![0usize];
    while let Some(bb_idx) = stack.pop() {
        if bb_idx < basic_blocks.len() && reachable.insert(bb_idx) {
            for succ in terminator_successors(&basic_blocks[bb_idx].terminator.kind) {
                stack.push(succ);
            }
        }
    }

    let mut remap = vec![0usize; basic_blocks.len()];
    let mut new_blocks = Vec::with_capacity(reachable.len());
    for (old_idx, bb) in basic_blocks.drain(..).enumerate() {
        if reachable.contains(&old_idx) {
            remap[old_idx] = new_blocks.len();
            new_blocks.push(bb);
        }
    }
    for bb in &mut new_blocks {
        let remap_unwind = |unwind: &mut IrUnwindAction| {
            if let IrUnwindAction::Cleanup(u) = unwind {
                *u = remap[*u];
            }
        };
        match &mut bb.terminator.kind {
            IrTerminatorKind::Goto(target) => *target = remap[*target],
            IrTerminatorKind::SwitchInt(_, targets) => {
                for (_, target) in &mut targets.branches {
                    *target = remap[*target];
                }
                targets.otherwise = remap[targets.otherwise];
            }
            IrTerminatorKind::Drop { target, unwind, .. }
            | IrTerminatorKind::Assert { target, unwind, .. } => {
                *target = remap[*target];
                remap_unwind(unwind);
            }
            IrTerminatorKind::Call { target, unwind, .. } => {
                if let Some(target_bb) = target {
                    *target_bb = remap[*target_bb];
                }
                remap_unwind(unwind);
            }
            IrTerminatorKind::InlineAsm {
                targets, unwind, ..
            } => {
                for target in targets {
                    *target = remap[*target];
                }
                remap_unwind(unwind);
            }
            IrTerminatorKind::UnwindResume
            | IrTerminatorKind::UnwindTerminate
            | IrTerminatorKind::Return
            | IrTerminatorKind::Unreachable
            | IrTerminatorKind::TailCall { .. } => {}
        }
    }
    *basic_blocks = new_blocks;
}

fn rewrite_closure_aggregates_to_tuples(basic_blocks: &mut [IrBasicBlockData]) {
    for bb in basic_blocks {
        for stmt in &mut bb.statements {
            if let IrStatementKind::Assign(_, IrRvalue::Aggregate(kind, _)) = &mut stmt.kind
                && matches!(kind, IrAggregateKind::Closure(_))
            {
                *kind = IrAggregateKind::Tuple;
            }
        }
    }
}

fn shift_place(place: &mut IrPlace, local_offset: usize) {
    place.local_ += local_offset;
    for proj in &mut place.projection {
        if let IrProjectionElem::Index(loc) = proj {
            *loc += local_offset;
        }
    }
}

fn shift_operand(op: &mut IrOperand, local_offset: usize) {
    match op {
        IrOperand::Copy(p) | IrOperand::Move(p) => shift_place(p, local_offset),
        IrOperand::Constant(_) => {}
    }
}

fn shift_rvalue(rv: &mut IrRvalue, local_offset: usize) {
    match rv {
        IrRvalue::Use(op)
        | IrRvalue::Repeat(op, _)
        | IrRvalue::Cast(_, op, _)
        | IrRvalue::UnaryOp(_, op)
        | IrRvalue::ShallowInitBox(op, _)
        | IrRvalue::WrapUnsafeBinder(op, _) => shift_operand(op, local_offset),
        IrRvalue::Ref(_, p)
        | IrRvalue::RawPtr(_, p)
        | IrRvalue::Len(p)
        | IrRvalue::Discriminant(p)
        | IrRvalue::CopyForDeref(p) => shift_place(p, local_offset),
        IrRvalue::BinaryOp(_, lhs, rhs) => {
            shift_operand(lhs, local_offset);
            shift_operand(rhs, local_offset);
        }
        IrRvalue::Aggregate(_, ops) => {
            for op in ops {
                shift_operand(op, local_offset);
            }
        }
        IrRvalue::ThreadLocalRef(_) | IrRvalue::NullaryOp(_, _) => {}
    }
}

fn shift_unwind_action(unwind: &mut IrUnwindAction, block_offset: usize) {
    if let IrUnwindAction::Cleanup(bb) = unwind {
        *bb += block_offset;
    }
}

fn shift_basic_block(bb: &mut IrBasicBlockData, local_offset: usize, block_offset: usize) {
    for stmt in &mut bb.statements {
        match &mut stmt.kind {
            IrStatementKind::Assign(p, rv) => {
                shift_place(p, local_offset);
                shift_rvalue(rv, local_offset);
            }
            IrStatementKind::SetDiscriminant(p, _)
            | IrStatementKind::Deinit(p)
            | IrStatementKind::Retag(_, p)
            | IrStatementKind::PlaceMention(p)
            | IrStatementKind::BackwardIncompatibleDropHint(p) => shift_place(p, local_offset),
            IrStatementKind::StorageLive(loc) | IrStatementKind::StorageDead(loc) => {
                *loc += local_offset;
            }
            IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
                shift_operand(op, local_offset);
            }
            IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
                src,
                dst,
                count,
            }) => {
                shift_operand(src, local_offset);
                shift_operand(dst, local_offset);
                shift_operand(count, local_offset);
            }
            IrStatementKind::Coverage | IrStatementKind::ConstEvalCounter | IrStatementKind::Nop => {
            }
        }
    }
    match &mut bb.terminator.kind {
        IrTerminatorKind::Goto(target) => *target += block_offset,
        IrTerminatorKind::SwitchInt(op, targets) => {
            shift_operand(op, local_offset);
            for (_, target) in &mut targets.branches {
                *target += block_offset;
            }
            targets.otherwise += block_offset;
        }
        IrTerminatorKind::Drop {
            place,
            target,
            unwind,
        } => {
            shift_place(place, local_offset);
            *target += block_offset;
            shift_unwind_action(unwind, block_offset);
        }
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            shift_operand(func, local_offset);
            for arg in args {
                shift_operand(arg, local_offset);
            }
            shift_place(destination, local_offset);
            if let Some(target_bb) = target {
                *target_bb += block_offset;
            }
            shift_unwind_action(unwind, block_offset);
        }
        IrTerminatorKind::TailCall { func, args } => {
            shift_operand(func, local_offset);
            for arg in args {
                shift_operand(arg, local_offset);
            }
        }
        IrTerminatorKind::Assert {
            cond,
            expected: _,
            target,
            unwind,
        } => {
            shift_operand(cond, local_offset);
            *target += block_offset;
            shift_unwind_action(unwind, block_offset);
        }
        IrTerminatorKind::InlineAsm {
            targets, unwind, ..
        } => {
            for target in targets {
                *target += block_offset;
            }
            shift_unwind_action(unwind, block_offset);
        }
        IrTerminatorKind::UnwindResume
        | IrTerminatorKind::UnwindTerminate
        | IrTerminatorKind::Return
        | IrTerminatorKind::Unreachable => {}
    }
}

fn read_uint_bytes(endian: Endian, bytes: &[u8]) -> u64 {
    let mut val = 0u64;
    match endian {
        Endian::Little => {
            for (i, &b) in bytes.iter().take(8).enumerate() {
                val |= u64::from(b) << (i * 8);
            }
        }
        Endian::Big => {
            for &b in bytes.iter().take(8) {
                val = (val << 8) | u64::from(b);
            }
        }
    }
    val
}

fn lower_mutability(m: Mutability) -> IrMutability {
    match m {
        Mutability::Not => IrMutability::Not,
        Mutability::Mut => IrMutability::Mut,
    }
}

fn lower_uint_ty(u: UintTy) -> IrUintTy {
    match u {
        UintTy::U8 => IrUintTy::U8,
        UintTy::U16 => IrUintTy::U16,
        UintTy::U32 => IrUintTy::U32,
        UintTy::U64 => IrUintTy::U64,
        UintTy::U128 => IrUintTy::U128,
        UintTy::Usize => IrUintTy::Usize,
    }
}

fn lower_int_ty(i: IntTy) -> IrIntTy {
    match i {
        IntTy::I8 => IrIntTy::I8,
        IntTy::I16 => IrIntTy::I16,
        IntTy::I32 => IrIntTy::I32,
        IntTy::I64 => IrIntTy::I64,
        IntTy::I128 => IrIntTy::I128,
        IntTy::Isize => IrIntTy::Isize,
    }
}

fn lower_float_ty(f: FloatTy) -> IrFloatTy {
    match f {
        FloatTy::F16 => IrFloatTy::F16,
        FloatTy::F32 => IrFloatTy::F32,
        FloatTy::F64 => IrFloatTy::F64,
        FloatTy::F128 => IrFloatTy::F128,
    }
}

fn lower_scalar_int(si: ScalarInt) -> IrScalarInt {
    let size = si.size();
    IrScalarInt {
        bits: si.to_bits(size),
        size_bytes: size.bytes(),
    }
}

/// Lowers `rustc_middle::mir::BinOp` into `IrBinOp`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `BinOp` as:
///
/// >```text
/// >pub enum BinOp {
/// >    Add,
/// >    AddUnchecked,
/// >    AddWithOverflow,
/// >    Sub,
/// >    SubUnchecked,
/// >    SubWithOverflow,
/// >    Mul,
/// >    MulUnchecked,
/// >    MulWithOverflow,
/// >    Div,
/// >    Rem,
/// >    BitXor,
/// >    BitAnd,
/// >    BitOr,
/// >    Shl,
/// >    ShlUnchecked,
/// >    Shr,
/// >    ShrUnchecked,
/// >    Eq,
/// >    Lt,
/// >    Le,
/// >    Ne,
/// >    Ge,
/// >    Gt,
/// >    Cmp,
/// >    Offset,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709
fn lower_bin_op(op: BinOp) -> IrBinOp {
    match op {
        BinOp::Add => IrBinOp::Add,
        BinOp::AddUnchecked => IrBinOp::AddUnchecked,
        BinOp::AddWithOverflow => IrBinOp::AddWithOverflow,
        BinOp::Sub => IrBinOp::Sub,
        BinOp::SubUnchecked => IrBinOp::SubUnchecked,
        BinOp::SubWithOverflow => IrBinOp::SubWithOverflow,
        BinOp::Mul => IrBinOp::Mul,
        BinOp::MulUnchecked => IrBinOp::MulUnchecked,
        BinOp::MulWithOverflow => IrBinOp::MulWithOverflow,
        BinOp::Div => IrBinOp::Div,
        BinOp::Rem => IrBinOp::Rem,
        BinOp::BitXor => IrBinOp::BitXor,
        BinOp::BitAnd => IrBinOp::BitAnd,
        BinOp::BitOr => IrBinOp::BitOr,
        BinOp::Shl => IrBinOp::Shl,
        BinOp::ShlUnchecked => IrBinOp::ShlUnchecked,
        BinOp::Shr => IrBinOp::Shr,
        BinOp::ShrUnchecked => IrBinOp::ShrUnchecked,
        BinOp::Eq => IrBinOp::Eq,
        BinOp::Lt => IrBinOp::Lt,
        BinOp::Le => IrBinOp::Le,
        BinOp::Ne => IrBinOp::Ne,
        BinOp::Ge => IrBinOp::Ge,
        BinOp::Gt => IrBinOp::Gt,
        BinOp::Cmp => IrBinOp::Cmp,
        BinOp::Offset => IrBinOp::Offset,
    }
}

/// Lowers `rustc_middle::mir::UnOp` into `IrUnOp`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `UnOp` as:
///
/// >```text
/// >pub enum UnOp {
/// >    Not,
/// >    Neg,
/// >    PtrMetadata,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617
fn lower_un_op(op: UnOp) -> IrUnOp {
    match op {
        UnOp::Not => IrUnOp::Not,
        UnOp::Neg => IrUnOp::Neg,
        UnOp::PtrMetadata => IrUnOp::PtrMetadata,
    }
}

/// Lowers `rustc_middle::mir::CastKind` into `IrCastKind`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `CastKind` as:
///
/// >```text
/// >pub enum CastKind {
/// >    PointerExposeProvenance,
/// >    PointerWithExposedProvenance,
/// >    PointerCoercion(PointerCoercion, CoercionSource),
/// >    IntToInt,
/// >    FloatToInt,
/// >    FloatToFloat,
/// >    IntToFloat,
/// >    PtrToPtr,
/// >    FnPtrToPtr,
/// >    Transmute,
/// >    Subtype,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532
fn lower_cast_kind(ck: CastKind) -> IrCastKind {
    match ck {
        CastKind::PointerExposeProvenance => IrCastKind::PointerExposeProvenance,
        CastKind::PointerWithExposedProvenance => IrCastKind::PointerWithExposedProvenance,
        CastKind::PointerCoercion(coercion, _source) => {
            IrCastKind::PointerCoercion(format!("{coercion:?}"))
        }
        CastKind::IntToInt => IrCastKind::IntToInt,
        CastKind::FloatToInt => IrCastKind::FloatToInt,
        CastKind::FloatToFloat => IrCastKind::FloatToFloat,
        CastKind::IntToFloat => IrCastKind::IntToFloat,
        CastKind::PtrToPtr => IrCastKind::PtrToPtr,
        CastKind::FnPtrToPtr => IrCastKind::FnPtrToPtr,
        CastKind::Transmute => IrCastKind::Transmute,
        CastKind::Subtype => IrCastKind::Subtype,
    }
}

/// Lowers `rustc_middle::mir::SwitchTargets` into `IrSwitchTargets`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `SwitchTargets`
/// as:
///
/// >```text
/// >pub struct SwitchTargets {
/// >    values: SmallVec<[u128; 1]>,
/// >    targets: SmallVec<[BasicBlock; 2]>,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L999-L1014
fn lower_switch_targets(targets: &SwitchTargets) -> IrSwitchTargets {
    IrSwitchTargets {
        branches: targets
            .iter()
            .map(|(val, bb)| (val, bb.as_usize()))
            .collect(),
        otherwise: targets.otherwise().as_usize(),
    }
}

/// Lowers `rustc_middle::mir::UnwindAction` into `IrUnwindAction`.
///
/// `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`) defines `UnwindAction`
/// as:
///
/// >```text
/// >pub enum UnwindAction {
/// >    Continue,
/// >    Unreachable,
/// >    Terminate(UnwindTerminateReason),
/// >    Cleanup(BasicBlock),
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1018-L1044
fn lower_unwind_action(ua: UnwindAction) -> IrUnwindAction {
    match ua {
        UnwindAction::Cleanup(bb) => IrUnwindAction::Cleanup(bb.as_usize()),
        UnwindAction::Unreachable => IrUnwindAction::Unreachable,
        UnwindAction::Terminate(_) => IrUnwindAction::Terminate,
        UnwindAction::Continue => IrUnwindAction::Continue,
    }
}

fn format_span(tcx: TyCtxt<'_>, span: rustc_span::Span) -> String {
    if span.is_dummy() {
        return String::from("<dummy>");
    }
    tcx.sess.source_map().span_to_diagnostic_string(span)
}
