//! Target layout and function ABI extraction from `rustc_abi` and
//! `rustc_target` (`V2026_06_01`).
//!
//! This module lowers `rustc_abi::LayoutData` and
//! `rustc_target::callconv::FnAbi` into the toolchain-independent
//! `IrTypeLayout`, `IrLayoutTable`, and `IrFnAbi` structures emitted as
//! `Trusted.Rustc.V2026_06_01.Layout` records.
//!
//! `rustc` (`compiler/rustc_abi/src/lib.rs`) describes its layout and ABI
//! representations as:
//!
//! >Defines shared types used by both the `rustc_middle::ty::layout` module and
//! >the `rustc_target::callconv` module.
//!
//! Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1-L2

use rustc_abi::{
    Align, BackendRepr, CanonAbi, Endian, ExternAbi, FieldIdx, FieldsShape, Float, HasDataLayout,
    Integer, LayoutData, Primitive, Scalar, Size, VariantIdx, Variants, WrappingRange,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TypingEnv};
use rustc_target::callconv::{ArgAbi, FnAbi, PassMode};

use crate::lean_emit::{
    IrAbiPassMode, IrAlign, IrArgAbi, IrBackendRepr, IrCallConv, IrFieldsShape, IrFnAbi,
    IrLayoutTable, IrPrimitiveKind, IrScalarLayout, IrSize, IrTypeLayout, IrVariantsShape,
    IrWrappingRange,
};

/// Deduplicating table of monomorphized type layouts collected while lowering a
/// single MIR body.
pub struct LayoutTableBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    entries: Vec<IrTypeLayout>,
}

impl<'tcx> LayoutTableBuilder<'tcx> {
    /// Creates a new layout table builder for `def_id`.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            typing_env: TypingEnv::post_analysis(tcx, def_id),
            entries: Vec::new(),
        }
    }

    /// Returns the `TypingEnv` used for layout and constant evaluation queries.
    pub fn typing_env(&self) -> TypingEnv<'tcx> {
        self.typing_env
    }

    /// Interns the layout of `ty` into `self.entries` and returns its
    /// 0-based `layout_idx`.
    ///
    /// Queries `tcx.layout_of(...)` using `TypingEnv::post_analysis`
    /// (`compiler/rustc_middle/src/ty/layout.rs`):
    ///
    /// >```text
    /// >pub trait LayoutOf<'tcx>: LayoutOfHelpers<'tcx> {
    /// >    /// Computes the layout of a type. Note that this implicitly
    /// >    /// executes in `TypingMode::PostAnalysis`, and will normalize the input type.
    /// >    #[inline]
    /// >    fn layout_of(&self, ty: Ty<'tcx>) -> Self::LayoutOfResult {
    /// >        self.spanned_layout_of(ty, DUMMY_SP)
    /// >    }
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L706-L712
    ///
    /// For single-variant `FieldsShape::Arbitrary` aggregates (`ty::Tuple`,
    /// `ty::Closure`, and non-union `ty::Adt`), each field's monomorphized type
    /// is resolved in source field order (`FieldIdx::from_usize(i)`) and
    /// recursively interned into `IrTypeLayout::field_layouts`, matching
    /// `TyAndLayout::ty_and_layout_field` (`compiler/rustc_middle/src/ty/layout.rs`):
    ///
    /// >```text
    /// >                ty::Tuple(tys) => TyMaybeWithLayout::Ty(tys[i]),
    /// >
    /// >                // ADTs.
    /// >                ty::Adt(def, args) => {
    /// >                    match this.variants {
    /// >                        Variants::Single { index } => {
    /// >                            let field = &def.variant(index).fields[FieldIdx::from_usize(i)];
    /// >                            TyMaybeWithLayout::Ty(field.ty(tcx, args).skip_norm_wip())
    /// >                        }
    /// >```
    ///
    /// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L947-L955
    pub fn intern_ty_layout(&mut self, ty: Ty<'tcx>) -> usize {
        self.intern_ty_layout_depth(ty, 0)
    }

    fn intern_ty_layout_depth(&mut self, ty: Ty<'tcx>, depth: usize) -> usize {
        let ir_layout = match self.tcx.layout_of(self.typing_env.as_query_input(ty)) {
            Ok(ty_and_layout) => {
                let mut lowered = lower_layout_data(&ty_and_layout.layout.0);
                if depth < 16
                    && let FieldsShape::Arbitrary { ref offsets, .. } = ty_and_layout.fields
                    && !offsets.is_empty()
                    && let Variants::Single { index } = ty_and_layout.variants
                {
                    let field_tys: Option<Vec<Ty<'tcx>>> = match *ty_and_layout.ty.kind() {
                        ty::Tuple(tys) if tys.len() == offsets.len() => Some(tys.iter().collect()),
                        ty::Closure(_, args)
                            if args.as_closure().upvar_tys().len() == offsets.len() =>
                        {
                            Some(args.as_closure().upvar_tys().iter().collect())
                        }
                        ty::Adt(def, args)
                            if !def.is_union()
                                && def.variant(index).fields.len() == offsets.len() =>
                        {
                            let variant = def.variant(index);
                            Some(
                                (0..offsets.len())
                                    .map(|i| {
                                        variant.fields[FieldIdx::from_usize(i)]
                                            .ty(self.tcx, args)
                                            .skip_norm_wip()
                                    })
                                    .collect(),
                            )
                        }
                        _ => None,
                    };
                    if let Some(tys) = field_tys {
                        lowered.field_layouts = tys
                            .into_iter()
                            .map(|fty| self.intern_ty_layout_depth(fty, depth + 1))
                            .collect();
                    }
                }
                lowered
            }
            Err(_) => fallback_zst_layout(),
        };
        self.intern_ir_layout(ir_layout)
    }

    /// Interns an already-lowered `IrTypeLayout` and returns its deduplicated
    /// index.
    pub fn intern_ir_layout(&mut self, layout: IrTypeLayout) -> usize {
        if let Some(idx) = self.entries.iter().position(|existing| *existing == layout) {
            return idx;
        }
        let idx = self.entries.len();
        self.entries.push(layout);
        idx
    }

    /// Consumes the builder and returns the completed `IrLayoutTable`.
    pub fn finish(self) -> IrLayoutTable {
        let dl = self.tcx.data_layout();
        IrLayoutTable {
            pointer_bits: dl.pointer_size().bits(),
            is_little_endian: matches!(dl.endian, Endian::Little),
            entries: self.entries,
        }
    }
}

/// Lowers `rustc_abi::Size` (`Size::bytes()`) into `IrSize`.
pub fn lower_size(size: Size) -> IrSize {
    IrSize {
        bytes: size.bytes(),
    }
}

/// Lowers `rustc_abi::Align` (`Align::bytes()`) into `IrAlign`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `Align` as:
///
/// >```text
/// >/// Alignment of a type in bytes (always a power of two).
/// >#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// >#[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
/// >pub struct Align {
/// >    pow2: u8,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1019-L1024
pub fn lower_align(align: Align) -> IrAlign {
    IrAlign {
        bytes: align.bytes(),
    }
}

/// Lowers `rustc_abi::WrappingRange` into `IrWrappingRange`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `WrappingRange` as:
///
/// >```text
/// >#[derive(Clone, Copy, PartialEq, Eq, Hash)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub struct WrappingRange {
/// >    pub start: u128,
/// >    pub end: u128,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1428-L1433
pub fn lower_wrapping_range(range: WrappingRange) -> IrWrappingRange {
    IrWrappingRange {
        start: range.start,
        end_: range.end,
    }
}

/// Lowers `rustc_abi::Primitive` into `IrPrimitiveKind`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `Primitive` as:
///
/// >```text
/// >/// Fundamental unit of memory access and layout.
/// >#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub enum Primitive {
/// >    Int(Integer, bool),
/// >    Float(Float),
/// >    Pointer(AddressSpace),
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1379-L1393
pub fn lower_primitive(prim: Primitive) -> IrPrimitiveKind {
    match prim {
        Primitive::Int(int, signed) => {
            let bits = match int {
                Integer::I8 => 8,
                Integer::I16 => 16,
                Integer::I32 => 32,
                Integer::I64 => 64,
                Integer::I128 => 128,
            };
            IrPrimitiveKind::Int { bits, signed }
        }
        Primitive::Float(flt) => {
            let bits = match flt {
                Float::F16 => 16,
                Float::F32 => 32,
                Float::F64 => 64,
                Float::F128 => 128,
            };
            IrPrimitiveKind::Float { bits }
        }
        Primitive::Pointer(addr_space) => IrPrimitiveKind::Pointer {
            address_space: addr_space.0,
        },
    }
}

/// Lowers `rustc_abi::Scalar` into `IrScalarLayout`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `Scalar` as:
///
/// >```text
/// >/// Information about one scalar component of a Rust type.
/// >#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub enum Scalar {
/// >    Initialized {
/// >        value: Primitive,
/// >        valid_range: WrappingRange,
/// >    },
/// >    Union {
/// >        value: Primitive,
/// >    },
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1539-L1559
pub fn lower_scalar(scalar: Scalar) -> IrScalarLayout {
    match scalar {
        Scalar::Initialized { value, valid_range } => IrScalarLayout::Initialized {
            value: lower_primitive(value),
            valid_range: lower_wrapping_range(valid_range),
        },
        Scalar::Union { value } => IrScalarLayout::Union {
            value: lower_primitive(value),
        },
    }
}

/// Lowers `rustc_abi::FieldsShape<FieldIdx>` into `IrFieldsShape`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `FieldsShape` as:
///
/// >```text
/// >/// Describes how the fields of a type are located in memory.
/// >#[derive(PartialEq, Eq, Hash, Clone, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub enum FieldsShape<FieldIdx: Idx> {
/// >    Primitive,
/// >    Union(NonZeroUsize),
/// >    Array { stride: Size, count: u64 },
/// >    Arbitrary {
/// >        offsets: IndexVec<FieldIdx, Size>,
/// >        in_memory_order: IndexVec<u32, FieldIdx>,
/// >    },
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1643-L1679
pub fn lower_fields_shape(fields: &FieldsShape<FieldIdx>) -> IrFieldsShape {
    match fields {
        FieldsShape::Primitive => IrFieldsShape::Primitive,
        FieldsShape::Union(count) => IrFieldsShape::Union { count: count.get() },
        FieldsShape::Array { stride, count } => IrFieldsShape::Array {
            stride: lower_size(*stride),
            count: *count,
        },
        FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } => IrFieldsShape::Arbitrary {
            offsets: offsets.iter().copied().map(lower_size).collect(),
            memory_index: in_memory_order.iter().map(|idx| idx.as_usize()).collect(),
        },
    }
}

/// Lowers `rustc_abi::Variants<FieldIdx, VariantIdx>` into `IrVariantsShape`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `Variants` as:
///
/// >```text
/// >#[derive(PartialEq, Eq, Hash, Clone, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
/// >    Empty,
/// >    Single {
/// >        index: VariantIdx,
/// >    },
/// >    Multiple {
/// >        tag: Scalar,
/// >        tag_encoding: TagEncoding<VariantIdx>,
/// >        tag_field: FieldIdx,
/// >        variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>>,
/// >    },
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1935-L1959
pub fn lower_variants_shape(variants: &Variants<FieldIdx, VariantIdx>) -> IrVariantsShape {
    match variants {
        Variants::Empty => IrVariantsShape::Empty,
        Variants::Single { index } => IrVariantsShape::Single {
            index: index.as_usize(),
        },
        Variants::Multiple {
            tag,
            tag_field,
            variants,
            ..
        } => IrVariantsShape::Multiple {
            tag: lower_scalar(*tag),
            tag_field: tag_field.as_usize(),
            variants: variants
                .iter()
                .map(|v| {
                    let offsets: Vec<IrSize> =
                        v.field_offsets.iter().copied().map(lower_size).collect();
                    let mut memory_index: Vec<usize> = (0..offsets.len()).collect();
                    memory_index.sort_by_key(|&idx| offsets[idx].bytes);
                    IrFieldsShape::Arbitrary {
                        offsets,
                        memory_index,
                    }
                })
                .collect(),
        },
    }
}

/// Lowers `rustc_abi::BackendRepr` into `IrBackendRepr`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `BackendRepr` as:
///
/// >```text
/// >#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(StableHash))]
/// >pub enum BackendRepr {
/// >    Scalar(Scalar),
/// >    ScalarPair(Scalar, Scalar),
/// >    SimdScalableVector {
/// >        element: Scalar,
/// >        count: u64,
/// >        number_of_vectors: NumScalableVectors,
/// >    },
/// >    SimdVector {
/// >        element: Scalar,
/// >        count: u64,
/// >    },
/// >    Memory {
/// >        sized: bool,
/// >    },
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1791-L1810
pub fn lower_backend_repr(repr: BackendRepr) -> IrBackendRepr {
    match repr {
        BackendRepr::Scalar(s) => IrBackendRepr::Scalar(lower_scalar(s)),
        BackendRepr::ScalarPair(a, b) => IrBackendRepr::ScalarPair(lower_scalar(a), lower_scalar(b)),
        BackendRepr::Memory { .. }
        | BackendRepr::SimdVector { .. }
        | BackendRepr::SimdScalableVector { .. } => IrBackendRepr::Memory,
    }
}

/// Lowers `rustc_abi::LayoutData<FieldIdx, VariantIdx>` into `IrTypeLayout`.
///
/// `rustc` (`compiler/rustc_abi/src/lib.rs`) defines `LayoutData` as:
///
/// >```text
/// >pub struct LayoutData<FieldIdx: Idx, VariantIdx: Idx> {
/// >    pub fields: FieldsShape<FieldIdx>,
/// >    pub variants: Variants<FieldIdx, VariantIdx>,
/// >    pub backend_repr: BackendRepr,
/// >    pub largest_niche: Option<Niche>,
/// >    pub uninhabited: bool,
/// >    pub align: AbiAlign,
/// >    pub size: Size,
/// >    pub max_repr_align: Option<Align>,
/// >    pub unadjusted_abi_align: Align,
/// >    pub randomization_seed: Hash64,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L2102-L2157
pub fn lower_layout_data(layout: &LayoutData<FieldIdx, VariantIdx>) -> IrTypeLayout {
    IrTypeLayout {
        size: lower_size(layout.size),
        align: lower_align(layout.align.abi),
        backend_repr: lower_backend_repr(layout.backend_repr),
        fields: lower_fields_shape(&layout.fields),
        variants: lower_variants_shape(&layout.variants),
        is_uninhabited: layout.uninhabited,
        field_layouts: Vec::new(),
    }
}

/// Lowers `rustc_target::callconv::PassMode` into `IrAbiPassMode`.
///
/// `rustc` (`compiler/rustc_target/src/callconv/mod.rs`) defines `PassMode` as:
///
/// >```text
/// >#[derive(Clone, PartialEq, Eq, Hash, Debug, StableHash)]
/// >pub enum PassMode {
/// >    Ignore,
/// >    Direct(ArgAttributes),
/// >    Pair(ArgAttributes, ArgAttributes),
/// >    Cast { pad_i32: bool, cast: Box<CastTarget> },
/// >    Indirect { attrs: ArgAttributes, meta_attrs: Option<ArgAttributes>, on_stack: bool },
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_target/src/callconv/mod.rs#L38-L74
pub fn lower_pass_mode(mode: &PassMode) -> IrAbiPassMode {
    match mode {
        PassMode::Ignore => IrAbiPassMode::Ignore,
        PassMode::Direct(_) | PassMode::Cast { .. } => IrAbiPassMode::Direct,
        PassMode::Pair(_, _) => IrAbiPassMode::Pair,
        PassMode::Indirect { .. } => IrAbiPassMode::Indirect,
    }
}

/// Lowers `rustc_target::callconv::ArgAbi` into `IrArgAbi`.
///
/// `rustc` (`compiler/rustc_target/src/callconv/mod.rs`) defines `ArgAbi` as:
///
/// >```text
/// >#[derive(Clone, PartialEq, Eq, Hash, StableHash)]
/// >pub struct ArgAbi<'a, Ty> {
/// >    pub layout: TyAndLayout<'a, Ty>,
/// >    pub mode: PassMode,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_target/src/callconv/mod.rs#L366-L370
pub fn lower_arg_abi<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> IrArgAbi {
    IrArgAbi {
        layout: lower_layout_data(&arg.layout.layout.0),
        mode: lower_pass_mode(&arg.mode),
    }
}

/// Lowers `rustc_abi::CanonAbi` into `IrCallConv`.
///
/// `rustc` (`compiler/rustc_abi/src/canon_abi.rs`) defines `CanonAbi` as:
///
/// >```text
/// >pub enum CanonAbi {
/// >    C,
/// >    Rust,
/// >    RustCold,
/// >    RustPreserveNone,
/// >    Custom,
/// >    Swift,
/// >    Arm(ArmCall),
/// >    GpuKernel,
/// >    Interrupt(InterruptKind),
/// >    X86(X86Call),
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/canon_abi.rs#L22-L57
pub fn lower_canon_abi(conv: CanonAbi) -> IrCallConv {
    match conv {
        CanonAbi::Rust => IrCallConv::Rust,
        CanonAbi::C => IrCallConv::C,
        other => IrCallConv::Other(other.to_string()),
    }
}

/// Lowers `rustc_abi::ExternAbi` (used on `ty::FnPtr` signatures) into
/// `IrCallConv`.
///
/// `rustc` (`compiler/rustc_abi/src/extern_abi.rs`) defines `ExternAbi` as:
///
/// >```text
/// >/// ABI we expect to see within `extern "{abi}"`
/// >#[derive(Clone, Copy, Debug)]
/// >#[cfg_attr(feature = "nightly", derive(Encodable, Decodable))]
/// >pub enum ExternAbi {
/// >    C {
/// >        unwind: bool,
/// >    },
/// >    System {
/// >        unwind: bool,
/// >    },
/// >    Rust,
/// >    RustCall,
/// >    RustCold,
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/extern_abi.rs#L17-L39
pub fn lower_extern_abi(abi: ExternAbi) -> IrCallConv {
    match abi {
        ExternAbi::Rust => IrCallConv::Rust,
        ExternAbi::C { .. } => IrCallConv::C,
        other => IrCallConv::Other(other.as_str().to_owned()),
    }
}

/// Lowers `rustc_target::callconv::FnAbi` into `IrFnAbi`.
///
/// `rustc` (`compiler/rustc_target/src/callconv/mod.rs`) defines `FnAbi` as:
///
/// >```text
/// >pub struct FnAbi<'a, Ty> {
/// >    pub args: Box<[ArgAbi<'a, Ty>]>,
/// >    pub ret: ArgAbi<'a, Ty>,
/// >    pub c_variadic: bool,
/// >    pub fixed_count: u32,
/// >    pub conv: CanonAbi,
/// >    pub can_unwind: bool,
/// >}
/// >```
///
/// Source: https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_target/src/callconv/mod.rs#L593-L612
pub fn lower_fn_abi<'tcx>(abi: &FnAbi<'tcx, Ty<'tcx>>) -> IrFnAbi {
    IrFnAbi {
        args: abi.args.iter().map(lower_arg_abi).collect(),
        ret: lower_arg_abi(&abi.ret),
        conv: lower_canon_abi(abi.conv),
        can_unwind: abi.can_unwind,
    }
}

/// Queries `tcx.fn_abi_of_instance` for a monomorphic function `def_id`, or
/// synthesizes a fallback `IrFnAbi` from the MIR local declarations when the
/// item is a constant, static, or generic function with uninstantiated type
/// parameters.
pub fn extract_fn_abi_for_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    typing_env: TypingEnv<'tcx>,
    arg_count: usize,
    local_layouts: &[IrTypeLayout],
) -> IrFnAbi {
    let generics = tcx.generics_of(def_id);
    if generics.count() == 0 && tcx.def_kind(def_id).is_fn_like() {
        let instance = Instance::mono(tcx, def_id);
        let query_input = typing_env.as_query_input((instance, ty::List::empty()));
        if let Ok(fn_abi) = tcx.fn_abi_of_instance(query_input) {
            return lower_fn_abi(fn_abi);
        }
    }

    let ret_layout = local_layouts
        .first()
        .cloned()
        .unwrap_or_else(fallback_zst_layout);
    let ret = IrArgAbi {
        mode: default_pass_mode_for_layout(&ret_layout),
        layout: ret_layout,
    };
    let mut args = Vec::with_capacity(arg_count);
    for i in 0..arg_count {
        let arg_layout = local_layouts
            .get(i + 1)
            .cloned()
            .unwrap_or_else(fallback_zst_layout);
        args.push(IrArgAbi {
            mode: default_pass_mode_for_layout(&arg_layout),
            layout: arg_layout,
        });
    }
    IrFnAbi {
        args,
        ret,
        conv: IrCallConv::Rust,
        can_unwind: true,
    }
}

fn default_pass_mode_for_layout(layout: &IrTypeLayout) -> IrAbiPassMode {
    if layout.size.bytes == 0 {
        return IrAbiPassMode::Ignore;
    }
    match layout.backend_repr {
        IrBackendRepr::Scalar(_) => IrAbiPassMode::Direct,
        IrBackendRepr::ScalarPair(_, _) => IrAbiPassMode::Pair,
        IrBackendRepr::Memory => IrAbiPassMode::Indirect,
    }
}

pub fn fallback_zst_layout() -> IrTypeLayout {
    IrTypeLayout {
        size: IrSize { bytes: 0 },
        align: IrAlign { bytes: 1 },
        backend_repr: IrBackendRepr::Memory,
        fields: IrFieldsShape::Arbitrary {
            offsets: Vec::new(),
            memory_index: Vec::new(),
        },
        variants: IrVariantsShape::Single { index: 0 },
        is_uninhabited: false,
        field_layouts: Vec::new(),
    }
}
