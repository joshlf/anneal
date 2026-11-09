//! Lowering and evaluation for MIR casts, including:
//! 1. `rustc` MIR pointer-to-integer (`CastKind::PointerExposeProvenance`) and
//!    integer-to-pointer (`CastKind::PointerWithExposedProvenance`) casts;
//! 2. MiniRust `IntPtrCast` provenance-exposure semantics (`spec/mem/intptrcast.md`); and
//! 3. UCG `#286` / MiniRust same-size `CastKind::Transmute` semantics across 32-bit and
//!    64-bit target pointer widths (`PtrWidth::Bits32` and `PtrWidth::Bits64`), preserving
//!    provenance on `Ptr -> Ptr`, rejecting or stripping provenance on `Ptr -> Int` without
//!    exposing it, and enforcing bit-validity on niche-constrained types (`bool`, `char`, `&T`).

use std::collections::BTreeSet;

use crate::ir::{CastKind, Operand, PointerValue, Provenance, PtrWidth, ScalarTy, Ty};

/// Policy governing pointer-to-integer reinterpretation in `CastKind::Transmute`.
///
/// A transmute is `Ptr -> Int` iff some pointer (`RawPtr`/`Ref`) in the source's byte layout
/// does not land exactly on a pointer at the same byte offset of the target's layout (e.g.
/// `*const T -> usize`, `&T -> [u8; 8]`, or `(*const T, u64) -> (u64, *const T)`). Transmutes
/// that keep every pointer on a pointer (e.g. `*const T -> &U`, `*const T -> [*mut U; 1]`, or
/// `(*const T, u64) -> (*mut U, u64)`) are `Ptr -> Ptr` and preserve provenance.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum TransmutePolicy {
    /// Rejects `Ptr -> Int` transmutes, requiring callers to use
    /// `CastKind::PointerExposeProvenance` or explicitly opt into provenance stripping.
    #[default]
    RejectPtrToInt,
    /// Permits same-size `Ptr -> Int` transmutes while stripping pointer provenance
    /// (`exposes_provenance: false`) without adding it to `ExposedProvenanceTracker`.
    AllowPtrToIntStripProvenance,
}

/// Lowered transmute and cast descriptor distinguishing scalar-to-scalar transmutes,
/// composite/aggregate byte transmutes, and `char -> Int/Uint` conversions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastOp {
    /// Scalar-to-scalar bit reinterpretation (`ScalarTy -> ScalarTy`).
    Transmute { src: ScalarTy, dst: ScalarTy },
    /// Same-size aggregate/composite byte reinterpretation (e.g. `[u8; 4] <-> u32`).
    AggregateTransmute { size_bytes: usize },
    /// Unicode scalar (`char`) to integer conversion (`CastKind::CharToInt`).
    CharToInt,
}

/// Errors encountered during MIR cast lowering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastLowerError {
    /// Source type is invalid for the requested cast kind.
    InvalidSourceType {
        expected: &'static str,
        got: Ty,
    },
    /// Target type is invalid for the requested cast kind.
    InvalidTargetType {
        expected: &'static str,
        got: Ty,
    },
    /// Incompatible sizes or unsupported conversion.
    UnsupportedCast {
        kind: CastKind,
        src_ty: Ty,
        target_ty: Ty,
    },
    /// Source and target types have different byte sizes under the target pointer width.
    SizeMismatchTransmute {
        src_ty: Ty,
        target_ty: Ty,
        src_bytes: usize,
        target_bytes: usize,
    },
    /// Target type of a transmute is uninhabited (e.g. `!`, `(!, u32)`, `[!; 1]`).
    UninhabitedTarget {
        target_ty: Ty,
    },
    /// `Ptr -> Int` transmute rejected by `TransmutePolicy::RejectPtrToInt`.
    PtrToIntTransmuteDisallowed {
        src_ty: Ty,
        target_ty: Ty,
    },
    /// Type's layout is not representable on the target (array length above `usize::MAX`
    /// or size above `isize::MAX`; see [`Ty::layout_size_for`]).
    LayoutTooLarge {
        ty: Ty,
    },
    /// Byte-level transmute through a type without a canonical byte layout (see
    /// [`Ty::has_canonical_byte_layout`]), e.g. a tuple with padding or reordered fields.
    UnsupportedLayout {
        ty: Ty,
    },
}

impl std::fmt::Display for CastLowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CastLowerError::InvalidSourceType { expected, got } => {
                write!(f, "invalid cast source type: expected {expected}, got {got:?}")
            }
            CastLowerError::InvalidTargetType { expected, got } => {
                write!(f, "invalid cast target type: expected {expected}, got {got:?}")
            }
            CastLowerError::UnsupportedCast { kind, src_ty, target_ty } => {
                write!(f, "unsupported cast {kind:?} from {src_ty:?} to {target_ty:?}")
            }
            CastLowerError::SizeMismatchTransmute {
                src_ty,
                target_ty,
                src_bytes,
                target_bytes,
            } => {
                write!(
                    f,
                    "transmute size mismatch from {src_ty:?} ({src_bytes} bytes) to {target_ty:?} ({target_bytes} bytes)"
                )
            }
            CastLowerError::UninhabitedTarget { target_ty } => {
                write!(f, "cannot transmute to uninhabited target type {target_ty:?}")
            }
            CastLowerError::PtrToIntTransmuteDisallowed { src_ty, target_ty } => {
                write!(
                    f,
                    "pointer-to-integer transmute from {src_ty:?} to {target_ty:?} disallowed by policy"
                )
            }
            CastLowerError::LayoutTooLarge { ty } => {
                write!(f, "type {ty:?} is too large for the target architecture")
            }
            CastLowerError::UnsupportedLayout { ty } => {
                write!(f, "type {ty:?} has no canonical byte layout for transmute")
            }
        }
    }
}

impl std::error::Error for CastLowerError {}

/// Lowered representation of a MIR type cast.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredCast {
    /// Pointer-to-integer cast (`CastKind::PointerExposeProvenance`).
    ///
    /// Evaluates the address of the pointer operand as an integer and exposes
    /// its provenance tag in the global exposed-provenance set.
    PtrToInt {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        expose_provenance: bool,
    },
    /// Integer-to-pointer cast (`CastKind::PointerWithExposedProvenance`).
    ///
    /// Interprets an integer address as a pointer, non-deterministically
    /// reconstructing provenance from previously exposed tags (or wildcard/none).
    IntToPtr {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        pick_exposed_provenance: bool,
    },
    /// Standard integer-to-integer conversion (`CastKind::IntToInt`).
    IntToInt {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
    },
    /// Unicode scalar (`char`) to integer conversion (`CastKind::CharToInt`).
    CharToInt {
        operand: Operand,
        target_ty: Ty,
    },
    /// Raw pointer to raw pointer reinterpretation (`CastKind::PtrToPtr`).
    PtrToPtr {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
    },
    /// Same-size bitwise reinterpretation (`CastKind::Transmute`).
    ///
    /// Never exposes pointer provenance (`exposes_provenance == false`).
    Transmute {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        op: CastOp,
        size_bytes: usize,
        exposes_provenance: bool,
    },
}

/// Lowers a pointer-to-integer cast (`Rvalue::Cast(PointerExposeProvenance)`).
///
/// Preconditions:
/// - `src_ty` must be a raw pointer (`*const T`, `*mut T`) or reference (`&T`, `&mut T`).
/// - `target_ty` must be an integer type (`usize`, `u64`, `isize`, `i64`, `u32`, etc.).
pub fn lower_ptr_to_int(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    if !src_ty.is_any_ptr() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "raw pointer or reference",
            got: src_ty.clone(),
        });
    }
    if !target_ty.is_integral() {
        return Err(CastLowerError::InvalidTargetType {
            expected: "integral type",
            got: target_ty.clone(),
        });
    }

    Ok(LoweredCast::PtrToInt {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        expose_provenance: true,
    })
}

/// Lowers an integer-to-pointer cast (`Rvalue::Cast(PointerWithExposedProvenance)`).
///
/// Preconditions:
/// - `src_ty` must be an integer type (`usize`, `u64`, `isize`, etc.).
/// - `target_ty` must be a raw pointer (`*const T` or `*mut T`).
pub fn lower_int_to_ptr(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    if !src_ty.is_integral() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "integral type",
            got: src_ty.clone(),
        });
    }
    if !target_ty.is_raw_ptr() {
        return Err(CastLowerError::InvalidTargetType {
            expected: "raw pointer",
            got: target_ty.clone(),
        });
    }

    Ok(LoweredCast::IntToPtr {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        pick_exposed_provenance: true,
    })
}

/// Maximum number of pointer leaves analyzed when checking a transmute's provenance policy.
const MAX_POINTER_LEAVES: usize = 1 << 16;

/// Collects the byte offsets (in increasing order) of every thin pointer (`RawPtr`/`Ref`)
/// inside the canonical byte layout of `ty`, starting at `base`. Returns `false` if more
/// than `budget` pointers would be collected.
fn collect_pointer_offsets(
    ty: &Ty,
    ptr_width: PtrWidth,
    base: usize,
    out: &mut Vec<usize>,
    budget: &mut usize,
) -> bool {
    if !ty.contains_ptr() {
        return true;
    }
    match ty {
        Ty::RawPtr(_, _) | Ty::Ref(_, _) => {
            if *budget == 0 {
                return false;
            }
            *budget -= 1;
            out.push(base);
            true
        }
        Ty::Array(elem, count) => {
            let elem_size = elem.byte_size_for(ptr_width);
            (0..*count).all(|i| {
                collect_pointer_offsets(elem, ptr_width, base + i * elem_size, out, budget)
            })
        }
        Ty::Tuple(fields) => {
            let mut offset = base;
            for field in fields {
                if !collect_pointer_offsets(field, ptr_width, offset, out, budget) {
                    return false;
                }
                offset += field.byte_size_for(ptr_width);
            }
            true
        }
        Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) | Ty::Never => true,
    }
}

/// Failure of the static layout/provenance checks shared by `lower_transmute` and
/// `eval_transmute`.
enum TransmuteLayoutError {
    /// The given type has no canonical byte layout (or too many pointers to analyze).
    Unsupported(Ty),
    /// Some source pointer's bytes would be reinterpreted as non-pointer data.
    PtrToInt,
}

/// Checks that both sides of a same-size transmute have canonical byte layouts and applies
/// `policy` to source pointers: a transmute is `Ptr -> Int` iff some source pointer does not
/// land exactly on a target pointer at the same byte offset (e.g. `*const u8 -> usize`,
/// `(*const u8, u64) -> (u64, *const u8)`), whereas `*const u8 -> [&u8; 1]` or
/// `(*const u8, u64) -> (*mut u16, u64)` preserve every pointer.
fn check_transmute_layouts(
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<(), TransmuteLayoutError> {
    for ty in [src_ty, target_ty] {
        if !ty.has_canonical_byte_layout(ptr_width) {
            return Err(TransmuteLayoutError::Unsupported(ty.clone()));
        }
    }
    if src_ty == target_ty {
        return Ok(());
    }
    let mut src_ptrs = Vec::new();
    let mut src_budget = MAX_POINTER_LEAVES;
    if !collect_pointer_offsets(src_ty, ptr_width, 0, &mut src_ptrs, &mut src_budget) {
        return Err(TransmuteLayoutError::Unsupported(src_ty.clone()));
    }
    let mut target_ptrs = Vec::new();
    let mut target_budget = MAX_POINTER_LEAVES;
    if !collect_pointer_offsets(target_ty, ptr_width, 0, &mut target_ptrs, &mut target_budget) {
        return Err(TransmuteLayoutError::Unsupported(target_ty.clone()));
    }
    let ptr_to_int = src_ptrs.iter().any(|off| target_ptrs.binary_search(off).is_err());
    if ptr_to_int && policy == TransmutePolicy::RejectPtrToInt {
        return Err(TransmuteLayoutError::PtrToInt);
    }
    Ok(())
}

/// Lowers a `CastKind::Transmute` under an explicit `PtrWidth` and `TransmutePolicy`.
///
/// Checks, in order: the target (then source) is inhabited; both layouts are representable
/// on the target ([`Ty::layout_size_for`]); the sizes match; non-scalar sides have canonical
/// byte layouts ([`Ty::has_canonical_byte_layout`]); and `policy` permits every source
/// pointer that does not land exactly on a target pointer.
pub fn lower_transmute(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredCast, CastLowerError> {
    if !target_ty.is_inhabited() {
        return Err(CastLowerError::UninhabitedTarget {
            target_ty: target_ty.clone(),
        });
    }
    if !src_ty.is_inhabited() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "inhabited type",
            got: src_ty.clone(),
        });
    }

    let src_bytes = src_ty
        .layout_size_for(ptr_width)
        .ok_or_else(|| CastLowerError::LayoutTooLarge { ty: src_ty.clone() })?;
    let target_bytes = target_ty
        .layout_size_for(ptr_width)
        .ok_or_else(|| CastLowerError::LayoutTooLarge {
            ty: target_ty.clone(),
        })?;
    if src_bytes != target_bytes {
        return Err(CastLowerError::SizeMismatchTransmute {
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
            src_bytes,
            target_bytes,
        });
    }

    // Transmuting a type to itself is the identity on its values (MiniRust:
    // `T.decode(T.encode(v)) == v`) whatever its layout, and keeps every pointer on itself, so
    // neither a canonical byte layout nor the `Ptr -> Int` policy applies.
    if src_ty != target_ty {
        check_transmute_layouts(src_ty, target_ty, ptr_width, policy).map_err(|err| match err {
            TransmuteLayoutError::Unsupported(ty) => CastLowerError::UnsupportedLayout { ty },
            TransmuteLayoutError::PtrToInt => CastLowerError::PtrToIntTransmuteDisallowed {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
            },
        })?;
    }

    let op = match (src_ty.to_scalar_ty(), target_ty.to_scalar_ty()) {
        (Some(src), Some(dst)) => CastOp::Transmute { src, dst },
        _ => CastOp::AggregateTransmute {
            size_bytes: src_bytes,
        },
    };

    Ok(LoweredCast::Transmute {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        op,
        size_bytes: src_bytes,
        exposes_provenance: false,
    })
}

/// Lowers any supported MIR cast rvalue under an explicit `PtrWidth` and `TransmutePolicy`.
pub fn lower_cast_rvalue_with_ptr_width(
    kind: CastKind,
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredCast, CastLowerError> {
    match kind {
        CastKind::PointerExposeProvenance => lower_ptr_to_int(operand, src_ty, target_ty),
        CastKind::PointerWithExposedProvenance => lower_int_to_ptr(operand, src_ty, target_ty),
        CastKind::IntToInt => {
            let valid_src = src_ty.is_integral() || matches!(src_ty, Ty::Bool | Ty::Char);
            let valid_dst = target_ty.is_integral() || matches!(target_ty, Ty::Char);
            if !valid_src {
                return Err(CastLowerError::InvalidSourceType {
                    expected: "integral, bool, or char type",
                    got: src_ty.clone(),
                });
            }
            if !valid_dst {
                return Err(CastLowerError::InvalidTargetType {
                    expected: "integral or char type",
                    got: target_ty.clone(),
                });
            }
            // Note: rustc only permits `u8 as char` for char target in IntToInt.
            if *target_ty == Ty::Char && *src_ty != Ty::Uint(crate::ir::UintTy::U8) {
                return Err(CastLowerError::UnsupportedCast {
                    kind,
                    src_ty: src_ty.clone(),
                    target_ty: target_ty.clone(),
                });
            }
            Ok(LoweredCast::IntToInt {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: operand.clone(),
            })
        }
        CastKind::CharToInt => lower_char_to_int(operand, src_ty, target_ty, ptr_width),
        CastKind::PtrToPtr => {
            if !src_ty.is_raw_ptr() {
                return Err(CastLowerError::InvalidSourceType {
                    expected: "raw pointer",
                    got: src_ty.clone(),
                });
            }
            if !target_ty.is_raw_ptr() {
                return Err(CastLowerError::InvalidTargetType {
                    expected: "raw pointer",
                    got: target_ty.clone(),
                });
            }
            Ok(LoweredCast::PtrToPtr {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: operand.clone(),
            })
        }
        CastKind::Transmute => lower_transmute(operand, src_ty, target_ty, ptr_width, policy),
    }
}

/// Lowers any supported MIR cast rvalue using the default 64-bit target pointer width
/// (`PtrWidth::Bits64`) and strict `TransmutePolicy::RejectPtrToInt`.
pub fn lower_cast_rvalue(
    kind: CastKind,
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    lower_cast_rvalue_with_ptr_width(
        kind,
        operand,
        src_ty,
        target_ty,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
    )
}

/// Dynamic tracker for exposed pointer provenances, modeling MiniRust's `IntPtrCast`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExposedProvenanceTracker {
    pub exposed: BTreeSet<Provenance>,
}

impl ExposedProvenanceTracker {
    /// Creates a new empty provenance tracker.
    pub fn new() -> Self {
        Self { exposed: BTreeSet::new() }
    }

    /// Exposes a provenance tag, recording it as available for address-to-pointer casts.
    pub fn expose(&mut self, prov: Provenance) {
        self.exposed.insert(prov);
    }

    /// Returns true if the given provenance tag has been exposed.
    pub fn is_exposed(&self, prov: &Provenance) -> bool {
        self.exposed.contains(prov)
    }

    /// Count of exposed provenances.
    pub fn len(&self) -> usize {
        self.exposed.len()
    }

    /// Returns true if no provenance has been exposed.
    pub fn is_empty(&self) -> bool {
        self.exposed.is_empty()
    }
}

/// Errors during dynamic cast evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastEvalError {
    /// Target integer type width cannot fit address bits without truncation.
    IntegerOverflow {
        addr: u64,
        target_bytes: usize,
    },
    /// Requested provenance is not in the set of exposed provenances.
    UnexposedProvenance(Provenance),
    /// Invalid types passed to evaluator.
    TypeMismatch(&'static str),
    /// Bit pattern violates the validity invariant (niche) of `target_ty`
    /// (e.g. `bool` not in `0..=1`, `char` surrogate or `> 0x10FFFF`, or null `&T`).
    InvalidBitPattern {
        target_ty: Ty,
        bits: u128,
    },
    /// Source and target byte sizes do not match under the target pointer width.
    SizeMismatch {
        src_bytes: usize,
        target_bytes: usize,
    },
    /// Target type is uninhabited (`!`, `(!, u32)`, `[!; 1]`).
    UninhabitedTarget {
        target_ty: Ty,
    },
    /// Pointer-to-integer transmute rejected by `TransmutePolicy::RejectPtrToInt`.
    PtrToIntDisallowed {
        src_ty: Ty,
        target_ty: Ty,
    },
    /// Type's layout is not representable on the target (see [`Ty::layout_size_for`]).
    LayoutTooLarge {
        ty: Ty,
    },
    /// Byte-level transmute through a type without a canonical byte layout (see
    /// [`Ty::has_canonical_byte_layout`]).
    UnsupportedLayout {
        ty: Ty,
    },
}

impl std::fmt::Display for CastEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CastEvalError::IntegerOverflow { addr, target_bytes } => {
                write!(f, "pointer address {addr:#x} overflows target width ({target_bytes} bytes)")
            }
            CastEvalError::UnexposedProvenance(p) => {
                write!(f, "provenance tag (alloc_id={}, tag={}) is not exposed", p.alloc_id, p.tag)
            }
            CastEvalError::TypeMismatch(msg) => write!(f, "type mismatch: {msg}"),
            CastEvalError::InvalidBitPattern { target_ty, bits } => {
                write!(f, "invalid bit pattern {bits:#x} for target type {target_ty:?}")
            }
            CastEvalError::SizeMismatch {
                src_bytes,
                target_bytes,
            } => {
                write!(f, "transmute size mismatch: {src_bytes} bytes vs {target_bytes} bytes")
            }
            CastEvalError::UninhabitedTarget { target_ty } => {
                write!(f, "cannot evaluate transmute to uninhabited target type {target_ty:?}")
            }
            CastEvalError::PtrToIntDisallowed { src_ty, target_ty } => {
                write!(
                    f,
                    "pointer-to-integer transmute from {src_ty:?} to {target_ty:?} disallowed by policy"
                )
            }
            CastEvalError::LayoutTooLarge { ty } => {
                write!(f, "type {ty:?} is too large for the target architecture")
            }
            CastEvalError::UnsupportedLayout { ty } => {
                write!(f, "type {ty:?} has no canonical byte layout for transmute")
            }
        }
    }
}

impl std::error::Error for CastEvalError {}

/// Runtime value representation for `CastKind::Transmute` evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransmuteValue {
    /// Scalar bit pattern (`bool`, `char`, `Int`, `Uint`).
    Scalar(u128),
    /// Machine pointer with address and optional provenance (`RawPtr` or `Ref`).
    Ptr(PointerValue),
    /// Provenance-free little-endian byte representation of an aggregate value
    /// (`Array`, `Tuple`) laid out canonically (see [`Ty::has_canonical_byte_layout`]).
    Bytes(Vec<u8>),
    /// Byte representation of an aggregate value whose pointer bytes carry provenance
    /// fragments (MiniRust `AbstractByte`), e.g. `[*const u8; 2]` or `(*const u8, u64)`.
    AbstractBytes(Vec<AbstractByte>),
}

/// Provenance fragment carried by one byte of an encoded pointer (MiniRust
/// `ProvenanceFrag`): the pointer's provenance plus the byte's position within the
/// pointer's encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProvenanceFrag {
    pub provenance: Provenance,
    pub position: usize,
}

/// Initialized abstract byte (MiniRust `AbstractByte::Init`): a data byte plus an optional
/// pointer-provenance fragment. Canonical layouts have no padding, so MiniRust's
/// `AbstractByte::Uninit` never arises in Anneal's transmute model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbstractByte {
    pub data: u8,
    pub provenance: Option<ProvenanceFrag>,
}

impl AbstractByte {
    /// A data byte without provenance.
    pub const fn new(data: u8) -> Self {
        AbstractByte {
            data,
            provenance: None,
        }
    }
}

/// Encodes the low `size` (`<= 16`) bytes of `bits` little-endian, without provenance.
pub(crate) fn encode_int_bytes(bits: u128, size: usize) -> impl Iterator<Item = AbstractByte> {
    (0..size.min(16)).map(move |i| AbstractByte::new((bits >> (i * 8)) as u8))
}

/// Decodes up to 16 little-endian bytes into an unsigned bit pattern, ignoring provenance
/// (MiniRust integer/`bool`/`char` decoding strips provenance without exposing it).
pub(crate) fn decode_int_bytes(bytes: &[AbstractByte]) -> u128 {
    bytes
        .iter()
        .take(16)
        .enumerate()
        .fold(0u128, |acc, (i, b)| acc | (u128::from(b.data) << (i * 8)))
}

/// Encodes a thin pointer as little-endian address bytes (masked to `ptr_width`), each
/// tagged with a provenance fragment recording its position (MiniRust `encode_ptr`).
pub(crate) fn encode_ptr_bytes(ptr: PointerValue, ptr_width: PtrWidth) -> Vec<AbstractByte> {
    let addr = u128::from(ptr.addr) & ptr_width.mask();
    (0..ptr_width.byte_size())
        .map(|position| AbstractByte {
            data: (addr >> (position * 8)) as u8,
            provenance: ptr
                .provenance
                .map(|provenance| ProvenanceFrag { provenance, position }),
        })
        .collect()
}

/// Decodes a thin pointer (MiniRust `decode_ptr`): the result keeps a provenance only if
/// every byte carries a fragment of that same provenance at its matching position;
/// otherwise (mixed, missing, or shuffled fragments) the pointer has no provenance.
pub(crate) fn decode_ptr_bytes(bytes: &[AbstractByte]) -> PointerValue {
    let addr = decode_int_bytes(bytes) as u64;
    let provenance = bytes
        .first()
        .and_then(|b| b.provenance)
        .map(|frag| frag.provenance)
        .filter(|prov| {
            bytes.iter().enumerate().all(|(idx, b)| {
                matches!(b.provenance, Some(frag) if frag.position == idx && frag.provenance == *prov)
            })
        });
    PointerValue { addr, provenance }
}

/// Decodes `bytes` at `ty` (a canonical layout of exactly `bytes.len()` bytes), validating
/// every scalar leaf, and appends the re-encoded value to `out`: non-pointer leaves drop any
/// provenance (stripping without exposing), and pointer leaves keep a provenance only if
/// all of their bytes agree on it (MiniRust `decode_ptr`).
fn normalize_bytes(
    bytes: &[AbstractByte],
    ty: &Ty,
    ptr_width: PtrWidth,
    out: &mut Vec<AbstractByte>,
) -> Result<(), CastEvalError> {
    match ty {
        Ty::RawPtr(_, _) | Ty::Ref(_, _) => {
            let ptr = decode_ptr_bytes(bytes);
            let bits = u128::from(ptr.addr);
            if !ty.is_valid_scalar_bits(bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits,
                });
            }
            out.extend(encode_ptr_bytes(ptr, ptr_width));
            Ok(())
        }
        Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) => {
            let bits = decode_int_bytes(bytes);
            if !ty.is_valid_scalar_bits(bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits,
                });
            }
            out.extend(encode_int_bytes(bits, bytes.len()));
            Ok(())
        }
        Ty::Array(elem, count) => {
            let elem_size = elem.byte_size_for(ptr_width);
            if elem_size == 0 {
                // Zero-sized elements occupy no bytes; inhabited ZST elements are always valid.
                return if *count == 0 || elem.is_inhabited() {
                    Ok(())
                } else {
                    Err(CastEvalError::UninhabitedTarget {
                        target_ty: ty.clone(),
                    })
                };
            }
            for chunk in bytes.chunks_exact(elem_size) {
                normalize_bytes(chunk, elem, ptr_width, out)?;
            }
            Ok(())
        }
        Ty::Tuple(fields) => {
            let mut offset = 0usize;
            for field in fields {
                let size = field.byte_size_for(ptr_width);
                normalize_bytes(&bytes[offset..offset + size], field, ptr_width, out)?;
                offset += size;
            }
            Ok(())
        }
        Ty::Never => Err(CastEvalError::UninhabitedTarget {
            target_ty: Ty::Never,
        }),
    }
}

/// Evaluates a lowered `PtrToInt` cast on a concrete pointer value under `ptr_width`.
pub fn eval_ptr_to_int_with_ptr_width(
    ptr: PointerValue,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<u128, CastEvalError> {
    if !target_ty.is_integral() {
        return Err(CastEvalError::TypeMismatch("target type must be integral"));
    }

    // Expose provenance if present.
    if let Some(prov) = ptr.provenance {
        tracker.expose(prov);
    }

    let target_bytes = target_ty.byte_size_for(ptr_width);
    let addr = (ptr.addr as u128) & ptr_width.mask();

    if target_bytes < 16 {
        let modulus = 1u128 << (target_bytes * 8);
        Ok(addr % modulus)
    } else {
        Ok(addr)
    }
}

/// Evaluates a lowered `PtrToInt` cast on a concrete pointer value (64-bit default).
///
/// Corresponds to MiniRust:
/// `IntPtrCast::expose` followed by converting the thin pointer address to integer.
pub fn eval_ptr_to_int(
    ptr: PointerValue,
    target_ty: &Ty,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<u128, CastEvalError> {
    eval_ptr_to_int_with_ptr_width(ptr, target_ty, PtrWidth::Bits64, tracker)
}

/// Evaluates a lowered `IntToPtr` cast from an address value to a pointer under `ptr_width`.
pub fn eval_int_to_ptr_with_ptr_width(
    addr: u128,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    tracker: &ExposedProvenanceTracker,
    predicted_prov: Option<Provenance>,
) -> Result<PointerValue, CastEvalError> {
    if !target_ty.is_raw_ptr() {
        return Err(CastEvalError::TypeMismatch("target type must be raw pointer"));
    }

    if let Some(prov) = predicted_prov {
        if !tracker.is_exposed(&prov) {
            return Err(CastEvalError::UnexposedProvenance(prov));
        }
    }

    let masked_addr = (addr & ptr_width.mask()) as u64;
    Ok(PointerValue {
        addr: masked_addr,
        provenance: predicted_prov,
    })
}

/// Evaluates a lowered `IntToPtr` cast from an address value to a pointer (64-bit default).
///
/// Corresponds to MiniRust:
/// `IntPtrCast::int2ptr` predicting either `None` (untagged/wildcard) or an already-exposed provenance.
pub fn eval_int_to_ptr(
    addr: u128,
    target_ty: &Ty,
    tracker: &ExposedProvenanceTracker,
    predicted_prov: Option<Provenance>,
) -> Result<PointerValue, CastEvalError> {
    eval_int_to_ptr_with_ptr_width(addr, target_ty, PtrWidth::Bits64, tracker, predicted_prov)
}

/// Lowers a `CastKind::CharToInt` cast (`char -> Int/Uint`) under `ptr_width`.
///
/// Preconditions:
/// - `src_ty` must be `Ty::Char`.
/// - `target_ty` must be an integral type (`Ty::Int(_)` or `Ty::Uint(_)`) with a
///   representable layout under `ptr_width`.
pub fn lower_char_to_int(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<LoweredCast, CastLowerError> {
    if *src_ty != Ty::Char {
        return Err(CastLowerError::InvalidSourceType {
            expected: "char",
            got: src_ty.clone(),
        });
    }
    if !target_ty.is_integral() {
        return Err(CastLowerError::InvalidTargetType {
            expected: "integral type",
            got: target_ty.clone(),
        });
    }
    if target_ty.layout_size_for(ptr_width).is_none() {
        return Err(CastLowerError::LayoutTooLarge {
            ty: target_ty.clone(),
        });
    }
    Ok(LoweredCast::CharToInt {
        operand: operand.clone(),
        target_ty: target_ty.clone(),
    })
}

/// Evaluates a `CastKind::CharToInt` conversion on a `char` codepoint bit pattern.
///
/// Validates that `codepoint_bits` is a Unicode scalar value (`codepoint_bits <= 0xD7FF`
/// or `0xE000 <= codepoint_bits <= 0x10FFFF`), returning
/// `CastEvalError::InvalidBitPattern { target_ty: Ty::Char, bits: codepoint_bits }`
/// otherwise, and masks the codepoint to `target_ty`'s bit width under `ptr_width`.
pub fn eval_char_to_int(
    codepoint_bits: u128,
    target_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<u128, CastEvalError> {
    let dst_mask = match target_ty {
        Ty::Int(it) => it.mask(ptr_width),
        Ty::Uint(ut) => ut.mask(ptr_width),
        _ => {
            return Err(CastEvalError::TypeMismatch(
                "CharToInt target must be Int or Uint",
            ));
        }
    };
    if !ScalarTy::Char.is_valid_bits(codepoint_bits, ptr_width) {
        return Err(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Char,
            bits: codepoint_bits,
        });
    }
    Ok(codepoint_bits & dst_mask)
}

/// Evaluates a numeric `CastKind::IntToInt` conversion (including `bool`/`char` as integer).
///
/// Signed sources sign-extend, unsigned/`bool`/`char` sources zero-extend, and the result is
/// truncated to the target width. A `char` target (`u8 as char`) must yield a Unicode
/// scalar value, otherwise `CastEvalError::InvalidBitPattern` is returned.
pub fn eval_int_to_int(
    src_bits: u128,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<u128, CastEvalError> {
    let dst_mask = match target_ty {
        Ty::Int(it) => it.mask(ptr_width),
        Ty::Uint(ut) => ut.mask(ptr_width),
        Ty::Char => 0xFFFF_FFFF,
        _ => return Err(CastEvalError::TypeMismatch("IntToInt target must be Int, Uint, or Char")),
    };

    let result = match src_ty {
        Ty::Int(src_it) => {
            let signed = src_it.sign_extend(src_bits, ptr_width);
            (signed as u128) & dst_mask
        }
        Ty::Uint(src_ut) => {
            let unsigned = src_bits & src_ut.mask(ptr_width);
            unsigned & dst_mask
        }
        Ty::Bool => {
            if src_bits > 1 {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Bool,
                    bits: src_bits,
                });
            }
            src_bits & dst_mask
        }
        Ty::Char => {
            if !ScalarTy::Char.is_valid_bits(src_bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Char,
                    bits: src_bits,
                });
            }
            src_bits & dst_mask
        }
        _ => {
            return Err(CastEvalError::TypeMismatch(
                "IntToInt source must be Int, Uint, Bool, or Char",
            ));
        }
    };

    if *target_ty == Ty::Char && !ScalarTy::Char.is_valid_bits(result, ptr_width) {
        return Err(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Char,
            bits: result,
        });
    }
    Ok(result)
}

/// Evaluates a same-size `CastKind::Transmute` on `val` under `ptr_width` and `policy`.
///
/// Semantics follow MiniRust's `transmute(v, src, dst) = dst.decode(src.encode(v))` over
/// [`AbstractByte`]s, restricted to canonical byte layouts
/// ([`Ty::has_canonical_byte_layout`]), with scalars encoded little-endian.
///
/// Key invariants (UCG `#286` / MiniRust):
/// 1. **Never** exposes provenance in `tracker` (`tracker` is borrowed only to prove/assert
///    that `eval_transmute` leaves the exposed provenance set untouched).
/// 2. `Ptr -> Ptr` (including pointers nested at matching offsets inside arrays/tuples, e.g.
///    `*const u8 -> [&u8; 1]`): preserves `PointerValue { addr, provenance }` (masked to
///    `ptr_width`), and rejects `addr == 0` when the target pointer is a `Ty::Ref`.
/// 3. `Ptr -> Int` (only under `TransmutePolicy::AllowPtrToIntStripProvenance`): strips
///    provenance without exposing it and validates the target's bit-validity niche
///    (e.g. `Ptr -> Char` on 32-bit checks Unicode scalar validity!). Pointer bytes that
///    are split across, or shuffled into, a different pointer yield a pointer without
///    provenance (MiniRust `decode_ptr`).
/// 4. `Int -> Ptr`: produces `PointerValue { addr, provenance: None }`, rejecting `addr == 0`
///    when the target is `Ty::Ref`.
/// 5. `Scalar -> Scalar`: validates `target_ty` niche (`bool` `0..=1`, `char` scalar value),
///    returning `CastEvalError::InvalidBitPattern` on invalid bit patterns.
///
/// Aggregate results are returned as `TransmuteValue::Bytes` when no byte carries
/// provenance, and as `TransmuteValue::AbstractBytes` otherwise.
pub fn eval_transmute(
    val: TransmuteValue,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    _tracker: &ExposedProvenanceTracker,
) -> Result<TransmuteValue, CastEvalError> {
    if !target_ty.is_inhabited() {
        return Err(CastEvalError::UninhabitedTarget {
            target_ty: target_ty.clone(),
        });
    }
    if !src_ty.is_inhabited() {
        return Err(CastEvalError::TypeMismatch("source type is uninhabited"));
    }

    let src_bytes = src_ty
        .layout_size_for(ptr_width)
        .ok_or_else(|| CastEvalError::LayoutTooLarge { ty: src_ty.clone() })?;
    let target_bytes = target_ty
        .layout_size_for(ptr_width)
        .ok_or_else(|| CastEvalError::LayoutTooLarge {
            ty: target_ty.clone(),
        })?;
    if src_bytes != target_bytes {
        return Err(CastEvalError::SizeMismatch {
            src_bytes,
            target_bytes,
        });
    }

    check_transmute_layouts(src_ty, target_ty, ptr_width, policy).map_err(|err| match err {
        TransmuteLayoutError::Unsupported(ty) => CastEvalError::UnsupportedLayout { ty },
        TransmuteLayoutError::PtrToInt => CastEvalError::PtrToIntDisallowed {
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
        },
    })?;

    // 1. Encode the (validated) source value at `src_ty`.
    let bytes: Vec<AbstractByte> = match val {
        TransmuteValue::Scalar(src_bits) => {
            if src_ty.is_any_ptr() || !src_ty.is_scalar() {
                return Err(CastEvalError::TypeMismatch(
                    "TransmuteValue::Scalar requires non-pointer scalar source type",
                ));
            }
            if !src_ty.is_valid_scalar_bits(src_bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: src_ty.clone(),
                    bits: src_bits,
                });
            }
            encode_int_bytes(src_bits, src_bytes).collect()
        }
        TransmuteValue::Ptr(ptr) => {
            if !src_ty.is_any_ptr() {
                return Err(CastEvalError::TypeMismatch(
                    "TransmuteValue::Ptr requires pointer or reference source type",
                ));
            }
            let addr_bits = u128::from(ptr.addr) & ptr_width.mask();
            if !src_ty.is_valid_scalar_bits(addr_bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: src_ty.clone(),
                    bits: addr_bits,
                });
            }
            encode_ptr_bytes(ptr, ptr_width)
        }
        TransmuteValue::Bytes(raw) => {
            if raw.len() != src_bytes {
                return Err(CastEvalError::SizeMismatch {
                    src_bytes: raw.len(),
                    target_bytes,
                });
            }
            let raw: Vec<AbstractByte> = raw.into_iter().map(AbstractByte::new).collect();
            let mut normalized = Vec::with_capacity(src_bytes);
            normalize_bytes(&raw, src_ty, ptr_width, &mut normalized)?;
            normalized
        }
        TransmuteValue::AbstractBytes(raw) => {
            if raw.len() != src_bytes {
                return Err(CastEvalError::SizeMismatch {
                    src_bytes: raw.len(),
                    target_bytes,
                });
            }
            let mut normalized = Vec::with_capacity(src_bytes);
            normalize_bytes(&raw, src_ty, ptr_width, &mut normalized)?;
            normalized
        }
    };

    // 2. Decode the bytes at `target_ty`, validating every scalar leaf.
    match target_ty.to_scalar_ty() {
        Some(ScalarTy::Ptr(_)) => {
            // Int -> Ptr never fabricates provenance; Ptr -> Ptr keeps it only if every
            // pointer byte still carries the same provenance fragment in order.
            let ptr = decode_ptr_bytes(&bytes);
            let bits = u128::from(ptr.addr);
            if !target_ty.is_valid_scalar_bits(bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: target_ty.clone(),
                    bits,
                });
            }
            Ok(TransmuteValue::Ptr(ptr))
        }
        Some(_) => {
            // Ptr -> Int strips provenance without exposing it.
            let bits = decode_int_bytes(&bytes);
            if !target_ty.is_valid_scalar_bits(bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: target_ty.clone(),
                    bits,
                });
            }
            Ok(TransmuteValue::Scalar(bits))
        }
        None => {
            let mut normalized = Vec::with_capacity(target_bytes);
            normalize_bytes(&bytes, target_ty, ptr_width, &mut normalized)?;
            if normalized.iter().all(|b| b.provenance.is_none()) {
                Ok(TransmuteValue::Bytes(
                    normalized.into_iter().map(|b| b.data).collect(),
                ))
            } else {
                Ok(TransmuteValue::AbstractBytes(normalized))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, Mutability, UintTy};

    #[test]
    fn test_lower_ptr_to_int_valid() {
        let op = Operand::Constant(crate::ir::Constant::Int(0, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let target_ty = Ty::Uint(UintTy::Usize);

        let lowered = lower_ptr_to_int(&op, &src_ty, &target_ty).expect("lowering must succeed");
        assert_eq!(
            lowered,
            LoweredCast::PtrToInt {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: op,
                expose_provenance: true,
            }
        );
    }

    #[test]
    fn test_lower_ptr_to_int_rejects_non_ptr_source() {
        let op = Operand::Constant(crate::ir::Constant::Int(42, Ty::Uint(UintTy::U32)));
        let src_ty = Ty::Uint(UintTy::U32);
        let target_ty = Ty::Uint(UintTy::Usize);

        let err = lower_ptr_to_int(&op, &src_ty, &target_ty).expect_err("must reject non-ptr source");
        assert!(matches!(err, CastLowerError::InvalidSourceType { .. }));
    }

    #[test]
    fn test_lower_ptr_to_int_rejects_non_int_target() {
        let op = Operand::Constant(crate::ir::Constant::Int(0, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let target_ty = Ty::Bool;

        let err = lower_ptr_to_int(&op, &src_ty, &target_ty).expect_err("must reject non-int target");
        assert!(matches!(err, CastLowerError::InvalidTargetType { .. }));
    }

    #[test]
    fn test_lower_int_to_ptr_valid() {
        let op = Operand::Constant(crate::ir::Constant::Int(0x1000, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::Uint(UintTy::Usize);
        let target_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mut);

        let lowered = lower_int_to_ptr(&op, &src_ty, &target_ty).expect("lowering must succeed");
        assert_eq!(
            lowered,
            LoweredCast::IntToPtr {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: op,
                pick_exposed_provenance: true,
            }
        );
    }

    #[test]
    fn test_lower_int_to_ptr_rejects_non_int_source() {
        let op = Operand::Constant(crate::ir::Constant::Bool(true));
        let src_ty = Ty::Bool;
        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);

        let err = lower_int_to_ptr(&op, &src_ty, &target_ty).expect_err("must reject non-int source");
        assert!(matches!(err, CastLowerError::InvalidSourceType { .. }));
    }

    #[test]
    fn test_eval_ptr_to_int_exposes_provenance() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 1, tag: 42 };
        let ptr = PointerValue {
            addr: 0x7fff_0000,
            provenance: Some(prov),
        };
        let target_ty = Ty::Uint(UintTy::Usize);

        let int_val = eval_ptr_to_int(ptr, &target_ty, &mut tracker).expect("evaluation succeeds");
        assert_eq!(int_val, 0x7fff_0000);
        assert!(tracker.is_exposed(&prov));
    }

    #[test]
    fn test_eval_ptr_to_int_truncation() {
        let mut tracker = ExposedProvenanceTracker::new();
        let ptr = PointerValue::without_provenance(0x1_0000_0005);
        let target_ty = Ty::Uint(UintTy::U32);

        let int_val = eval_ptr_to_int(ptr, &target_ty, &mut tracker).expect("evaluation succeeds");
        assert_eq!(int_val, 5);
    }

    #[test]
    fn test_eval_int_to_ptr_with_exposed_provenance() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 2, tag: 99 };
        tracker.expose(prov);

        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
        let ptr = eval_int_to_ptr(0x8000_1234, &target_ty, &tracker, Some(prov))
            .expect("must succeed with exposed provenance");

        assert_eq!(ptr.addr, 0x8000_1234);
        assert_eq!(ptr.provenance, Some(prov));
    }

    #[test]
    fn test_eval_int_to_ptr_rejects_unexposed_provenance() {
        let tracker = ExposedProvenanceTracker::new();
        let unexposed_prov = Provenance { alloc_id: 99, tag: 1 };

        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
        let err = eval_int_to_ptr(0x8000_1234, &target_ty, &tracker, Some(unexposed_prov))
            .expect_err("must reject unexposed provenance");

        assert_eq!(err, CastEvalError::UnexposedProvenance(unexposed_prov));
    }

    #[test]
    fn test_roundtrip_pointer_int_pointer() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 5, tag: 123 };
        let original_ptr = PointerValue {
            addr: 0x4000_8000,
            provenance: Some(prov),
        };

        let int_ty = Ty::Uint(UintTy::Usize);
        let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);

        // Step 1: Ptr to Int (exposes provenance)
        let int_val = eval_ptr_to_int(original_ptr, &int_ty, &mut tracker).unwrap();
        assert_eq!(int_val, 0x4000_8000);

        // Step 2: Int to Ptr (reconstructs pointer with exposed provenance)
        let roundtrip_ptr = eval_int_to_ptr(int_val, &ptr_ty, &tracker, Some(prov)).unwrap();
        assert_eq!(roundtrip_ptr, original_ptr);
    }

    #[test]
    fn test_transmute_ptr_width_32_vs_64() {
        let op = Operand::Constant(crate::ir::Constant::Int(42, Ty::Uint(UintTy::Usize)));
        let usize_ty = Ty::Uint(UintTy::Usize);
        let u32_ty = Ty::Uint(UintTy::U32);
        let u64_ty = Ty::Uint(UintTy::U64);

        // On 64-bit: usize <-> u64 succeeds, usize <-> u32 fails with SizeMismatchTransmute
        assert!(
            lower_transmute(
                &op,
                &usize_ty,
                &u64_ty,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );
        let err_64 = lower_transmute(
            &op,
            &usize_ty,
            &u32_ty,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("64-bit usize -> u32 must fail");
        assert_eq!(
            err_64,
            CastLowerError::SizeMismatchTransmute {
                src_ty: usize_ty.clone(),
                target_ty: u32_ty.clone(),
                src_bytes: 8,
                target_bytes: 4,
            }
        );

        // On 32-bit: usize <-> u32 succeeds, usize <-> u64 fails with SizeMismatchTransmute
        assert!(
            lower_transmute(
                &op,
                &usize_ty,
                &u32_ty,
                PtrWidth::Bits32,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );
        let err_32 = lower_transmute(
            &op,
            &usize_ty,
            &u64_ty,
            PtrWidth::Bits32,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("32-bit usize -> u64 must fail");
        assert_eq!(
            err_32,
            CastLowerError::SizeMismatchTransmute {
                src_ty: usize_ty,
                target_ty: u64_ty,
                src_bytes: 4,
                target_bytes: 8,
            }
        );
    }

    #[test]
    fn test_transmute_inhabitation_empty_array_of_never_vs_nonempty() {
        let op = Operand::Constant(crate::ir::Constant::Unit);
        let unit_ty = Ty::unit();
        let empty_never_arr = Ty::Array(Box::new(Ty::Never), 0);
        let nonempty_never_arr = Ty::Array(Box::new(Ty::Never), 1);
        let tuple_with_never = Ty::Tuple(vec![Ty::Never, Ty::Uint(UintTy::U32)]);

        // [!; 0] is inhabited and has size 0, so () <-> [!; 0] succeeds!
        assert!(empty_never_arr.is_inhabited());
        assert_eq!(empty_never_arr.checked_byte_size(PtrWidth::Bits64), Some(0));
        assert!(
            lower_transmute(
                &op,
                &unit_ty,
                &empty_never_arr,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );

        // !, [!; 1], and (!, u32) are uninhabited and rejected with UninhabitedTarget!
        for bad_target in [Ty::Never, nonempty_never_arr, tuple_with_never] {
            assert!(!bad_target.is_inhabited());
            assert_eq!(bad_target.checked_byte_size(PtrWidth::Bits64), None);
            let err = lower_transmute(
                &op,
                &unit_ty,
                &bad_target,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt,
            )
            .expect_err("uninhabited target must be rejected");
            assert_eq!(
                err,
                CastLowerError::UninhabitedTarget {
                    target_ty: bad_target
                }
            );
        }
    }

    #[test]
    fn test_transmute_provenance_never_exposed_and_null_ref_rejected() {
        let tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 7, tag: 77 };
        let ptr = PointerValue {
            addr: 0x1000,
            provenance: Some(prov),
        };
        let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let ref_u8 = Ty::Ref(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let usize_ty = Ty::Uint(UintTy::Usize);

        // Ptr -> Ptr preserves provenance without exposing it
        let res = eval_transmute(
            TransmuteValue::Ptr(ptr),
            &raw_u8,
            &ref_u8,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect("non-null Ptr -> Ref transmute succeeds");
        assert_eq!(res, TransmuteValue::Ptr(ptr));
        assert!(!tracker.is_exposed(&prov));

        // Null 0usize -> &u8 must fail with InvalidBitPattern
        let null_err = eval_transmute(
            TransmuteValue::Scalar(0),
            &usize_ty,
            &ref_u8,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect_err("null reference transmute must fail");
        assert_eq!(
            null_err,
            CastEvalError::InvalidBitPattern {
                target_ty: ref_u8,
                bits: 0,
            }
        );

        // Ptr ->Char on 32-bit under AllowPtrToIntStripProvenance must check Unicode scalar validity!
        let surrogate_ptr = PointerValue {
            addr: 0xD800,
            provenance: Some(prov),
        };
        let char_err = eval_transmute(
            TransmuteValue::Ptr(surrogate_ptr),
            &raw_u8,
            &Ty::Char,
            PtrWidth::Bits32,
            TransmutePolicy::AllowPtrToIntStripProvenance,
            &tracker,
        )
        .expect_err("surrogate address transmuted to char on 32-bit must fail");
        assert_eq!(
            char_err,
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Char,
                bits: 0xD800,
            }
        );
    }

    #[test]
    fn test_b1_collect_pointer_offsets_in_layout_order() {
        let raw = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let raw_mut = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U16)), Mutability::Mut);
        // ([*const u8; 2], (u64, *mut u16)) on 64-bit: pointers at 0, 8, and 24.
        let ty = Ty::Tuple(vec![
            Ty::Array(Box::new(raw.clone()), 2),
            Ty::Tuple(vec![Ty::Uint(UintTy::U64), raw_mut]),
        ]);
        assert!(ty.has_canonical_byte_layout(PtrWidth::Bits64));
        let mut offsets = Vec::new();
        let mut budget = MAX_POINTER_LEAVES;
        assert!(collect_pointer_offsets(&ty, PtrWidth::Bits64, 0, &mut offsets, &mut budget));
        assert_eq!(offsets, vec![0, 8, 24]);
        assert_eq!(budget, MAX_POINTER_LEAVES - 3);

        // On 32-bit the same pointers sit at 0 and 4 (u64 still takes 8 bytes), then 16; the
        // inner tuple then has tail padding, so the whole type is not canonical there.
        let mut offsets32 = Vec::new();
        let mut budget32 = MAX_POINTER_LEAVES;
        assert!(collect_pointer_offsets(&ty, PtrWidth::Bits32, 0, &mut offsets32, &mut budget32));
        assert_eq!(offsets32, vec![0, 4, 16]);
        assert!(!ty.has_canonical_byte_layout(PtrWidth::Bits32));

        // Budget exhaustion is reported instead of enumerating unboundedly.
        let mut tiny_budget = 2;
        assert!(!collect_pointer_offsets(&ty, PtrWidth::Bits64, 0, &mut Vec::new(), &mut tiny_budget));
        // Pointer-free subtrees are skipped without consuming budget.
        let mut zero_budget = 0;
        let ints = Ty::Array(Box::new(Ty::Uint(UintTy::U64)), usize::MAX / 8);
        assert!(collect_pointer_offsets(&ints, PtrWidth::Bits64, 0, &mut Vec::new(), &mut zero_budget));
    }

    #[test]
    fn test_b1_pointer_byte_codec_masks_and_tracks_fragment_positions() {
        let prov = Provenance { alloc_id: 4, tag: 2 };
        // Addresses are masked to the target pointer width when encoded.
        let ptr = PointerValue::with_provenance(0x1_2345_6789, prov.alloc_id, prov.tag);
        let bytes32 = encode_ptr_bytes(ptr, PtrWidth::Bits32);
        assert_eq!(bytes32.len(), 4);
        assert_eq!(
            bytes32.iter().map(|b| b.data).collect::<Vec<_>>(),
            vec![0x89, 0x67, 0x45, 0x23]
        );
        for (position, byte) in bytes32.iter().enumerate() {
            assert_eq!(byte.provenance, Some(ProvenanceFrag { provenance: prov, position }));
        }
        assert_eq!(
            decode_ptr_bytes(&bytes32),
            PointerValue::with_provenance(0x2345_6789, prov.alloc_id, prov.tag)
        );
        // Integer decoding ignores (strips) provenance fragments.
        assert_eq!(decode_int_bytes(&bytes32), 0x2345_6789);
        // A byte image without fragments decodes to a pointer without provenance.
        let plain: Vec<AbstractByte> = encode_int_bytes(0x2345_6789, 4).collect();
        assert_eq!(decode_ptr_bytes(&plain), PointerValue::without_provenance(0x2345_6789));
    }
}
