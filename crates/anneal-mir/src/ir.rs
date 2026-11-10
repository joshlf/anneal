//! Core MIR abstract syntax types for `anneal-mir`.

use std::collections::BTreeSet;
use std::sync::Arc;

/// Target machine pointer width (32-bit or 64-bit).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PtrWidth {
    /// 32-bit target pointer width (`4` bytes).
    Bits32,
    /// 64-bit target pointer width (`8` bytes, default).
    #[default]
    Bits64,
}

impl PtrWidth {
    /// Size of a thin pointer (`usize`, `isize`, `*const T`, `&T`) in bytes (`4` or `8`).
    pub const fn byte_size(self) -> usize {
        match self {
            PtrWidth::Bits32 => 4,
            PtrWidth::Bits64 => 8,
        }
    }

    /// Width of a thin pointer in bits (`32` or `64`).
    pub const fn bit_width(self) -> u32 {
        match self {
            PtrWidth::Bits32 => 32,
            PtrWidth::Bits64 => 64,
        }
    }

    /// Unsigned bitmask covering all bits of this pointer width.
    pub const fn mask(self) -> u128 {
        match self {
            PtrWidth::Bits32 => 0xFFFF_FFFF,
            PtrWidth::Bits64 => 0xFFFF_FFFF_FFFF_FFFF,
        }
    }

    /// Maximum unsigned `usize` value under this target pointer width.
    pub const fn max_usize(self) -> u128 {
        self.mask()
    }

    /// Minimum signed `isize` value under this target pointer width.
    pub const fn min_isize(self) -> i128 {
        match self {
            PtrWidth::Bits32 => i32::MIN as i128,
            PtrWidth::Bits64 => i64::MIN as i128,
        }
    }

    /// Maximum signed `isize` value under this target pointer width.
    pub const fn max_isize(self) -> i128 {
        match self {
            PtrWidth::Bits32 => i32::MAX as i128,
            PtrWidth::Bits64 => i64::MAX as i128,
        }
    }

    /// Maximum size in bytes of any Rust object on this target (`isize::MAX`).
    ///
    /// `rustc` rejects types whose size exceeds `isize::MAX` ("values of the type are too
    /// big for the target architecture"), and pointer offsets in bytes must also fit in
    /// `isize`.
    pub const fn max_object_size(self) -> u128 {
        self.max_isize() as u128
    }
}

/// Integer scalar width and signedness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl IntTy {
    /// Size in bytes on a 64-bit target (`PtrWidth::Bits64`).
    pub const fn byte_size(self) -> usize {
        self.byte_size_for(PtrWidth::Bits64)
    }

    /// Size in bytes for the given target pointer width.
    pub const fn byte_size_for(self, ptr_width: PtrWidth) -> usize {
        match self {
            IntTy::Isize => ptr_width.byte_size(),
            IntTy::I8 => 1,
            IntTy::I16 => 2,
            IntTy::I32 => 4,
            IntTy::I64 => 8,
            IntTy::I128 => 16,
        }
    }

    /// Bit width on a 64-bit target (`PtrWidth::Bits64`).
    pub const fn bit_width(self) -> u32 {
        self.bit_width_for(PtrWidth::Bits64)
    }

    /// Bit width for the given target pointer width.
    pub const fn bit_width_for(self, ptr_width: PtrWidth) -> u32 {
        (self.byte_size_for(ptr_width) * 8) as u32
    }

    /// Bitmask covering all bits of this integer width under `ptr_width`.
    pub const fn mask(self, ptr_width: PtrWidth) -> u128 {
        let bytes = self.byte_size_for(ptr_width);
        if bytes >= 16 {
            u128::MAX
        } else {
            (1u128 << (bytes * 8)) - 1
        }
    }

    /// Minimum representable signed value (`INT_MIN`) under `ptr_width`.
    pub const fn min_value(self, ptr_width: PtrWidth) -> i128 {
        match self {
            IntTy::Isize => ptr_width.min_isize(),
            IntTy::I8 => i8::MIN as i128,
            IntTy::I16 => i16::MIN as i128,
            IntTy::I32 => i32::MIN as i128,
            IntTy::I64 => i64::MIN as i128,
            IntTy::I128 => i128::MIN,
        }
    }

    /// Maximum representable signed value (`INT_MAX`) under `ptr_width`.
    pub const fn max_value(self, ptr_width: PtrWidth) -> i128 {
        match self {
            IntTy::Isize => ptr_width.max_isize(),
            IntTy::I8 => i8::MAX as i128,
            IntTy::I16 => i16::MAX as i128,
            IntTy::I32 => i32::MAX as i128,
            IntTy::I64 => i64::MAX as i128,
            IntTy::I128 => i128::MAX,
        }
    }

    /// Sign-extends the low `bit_width_for(ptr_width)` bits of `bits` to `i128`.
    pub const fn sign_extend(self, bits: u128, ptr_width: PtrWidth) -> i128 {
        match self.byte_size_for(ptr_width) {
            1 => (bits as u8 as i8) as i128,
            2 => (bits as u16 as i16) as i128,
            4 => (bits as u32 as i32) as i128,
            8 => (bits as u64 as i64) as i128,
            _ => bits as i128,
        }
    }

    /// Truncates a signed `i128` value to the two's-complement bit pattern of this width.
    pub const fn truncate_signed(self, val: i128, ptr_width: PtrWidth) -> u128 {
        (val as u128) & self.mask(ptr_width)
    }
}

/// Unsigned integer scalar width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl UintTy {
    /// Size in bytes on a 64-bit target (`PtrWidth::Bits64`).
    pub const fn byte_size(self) -> usize {
        self.byte_size_for(PtrWidth::Bits64)
    }

    /// Size in bytes for the given target pointer width.
    pub const fn byte_size_for(self, ptr_width: PtrWidth) -> usize {
        match self {
            UintTy::Usize => ptr_width.byte_size(),
            UintTy::U8 => 1,
            UintTy::U16 => 2,
            UintTy::U32 => 4,
            UintTy::U64 => 8,
            UintTy::U128 => 16,
        }
    }

    /// Bit width on a 64-bit target (`PtrWidth::Bits64`).
    pub const fn bit_width(self) -> u32 {
        self.bit_width_for(PtrWidth::Bits64)
    }

    /// Bit width for the given target pointer width.
    pub const fn bit_width_for(self, ptr_width: PtrWidth) -> u32 {
        (self.byte_size_for(ptr_width) * 8) as u32
    }

    /// Bitmask covering all bits of this unsigned integer width under `ptr_width`.
    pub const fn mask(self, ptr_width: PtrWidth) -> u128 {
        let bytes = self.byte_size_for(ptr_width);
        if bytes >= 16 {
            u128::MAX
        } else {
            (1u128 << (bytes * 8)) - 1
        }
    }

    /// Maximum representable unsigned value (`UINT_MAX`) under `ptr_width`.
    pub const fn max_value(self, ptr_width: PtrWidth) -> u128 {
        self.mask(ptr_width)
    }
}

/// Mutability qualifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mutability {
    Not,
    Mut,
}

/// Niche-aware scalar type descriptor for MIR cast and transmute validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarTy {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Ptr(Mutability),
}

impl ScalarTy {
    /// Size in bytes under `ptr_width`.
    pub const fn size_bytes(&self, ptr_width: PtrWidth) -> usize {
        match self {
            ScalarTy::Bool => 1,
            ScalarTy::Char => 4,
            ScalarTy::Int(it) => it.byte_size_for(ptr_width),
            ScalarTy::Uint(ut) => ut.byte_size_for(ptr_width),
            ScalarTy::Ptr(_) => ptr_width.byte_size(),
        }
    }

    /// Size in bytes on a 64-bit target (`PtrWidth::Bits64`).
    pub const fn byte_size(&self) -> usize {
        self.size_bytes(PtrWidth::Bits64)
    }

    /// Bit width under `ptr_width`.
    pub const fn bit_width(&self, ptr_width: PtrWidth) -> u32 {
        (self.size_bytes(ptr_width) * 8) as u32
    }

    /// Returns true if this scalar descriptor is a pointer.
    pub const fn is_ptr(&self) -> bool {
        matches!(self, ScalarTy::Ptr(_))
    }

    /// Checks whether `bits` is a valid bit pattern for this scalar type under `ptr_width`.
    ///
    /// - Enforces width bound: for `size < 16`, `bits < (1u128 << (size * 8))`.
    /// - `ScalarTy::Bool`: only `0` and `1` are valid.
    /// - `ScalarTy::Char`: only Unicode scalar values (`bits < 0xD800` or `0xE000 <= bits <= 0x10FFFF`) are valid.
    /// - `ScalarTy::Int(_)` / `ScalarTy::Uint(_)` / `ScalarTy::Ptr(_)`: all bit patterns within the width bound are valid.
    pub const fn is_valid_bits(&self, bits: u128, ptr_width: PtrWidth) -> bool {
        let size = self.size_bytes(ptr_width);
        if size < 16 {
            let limit = 1u128 << (size * 8);
            if bits >= limit {
                return false;
            }
        }
        match self {
            ScalarTy::Bool => bits <= 1,
            ScalarTy::Char => bits < 0xD800 || (bits >= 0xE000 && bits <= 0x10FFFF),
            ScalarTy::Int(_) | ScalarTy::Uint(_) | ScalarTy::Ptr(_) => true,
        }
    }

    /// Returns true for integer scalar descriptors (`Int` / `Uint`).
    pub const fn is_integral(&self) -> bool {
        matches!(self, ScalarTy::Int(_) | ScalarTy::Uint(_))
    }

    /// Converts an integer scalar descriptor to its MIR `Ty` (`None` for `Bool`, `Char`, `Ptr`).
    pub fn int_ty(&self) -> Option<Ty> {
        match self {
            ScalarTy::Int(it) => Some(Ty::Int(*it)),
            ScalarTy::Uint(ut) => Some(Ty::Uint(*ut)),
            ScalarTy::Bool | ScalarTy::Char | ScalarTy::Ptr(_) => None,
        }
    }
}

/// Bitmask of the low `bit_width` bits: `0` for width `0` and `u128::MAX` for widths `>= 128`
/// (never evaluating the overflowing shift `1u128 << 128`).
pub const fn width_mask(bit_width: u32) -> u128 {
    if bit_width == 0 {
        0
    } else if bit_width >= 128 {
        u128::MAX
    } else {
        (1u128 << bit_width) - 1
    }
}

/// Sign-extends the low `bit_width` bits of `bits` to an `i128` (`bit_width` in `1..=128`).
pub const fn sign_extend_bits(bits: u128, bit_width: u32) -> i128 {
    if bit_width == 0 {
        0
    } else if bit_width >= 128 {
        bits as i128
    } else {
        let shift = 128 - bit_width;
        ((bits << shift) as i128) >> shift
    }
}

/// Valid range of a scalar's bit pattern (`rustc`'s `WrappingRange`, `Anneal.BitValidity`), as
/// declared by `#[rustc_layout_scalar_valid_range_start/end]` niches such as `NonZero<T>`
/// (`1..=MAX`) or `NonNull<T>`.
///
/// For a scalar of `bit_width` bits, `bits` is contained iff `bits <= width_mask(bit_width)` and
/// - `start <= end` (non-wrapping): `start <= bits && bits <= end`;
/// - `start > end` (wrapping): `bits >= start || bits <= end`.
///
/// Bounds beyond `width_mask(bit_width)` are clipped by the width check: a non-wrapping range
/// whose `start` exceeds the width is empty, whereas a wrapping range always contains `0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScalarValidRange {
    /// First valid bit pattern.
    pub start: u128,
    /// Last valid bit pattern (inclusive; below `start` for a wrapping range).
    pub end: u128,
}

impl ScalarValidRange {
    /// Constructs the range `start..=end` (wrapping when `start > end`).
    pub const fn new(start: u128, end: u128) -> Self {
        ScalarValidRange { start, end }
    }

    /// The full range `0..=width_mask(bit_width)` (no niche).
    pub const fn full(bit_width: u32) -> Self {
        ScalarValidRange {
            start: 0,
            end: width_mask(bit_width),
        }
    }

    /// The non-zero range `1..=width_mask(bit_width)` (the `NonZero<T>` / `NonNull<T>` niche).
    pub const fn non_zero(bit_width: u32) -> Self {
        ScalarValidRange {
            start: 1,
            end: width_mask(bit_width),
        }
    }

    /// Returns true if this range wraps around (`start > end`).
    pub const fn is_wrapping(&self) -> bool {
        self.start > self.end
    }

    /// Returns true if `bits` is a valid bit pattern of a `bit_width`-bit scalar in this range.
    pub const fn contains(&self, bits: u128, bit_width: u32) -> bool {
        if bits > width_mask(bit_width) {
            return false;
        }
        if self.start <= self.end {
            bits >= self.start && bits <= self.end
        } else {
            bits >= self.start || bits <= self.end
        }
    }

    /// Returns true if no `bit_width`-bit pattern is contained in this range (only possible for
    /// a non-wrapping range whose `start` exceeds the width).
    pub const fn is_empty(&self, bit_width: u32) -> bool {
        self.start <= self.end && self.start > width_mask(bit_width)
    }

    /// Returns true if every `bit_width`-bit pattern is contained in this range.
    pub const fn is_full(&self, bit_width: u32) -> bool {
        let mask = width_mask(bit_width);
        if self.start <= self.end {
            self.start == 0 && self.end >= mask
        } else {
            // `end < start`, so `end + 1` cannot overflow.
            self.end >= mask || self.start == self.end + 1
        }
    }

    /// The contained `bit_width`-bit patterns as at most two disjoint inclusive intervals.
    pub fn intervals(&self, bit_width: u32) -> Vec<(u128, u128)> {
        let mask = width_mask(bit_width);
        let mut out = Vec::with_capacity(2);
        if self.start <= self.end {
            if self.start <= mask {
                out.push((self.start, self.end.min(mask)));
            }
        } else if self.end >= mask {
            out.push((0, mask));
        } else {
            out.push((0, self.end));
            if self.start <= mask {
                out.push((self.start, mask));
            }
        }
        out
    }
}

/// Returns true if two lists of inclusive intervals share at least one point.
fn intervals_intersect(a: &[(u128, u128)], b: &[(u128, u128)]) -> bool {
    a.iter()
        .any(|&(a0, a1)| b.iter().any(|&(b0, b1)| a0.max(b0) <= a1.min(b1)))
}

/// Primary `#[repr(...)]` of an ADT.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AdtReprKind {
    /// Default `#[repr(Rust)]` layout (field order chosen by the compiler).
    #[default]
    Rust,
    /// `#[repr(C)]` (declaration-order fields; with an enum `tag_ty`, `#[repr(C, Int)]`).
    C,
    /// `#[repr(transparent)]` (layout of the unique non-1-ZST field).
    Transparent,
}

/// `#[repr(...)]` options of an ADT: the primary representation and an optional
/// `#[repr(align(N))]`. An enum's `#[repr(Int)]` tag type is [`AdtKind::Enum::tag_ty`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AdtRepr {
    /// Primary representation (`Rust`, `C`, or `Transparent`).
    pub kind: AdtReprKind,
    /// Minimum alignment from `#[repr(align(N))]`; must be a power of two no larger than
    /// `2^29` ([`MAX_REPR_ALIGN`]), and is not allowed with `#[repr(transparent)]`.
    pub align: Option<usize>,
}

/// Largest alignment accepted by `#[repr(align(N))]` (`rustc`'s limit of `2^29`).
pub const MAX_REPR_ALIGN: usize = 1 << 29;

impl AdtRepr {
    /// `#[repr(Rust)]`.
    pub const fn rust() -> Self {
        AdtRepr {
            kind: AdtReprKind::Rust,
            align: None,
        }
    }

    /// `#[repr(C)]`.
    pub const fn c() -> Self {
        AdtRepr {
            kind: AdtReprKind::C,
            align: None,
        }
    }

    /// `#[repr(transparent)]`.
    pub const fn transparent() -> Self {
        AdtRepr {
            kind: AdtReprKind::Transparent,
            align: None,
        }
    }

    /// Adds `#[repr(align(align))]`.
    pub const fn with_align(self, align: usize) -> Self {
        AdtRepr {
            kind: self.kind,
            align: Some(align),
        }
    }
}

/// Enum variant definition.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VariantDef {
    /// Variant name (diagnostic only).
    pub name: String,
    /// Explicit discriminant (`V = d`), as a bit pattern of the enum's discriminant type
    /// ([`AdtDef::discr_ty`]); signed discriminants may be given masked (`0xFF` for `-1i8`) or
    /// sign-extended (`u128::MAX`). `None` follows `rustc`'s sequential rule: `0` for the first
    /// variant, otherwise the previous variant's discriminant plus one.
    pub discriminant: Option<u128>,
    /// Field types in declaration order.
    pub fields: Vec<Ty>,
}

impl VariantDef {
    /// Constructs a variant with an implicit (sequential) discriminant.
    pub fn new(name: impl Into<String>, fields: Vec<Ty>) -> Self {
        VariantDef {
            name: name.into(),
            discriminant: None,
            fields,
        }
    }

    /// Sets an explicit discriminant.
    pub fn with_discriminant(mut self, discriminant: u128) -> Self {
        self.discriminant = Some(discriminant);
        self
    }
}

/// Kind of an algebraic data type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AdtKind {
    /// Struct with fields in declaration order.
    Struct { fields: Vec<Ty> },
    /// Enum with an optional explicit `#[repr(Int)]` tag type and its variants.
    Enum {
        tag_ty: Option<ScalarTy>,
        variants: Vec<VariantDef>,
    },
    /// Union with fields in declaration order (all at offset `0`).
    Union { fields: Vec<Ty> },
}

/// Algebraic data type definition carried by [`Ty::Adt`].
///
/// # Layout model
///
/// Layouts follow the natural-alignment model of [`Ty::align_for`]:
/// - **Structs**: `#[repr(C)]` places fields in declaration order, each at the next multiple of
///   its alignment, and rounds the size up to the struct's alignment (the `max` of the field and
///   `repr(align)` alignments, at least `1`). `#[repr(transparent)]` has the layout of its unique
///   field that is not a 1-ZST (size `0`, alignment `1`), or size `0` / alignment `1` if all
///   fields are 1-ZSTs; several non-1-ZST fields, a zero-sized field with alignment above `1`, or
///   `repr(align)` are ill-formed (`E0690`, `E0691`, `E0692`). `#[repr(Rust)]` has the layout of
///   the [`Ty::Tuple`] of its fields (rounded up to `repr(align)`); its field offsets are only
///   determined when that tuple has a canonical byte layout ([`Ty::has_canonical_byte_layout`]).
/// - **Unions** (at least one field, `E0784`): every field at offset `0`; alignment is the `max`
///   of the field and `repr(align)` alignments, size the largest field size rounded up to it.
/// - **Enums**: no variants: size `0`, alignment `1` (any `repr` other than `Rust` is
///   ill-formed, `E0084`). With an explicit `tag_ty` (an integer type), `#[repr(Int)]`
///   (RFC 2195) is a `repr(C)` union of one `repr(C)` struct `(tag, fields...)` per variant, and
///   `#[repr(C, Int)]` is a `repr(C)` struct `(tag, payload)` whose `payload` is a `repr(C)`
///   union of the variants' `repr(C)` field structs. A tagless `#[repr(C)]` enum stores a tag
///   of the target's C `int` size even with a single variant (`#[repr(C)] enum E { A(u32) }`
///   is 8 bytes), which the pointer width does not determine, so its layout is **unspecified**.
///   A tagless `repr(Rust)`/`repr(transparent)` enum follows `rustc`'s univariant rule: a
///   variant is *absent* when some field is uninhabited and every field is a 1-ZST (e.g.
///   `B(!)`, decided for both pointer widths); with no present variant the enum is laid out
///   like `!` (size `0`, alignment `1`, ignoring `repr(align)`), and with exactly one present
///   variant like a struct of that variant's fields with the enum's `repr` (no tag is stored;
///   the absent variants' 1-ZST fields sit at offset `0`). Any other tagless enum has an
///   **unspecified** layout (`repr(Rust)` niche/tag optimizations): it is representable when
///   an upper bound of its size fits in `isize::MAX`, but [`Ty::layout_for`] reports
///   [`LayoutError::Unspecified`], so `size_of`, `align_of`, `offset_of!`, and transmutes
///   through it fail closed.
///
/// A `scalar_valid_range` restricts the bit pattern of a struct whose only non-1-ZST field is a
/// primitive scalar (`bool`, `char`, integers, pointers), e.g. `NonZeroU32` or `NonNull<T>`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AdtDef {
    /// Definition path (e.g. `core::num::NonZeroU32`).
    pub def_path: String,
    /// Struct, enum, or union definition.
    pub kind: AdtKind,
    /// `#[repr(...)]` options.
    pub repr: AdtRepr,
    /// Optional scalar valid range (niche) of a scalar-wrapping struct.
    pub scalar_valid_range: Option<ScalarValidRange>,
}

/// Exact size and alignment of a type under a target pointer width (see [`Ty::layout_for`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TyLayout {
    /// Size in bytes.
    pub size: usize,
    /// ABI alignment in bytes (a power of two).
    pub align: usize,
}

/// Reason a type has no exact layout under a target pointer width.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LayoutError {
    /// An array length exceeds the target's `usize::MAX`, or the size exceeds the target's
    /// `isize::MAX` ([`PtrWidth::max_object_size`]).
    TooLarge,
    /// The representable but not exactly determined layout of a type: a tagless enum with
    /// more than one present variant, a tagless `#[repr(C)]` enum (see [`AdtDef`]), or a type
    /// containing one.
    Unspecified,
    /// Ill-formed ADT definition (with the violated rule).
    IllFormed(&'static str),
}

impl std::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LayoutError::TooLarge => write!(f, "type is too large for the target architecture"),
            LayoutError::Unspecified => write!(f, "type layout is unspecified"),
            LayoutError::IllFormed(reason) => write!(f, "ill-formed ADT definition: {reason}"),
        }
    }
}

impl std::error::Error for LayoutError {}

/// Possibly inexact layout used internally: exact when `exact`, otherwise `size` and `align` are
/// upper bounds and `min_align` a lower bound of the (unspecified) actual layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LayoutInfo {
    size: usize,
    align: usize,
    min_align: usize,
    exact: bool,
}

impl LayoutInfo {
    const fn exact(size: usize, align: usize) -> Self {
        LayoutInfo {
            size,
            align,
            min_align: align,
            exact: true,
        }
    }

    const fn is_one_zst(&self) -> bool {
        self.exact && self.size == 0 && self.align == 1
    }
}

/// MIR type representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    RawPtr(Box<Ty>, Mutability),
    Ref(Box<Ty>, Mutability),
    Array(Box<Ty>, usize),
    Tuple(Vec<Ty>),
    Never,
    /// Struct, enum, or union with a known definition (see [`AdtDef`]). Legacy MIR captures may
    /// still model ADTs as the `Ty::Tuple` of their fields.
    Adt(Arc<AdtDef>),
}

impl Ty {
    /// Constructs the unit type `()`.
    pub fn unit() -> Self {
        Ty::Tuple(Vec::new())
    }

    /// Constructs `Ty::Adt` from an ADT definition.
    pub fn adt(def: AdtDef) -> Self {
        Ty::Adt(Arc::new(def))
    }

    /// Returns the ADT definition if `self` is `Ty::Adt`.
    pub fn as_adt(&self) -> Option<&AdtDef> {
        match self {
            Ty::Adt(def) => Some(def),
            _ => None,
        }
    }

    /// Returns true if this type is the unit tuple `()`.
    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Tuple(fields) if fields.is_empty())
    }

    /// Returns true if this type is an integer type (signed or unsigned).
    pub fn is_integral(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Uint(_))
    }

    /// Returns true if this type is a signed integer type (`IntTy`).
    pub fn is_signed_int(&self) -> bool {
        matches!(self, Ty::Int(_))
    }

    /// Returns true if this type is an unsigned integer type (`UintTy`).
    pub fn is_unsigned_int(&self) -> bool {
        matches!(self, Ty::Uint(_))
    }

    /// Returns true if this type is a raw pointer.
    pub fn is_raw_ptr(&self) -> bool {
        matches!(self, Ty::RawPtr(_, _))
    }

    /// Returns true if this type is a reference.
    pub fn is_ref(&self) -> bool {
        matches!(self, Ty::Ref(_, _))
    }

    /// Returns true if this type is a pointer (raw pointer or reference).
    pub fn is_any_ptr(&self) -> bool {
        self.is_raw_ptr() || self.is_ref()
    }

    /// Returns true if this type or any nested field/element contains a pointer or reference.
    ///
    /// For `Ty::Adt`, every declared field of a struct or union and of every enum variant is
    /// considered (independently of inhabitedness), matching the conservative pointer analysis
    /// of `Ptr -> Int` transmute checks.
    pub fn contains_ptr(&self) -> bool {
        match self {
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => true,
            Ty::Array(elem, count) => *count > 0 && elem.contains_ptr(),
            Ty::Tuple(fields) => fields.iter().any(Ty::contains_ptr),
            Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) | Ty::Never => false,
            Ty::Adt(def) => def.all_fields().any(Ty::contains_ptr),
        }
    }

    /// Returns true if this type or any value it contains without indirection holds a
    /// reference (`&T` / `&mut T`) that `Statement::Retag` must validate: references directly
    /// or inside arrays, tuples, structs, and enum variants, but not inside unions (whose
    /// contents are never retagged) or behind raw pointers.
    pub fn contains_ref(&self) -> bool {
        match self {
            Ty::Ref(_, _) => true,
            Ty::Array(elem, count) => *count > 0 && elem.contains_ref(),
            Ty::Tuple(fields) => fields.iter().any(Ty::contains_ref),
            Ty::Adt(def) => !def.is_union() && def.all_fields().any(Ty::contains_ref),
            Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) | Ty::RawPtr(_, _) | Ty::Never => false,
        }
    }

    /// Returns the pointee type if `self` is `RawPtr` or `Ref`.
    pub fn pointee_ty(&self) -> Option<&Ty> {
        match self {
            Ty::RawPtr(inner, _) | Ty::Ref(inner, _) => Some(inner),
            _ => None,
        }
    }

    /// Converts a scalar MIR `Ty` to its `ScalarTy` descriptor, or `None` for composites/`Never`.
    pub fn to_scalar_ty(&self) -> Option<ScalarTy> {
        match self {
            Ty::Bool => Some(ScalarTy::Bool),
            Ty::Char => Some(ScalarTy::Char),
            Ty::Int(it) => Some(ScalarTy::Int(*it)),
            Ty::Uint(ut) => Some(ScalarTy::Uint(*ut)),
            Ty::RawPtr(_, m) | Ty::Ref(_, m) => Some(ScalarTy::Ptr(*m)),
            Ty::Array(_, _) | Ty::Tuple(_) | Ty::Never | Ty::Adt(_) => None,
        }
    }

    /// Returns true if this type is a single scalar (`Bool`, `Char`, `Int`, `Uint`, `RawPtr`, `Ref`).
    pub fn is_scalar(&self) -> bool {
        self.to_scalar_ty().is_some()
    }

    /// Bitmask for scalar types under `ptr_width`.
    pub fn scalar_mask(&self, ptr_width: PtrWidth) -> u128 {
        match self {
            Ty::Bool => 1,
            Ty::Char => 0xFFFF_FFFF,
            Ty::Int(it) => it.mask(ptr_width),
            Ty::Uint(ut) => ut.mask(ptr_width),
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => ptr_width.mask(),
            Ty::Array(_, _) | Ty::Tuple(_) | Ty::Never | Ty::Adt(_) => 0,
        }
    }

    /// Bit width of a scalar type under `ptr_width` (`None` for non-scalars).
    pub fn scalar_bit_width(&self, ptr_width: PtrWidth) -> Option<u32> {
        self.to_scalar_ty().map(|scalar| scalar.bit_width(ptr_width))
    }

    /// Valid bit patterns of a scalar type under `ptr_width` as disjoint inclusive intervals
    /// (`bool`: `0..=1`; `char`: Unicode scalar values; `&T`: non-null; integers and raw
    /// pointers: every pattern of their width). Empty for non-scalar types.
    pub fn scalar_valid_intervals(&self, ptr_width: PtrWidth) -> Vec<(u128, u128)> {
        match self {
            Ty::Bool => vec![(0, 1)],
            Ty::Char => vec![(0, 0xD7FF), (0xE000, 0x10FFFF)],
            Ty::Int(_) | Ty::Uint(_) | Ty::RawPtr(_, _) => vec![(0, self.scalar_mask(ptr_width))],
            Ty::Ref(_, _) => vec![(1, ptr_width.mask())],
            Ty::Array(_, _) | Ty::Tuple(_) | Ty::Never | Ty::Adt(_) => Vec::new(),
        }
    }

    /// Checks whether `bits` is a valid bit pattern for a scalar `Ty`, including the
    /// non-null niche requirement (`bits != 0`) on `Ty::Ref`.
    pub fn is_valid_scalar_bits(&self, bits: u128, ptr_width: PtrWidth) -> bool {
        let Some(scalar) = self.to_scalar_ty() else {
            return false;
        };
        if !scalar.is_valid_bits(bits, ptr_width) {
            return false;
        }
        if self.is_ref() && bits == 0 {
            return false;
        }
        true
    }

    /// Returns true if this type is inhabited (has at least one valid value).
    ///
    /// Recursively detects uninhabited `Ty::Never`:
    /// - `Ty::Never` is uninhabited (`false`).
    /// - `Ty::Tuple(fields)` is inhabited iff all `fields` are inhabited.
    /// - `Ty::Array(elem, count)` is inhabited iff `count == 0` or `elem` is inhabited
    ///   (note: `[!; 0]` IS inhabited, whereas `[!; 1]` is uninhabited!).
    /// - `Ty::Adt` follows [`AdtDef::is_inhabited_for`] (structs: all fields; enums: some
    ///   variant with all fields inhabited; unions: no fields or some inhabited field; a
    ///   `scalar_valid_range` excluding every valid scalar bit pattern is uninhabited).
    ///
    /// Pointer-sized scalar valid ranges are evaluated on a 64-bit target; use
    /// [`Ty::is_inhabited_for`] for an explicit target pointer width.
    pub fn is_inhabited(&self) -> bool {
        self.is_inhabited_for(PtrWidth::Bits64)
    }

    /// Returns true if this type is inhabited under `ptr_width` (see [`Ty::is_inhabited`]).
    pub fn is_inhabited_for(&self, ptr_width: PtrWidth) -> bool {
        match self {
            Ty::Never => false,
            Ty::Tuple(fields) => fields.iter().all(|f| f.is_inhabited_for(ptr_width)),
            Ty::Array(elem, count) => *count == 0 || elem.is_inhabited_for(ptr_width),
            Ty::Bool
            | Ty::Char
            | Ty::Int(_)
            | Ty::Uint(_)
            | Ty::RawPtr(_, _)
            | Ty::Ref(_, _) => true,
            Ty::Adt(def) => def.is_inhabited_for(ptr_width),
        }
    }

    /// Size in bytes on a 64-bit target architecture (`PtrWidth::Bits64`).
    pub fn byte_size(&self) -> usize {
        self.byte_size_for(PtrWidth::Bits64)
    }

    /// ABI alignment in bytes under `ptr_width`.
    ///
    /// Anneal's layout model assumes *natural* alignment for primitive scalars
    /// (`align_of::<T>() == size_of::<T>()` for `bool`, `char`, every integer type, and thin
    /// pointers), as on `x86_64`, `aarch64`, `riscv`, and `wasm32`. Targets that under-align
    /// 64/128-bit integers (e.g. `i686`, where `align_of::<u64>() == 4`) are not modeled.
    /// Arrays have their element's alignment; tuples have the maximum field alignment
    /// (`1` for `()`); `!` has alignment `1`. `Ty::Adt` follows the [`AdtDef`] layout model
    /// (an upper bound for unspecified layouts, `1` for ill-formed or too-large ADTs).
    pub fn align_for(&self, ptr_width: PtrWidth) -> usize {
        match self {
            Ty::Bool | Ty::Never => 1,
            Ty::Char => 4,
            Ty::Int(it) => it.byte_size_for(ptr_width),
            Ty::Uint(ut) => ut.byte_size_for(ptr_width),
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => ptr_width.byte_size(),
            Ty::Array(elem, _) => elem.align_for(ptr_width),
            Ty::Tuple(fields) => fields.iter().map(|f| f.align_for(ptr_width)).max().unwrap_or(1),
            Ty::Adt(def) => def.layout_info(ptr_width).map(|l| l.align).unwrap_or(1),
        }
    }

    /// Size in bytes for the given target pointer width (saturating on overflow).
    ///
    /// Matches `rustc`'s `repr(Rust)` layout under the natural-alignment model of
    /// [`Ty::align_for`]: arrays are `count * size_of(elem)`, and tuples are the sum of their
    /// field sizes rounded up to the tuple's alignment, which is the minimal size `rustc`'s
    /// field reordering always achieves (e.g. `(u8, u32)` and `(u8, u32, u8)` are both `8`
    /// bytes, `(u16, u8)` is `4`, `(u64, u32)` is `16`). Uninhabited types still have a
    /// layout size (`!` is `0`, `(!, u32)` is `4`). `Ty::Adt` follows the [`AdtDef`] layout
    /// model (an upper bound for unspecified layouts, `usize::MAX` for ill-formed or too-large
    /// ADTs).
    ///
    /// Use [`Ty::layout_size_for`] to detect types that are too large for the target.
    pub fn byte_size_for(&self, ptr_width: PtrWidth) -> usize {
        match self {
            Ty::Bool => 1,
            Ty::Char => 4,
            Ty::Int(it) => it.byte_size_for(ptr_width),
            Ty::Uint(ut) => ut.byte_size_for(ptr_width),
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => ptr_width.byte_size(),
            Ty::Array(elem, count) => elem.byte_size_for(ptr_width).saturating_mul(*count),
            Ty::Tuple(fields) => {
                let unpadded = fields
                    .iter()
                    .fold(0usize, |acc, f| acc.saturating_add(f.byte_size_for(ptr_width)));
                let align = self.align_for(ptr_width);
                unpadded.checked_next_multiple_of(align).unwrap_or(usize::MAX)
            }
            Ty::Never => 0,
            Ty::Adt(def) => def.layout_info(ptr_width).map(|l| l.size).unwrap_or(usize::MAX),
        }
    }

    /// Computes this type's (possibly inexact) layout under `ptr_width`, checking that every
    /// component is representable and every ADT well-formed.
    fn layout_info(&self, ptr_width: PtrWidth) -> Result<LayoutInfo, LayoutError> {
        let info = match self {
            Ty::Bool
            | Ty::Char
            | Ty::Int(_)
            | Ty::Uint(_)
            | Ty::RawPtr(_, _)
            | Ty::Ref(_, _)
            | Ty::Never => LayoutInfo::exact(self.byte_size_for(ptr_width), self.align_for(ptr_width)),
            Ty::Array(elem, count) => {
                if (*count as u128) > ptr_width.max_usize() {
                    return Err(LayoutError::TooLarge);
                }
                let elem_info = elem.layout_info(ptr_width)?;
                let size = elem_info.size.checked_mul(*count).ok_or(LayoutError::TooLarge)?;
                LayoutInfo { size, ..elem_info }
            }
            Ty::Tuple(fields) => {
                let mut info = LayoutInfo::exact(0, 1);
                let mut unpadded = 0usize;
                for field in fields {
                    let field_info = field.layout_info(ptr_width)?;
                    unpadded = unpadded
                        .checked_add(field_info.size)
                        .ok_or(LayoutError::TooLarge)?;
                    info.align = info.align.max(field_info.align);
                    info.min_align = info.min_align.max(field_info.min_align);
                    info.exact &= field_info.exact;
                }
                info.size = unpadded
                    .checked_next_multiple_of(info.align)
                    .ok_or(LayoutError::TooLarge)?;
                info
            }
            Ty::Adt(def) => def.layout_info(ptr_width)?,
        };
        if (info.size as u128) > ptr_width.max_object_size() {
            return Err(LayoutError::TooLarge);
        }
        Ok(info)
    }

    /// Exact size and alignment of this type under `ptr_width`.
    ///
    /// Fails with [`LayoutError::TooLarge`] when an array length exceeds the target's
    /// `usize::MAX` or the size exceeds its `isize::MAX`, [`LayoutError::IllFormed`] for an
    /// ill-formed [`AdtDef`] anywhere in the type (pointees excluded), and
    /// [`LayoutError::Unspecified`] when the layout model does not determine the layout (see
    /// [`AdtDef`]). Uninhabited types still have a layout (`!` is `0` bytes, `(!, u32)` `4`).
    pub fn layout_for(&self, ptr_width: PtrWidth) -> Result<TyLayout, LayoutError> {
        let info = self.layout_info(ptr_width)?;
        if !info.exact {
            return Err(LayoutError::Unspecified);
        }
        Ok(TyLayout {
            size: info.size,
            align: info.align,
        })
    }

    /// Checks that this type is representable under `ptr_width`: every ADT is well-formed and
    /// the size (or, for unspecified layouts, an upper bound of it) fits the target. Unlike
    /// [`Ty::layout_for`], unspecified layouts are accepted.
    pub fn check_representable(&self, ptr_width: PtrWidth) -> Result<(), LayoutError> {
        self.layout_info(ptr_width).map(|_| ())
    }

    /// Lower and upper bounds `(min_align, max_align)` of this type's alignment under
    /// `ptr_width` (equal when the layout is exact).
    pub fn align_bounds(&self, ptr_width: PtrWidth) -> Result<(usize, usize), LayoutError> {
        self.layout_info(ptr_width)
            .map(|info| (info.min_align, info.align))
    }

    /// Size in bytes of this type's layout under `ptr_width`, or `None` if the type is not
    /// representable on that target: an array length exceeding the target's `usize::MAX`,
    /// or a total size exceeding the target's `isize::MAX` ([`PtrWidth::max_object_size`]).
    /// Also `None` for an ill-formed or unspecified ADT layout (see [`Ty::layout_for`]).
    ///
    /// Unlike [`Ty::checked_byte_size`], uninhabited types still report their layout size
    /// (`!` is `Some(0)`, `(!, u32)` is `Some(4)`), because pointer arithmetic and transmute
    /// size checks operate on layout sizes.
    pub fn layout_size_for(&self, ptr_width: PtrWidth) -> Option<usize> {
        self.layout_for(ptr_width).ok().map(|layout| layout.size)
    }

    /// Computes the byte size of an inhabited type under `ptr_width`, returning `None`
    /// if the type is uninhabited (e.g., `!`, `(!, u32)`, `[!; 1]`) or if its layout is not
    /// representable on the target (see [`Ty::layout_size_for`]).
    ///
    /// Note that `[!; 0]` is inhabited and returns `Some(0)`.
    pub fn checked_byte_size(&self, ptr_width: PtrWidth) -> Option<usize> {
        if !self.is_inhabited_for(ptr_width) {
            return None;
        }
        self.layout_size_for(ptr_width)
    }

    /// Returns true if this type contains a niche-bearing scalar (`bool`, `char`, or `&T`), or
    /// an ADT exposing a niche (a non-full `scalar_valid_range`, an enum tag with invalid
    /// values, or an unspecified enum layout), whose placement `rustc` may optimize when laying
    /// out tuples. Unions never expose niches. Evaluated on a 64-bit target.
    pub fn contains_niche(&self) -> bool {
        self.contains_niche_for(PtrWidth::Bits64)
    }

    /// [`Ty::contains_niche`] under an explicit `ptr_width`.
    pub fn contains_niche_for(&self, ptr_width: PtrWidth) -> bool {
        match self {
            Ty::Bool | Ty::Char | Ty::Ref(_, _) => true,
            Ty::Array(elem, count) => *count > 0 && elem.contains_niche_for(ptr_width),
            Ty::Tuple(fields) => fields.iter().any(|f| f.contains_niche_for(ptr_width)),
            Ty::Int(_) | Ty::Uint(_) | Ty::RawPtr(_, _) | Ty::Never => false,
            Ty::Adt(def) => def.contains_niche_for(ptr_width),
        }
    }

    /// `rustc`'s field-ordering key `log2(max(align, size))` for niche-free fields.
    fn alignment_group_key(&self, ptr_width: PtrWidth) -> u32 {
        let align = self.align_for(ptr_width);
        let size = self.byte_size_for(ptr_width);
        align.max(size).trailing_zeros()
    }

    /// Returns true if this type has a *canonical byte layout* under `ptr_width`: its
    /// in-memory representation under `rustc`'s `repr(Rust)` layout is the padding-free
    /// concatenation of its fields in declaration order (arrays: elements in index order),
    /// with scalars encoded little-endian.
    ///
    /// - Scalars, `!`, and arrays of canonical element types are canonical.
    /// - A tuple is canonical when all fields are canonical and either
    ///   (a) it has at most one field,
    ///   (b) all of its fields have the same type, or
    ///   (c) no field contains a niche-bearing scalar (`bool`, `char`, `&T`), both the fields'
    ///   ABI alignments and their alignment-group keys `log2(max(align, size))` are
    ///   non-increasing in declaration order, and declaration order has no padding at all
    ///   (every field offset is aligned and the unpadded size is a multiple of the tuple's
    ///   alignment).
    ///
    /// These conditions are deliberately conservative: declaration order is then already
    /// size-optimal *and* sorted under every field-sorting key `rustc` has used (plain ABI
    /// alignment in older compilers, `log2(max(align, size))` in current ones), so its
    /// field-reordering heuristics keep it across compiler versions. (`rustc` 1.98 in fact also
    /// keeps declaration order for some tuples rejected here, e.g. `([u8; 4], u32)` has field
    /// offsets `[0, 4]`, but older `rustc` sorted the `u32` first.) Byte-level
    /// (`CastKind::Transmute`) reinterpretation is only defined for canonical layouts: e.g.
    /// `(u16, u16)`, `(u32, u16, u16)`, and `(*const u8, u64)` are canonical, whereas
    /// `(u8, u32)` (padding), `(u32, u64)` (fields not sorted by alignment), and `(u8, bool)`
    /// (niche placement is compiler-dependent) are not.
    ///
    /// A `Ty::Adt` must have an exact, well-formed layout and be canonical per
    /// [`AdtDef::has_canonical_byte_layout`].
    pub fn has_canonical_byte_layout(&self, ptr_width: PtrWidth) -> bool {
        match self {
            Ty::Bool
            | Ty::Char
            | Ty::Int(_)
            | Ty::Uint(_)
            | Ty::RawPtr(_, _)
            | Ty::Ref(_, _)
            | Ty::Never => true,
            Ty::Array(elem, _) => elem.has_canonical_byte_layout(ptr_width),
            Ty::Tuple(fields) => {
                if !fields.iter().all(|f| f.has_canonical_byte_layout(ptr_width)) {
                    return false;
                }
                if fields.len() <= 1 || fields.windows(2).all(|w| w[0] == w[1]) {
                    return true;
                }
                if fields.iter().any(|f| f.contains_niche_for(ptr_width)) {
                    return false;
                }
                let keys_non_increasing = fields.windows(2).all(|w| {
                    w[0].align_for(ptr_width) >= w[1].align_for(ptr_width)
                        && w[0].alignment_group_key(ptr_width)
                            >= w[1].alignment_group_key(ptr_width)
                });
                if !keys_non_increasing {
                    return false;
                }
                let mut offset = 0usize;
                for f in fields {
                    if !offset.is_multiple_of(f.align_for(ptr_width)) {
                        return false;
                    }
                    offset = offset.saturating_add(f.byte_size_for(ptr_width));
                }
                offset.is_multiple_of(self.align_for(ptr_width))
            }
            Ty::Adt(def) => def.has_canonical_byte_layout(ptr_width),
        }
    }
}

/// Byte offset of field `idx` in a `#[repr(Rust)]` field list: the declaration-order prefix
/// sum when the fields' tuple has a canonical byte layout, otherwise unspecified.
fn rust_field_offset(fields: &[Ty], idx: usize, ptr_width: PtrWidth) -> Result<usize, LayoutError> {
    if !Ty::Tuple(fields.to_vec()).has_canonical_byte_layout(ptr_width) {
        return Err(LayoutError::Unspecified);
    }
    let mut offset = 0usize;
    for field in &fields[..idx] {
        offset = offset
            .checked_add(field.layout_for(ptr_width)?.size)
            .ok_or(LayoutError::TooLarge)?;
    }
    Ok(offset)
}

/// Byte offset of field `idx` in a struct-like field list laid out with `kind`.
fn struct_like_field_offset(
    fields: &[Ty],
    idx: usize,
    kind: AdtReprKind,
    ptr_width: PtrWidth,
) -> Result<usize, LayoutError> {
    match kind {
        AdtReprKind::C => {
            let mut offset = 0usize;
            for (i, field) in fields.iter().enumerate().take(idx + 1) {
                let layout = field.layout_for(ptr_width)?;
                offset = offset
                    .checked_next_multiple_of(layout.align)
                    .ok_or(LayoutError::TooLarge)?;
                if i == idx {
                    return Ok(offset);
                }
                offset = offset.checked_add(layout.size).ok_or(LayoutError::TooLarge)?;
            }
            Err(LayoutError::IllFormed("field index out of range"))
        }
        AdtReprKind::Transparent => {
            let layout = fields[idx].layout_for(ptr_width)?;
            if layout.size != 0 || layout.align != 1 {
                // The unique non-1-ZST field shares the wrapper's address.
                return Ok(0);
            }
            if fields
                .iter()
                .all(|f| f.layout_for(ptr_width).is_ok_and(|l| l.size == 0))
            {
                return Ok(0);
            }
            // `rustc` reorders 1-ZST fields around the non-1-ZST field like `repr(Rust)`.
            rust_field_offset(fields, idx, ptr_width)
        }
        AdtReprKind::Rust => rust_field_offset(fields, idx, ptr_width),
    }
}

/// Possibly inexact layout of a struct-like field list (a struct, or the present variant of an
/// enum laid out without a tag) laid out with `kind` and minimum alignment `repr_align`.
fn struct_like_layout(
    fields: &[Ty],
    kind: AdtReprKind,
    repr_align: usize,
    ptr_width: PtrWidth,
) -> Result<LayoutInfo, LayoutError> {
    match kind {
        AdtReprKind::Rust | AdtReprKind::C => {
            let mut info = LayoutInfo::exact(0, repr_align);
            let mut offset = 0usize;
            for field in fields {
                let field_info = field.layout_info(ptr_width)?;
                if kind == AdtReprKind::C {
                    offset = offset
                        .checked_next_multiple_of(field_info.align)
                        .ok_or(LayoutError::TooLarge)?;
                }
                offset = offset
                    .checked_add(field_info.size)
                    .ok_or(LayoutError::TooLarge)?;
                info.align = info.align.max(field_info.align);
                info.min_align = info.min_align.max(field_info.min_align);
                info.exact &= field_info.exact;
            }
            info.size = offset
                .checked_next_multiple_of(info.align)
                .ok_or(LayoutError::TooLarge)?;
            Ok(info)
        }
        AdtReprKind::Transparent => {
            let mut inner: Option<LayoutInfo> = None;
            for field in fields {
                let field_info = field.layout_info(ptr_width)?;
                if field_info.exact && field_info.size == 0 {
                    if field_info.align != 1 {
                        return Err(LayoutError::IllFormed(
                            "repr(transparent) zero-sized fields must have alignment 1 (E0691)",
                        ));
                    }
                    continue;
                }
                if inner.is_some() {
                    return Err(LayoutError::IllFormed(
                        "repr(transparent) allows at most one non-zero-sized field (E0690)",
                    ));
                }
                inner = Some(field_info);
            }
            Ok(inner.unwrap_or(LayoutInfo::exact(0, 1)))
        }
    }
}

/// Possibly inexact layout of an enum with an explicit integer `tag` (`#[repr(Int)]` when
/// `kind` is `Rust`, `#[repr(C, Int)]` when `kind` is `C`).
fn tagged_layout(
    tag: ScalarTy,
    variants: &[VariantDef],
    kind: AdtReprKind,
    repr_align: usize,
    ptr_width: PtrWidth,
) -> Result<LayoutInfo, LayoutError> {
    let tag_size = tag.size_bytes(ptr_width);
    let mut info = LayoutInfo::exact(0, repr_align.max(tag_size));
    if kind == AdtReprKind::C {
        // `repr(C)` struct `(tag, payload)` with `payload` a `repr(C)` union of the variants'
        // `repr(C)` field structs.
        let mut payload_size = 0usize;
        let mut payload_align = 1usize;
        for variant in variants {
            let variant_info = struct_like_layout(&variant.fields, AdtReprKind::C, 1, ptr_width)?;
            payload_size = payload_size.max(variant_info.size);
            payload_align = payload_align.max(variant_info.align);
            info.min_align = info.min_align.max(variant_info.min_align);
            info.exact &= variant_info.exact;
        }
        let payload_offset = tag_size
            .checked_next_multiple_of(payload_align)
            .ok_or(LayoutError::TooLarge)?;
        let union_size = payload_size
            .checked_next_multiple_of(payload_align)
            .ok_or(LayoutError::TooLarge)?;
        info.align = info.align.max(payload_align);
        info.size = payload_offset
            .checked_add(union_size)
            .and_then(|end| end.checked_next_multiple_of(info.align))
            .ok_or(LayoutError::TooLarge)?;
    } else {
        // `repr(C)` union of one `repr(C)` struct `(tag, fields...)` per variant (RFC 2195).
        for variant in variants {
            let mut offset = tag_size;
            let mut variant_align = tag_size;
            for field in &variant.fields {
                let field_info = field.layout_info(ptr_width)?;
                offset = offset
                    .checked_next_multiple_of(field_info.align)
                    .and_then(|start| start.checked_add(field_info.size))
                    .ok_or(LayoutError::TooLarge)?;
                variant_align = variant_align.max(field_info.align);
                info.min_align = info.min_align.max(field_info.min_align);
                info.exact &= field_info.exact;
            }
            let variant_size = offset
                .checked_next_multiple_of(variant_align)
                .ok_or(LayoutError::TooLarge)?;
            info.size = info.size.max(variant_size);
            info.align = info.align.max(variant_align);
        }
        info.size = info
            .size
            .checked_next_multiple_of(info.align)
            .ok_or(LayoutError::TooLarge)?;
    }
    Ok(info)
}

/// Smallest integer tag (at least `min_bytes` wide) that can hold every discriminant in
/// `discrs`, given as `isize` bit patterns of `bit_width` bits.
fn smallest_fit_tag(discrs: &[u128], bit_width: u32, min_bytes: usize) -> ScalarTy {
    let values: Vec<i128> = discrs
        .iter()
        .map(|&d| sign_extend_bits(d, bit_width))
        .collect();
    let min = values.iter().copied().min().unwrap_or(0);
    let max = values.iter().copied().max().unwrap_or(0);
    let unsigned = [UintTy::U8, UintTy::U16, UintTy::U32, UintTy::U64, UintTy::U128];
    let signed = [IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::I128];
    if min >= 0 {
        for ut in unsigned {
            let bytes = ut.byte_size_for(PtrWidth::Bits64);
            if bytes >= min_bytes && (max as u128) <= ut.max_value(PtrWidth::Bits64) {
                return ScalarTy::Uint(ut);
            }
        }
        ScalarTy::Uint(UintTy::U128)
    } else {
        for it in signed {
            let bytes = it.byte_size_for(PtrWidth::Bits64);
            if bytes >= min_bytes
                && min >= it.min_value(PtrWidth::Bits64)
                && max <= it.max_value(PtrWidth::Bits64)
            {
                return ScalarTy::Int(it);
            }
        }
        ScalarTy::Int(IntTy::I128)
    }
}

impl AdtDef {
    /// Constructs a `#[repr(Rust)]` struct definition.
    pub fn new_struct(def_path: impl Into<String>, fields: Vec<Ty>) -> Self {
        AdtDef {
            def_path: def_path.into(),
            kind: AdtKind::Struct { fields },
            repr: AdtRepr::default(),
            scalar_valid_range: None,
        }
    }

    /// Constructs an enum definition with an optional explicit `#[repr(Int)]` tag type.
    pub fn new_enum(
        def_path: impl Into<String>,
        tag_ty: Option<ScalarTy>,
        variants: Vec<VariantDef>,
    ) -> Self {
        AdtDef {
            def_path: def_path.into(),
            kind: AdtKind::Enum { tag_ty, variants },
            repr: AdtRepr::default(),
            scalar_valid_range: None,
        }
    }

    /// Constructs a `#[repr(Rust)]` union definition.
    pub fn new_union(def_path: impl Into<String>, fields: Vec<Ty>) -> Self {
        AdtDef {
            def_path: def_path.into(),
            kind: AdtKind::Union { fields },
            repr: AdtRepr::default(),
            scalar_valid_range: None,
        }
    }

    /// Replaces the `#[repr(...)]` options.
    pub fn with_repr(mut self, repr: AdtRepr) -> Self {
        self.repr = repr;
        self
    }

    /// Sets the scalar valid range (niche) of a scalar-wrapping struct.
    pub fn with_scalar_valid_range(mut self, range: ScalarValidRange) -> Self {
        self.scalar_valid_range = Some(range);
        self
    }

    /// Wraps this definition as a `Ty::Adt`.
    pub fn into_ty(self) -> Ty {
        Ty::adt(self)
    }

    /// Returns true for struct definitions.
    pub fn is_struct(&self) -> bool {
        matches!(self.kind, AdtKind::Struct { .. })
    }

    /// Returns true for enum definitions.
    pub fn is_enum(&self) -> bool {
        matches!(self.kind, AdtKind::Enum { .. })
    }

    /// Returns true for union definitions.
    pub fn is_union(&self) -> bool {
        matches!(self.kind, AdtKind::Union { .. })
    }

    /// Number of variants (`1` for structs and unions).
    pub fn variant_count(&self) -> usize {
        match &self.kind {
            AdtKind::Enum { variants, .. } => variants.len(),
            AdtKind::Struct { .. } | AdtKind::Union { .. } => 1,
        }
    }

    /// Field types of variant `variant_idx` (structs and unions only have variant `0`).
    pub fn variant_fields(&self, variant_idx: usize) -> Option<&[Ty]> {
        match &self.kind {
            AdtKind::Struct { fields } | AdtKind::Union { fields } => {
                (variant_idx == 0).then_some(fields.as_slice())
            }
            AdtKind::Enum { variants, .. } => {
                variants.get(variant_idx).map(|v| v.fields.as_slice())
            }
        }
    }

    /// Iterates over every declared field type of every variant.
    pub fn all_fields(&self) -> impl Iterator<Item = &Ty> {
        let (direct, variants): (&[Ty], &[VariantDef]) = match &self.kind {
            AdtKind::Struct { fields } | AdtKind::Union { fields } => (fields, &[]),
            AdtKind::Enum { variants, .. } => (&[], variants),
        };
        direct
            .iter()
            .chain(variants.iter().flat_map(|v| v.fields.iter()))
    }

    /// Result type of `Rvalue::Discriminant` on this ADT (`rustc`'s `discriminant_ty`): the
    /// enum's `tag_ty` or `isize` for enums, and `u8` (always `0`) for structs and unions.
    pub fn discr_ty(&self) -> Ty {
        match &self.kind {
            AdtKind::Enum { tag_ty, .. } => tag_ty
                .and_then(|tag| tag.int_ty())
                .unwrap_or(Ty::Int(IntTy::Isize)),
            AdtKind::Struct { .. } | AdtKind::Union { .. } => Ty::Uint(UintTy::U8),
        }
    }

    /// Signedness and bit width of this enum's discriminant type under `ptr_width`.
    fn discr_int(&self, ptr_width: PtrWidth) -> Result<(bool, u32), LayoutError> {
        match &self.kind {
            AdtKind::Enum { tag_ty: None, .. } => Ok((true, IntTy::Isize.bit_width_for(ptr_width))),
            AdtKind::Enum {
                tag_ty: Some(ScalarTy::Int(it)),
                ..
            } => Ok((true, it.bit_width_for(ptr_width))),
            AdtKind::Enum {
                tag_ty: Some(ScalarTy::Uint(ut)),
                ..
            } => Ok((false, ut.bit_width_for(ptr_width))),
            AdtKind::Enum { tag_ty: Some(_), .. } => {
                Err(LayoutError::IllFormed("enum tag type must be an integer type"))
            }
            AdtKind::Struct { .. } | AdtKind::Union { .. } => Ok((false, 8)),
        }
    }

    /// Resolved discriminants of all variants under `ptr_width`, as bit patterns masked to the
    /// discriminant type's width (`[0]` for structs and unions).
    ///
    /// Explicit discriminants must fit the discriminant type (signed ones masked or
    /// sign-extended); implicit ones follow `rustc`'s sequential rule and must not overflow
    /// (`E0370`); all discriminants must be distinct (`E0081`).
    pub fn discriminants(&self, ptr_width: PtrWidth) -> Result<Vec<u128>, LayoutError> {
        let AdtKind::Enum { variants, .. } = &self.kind else {
            return Ok(vec![0]);
        };
        let (signed, bit_width) = self.discr_int(ptr_width)?;
        let mask = width_mask(bit_width);
        let min_signed = sign_extend_bits(1u128 << (bit_width - 1), bit_width);
        let max_signed = (mask >> 1) as i128;
        let mut out = Vec::with_capacity(variants.len());
        let mut seen = BTreeSet::new();
        let mut prev: Option<u128> = None;
        for variant in variants {
            let bits = match (variant.discriminant, prev) {
                (Some(d), _) => {
                    let sign_extended = d as i128;
                    if d <= mask {
                        d
                    } else if signed && sign_extended < 0 && sign_extended >= min_signed {
                        d & mask
                    } else {
                        return Err(LayoutError::IllFormed(
                            "enum discriminant does not fit the discriminant type",
                        ));
                    }
                }
                (None, None) => 0,
                (None, Some(p)) => {
                    let overflow = if signed {
                        sign_extend_bits(p, bit_width) == max_signed
                    } else {
                        p == mask
                    };
                    if overflow {
                        return Err(LayoutError::IllFormed("enum discriminant overflowed (E0370)"));
                    }
                    p.wrapping_add(1) & mask
                }
            };
            if !seen.insert(bits) {
                return Err(LayoutError::IllFormed("duplicate enum discriminant (E0081)"));
            }
            out.push(bits);
            prev = Some(bits);
        }
        Ok(out)
    }

    /// Discriminant bit pattern of variant `variant_idx` (masked to [`AdtDef::discr_ty`]).
    pub fn discriminant_bits(&self, variant_idx: usize, ptr_width: PtrWidth) -> Result<u128, LayoutError> {
        self.discriminants(ptr_width)?
            .get(variant_idx)
            .copied()
            .ok_or(LayoutError::IllFormed("variant index out of range"))
    }

    /// Variant whose discriminant is `bits` (a bit pattern of the discriminant type), if any.
    pub fn variant_index_of_discriminant(&self, bits: u128, ptr_width: PtrWidth) -> Option<usize> {
        self.discriminants(ptr_width)
            .ok()?
            .iter()
            .position(|d| *d == bits)
    }

    /// Returns true if `rustc` never represents a value of an enum variant with these `fields`
    /// (an *absent* variant): some field is uninhabited and every field is a 1-ZST (which is
    /// width-independent among representable types; `layout_info` checks `ptr_width` bounds).
    fn is_absent_variant(fields: &[Ty]) -> bool {
        let pw = PtrWidth::Bits64;
        fields.iter().any(|f| !f.is_inhabited_for(pw))
            && fields
                .iter()
                .all(|f| f.layout_info(pw).is_ok_and(|l| l.is_one_zst()))
    }

    /// For a tagless, non-`#[repr(C)]` enum, the indices of its variants that are not absent
    /// (see the layout model); `None` for explicit-tag or `#[repr(C)]` enums (which always
    /// store a tag), structs, and unions.
    fn untagged_present_variants(&self) -> Option<Vec<usize>> {
        match &self.kind {
            AdtKind::Enum {
                tag_ty: None,
                variants,
            } if self.repr.kind != AdtReprKind::C => Some(
                variants
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| !Self::is_absent_variant(&v.fields))
                    .map(|(i, _)| i)
                    .collect(),
            ),
            _ => None,
        }
    }

    /// Returns `Some(v)` if `rustc` lays this enum out as a struct of its only present variant
    /// `v` without storing a tag (a tagless, non-`#[repr(C)]` enum whose other variants are all
    /// absent, e.g. a single-variant enum or `enum { A(!), B(u32) }`): every value of the enum
    /// is variant `v`, and its discriminant is a constant.
    pub fn univariant_index(&self) -> Option<usize> {
        match self.untagged_present_variants()?.as_slice() {
            [v] => Some(*v),
            _ => None,
        }
    }

    /// Returns true if this is an enum whose value stores a tag: an explicit `tag_ty`, a
    /// tagless `#[repr(C)]` enum (a C `int` tag, even for a single variant), or a tagless enum
    /// with more than one present variant (see the layout model). An enum value built
    /// field-by-field is only complete once `SetDiscriminant` has written the tag. Enums laid
    /// out without a tag ([`AdtDef::univariant_index`], or no present variant), structs, and
    /// unions store no tag.
    pub fn requires_tag_write(&self) -> bool {
        match &self.kind {
            AdtKind::Enum { tag_ty, variants } => {
                tag_ty.is_some()
                    || (self.repr.kind == AdtReprKind::C && !variants.is_empty())
                    || self
                        .untagged_present_variants()
                        .is_some_and(|present| present.len() > 1)
            }
            AdtKind::Struct { .. } | AdtKind::Union { .. } => false,
        }
    }

    /// Returns true if writing uninitialized bytes into a variant field leaves this ADT's tag
    /// intact: an explicit `tag_ty` or the C `int` tag of a tagless `#[repr(C)]` enum is stored
    /// apart from the variant fields, and an enum laid out without a tag (or a struct/union)
    /// has none. A tagless `repr(Rust)` enum with several present variants may encode its tag
    /// in a field's niche, so its tag is conservatively lost.
    pub fn tag_survives_field_deinit(&self) -> bool {
        match &self.kind {
            AdtKind::Enum { tag_ty, .. } => {
                tag_ty.is_some() || self.repr.kind == AdtReprKind::C || !self.requires_tag_write()
            }
            AdtKind::Struct { .. } | AdtKind::Union { .. } => true,
        }
    }

    /// The unique field of a struct that is not a 1-ZST, if it is a primitive scalar (the field
    /// a `scalar_valid_range` restricts).
    pub fn scalar_field(&self, ptr_width: PtrWidth) -> Option<(usize, &Ty)> {
        let AdtKind::Struct { fields } = &self.kind else {
            return None;
        };
        let mut found = None;
        for (i, field) in fields.iter().enumerate() {
            if field.layout_info(ptr_width).is_ok_and(|l| l.is_one_zst()) {
                continue;
            }
            if found.is_some() || !field.is_scalar() {
                return None;
            }
            found = Some((i, field));
        }
        found
    }

    /// Returns true if `bits` (the scalar field's bit pattern) is a valid bit pattern of the
    /// scalar field and satisfies `scalar_valid_range` (always true without a range or scalar
    /// field).
    pub fn scalar_range_contains(&self, bits: u128, ptr_width: PtrWidth) -> bool {
        let Some(range) = &self.scalar_valid_range else {
            return true;
        };
        match self.scalar_field(ptr_width) {
            Some((_, field)) => {
                field.is_valid_scalar_bits(bits, ptr_width)
                    && field
                        .scalar_bit_width(ptr_width)
                        .is_some_and(|w| range.contains(bits, w))
            }
            None => true,
        }
    }

    /// Returns true if this ADT is inhabited under `ptr_width`: structs need every field
    /// inhabited, enums some variant whose fields are all inhabited, and unions no fields or
    /// some inhabited field (`union { a: u32, b: ! }` is inhabited). A `scalar_valid_range`
    /// that excludes every valid bit pattern of the scalar field (e.g. `bool` with `2..=3`)
    /// makes the struct uninhabited.
    pub fn is_inhabited_for(&self, ptr_width: PtrWidth) -> bool {
        if let Some(range) = &self.scalar_valid_range
            && let Some((_, field)) = self.scalar_field(ptr_width)
        {
            let width = field.scalar_bit_width(ptr_width).unwrap_or(0);
            if !intervals_intersect(&field.scalar_valid_intervals(ptr_width), &range.intervals(width)) {
                return false;
            }
        }
        match &self.kind {
            AdtKind::Struct { fields } => fields.iter().all(|f| f.is_inhabited_for(ptr_width)),
            AdtKind::Union { fields } => {
                fields.is_empty() || fields.iter().any(|f| f.is_inhabited_for(ptr_width))
            }
            AdtKind::Enum { variants, .. } => variants
                .iter()
                .any(|v| v.fields.iter().all(|f| f.is_inhabited_for(ptr_width))),
        }
    }

    /// Checks that this definition is well-formed and representable under `ptr_width`
    /// (unspecified layouts are accepted; see [`Ty::check_representable`]).
    pub fn validate(&self, ptr_width: PtrWidth) -> Result<(), LayoutError> {
        self.layout_info(ptr_width).map(|_| ())
    }

    /// Computes this ADT's (possibly inexact) layout, validating the definition.
    fn layout_info(&self, ptr_width: PtrWidth) -> Result<LayoutInfo, LayoutError> {
        let repr_align = match self.repr.align {
            None => 1,
            Some(align) if align.is_power_of_two() && align <= MAX_REPR_ALIGN => align,
            Some(_) => {
                return Err(LayoutError::IllFormed(
                    "repr(align) must be a power of two no larger than 2^29",
                ));
            }
        };
        let transparent = self.repr.kind == AdtReprKind::Transparent;
        if transparent && self.repr.align.is_some() {
            return Err(LayoutError::IllFormed(
                "repr(transparent) cannot be combined with repr(align) (E0692)",
            ));
        }
        let info = match &self.kind {
            AdtKind::Struct { fields } => {
                struct_like_layout(fields, self.repr.kind, repr_align, ptr_width)?
            }
            AdtKind::Union { fields } => {
                if fields.is_empty() {
                    return Err(LayoutError::IllFormed("unions must have at least one field (E0784)"));
                }
                let mut info = LayoutInfo::exact(0, repr_align);
                let mut non_zst_fields = 0usize;
                for field in fields {
                    let field_info = field.layout_info(ptr_width)?;
                    if transparent {
                        if field_info.exact && field_info.size == 0 {
                            if field_info.align != 1 {
                                return Err(LayoutError::IllFormed(
                                    "repr(transparent) zero-sized fields must have alignment 1 (E0691)",
                                ));
                            }
                        } else {
                            non_zst_fields += 1;
                            if non_zst_fields > 1 {
                                return Err(LayoutError::IllFormed(
                                    "repr(transparent) allows at most one non-zero-sized field (E0690)",
                                ));
                            }
                        }
                    }
                    info.size = info.size.max(field_info.size);
                    info.align = info.align.max(field_info.align);
                    info.min_align = info.min_align.max(field_info.min_align);
                    info.exact &= field_info.exact;
                }
                info.size = info
                    .size
                    .checked_next_multiple_of(info.align)
                    .ok_or(LayoutError::TooLarge)?;
                info
            }
            AdtKind::Enum { tag_ty, variants } => {
                let discrs = self.discriminants(ptr_width)?;
                if transparent && (tag_ty.is_some() || variants.len() != 1) {
                    return Err(LayoutError::IllFormed(
                        "repr(transparent) enums need exactly one variant and no integer repr (E0731)",
                    ));
                }
                if variants.is_empty() {
                    if tag_ty.is_some()
                        || self.repr.kind == AdtReprKind::C
                        || self.repr.align.is_some()
                    {
                        return Err(LayoutError::IllFormed(
                            "unsupported representation for zero-variant enum (E0084)",
                        ));
                    }
                    LayoutInfo::exact(0, 1)
                } else if let Some(tag) = tag_ty {
                    tagged_layout(*tag, variants, self.repr.kind, repr_align, ptr_width)?
                } else {
                    for variant in variants {
                        for field in &variant.fields {
                            field.layout_info(ptr_width)?;
                        }
                    }
                    if transparent {
                        struct_like_layout(
                            &variants[0].fields,
                            self.repr.kind,
                            repr_align,
                            ptr_width,
                        )?
                    } else {
                        match self.untagged_present_variants().as_deref() {
                            // Only absent variants: laid out like `!` (`repr(align)` is ignored).
                            Some([]) => LayoutInfo::exact(0, 1),
                            Some([v]) => struct_like_layout(
                                &variants[*v].fields,
                                self.repr.kind,
                                repr_align,
                                ptr_width,
                            )?,
                            _ => {
                                // Unspecified layout: bound it by the tagged layout with the smallest tag that
                                // fits every discriminant (at least the 4-byte C `int` for `repr(C)`).
                                let (_, bit_width) = self.discr_int(ptr_width)?;
                                let min_tag_bytes =
                                    if self.repr.kind == AdtReprKind::C { 4 } else { 1 };
                                let tag = smallest_fit_tag(&discrs, bit_width, min_tag_bytes);
                                let mut upper = tagged_layout(
                                    tag,
                                    variants,
                                    self.repr.kind,
                                    repr_align,
                                    ptr_width,
                                )?;
                                let mut min_align = repr_align;
                                for field in self.all_fields() {
                                    min_align = min_align.max(field.layout_info(ptr_width)?.min_align);
                                }
                                upper.min_align = min_align;
                                upper.exact = false;
                                upper
                            }
                        }
                    }
                }
            }
        };
        if self.scalar_valid_range.is_some() && self.scalar_field(ptr_width).is_none() {
            return Err(LayoutError::IllFormed(
                "scalar_valid_range requires a struct whose only non-1-ZST field is a primitive scalar",
            ));
        }
        Ok(info)
    }

    /// Byte offset of field `field_idx` of variant `variant_idx` within this ADT.
    ///
    /// Union fields are always at offset `0`; `#[repr(C)]` struct fields at their
    /// declaration-order offsets (padding included); the non-1-ZST field of a
    /// `#[repr(transparent)]` struct at `0`; `#[repr(Rust)]` struct fields at their
    /// declaration-order offsets only when the fields' tuple is canonical
    /// ([`Ty::has_canonical_byte_layout`]); enum variant fields per the tagged layouts of
    /// [`AdtDef`] (or the struct rules for the present variant of an enum laid out without a
    /// tag, whose absent variants' fields sit at `0`). Every other case is
    /// [`LayoutError::Unspecified`]. Every `Ok(off)` satisfies
    /// `off + size_of(field) <= size_of(self)` and `off % align_of(field) == 0`.
    pub fn field_offset(
        &self,
        variant_idx: usize,
        field_idx: usize,
        ptr_width: PtrWidth,
    ) -> Result<usize, LayoutError> {
        let info = self.layout_info(ptr_width)?;
        let Some(fields) = self.variant_fields(variant_idx) else {
            return Err(LayoutError::IllFormed("variant index out of range"));
        };
        if field_idx >= fields.len() {
            return Err(LayoutError::IllFormed("field index out of range"));
        }
        if !info.exact {
            return Err(LayoutError::Unspecified);
        }
        match &self.kind {
            AdtKind::Union { .. } => Ok(0),
            AdtKind::Struct { fields } => {
                struct_like_field_offset(fields, field_idx, self.repr.kind, ptr_width)
            }
            AdtKind::Enum {
                tag_ty: None,
                variants,
            } => match self.univariant_index() {
                Some(v) if v == variant_idx => {
                    struct_like_field_offset(&variants[v].fields, field_idx, self.repr.kind, ptr_width)
                }
                // `rustc` places the (1-ZST) fields of absent variants at offset `0`.
                _ if self.repr.kind != AdtReprKind::C
                    && Self::is_absent_variant(&variants[variant_idx].fields) =>
                {
                    Ok(0)
                }
                _ => Err(LayoutError::Unspecified),
            },
            AdtKind::Enum {
                tag_ty: Some(tag),
                variants,
            } => {
                let tag_size = tag.size_bytes(ptr_width);
                if self.repr.kind == AdtReprKind::C {
                    let mut payload_align = 1usize;
                    for variant in variants {
                        let info =
                            struct_like_layout(&variant.fields, AdtReprKind::C, 1, ptr_width)?;
                        if !info.exact {
                            return Err(LayoutError::Unspecified);
                        }
                        payload_align = payload_align.max(info.align);
                    }
                    let payload_offset = tag_size
                        .checked_next_multiple_of(payload_align)
                        .ok_or(LayoutError::TooLarge)?;
                    let inner = struct_like_field_offset(fields, field_idx, AdtReprKind::C, ptr_width)?;
                    payload_offset.checked_add(inner).ok_or(LayoutError::TooLarge)
                } else {
                    let mut offset = tag_size;
                    for (i, field) in fields.iter().enumerate().take(field_idx + 1) {
                        let layout = field.layout_for(ptr_width)?;
                        offset = offset
                            .checked_next_multiple_of(layout.align)
                            .ok_or(LayoutError::TooLarge)?;
                        if i == field_idx {
                            return Ok(offset);
                        }
                        offset = offset.checked_add(layout.size).ok_or(LayoutError::TooLarge)?;
                    }
                    Err(LayoutError::IllFormed("field index out of range"))
                }
            }
        }
    }

    /// Returns true if this ADT exposes a niche under `ptr_width` (see [`Ty::contains_niche`]).
    fn contains_niche_for(&self, ptr_width: PtrWidth) -> bool {
        if let Some(range) = &self.scalar_valid_range
            && let Some((_, field)) = self.scalar_field(ptr_width)
        {
            let width = field.scalar_bit_width(ptr_width).unwrap_or(0);
            if !range.is_full(width) {
                return true;
            }
        }
        match &self.kind {
            AdtKind::Struct { fields } => fields.iter().any(|f| f.contains_niche_for(ptr_width)),
            AdtKind::Union { .. } => false,
            AdtKind::Enum { tag_ty, variants } => {
                if variants.is_empty() {
                    return false;
                }
                match tag_ty {
                    Some(tag) => {
                        let width = tag.bit_width(ptr_width);
                        let inhabited_variants = variants
                            .iter()
                            .filter(|v| v.fields.iter().all(|f| f.is_inhabited_for(ptr_width)))
                            .count();
                        let tag_has_niche = match self.discriminants(ptr_width) {
                            Ok(_) => {
                                width >= 128
                                    || (inhabited_variants as u128) <= width_mask(width)
                            }
                            Err(_) => true,
                        };
                        tag_has_niche
                            || variants
                                .iter()
                                .any(|v| v.fields.iter().any(|f| f.contains_niche_for(ptr_width)))
                    }
                    None => match self.untagged_present_variants().as_deref() {
                        Some([]) => false,
                        Some([v]) => variants[*v]
                            .fields
                            .iter()
                            .any(|f| f.contains_niche_for(ptr_width)),
                        // A stored tag (C `int` or `repr(Rust)` tag/niche) has invalid values.
                        _ => true,
                    },
                }
            }
        }
    }

    /// Returns true if this ADT has a *canonical byte layout* under `ptr_width` (an exact,
    /// well-formed layout whose byte image is the padding-free concatenation of its fields in
    /// declaration order, see [`Ty::has_canonical_byte_layout`]):
    /// - structs whose fields are all canonical and that are `#[repr(C)]` without any padding,
    ///   `#[repr(transparent)]`, or `#[repr(Rust)]` with a canonical field tuple and no
    ///   `repr(align)` padding;
    /// - unions with exactly one field that is canonical, niche-free (so every initialized
    ///   byte pattern is a valid union value), inhabited, and as large as the union;
    /// - enums without (present) variants (like `!`), enums laid out without a tag
    ///   ([`AdtDef::univariant_index`]) under the struct rules for their present variant,
    ///   and explicit-tag enums whose every variant's byte image is exactly the tag
    ///   followed by its canonical, pointer-free fields without any padding (so all variants
    ///   have the enum's full size).
    pub fn has_canonical_byte_layout(&self, ptr_width: PtrWidth) -> bool {
        let Ok(info) = self.layout_info(ptr_width) else {
            return false;
        };
        if !info.exact {
            return false;
        }
        match &self.kind {
            AdtKind::Struct { fields } => {
                struct_like_canonical(fields, self.repr.kind, info.size, ptr_width)
            }
            AdtKind::Union { fields } => {
                fields.len() == 1
                    && fields[0].has_canonical_byte_layout(ptr_width)
                    && !fields[0].contains_niche_for(ptr_width)
                    && fields[0].is_inhabited_for(ptr_width)
                    && fields[0]
                        .layout_for(ptr_width)
                        .is_ok_and(|l| l.size == info.size)
            }
            AdtKind::Enum { tag_ty, variants } => match tag_ty {
                _ if variants.is_empty() => true,
                None => match self.untagged_present_variants().as_deref() {
                    Some([]) => true,
                    Some([v]) => {
                        struct_like_canonical(&variants[*v].fields, self.repr.kind, info.size, ptr_width)
                    }
                    _ => false,
                },
                Some(tag) => {
                    let tag_size = tag.size_bytes(ptr_width);
                    variants.iter().enumerate().all(|(v, variant)| {
                        let mut end = tag_size;
                        variant.fields.iter().enumerate().all(|(i, field)| {
                            if !field.has_canonical_byte_layout(ptr_width) || field.contains_ptr() {
                                return false;
                            }
                            match (self.field_offset(v, i, ptr_width), field.layout_for(ptr_width)) {
                                (Ok(offset), Ok(layout)) if offset == end => {
                                    end += layout.size;
                                    true
                                }
                                _ => false,
                            }
                        }) && end == info.size
                    })
                }
            },
        }
    }
}

/// Canonical-layout check for a struct-like field list laid out with `kind` in `size` bytes.
fn struct_like_canonical(fields: &[Ty], kind: AdtReprKind, size: usize, ptr_width: PtrWidth) -> bool {
    if !fields.iter().all(|f| f.has_canonical_byte_layout(ptr_width)) {
        return false;
    }
    match kind {
        AdtReprKind::C => {
            let mut end = 0usize;
            for field in fields {
                let Ok(layout) = field.layout_for(ptr_width) else {
                    return false;
                };
                if !end.is_multiple_of(layout.align) {
                    return false;
                }
                end += layout.size;
            }
            end == size
        }
        AdtReprKind::Transparent => true,
        AdtReprKind::Rust => {
            let tuple = Ty::Tuple(fields.to_vec());
            tuple.has_canonical_byte_layout(ptr_width) && tuple.layout_size_for(ptr_width) == Some(size)
        }
    }
}

/// Local variable index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Local(pub usize);

/// Projection element inside a place expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProjectionElem {
    Deref,
    Field(usize, Ty),
    Index(Local),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(usize),
}

/// A place expression: base local and sequence of projections.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<ProjectionElem>,
}

impl Place {
    pub fn from_local(local: usize) -> Self {
        Place { local: Local(local), projection: Vec::new() }
    }

    pub fn with_projection(local: usize, projection: Vec<ProjectionElem>) -> Self {
        Place { local: Local(local), projection }
    }
}

/// Pointer provenance representation matching Anneal/MiniRust provenance model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Provenance {
    pub alloc_id: u64,
    pub tag: u64,
}

/// Machine pointer value: address (or offset) paired with optional provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PointerValue {
    pub addr: u64,
    pub provenance: Option<Provenance>,
}

impl PointerValue {
    pub fn without_provenance(addr: u64) -> Self {
        PointerValue { addr, provenance: None }
    }

    pub fn with_provenance(addr: u64, alloc_id: u64, tag: u64) -> Self {
        PointerValue {
            addr,
            provenance: Some(Provenance { alloc_id, tag }),
        }
    }
}

/// Constant value in MIR operands.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constant {
    Int(u128, Ty),
    Bool(bool),
    Char(char),
    Ptr(PointerValue, Ty),
    Unit,
}

impl Constant {
    /// Returns the MIR `Ty` of this constant.
    pub fn ty(&self) -> Ty {
        match self {
            Constant::Int(_, ty) => ty.clone(),
            Constant::Bool(_) => Ty::Bool,
            Constant::Char(_) => Ty::Char,
            Constant::Ptr(_, ty) => ty.clone(),
            Constant::Unit => Ty::unit(),
        }
    }
}

/// Operand in MIR expressions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

/// Cast flavor in `Rvalue::Cast`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastKind {
    /// Exposing pointer-to-address cast (`*const T as usize`, `*mut T as u64`).
    PointerExposeProvenance,
    /// Provenance-capturing address-to-pointer cast (`usize as *const T`).
    PointerWithExposedProvenance,
    /// Direct integer numeric conversion (`u8 as u32`, `i64 as i32`).
    IntToInt,
    /// Unicode scalar (`char`) to integer conversion (`'A' as u8`, `c as i32`).
    CharToInt,
    /// Raw pointer type change (`*const u8 as *const i32`).
    PtrToPtr,
    /// Bitwise reinterpretation (`core::mem::transmute`).
    Transmute,
    /// Subtyping coercion inserted by `rustc` (`CastKind::Subtype`). Anneal MIR types carry no
    /// lifetimes or variance, so the source and target types must be equal (recursively).
    Subtype,
    /// Built-in pointer coercion (`CastKind::PointerCoercion`).
    PointerCoercion(PointerCoercionKind),
}

/// Built-in pointer coercion flavor for `CastKind::PointerCoercion`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PointerCoercionKind {
    /// `*mut T -> *const T` (same pointee).
    MutToConstPointer,
    /// `*const [T; N] -> *const T` / `*mut [T; N] -> *mut T` (mutability preserved).
    ArrayToPointer,
}

/// Nullary operation flavor for `Rvalue::NullaryOp`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NullOp {
    /// `core::mem::size_of::<T>()` in bytes (`usize`).
    SizeOf,
    /// `core::mem::align_of::<T>()` in bytes (`usize`).
    AlignOf,
    /// `core::mem::offset_of!(T, fields)` in bytes (`usize`), where each step is
    /// `(variant_idx, field_idx)`.
    OffsetOf(Vec<(usize, usize)>),
    /// Runtime undefined-behavior check query (`#[cfg(ub_checks)]`, `bool`).
    UbChecks,
}

/// Binary operation flavor matching `rustc` MIR `BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
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

/// Unary operation flavor matching `rustc` MIR `UnOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Aggregate construction flavor for `Rvalue::Aggregate`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AggregateKind {
    /// Fixed-size array literal `[op_0, ..., op_n]` with element type.
    Array(Ty),
    /// Tuple literal `(op_0, ..., op_n)`.
    Tuple,
    /// Struct, enum variant, or union construction (`def_path`, `variant_idx`,
    /// optional active union field index).
    ///
    /// With `adt_def: Some(def)`, the aggregate is typed `Ty::Adt(def)` and its operands are
    /// checked against `def`'s variant (or union field) types; with `adt_def: None` (legacy
    /// captures), it is typed as the `Ty::Tuple` of its operand types.
    Adt {
        def_path: String,
        variant_idx: usize,
        active_field: Option<usize>,
        adt_def: Option<Arc<AdtDef>>,
    },
    /// Closure environment capture aggregate.
    Closure,
    /// Raw pointer construction from `(data_ptr_or_addr, unit_metadata)`.
    RawPtr {
        pointee: Ty,
        mutability: Mutability,
    },
}

/// Right-hand side rvalue expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rvalue {
    Use(Operand),
    Repeat(Operand, usize),
    Ref(Mutability, Place),
    RawPtr(Mutability, Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    NullaryOp(NullOp, Ty),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, Vec<Operand>),
    CopyForDeref(Place),
    /// `ShallowInitBox(ptr, T)`: reinterprets the raw pointer `ptr` (a fresh allocation) as an
    /// owning pointer to an uninitialized `T`. Anneal has no `Box` type, so the result is the
    /// same address and provenance typed `*mut T`.
    ShallowInitBox(Operand, Ty),
    /// `WrapUnsafeBinder(op, binder_ty)`: wraps `op` into `binder_ty`, which must equal the
    /// operand's type or be a single-field struct `Ty::Adt` around it.
    WrapUnsafeBinder(Operand, Ty),
}

/// Flavor of a `Statement::Retag` (`rustc`'s `RetagKind`, with the raw-pointer flavor carrying
/// the pointer's mutability).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RetagKind {
    /// Ordinary retag of references after an assignment.
    Default,
    /// Retag of function arguments on function entry.
    FnEntry,
    /// Two-phase borrow retag.
    TwoPhase,
    /// Retag of a raw pointer of the given mutability (`&raw const` / `&raw mut`).
    Raw(Mutability),
}

/// MIR statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, Rvalue),
    SetDiscriminant {
        place: Place,
        variant_index: usize,
    },
    PlaceMention(Place),
    Assume(Operand),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
    /// `Deinit(place)`: writes uninitialized bytes over `place` (MiniRust's byte-level `Uninit`
    /// write), deinitializing it while keeping disjoint sibling fields initialized.
    Deinit(Place),
    /// `Retag(kind, place)`: validates every reference reachable in `place`'s value (non-null,
    /// aligned, inhabited pointee); Anneal does not model aliasing tags.
    Retag(RetagKind, Place),
    /// `copy_nonoverlapping::<T>(src, dst, count)` (`NonDivergingIntrinsic::CopyNonOverlapping`).
    CopyNonOverlapping {
        src: Operand,
        dst: Operand,
        count: Operand,
    },
}

/// Targets of a `Terminator::SwitchInt`: `values[i]` jumps to `targets[i]` (first match), any
/// other value to `otherwise`. Values are bit patterns of the discriminant's type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SwitchTargets {
    pub values: Vec<u128>,
    pub targets: Vec<usize>,
    pub otherwise: usize,
}

impl SwitchTargets {
    /// Constructs switch targets from `(value, target)` branches and an `otherwise` target.
    pub fn new(branches: impl IntoIterator<Item = (u128, usize)>, otherwise: usize) -> Self {
        let (values, targets) = branches.into_iter().unzip();
        SwitchTargets {
            values,
            targets,
            otherwise,
        }
    }

    /// Two-way switch: `value` jumps to `then`, anything else to `otherwise`.
    pub fn static_if(value: u128, then: usize, otherwise: usize) -> Self {
        SwitchTargets::new([(value, then)], otherwise)
    }

    /// Target block for discriminant bits `value` (first matching value, else `otherwise`).
    pub fn target_for_value(&self, value: u128) -> usize {
        self.values
            .iter()
            .zip(&self.targets)
            .find_map(|(v, t)| (*v == value).then_some(*t))
            .unwrap_or(self.otherwise)
    }

    /// Every target block (branch targets, then `otherwise`).
    pub fn all_targets(&self) -> impl Iterator<Item = usize> + '_ {
        self.targets.iter().copied().chain(std::iter::once(self.otherwise))
    }
}

/// What happens when a terminator unwinds (panics).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnwindAction {
    /// Continue unwinding into the caller (the panic leaves the body).
    Continue,
    /// Unwinding is undefined behavior.
    Unreachable,
    /// Abort the program (`panic in a function that cannot unwind`).
    Terminate,
    /// Run the cleanup block with this index.
    Cleanup(usize),
}

/// Panic message of a failing `Terminator::Assert` (`rustc`'s `AssertKind`). Operands are
/// evaluated only when the assertion fails.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AssertMessage {
    /// Index out of bounds (`len` and `index` are `usize`).
    BoundsCheck { len: Operand, index: Operand },
    /// Arithmetic overflow of `lhs op rhs` (integers of one type; shifts may mix types).
    Overflow(BinOp, Operand, Operand),
    /// Overflow negating the minimum value of a signed integer.
    OverflowNeg(Operand),
    /// Integer division of the operand by zero.
    DivisionByZero(Operand),
    /// Integer remainder of the operand by zero.
    RemainderByZero(Operand),
    /// Misaligned pointer dereference (`required` and `found` are `usize`).
    MisalignedPointerDereference { required: Operand, found: Operand },
    /// Null pointer dereference.
    NullPointerDereference,
    /// Construction of an enum from an invalid integer discriminant.
    InvalidEnumConstruction(Operand),
    /// Free-form message.
    Custom(String),
}

/// Basic block terminator.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Terminator {
    /// Jump to `target`.
    Goto { target: usize },
    /// Jump on the bits of an integer, `bool`, or `char` discriminant.
    SwitchInt { discr: Operand, targets: SwitchTargets },
    /// Return `_0` to the caller.
    Return,
    /// Reaching this terminator is undefined behavior.
    Unreachable,
    /// Drop `place` (drop glue), then jump to `target`.
    Drop {
        place: Place,
        target: usize,
        unwind: UnwindAction,
    },
    /// Continue at `target` if `cond == expected`, else panic with `msg`.
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: usize,
        unwind: UnwindAction,
    },
    /// Call `func(args...)`, writing the result to `destination` and jumping to `target`
    /// (`None` for a call that must not return).
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: Option<usize>,
        unwind: UnwindAction,
    },
    /// Resume unwinding out of the body (only in cleanup blocks).
    UnwindResume,
    /// Abort while unwinding (only in cleanup blocks).
    UnwindTerminate,
}

/// Basic block consisting of statements and cleanup metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    /// Block terminator (`None` only for statement-level captures that are never executed as
    /// a control-flow graph).
    pub terminator: Option<Terminator>,
    pub is_cleanup: bool,
}

impl BasicBlockData {
    /// Constructs a block without a terminator.
    pub fn new(statements: Vec<Statement>, is_cleanup: bool) -> Self {
        BasicBlockData {
            statements,
            terminator: None,
            is_cleanup,
        }
    }

    /// Constructs a block ending in `terminator`.
    pub fn with_terminator(statements: Vec<Statement>, terminator: Terminator, is_cleanup: bool) -> Self {
        BasicBlockData {
            statements,
            terminator: Some(terminator),
            is_cleanup,
        }
    }
}

/// Captured MIR body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub local_decls: Vec<Ty>,
    pub basic_blocks: Vec<BasicBlockData>,
}
