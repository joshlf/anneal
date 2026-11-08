//! Core MIR abstract syntax types for `anneal-mir`.

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
}

impl Ty {
    /// Constructs the unit type `()`.
    pub fn unit() -> Self {
        Ty::Tuple(Vec::new())
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
    pub fn contains_ptr(&self) -> bool {
        match self {
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => true,
            Ty::Array(elem, count) => *count > 0 && elem.contains_ptr(),
            Ty::Tuple(fields) => fields.iter().any(Ty::contains_ptr),
            Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) | Ty::Never => false,
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
            Ty::Array(_, _) | Ty::Tuple(_) | Ty::Never => None,
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
            Ty::Array(_, _) | Ty::Tuple(_) | Ty::Never => 0,
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
    pub fn is_inhabited(&self) -> bool {
        match self {
            Ty::Never => false,
            Ty::Tuple(fields) => fields.iter().all(Ty::is_inhabited),
            Ty::Array(elem, count) => *count == 0 || elem.is_inhabited(),
            Ty::Bool
            | Ty::Char
            | Ty::Int(_)
            | Ty::Uint(_)
            | Ty::RawPtr(_, _)
            | Ty::Ref(_, _) => true,
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
    /// (`1` for `()`); `!` has alignment `1`.
    pub fn align_for(&self, ptr_width: PtrWidth) -> usize {
        match self {
            Ty::Bool | Ty::Never => 1,
            Ty::Char => 4,
            Ty::Int(it) => it.byte_size_for(ptr_width),
            Ty::Uint(ut) => ut.byte_size_for(ptr_width),
            Ty::RawPtr(_, _) | Ty::Ref(_, _) => ptr_width.byte_size(),
            Ty::Array(elem, _) => elem.align_for(ptr_width),
            Ty::Tuple(fields) => fields.iter().map(|f| f.align_for(ptr_width)).max().unwrap_or(1),
        }
    }

    /// Size in bytes for the given target pointer width (saturating on overflow).
    ///
    /// Matches `rustc`'s `repr(Rust)` layout under the natural-alignment model of
    /// [`Ty::align_for`]: arrays are `count * size_of(elem)`, and tuples are the sum of their
    /// field sizes rounded up to the tuple's alignment, which is the minimal size `rustc`'s
    /// field reordering always achieves (e.g. `(u8, u32)` and `(u8, u32, u8)` are both `8`
    /// bytes, `(u16, u8)` is `4`, `(u64, u32)` is `16`). Uninhabited types still have a
    /// layout size (`!` is `0`, `(!, u32)` is `4`).
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
        }
    }

    /// Size in bytes of this type's layout under `ptr_width`, or `None` if the type is not
    /// representable on that target: an array length exceeding the target's `usize::MAX`,
    /// or a total size exceeding the target's `isize::MAX` ([`PtrWidth::max_object_size`]).
    ///
    /// Unlike [`Ty::checked_byte_size`], uninhabited types still report their layout size
    /// (`!` is `Some(0)`, `(!, u32)` is `Some(4)`), because pointer arithmetic and transmute
    /// size checks operate on layout sizes.
    pub fn layout_size_for(&self, ptr_width: PtrWidth) -> Option<usize> {
        let size = match self {
            Ty::Bool
            | Ty::Char
            | Ty::Int(_)
            | Ty::Uint(_)
            | Ty::RawPtr(_, _)
            | Ty::Ref(_, _)
            | Ty::Never => self.byte_size_for(ptr_width),
            Ty::Array(elem, count) => {
                if (*count as u128) > ptr_width.max_usize() {
                    return None;
                }
                elem.layout_size_for(ptr_width)?.checked_mul(*count)?
            }
            Ty::Tuple(fields) => {
                let mut unpadded = 0usize;
                for field in fields {
                    unpadded = unpadded.checked_add(field.layout_size_for(ptr_width)?)?;
                }
                unpadded.checked_next_multiple_of(self.align_for(ptr_width))?
            }
        };
        if (size as u128) > ptr_width.max_object_size() {
            return None;
        }
        Some(size)
    }

    /// Computes the byte size of an inhabited type under `ptr_width`, returning `None`
    /// if the type is uninhabited (e.g., `!`, `(!, u32)`, `[!; 1]`) or if its layout is not
    /// representable on the target (see [`Ty::layout_size_for`]).
    ///
    /// Note that `[!; 0]` is inhabited and returns `Some(0)`.
    pub fn checked_byte_size(&self, ptr_width: PtrWidth) -> Option<usize> {
        if !self.is_inhabited() {
            return None;
        }
        self.layout_size_for(ptr_width)
    }

    /// Returns true if this type contains a niche-bearing scalar (`bool`, `char`, or `&T`),
    /// whose placement `rustc` may optimize when laying out tuples.
    fn contains_niche(&self) -> bool {
        match self {
            Ty::Bool | Ty::Char | Ty::Ref(_, _) => true,
            Ty::Array(elem, count) => *count > 0 && elem.contains_niche(),
            Ty::Tuple(fields) => fields.iter().any(Ty::contains_niche),
            Ty::Int(_) | Ty::Uint(_) | Ty::RawPtr(_, _) | Ty::Never => false,
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
    ///   (c) no field contains a niche-bearing scalar (`bool`, `char`, `&T`), the fields'
    ///   alignment-group keys `log2(max(align, size))` are non-increasing in declaration order,
    ///   and the unpadded size is a multiple of the tuple's alignment (no padding at all).
    ///
    /// These conditions are conservative: declaration order is then already size-optimal and
    /// sorted by alignment group, so `rustc`'s field-reordering heuristics (which may otherwise
    /// move fields, or place niches, differently across compiler versions) keep it. Byte-level
    /// (`CastKind::Transmute`) reinterpretation is only defined for canonical layouts: e.g.
    /// `(u16, u16)`, `(u32, u16, u16)`, and `(*const u8, u64)` are canonical, whereas
    /// `(u8, u32)` (padding), `(u32, u64)` (fields not sorted by alignment), and `(u8, bool)`
    /// (niche placement is compiler-dependent) are not.
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
                if fields.iter().any(Ty::contains_niche) {
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
                    let f_align = f.align_for(ptr_width);
                    if offset % f_align != 0 {
                        return false;
                    }
                    offset = offset.saturating_add(f.byte_size_for(ptr_width));
                }
                offset % self.align_for(ptr_width) == 0
            }
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
    /// Raw pointer type change (`*const u8 as *const i32`).
    PtrToPtr,
    /// Bitwise reinterpretation (`core::mem::transmute`).
    Transmute,
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
    Adt {
        def_path: String,
        variant_idx: usize,
        active_field: Option<usize>,
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
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, Vec<Operand>),
    CopyForDeref(Place),
}

/// MIR statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

/// Basic block consisting of statements and cleanup metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub is_cleanup: bool,
}

/// Captured MIR body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub local_decls: Vec<Ty>,
    pub basic_blocks: Vec<BasicBlockData>,
}
