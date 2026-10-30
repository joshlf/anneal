import Trusted.Sequence

namespace Trusted.Rustc.V2026_06_01.Layout

/-!
Target-specific type layout and calling-convention ABI metadata extracted from
`rustc_abi` at `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`R-TY-01`, `#99`
§5, `#101`).

Rust `repr(Rust)` types have an unspecified in-memory field order and padding
unless queried directly from `tcx.layout_of(...)`. Rather than re-computing
layouts in Lean, `anneal-rustc-capture` serializes the compiler's concrete
`LayoutData` and `FnAbi` tables into each `Mir/<Item>.lean` module as supplied
compiler facts.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L17-L24>

> "When we discuss \"ABI\" in the context of rustc, we are probably discussing calling conventions.
> To describe those `rustc_abi` also covers type layout, as it must for values passed on the stack.
> Despite `rustc_abi` being about calling conventions, it is good to remember these usages exist.
> You will encounter all of them and more if you study target-specific codegen enough!
> Even in general conversation, when someone says \"the Rust ABI is unstable\", it may allude to
> either or both of
> - `repr(Rust)` types have a mostly-unspecified layout
> - `extern \"Rust\" fn(A) -> R` has an unspecified calling convention"

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "All values have an alignment and size."
-/

/--
Size of a concrete monomorphized Rust type in bytes, modeling `rustc_abi::Size`.

Field `bytes` corresponds to `Size::bytes()` (the private `raw: u64` byte count
in `rustc_abi::Size`). Under the Rust Reference, a type's size is the byte
stride between successive array elements of that type, and is always a multiple
of the type's alignment.

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an array with that item type including alignment padding. The size of a value is always a multiple of its alignment."

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L794-L799>

> "/// Size of a type in bytes.
> #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
> #[cfg_attr(feature = \"nightly\", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
> pub struct Size {
>     raw: u64,
> }"

Modeling choice: `bytes` is stored as an arbitrary-precision `Nat` in
`Init.Core` rather than a bounded `u64`, avoiding machine-word wrapping in
layout arithmetic; `anneal-rustc-capture` populates `bytes` from
`Size::bytes()` on the target's `LayoutData`.
-/
structure Size : Type where
  /-- Number of bytes (`Size::bytes()`). -/
  bytes : Nat

/--
Alignment of a concrete monomorphized Rust type in bytes, modeling
`rustc_abi::Align`.

Field `bytes` corresponds to `Align::bytes()` (`1 << pow2` in
`rustc_abi::Align`). Under both the Rust Reference and `rustc_abi`, alignment in
bytes is at least `1` and always a power of two.

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the value at. A value of alignment n must only be stored at an address that is a multiple of n. So alignment 2 means that the value must be stored at an even address, while 1 means that it can be stored at any address. Alignment is measured in bytes, and must be at least 1, and always a power of 2."

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1019-L1024>

> "/// Alignment of a type in bytes (always a power of two).
> #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
> #[cfg_attr(feature = \"nightly\", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
> pub struct Align {
>     pow2: u8,
> }"

Modeling choice: Whereas `rustc` stores log-base-2 alignment (`pow2: u8`),
`Align` records the decoded byte count `bytes : Nat` directly and verifies the
power-of-two invariant via `Align.isPowerOfTwoBytes` in
`TypeLayout.isWellFormed`.
-/
structure Align : Type where
  /-- Alignment in bytes (`Align::bytes()`). -/
  bytes : Nat

/--
Fuel-bounded helper testing whether `n` is a positive power of two by repeated
division by `2`.

Because `Init.Core` does not include well-founded recursion lemmas, structural
recursion on `fuel` guarantees termination in the Lean kernel. When invoked with
`fuel = n`, `isPowerOfTwoAux n n` decreases `fuel` by `1` on each halving step
and decides whether `n = 2^k` for some `k : Nat`.
-/
def isPowerOfTwoAux : Nat → Nat → Bool
  | _, 0 => false
  | _, 1 => true
  | 0, _ => false
  | .succ fuel, n =>
    match Nat.beq (Nat.mod n 2) 0 with
    | true => isPowerOfTwoAux fuel (Nat.div n 2)
    | false => false

/--
Test whether `a.bytes` satisfies the Rust alignment invariant of being a
positive power of two (`a.bytes >= 1` and `a.bytes = 2^k`).

This check enforces the Rust Reference guarantee that every alignment in bytes
is at least `1` and a power of two (`rustc_abi::Align`).
-/
def Align.isPowerOfTwoBytes (a : Align) : Bool :=
  isPowerOfTwoAux a.bytes a.bytes

/--
Test whether `s.bytes` is an exact multiple of a non-zero alignment `a.bytes`.

This check enforces the Rust Reference guarantee that the size of any value is
always a multiple of its alignment (`s.bytes % a.bytes == 0` with
`a.bytes > 0`).
-/
def Size.isMultipleOfAlign (s : Size) (a : Align) : Bool :=
  Bool.and (Bool.not (Nat.beq a.bytes 0)) (Nat.beq (Nat.mod s.bytes a.bytes) 0)

/--
Inclusive wrap-around range of valid scalar bit patterns, modeling
`rustc_abi::WrappingRange`.

Fields `start` and `end_` correspond to `WrappingRange::start` and
`WrappingRange::end`. When `start <= end_`, the range permits bit patterns `v`
with `start <= v <= end_` (for example, `bool` has `0..=1` and `char` without
surrogates or niche types restrict their valid bit patterns). When
`start > end_`, the range wraps around the scalar modulus and permits
`v >= start` or `v <= end_`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1419-L1448>

> "/// Inclusive wrap-around range of valid values, that is, if
> /// start > end, it represents `start..=MAX`, followed by `0..=end`.
> #[derive(Clone, Copy, PartialEq, Eq, Hash)]
> #[cfg_attr(feature = \"nightly\", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
> pub struct WrappingRange {
>     pub start: u128,
>     pub end: u128,
> }"
>
> "/// Returns `true` if `v` is contained in the range.
> #[inline(always)]
> pub fn contains(&self, v: u128) -> bool {
>     if self.start <= self.end {
>         self.start <= v && v <= self.end
>     } else {
>         self.start <= v || v <= self.end
>     }
> }"

Modeling choice: Because `end` is a reserved keyword in Lean 4, the upper bound
field is named `end_`, and bounds are stored as `Nat` values representing the
unsigned 128-bit scalar bit pattern clipped to the scalar's size.
-/
structure WrappingRange : Type where
  /-- Start of the valid bit-pattern range (inclusive). -/
  start : Nat
  /-- End of the valid bit-pattern range (inclusive). -/
  end_ : Nat

/--
Fundamental machine representation of a scalar value, modeling
`rustc_abi::Primitive`.

Constructors `.int`, `.float`, and `.pointer` correspond 1-to-1 to
`Primitive::Int(Integer, bool)`, `Primitive::Float(Float)`, and
`Primitive::Pointer(AddressSpace)`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1379-L1393>

> "/// Fundamental unit of memory access and layout.
> #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
> #[cfg_attr(feature = \"nightly\", derive(StableHash))]
> pub enum Primitive {
>     /// The `bool` is the signedness of the `Integer` type.
>     ///
>     /// One would think we would not care about such details this low down,
>     /// wait until you hear about how sinusoidally Vibrant C ABIs are!
>     /// Literally: Everything Is Broken, Always Has Been.
>     Int(Integer, bool),
>     Float(Float),
>     Pointer(AddressSpace),
> }"

Modeling choice: `rustc_abi::Integer` (`I8`..`I128`) and `rustc_abi::Float`
(`F16`..`F128`) are flattened into their concrete bit widths `bits : Nat`, and
`AddressSpace` is represented by its raw index `addressSpace : Nat`.
-/
inductive PrimitiveKind : Type where
  /-- Integer of `bits` width (`8, 16, 32, 64, 128`) and signedness `signed`. -/
  | int (bits : Nat) (signed : Bool) : PrimitiveKind
  /-- IEEE-754 floating-point value of `bits` width (`16, 32, 64, 128`). -/
  | float (bits : Nat) : PrimitiveKind
  /-- Pointer or reference in address space `addressSpace`. -/
  | pointer (addressSpace : Nat) : PrimitiveKind

/--
Layout and initialization validity of a single machine scalar, modeling
`rustc_abi::Scalar`.

Constructor `.initialized` corresponds to `Scalar::Initialized { value,
valid_range }`, which requires the underlying bytes to be initialized and within
`validRange`. Constructor `.union` corresponds to `Scalar::Union { value }`,
which permits uninitialized bytes inside a union represented in a scalar
register.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1539-L1559>

> "/// Information about one scalar component of a Rust type.
> #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
> #[cfg_attr(feature = \"nightly\", derive(StableHash))]
> pub enum Scalar {
>     Initialized {
>         value: Primitive,
>
>         /// Inclusive wrap-around range of valid values, that is, if
>         /// start > end, it represents `start..=MAX`, followed by `0..=end`.
>         ///
>         /// That is, for an i8 primitive, a range of `254..=2` means following
>         /// sequence:
>         ///
>         ///    254 (-2), 255 (-1), 0, 1, 2
>         ///
>         /// This is intended specifically to mirror LLVM's `!range` metadata,
>         /// semantics.
>         valid_range: WrappingRange,
>     },
>     Union {
>         /// Even for unions, we need to use the correct registers for the kind of
>         /// values inside the union, so we keep the `Primitive` type around. We
>         ///also use it to compute the size of the scalar.
>         /// However, unions never have niches and even allow undef/uninit,
>         /// so there is no valid_range.
>         value: Primitive,
>     },
> }"

Modeling choice: This inductive matches `rustc_abi::Scalar` 1-to-1; scalar reads
in `Trusted.MirSemantics.Eval` enforce `validRange` on `.initialized` scalars
via `ScalarInt.inRange`.
-/
inductive ScalarLayout : Type where
  /-- Always-initialized scalar with primitive representation and valid
      range. -/
  | initialized (value : PrimitiveKind) (validRange : WrappingRange) : ScalarLayout
  /-- Union scalar field that may contain uninitialized bytes. -/
  | union (value : PrimitiveKind) : ScalarLayout

/--
Placement of interior fields within a type's memory layout, modeling
`rustc_abi::FieldsShape`.

Constructors `.primitive`, `.union`, `.array`, and `.arbitrary` correspond
1-to-1 to `FieldsShape::Primitive`, `FieldsShape::Union`, `FieldsShape::Array`,
and `FieldsShape::Arbitrary`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1643-L1679>

> "/// Describes how the fields of a type are located in memory.
> #[derive(PartialEq, Eq, Hash, Clone, Debug)]
> #[cfg_attr(feature = \"nightly\", derive(StableHash))]
> pub enum FieldsShape<FieldIdx: Idx> {
>     /// Scalar primitives and `!`, which never have fields.
>     Primitive,
>
>     /// All fields start at no offset. The `usize` is the field count.
>     Union(NonZeroUsize),
>
>     /// Array/vector-like placement, with all fields of identical types.
>     Array { stride: Size, count: u64 },
>
>     /// Struct-like placement, with precomputed offsets.
>     ///
>     /// Fields are guaranteed to not overlap, though note that gaps
>     /// before, between and after all the fields are NOT always
>     /// padding, and as such their contents may not be discarded.
>     /// For example, enum variants leave a gap at the front,
>     /// where the discriminant is kept in the enum's layout.
>     Arbitrary {
>         /// Offsets for the first byte of each field,
>         /// ordered to match the source definition order.
>         /// This vector always goes in increasing order of `FieldIdx`
>         /// (i.e. `0..fields.len()`), though note that the offsets
>         /// aren't guaranteed to increase monotonically with the index
>         /// (as `rustc` may reorder fields to reduce padding).
>         offsets: IndexVec<FieldIdx, Size>,
>
>         /// Maps the placement of fields in memory, from lowest
>         /// offset to highest offset, back to their `FieldIdx`
>         /// in the source definition.
>         ///
>         /// This can be used to iterate through the fields in the order
>         /// in which they appear in memory, for example to detect padding.
>         in_memory_order: IndexVec<u32, FieldIdx>,
>     },
> }"

Supplying compiler facts: Because `repr(Rust)` structs and enums may reorder
fields arbitrarily, `anneal-rustc-capture` serializes the compiler's exact
`offsets` and `in_memory_order` (`memoryIndex`) lists from `tcx.layout_of(...)`
so place projection (`ProjectionElem.field`) resolves the exact byte offset in
source-definition order (`#99` §5).
-/
inductive FieldsShape : Type where
  /-- Scalar or zero-sized primitive with no interior fields. -/
  | primitive : FieldsShape
  /-- Union where all `count` fields start at byte offset `0`. -/
  | union (count : Nat) : FieldsShape
  /-- Homogeneous array with `stride` bytes between each of the `count`
      elements. -/
  | array (stride : Size) (count : Nat) : FieldsShape
  /-- Arbitrary struct/tuple/enum-variant layout giving each source field's byte
      offset (`offsets`, indexed by source field index) and the memory-ordered
      field indices (`memoryIndex`). -/
  | arbitrary (offsets : List Size) (memoryIndex : List Nat) : FieldsShape

/--
Variant layout shape of a type, modeling `rustc_abi::Variants`.

Constructors `.empty`, `.single`, and `.multiple` correspond to
`Variants::Empty` (uninhabited types with no variants), `Variants::Single`
(structs, tuples, unions, scalars, and single-variant enums), and
`Variants::Multiple` (multi-variant enums with a discriminant tag).

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1937-L1959>

> "pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
>     /// A type with no valid variants. Must be uninhabited.
>     Empty,
>
>     /// Single enum variants, structs/tuples, unions, and all non-ADTs.
>     Single {
>         /// Always `0` for types that cannot have multiple variants.
>         index: VariantIdx,
>     },
>
>     /// Enum-likes with more than one variant: each variant comes with
>     /// a *discriminant* (usually the same as the variant index but the user can
>     /// assign explicit discriminant values). That discriminant gets encoded
>     /// as a *tag* on the machine. The layout of each variant is
>     /// a struct, and theseenum-likes also have a `fields` layout describing the
>     /// outer field(s) shared between all variants (namely, the tag).
>     Multiple {
>         tag: Scalar,
>         tag_encoding: TagEncoding<VariantIdx>,
>         tag_field: FieldIdx,
>         variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>>,
>     },
> }"

Modeling choice: In `.multiple`, each variant's interior field offsets are
stored as `variants : List FieldsShape` indexed by `VariantIdx`, while
`tagField` indexes into the outer `TypeLayout.fields` to locate the discriminant
tag (`tag : ScalarLayout`).
-/
inductive VariantsShape : Type where
  /-- Single uninhabited variant (`!` or empty enum). -/
  | empty : VariantsShape
  /-- Single inhabited variant with index `index` (structs, tuples, scalars, and
      single-variant enums). -/
  | single (index : Nat) : VariantsShape
  /-- Multi-variant enum layout with discriminant field `tagField` and
      per-variant field layouts (`variants`). -/
  | multiple (tag : ScalarLayout) (tagField : Nat) (variants : List FieldsShape) : VariantsShape

/--
Low-level backend value representation class, modeling `rustc_abi::BackendRepr`.

Constructors `.scalar`, `.scalarPair`, and `.memory` correspond to
`BackendRepr::Scalar`, `BackendRepr::ScalarPair`, and `BackendRepr::Memory`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1793-L1810>

> "pub enum BackendRepr {
>     Scalar(Scalar),
>     ScalarPair(Scalar, Scalar),
>     SimdScalableVector {
>         element: Scalar,
>         count: u64,
>         number_of_vectors: NumScalableVectors,
>     },
>     SimdVector {
>         element: Scalar,
>         count: u64,
>     },
>     Memory {
>         /// If true, the size is exact, otherwise it's only a lower bound.
>         sized: bool,
>     },
> }"

Modeling choice: Target-specific SIMD vector representations (`SimdVector`,
`SimdScalableVector`) and `Memory` aggregates are modeled via `.memory` for
byte-level storage in `Trusted.MirSemantics`, while `.scalar` and `.scalarPair`
carry their exact `ScalarLayout` validity metadata.
-/
inductive BackendRepr : Type where
  /-- Passed/stored as a single machine scalar. -/
  | scalar (s : ScalarLayout) : BackendRepr
  /-- Passed/stored as a pair of machine scalars (e.g., fat pointers, slices,
      or `(u64, u64)`). -/
  | scalarPair (first : ScalarLayout) (second : ScalarLayout) : BackendRepr
  /-- Passed/stored in memory (aggregate struct, array, or large enum). -/
  | memory : BackendRepr

/--
Complete compiler-computed layout for a concrete monomorphized type, modeling
`rustc_abi::LayoutData`.

Fields `size`, `align`, `backendRepr`, `fields`, `variants`, and `isUninhabited`
correspond to the eponymous fields of `rustc_abi::LayoutData` (`align` stores
 the ABI-required alignment `AbiAlign::abi`).

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L2102-L2135>

> "pub struct LayoutData<FieldIdx: Idx, VariantIdx: Idx> {
>     /// Says where the fields are located within the layout.
>     pub fields: FieldsShape<FieldIdx>,
>
>     /// Encodes information about multi-variant layouts.
>     /// Even with `Multiple` variants, a layout still has its own fields! Those are then
>     /// shared between all variants. One of them will be the discriminant,
>     /// but e.g. generators can have more.
>     ///
>     /// To access all fields of this layout, both `fields` and the fields of the active variant
>     /// must be taken into account.
>     pub variants: Variants<FieldIdx, VariantIdx>,
>
>     /// The `backend_repr` specifies how the type is passed to the codegen backend,
>     /// and encodes value restrictions via `valid_range`.
>     ///
>     /// Note that this is entirely orthogonal to the recursive structure of the
>     /// layout as defined by `variants` and `fields`; for example, `ManuallyDrop<Result<isize, isize>>`
>     /// has `BackendRepr::ScalarPair`! So, even with non-`Memory` `backend_repr`,
>     /// you have to take `fields` and `variants` into account to find all the
>     /// fields of this layout.
>     pub backend_repr: BackendRepr,
>
>     pub largest_niche: Option<Niche>,
>     pub uninhabited: bool,
>     pub align: AbiAlign,
>     pub size: Size,
>
>     /// The largest alignment explicitly requested with `repr(align)` on this type or any field.
>     /// This only gets used when combining the layout of multiple fields into the layout of the whole ADT;
>     /// outside of layout computation nothing should ever look at this.
>     pub max_repr_align: Option<Align>,
>
>     /// The alignment the type would have had, without `repr(packed)`.
>     /// This isonly used by the `unaligned_references` lint, and outside of layout
>     /// computation nothing else should ever look at this.
>     pub unadjusted_abi_align: Align,
>
>     /// Randomization seed used for layout randomization.
>     /// This guarantees that two types with different randomization seeds get
>     /// different stacks slots if they conflict, etc.
>     pub randomization_seed: Hash64,
> }"

Supplying compiler facts: `anneal-rustc-capture` extracts `TypeLayout` directly
from `tcx.layout_of(typing_env.as_query_input(ty))` and records it in
`LayoutTable.entries` together with `fieldLayouts` (per-field `LayoutIdx`
entries computed via `TyAndLayout::field` in `compiler/rustc_middle/src/ty/layout.rs`);
`TypeLayout.isWellFormed` checks the fundamental size and alignment invariants
from the Rust Reference.

Reference (`compiler/rustc_middle/src/ty/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L706-L712>

> "pub trait LayoutOf<'tcx>: LayoutOfHelpers<'tcx> {
>     /// Computes the layout of a type. Note that this implicitly
>     /// executes in `TypingMode::PostAnalysis`, and will normalize the input type.
>     #[inline]
>     fn layout_of(&self, ty: Ty<'tcx>) -> Self::LayoutOfResult {
>         self.spanned_layout_of(ty, DUMMY_SP)
>     }
> }"
-/
structure TypeLayout : Type where
  /-- Total size in bytes (always a multiple of `align.bytes`). -/
  size : Size
  /-- ABI alignment in bytes. -/
  align : Align
  /-- Backend representation class. -/
  backendRepr : BackendRepr
  /-- Field offset descriptor. -/
  fields : FieldsShape
  /-- Variant descriptor. -/
  variants : VariantsShape
  /-- True if the type is uninhabited (`LayoutData::is_uninhabited()`). -/
  isUninhabited : Bool
  /-- Optional per-field `LayoutTable.entries` indices in source field order for
      single-variant `FieldsShape.arbitrary` aggregates, enabling byte-level
      `decodeValueFromBytes` checks to enforce per-field `ScalarLayout`
      bit-validity ranges across multi-field structs. -/
  fieldLayouts : List Nat := .nil

/--
Check structural well-formedness of a `TypeLayout` entry: `l.align` must be a
positive power of two in bytes and `l.size` must be an exact multiple of
`l.align`.

These two invariants correspond directly to the Rust Reference "Size and
Alignment" guarantees.
-/
def TypeLayout.isWellFormed (l : TypeLayout) : Bool :=
  Bool.and (Align.isPowerOfTwoBytes l.align) (Size.isMultipleOfAlign l.size l.align)

/--
Calling-convention argument and return passing mode, modeling
`rustc_target::callconv::PassMode` (re-exported via `rustc_abi`).

Constructors `.ignore`, `.direct`, `.pair`, and `.indirect` correspond to
zero-sized ignored arguments (`PassMode::Ignore`), single-register/direct values
(`PassMode::Direct` / `PassMode::Cast`), two-register scalar pairs
(`PassMode::Pair`), and memory-passed arguments (`PassMode::Indirect`).

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L28-L35>

> "Instead, `rustc_abi` is intended to provide the interface for reasoning about the binary interface.
> It should contain traits and types that other crates then use in their implementation.
> For example, a platform's `extern \"C\" fn` calling convention will be implemented in `rustc_target`
> but `rustc_abi` contains the types for calculating layout and describing register-passing."

Modeling choice: Target-specific register cast attributes (`PassMode::Cast` and
`PassAttributes`) are abstracted into `.direct`, `.pair`, `.indirect`, and
`.ignore`, since MIR-level call evaluation transfers values according to their
`TypeLayout` and ABI pass category.
-/
inductive AbiPassMode : Type where
  /-- Zero-sized value ignored in the machine ABI. -/
  | ignore : AbiPassMode
  /-- Passed directly in register(s). -/
  | direct : AbiPassMode
  /-- Passed as a pair of registers. -/
  | pair : AbiPassMode
  /-- Passed indirectly by pointer in memory. -/
  | indirect : AbiPassMode

/--
Calling-convention descriptor for a single function parameter or return value,
modeling `rustc_target::callconv::ArgAbi`.

Field `layout` records the parameter's `TypeLayout` and `mode` records its
`AbiPassMode`.

Reference (The Rust Reference, "Functions"):
<https://doc.rust-lang.org/1.98.0/reference/items/functions.html#functions>

> "Functions may declare a set of input variables as parameters, through which the caller passes arguments into the function, and the output type of the value the function will return to its caller on completion."
-/
structure ArgAbi : Type where
  /-- In-memory layout of the argument or return type. -/
  layout : TypeLayout
  /-- Calling-convention passing mode. -/
  mode : AbiPassMode

/--
Calling-convention ABI string of a function or function pointer, modeling
`rustc_abi::ExternAbi`.

Constructors `.rust`, `.c`, `.rustIntrinsic`, and `.other` correspond to
`extern "Rust"`, `extern "C"`, `extern "rust-intrinsic"`, and any other target
ABI string recognized by `rustc`.

Reference (The Rust Reference, "External blocks - ABI"):
<https://doc.rust-lang.org/1.98.0/reference/items/external-blocks.html#abi>

> "By default external blocks assume that the library they are calling uses the standard C ABI on the specific platform. Other ABIs may be specified using an abi string, as shown here:"
-/
inductive CallConv : Type where
  /-- Standard Rust ABI (`extern "Rust"`). -/
  | rust : CallConv
  /-- C ABI (`extern "C"`). -/
  | c : CallConv
  /-- Rust intrinsic ABI (`extern "rust-intrinsic"`). -/
  | rustIntrinsic : CallConv
  /-- Other target or platform ABI named `name`. -/
  | other (name : String) : CallConv

/--
Complete calling-convention signature of a function, modeling
`rustc_target::callconv::FnAbi`.

Fields `args`, `ret`, `conv`, and `canUnwind` correspond to `FnAbi::args`,
`FnAbi::ret`, `FnAbi::conv`, and `FnAbi::can_unwind` computed by
`tcx.fn_abi_of_instance(...)`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L17-L20>

> "When we discuss \"ABI\" in the context of rustc, we are probably discussing calling conventions.
> To describe those `rustc_abi` also covers type layout, as it must for values passed on the stack."
-/
structure FnAbi : Type where
  /-- Argument ABIs in parameter order. -/
  args : List ArgAbi
  /-- Return value ABI. -/
  ret : ArgAbi
  /-- Calling convention. -/
  conv : CallConv
  /-- Whether unwinding across a call with this ABI is permitted. -/
  canUnwind : Bool

/--
Target data-layout parameters and indexed table of concrete `TypeLayout` entries
for a captured compilation unit, modeling `rustc_abi::TargetDataLayout` and the
per-body layout table (`R-TY-01`).

Field `pointerBits` corresponds to `TargetDataLayout::pointer_size().bits()`,
`isLittleEndian` corresponds to `TargetDataLayout::endian == Endian::Little`,
and `entries` stores the `TypeLayout` values indexed by `LayoutIdx`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L259-L264>

> "/// Endianness of the target, which must match cfg(target-endian).
> #[derive(Copy, Clone, PartialEq, Eq)]
> pub enum Endian {
>     Little,
>     Big,
> }"
-/
structure LayoutTable : Type where
  /-- Target pointer width in bits (e.g., `64` on `x86_64` Linux). -/
  pointerBits : Nat
  /-- True if the target is little-endian. -/
  isLittleEndian : Bool
  /-- Indexed list of `TypeLayout` entries (`LayoutIdx`). -/
  entries : List TypeLayout

/--
Look up the `TypeLayout` at 0-based index `idx` in `tbl.entries`, returning
`.none` if `idx` is out of bounds.
-/
def LayoutTable.lookup (tbl : LayoutTable) (idx : Nat) : Option TypeLayout :=
  Trusted.Sequence.get? tbl.entries idx

end Trusted.Rustc.V2026_06_01.Layout
