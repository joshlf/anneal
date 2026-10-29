import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR binary, unary, and nullary
operators, borrow kinds, cast kinds, aggregate kinds, and rvalue expressions for
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#99`, `#101`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1709>

> "pub enum Rvalue<'tcx> {
>     /// Yields the operand unchanged
>     Use(Operand<'tcx>),
> ...
>     /// Wrap a value in an unsafe binder, i.e. `T -> unsafe<'a> T`.
>     WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>),
> }"
-/

/--
Binary arithmetic, bitwise, comparison, and pointer-offset operators, modeling
`rustc_middle::mir::BinOp`.

Each constructor of `BinOp` corresponds 1-to-1 to the variant of
`rustc_middle::mir::BinOp` with the same name:
- `.add`, `.sub`, `.mul`: wrapping two's-complement integer or IEEE-754 float
  arithmetic (`Add`, `Sub`, `Mul`).
- `.addUnchecked`, `.subUnchecked`, `.mulUnchecked`: unchecked integer
  arithmetic where signed or unsigned overflow is immediate undefined behavior
  (`AddUnchecked`, `SubUnchecked`, `MulUnchecked`).
- `.addWithOverflow`, `.subWithOverflow`, `.mulWithOverflow`: checked integer
  arithmetic returning `(T, bool)` (`AddWithOverflow`, `SubWithOverflow`,
  `MulWithOverflow`).
- `.div`, `.rem`: division and remainder (`Div`, `Rem`), where division by zero
  or signed `MIN / -1` is undefined behavior on integers in MIR.
- `.bitXor`, `.bitAnd`, `.bitOr`: bitwise logical operators (`BitXor`, `BitAnd`,
  `BitOr`).
- `.shl`, `.shr`: bit shifts masking the shift distance to `bit_width - 1`
  (`Shl`, `Shr`).
- `.shlUnchecked`, `.shrUnchecked`: unchecked bit shifts where a shift distance
  `< 0` or `>= bit_width` is immediate undefined behavior (`ShlUnchecked`,
  `ShrUnchecked`).
- `.eq`, `.lt`, `.le`, `.ne`, `.ge`, `.gt`: boolean relational comparisons
  (`Eq`, `Lt`, `Le`, `Ne`, `Ge`, `Gt`).
- `.cmp`: three-way integer comparison returning `core::cmp::Ordering` (`Cmp`).
- `.offset`: in-bounds pointer arithmetic (`Offset`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709>

> "pub enum BinOp {
>     /// The `+` operator (addition)
>     Add,
>     /// Like `Add`, but with UB on overflow. (Integers only.)
>     AddUnchecked,
>     /// The `+` operator (addition) with overflow check.
>     AddWithOverflow,
>     /// The `-` operator (subtraction)
>     Sub,
>     /// Like `Sub`, but with UB on overflow. (Integers only.)
>     SubUnchecked,
>     /// The `-` operator (subtraction) with overflow check.
>     SubWithOverflow,
>     /// The `*` operator (multiplication)
>     Mul,
>     /// Like `Mul`, but with UB on overflow. (Integers only.)
>     MulUnchecked,
>     /// The `*` operator (multiplication) with overflow check.
>     MulWithOverflow,
>     /// The `/` operator (division)
>     ///
>     /// For integer types, division by zero is UB, as is `MIN / -1` for signed.
>     /// The compiler must insert checks prior to this if it wants to prevent UB.
>     Div,
>     /// The `%` operator (modulus)
>     ///
>     /// For integer types, using zero as the modulus (second operand) is UB, as is `MIN % -1` for
>     /// signed. The compiler must insert checks prior to this if it wants to prevent UB.
>     Rem,
>     /// The `^` operator (bitwise xor)
>     BitXor,
>     /// The `&` operator (bitwise and)
>     BitAnd,
>     /// The `|` operator (bitwise or)
>     BitOr,
>     /// The `<<` operator (shift left)
>     ///
>     /// The offset is truncated to the size of the first operand before shifting,
>     /// and the offset may have any integer type (signed or unsigned).
>     Shl,
>     /// Like `Shl`, but Is UB if the RHS >= LHS::BITS or RHS < 0
>     ShlUnchecked,
>     /// The `>>` operator (shift right)
>     ///
>     /// The offset is truncated to the size of the first operand before shifting,
>     /// and the offset may have any integer type (signed or unsigned).
>     ///
>     /// This is an arithmetic shift if the LHS is signed
>     /// and a logical shift if the LHS is unsigned.
>     Shr,
>     /// Like `Shr`, but is UB if the RHS >= LHS::BITS or RHS < 0
>     ShrUnchecked,
>     /// The `==` operator (equality)
>     Eq,
>     /// The `<` operator (less than)
>     Lt,
>     /// The `<=` operator (less than or equal to)
>     Le,
>     /// The `!=` operator (not equal to)
>     Ne,
>     /// The `>=` operator (greater than or equal to)
>     Ge,
>     /// The `>` operator (greater than)
>     Gt,
>     /// The `<=>` operator (three-way comparison, like `Ord::cmp`)
>     ///
>     /// Probably only supported on integers types (`char`, `u*`, `i*`).
>     Cmp,
>     /// The `pointer.offset` operator
>     Offset,
> }"
-/
inductive BinOp : Type where
  /-- Wrapping two's-complement addition (`Add`). -/
  | add : BinOp
  /-- Addition where signed or unsigned overflow is immediate UB
      (`AddUnchecked`). -/
  | addUnchecked : BinOp
  /-- Checked addition returning `(T, bool)` (`AddWithOverflow`). -/
  | addWithOverflow : BinOp
  /-- Wrapping two's-complement subtraction (`Sub`). -/
  | sub : BinOp
  /-- Subtraction where overflow is immediate UB (`SubUnchecked`). -/
  | subUnchecked : BinOp
  /-- Checked subtraction returning `(T, bool)` (`SubWithOverflow`). -/
  | subWithOverflow : BinOp
  /-- Wrapping multiplication (`Mul`). -/
  | mul : BinOp
  /-- Multiplication where overflow is immediate UB (`MulUnchecked`). -/
  | mulUnchecked : BinOp
  /-- Checked multiplication returning `(T, bool)` (`MulWithOverflow`). -/
  | mulWithOverflow : BinOp
  /-- Integer or float division (`Div`). -/
  | div : BinOp
  /-- Integer or float remainder (`Rem`). -/
  | rem : BinOp
  /-- Bitwise XOR (`BitXor`). -/
  | bitXor : BinOp
  /-- Bitwise AND (`BitAnd`). -/
  | bitAnd : BinOp
  /-- Bitwise OR (`BitOr`). -/
  | bitOr : BinOp
  /-- Left shift (`Shl`). -/
  | shl : BinOp
  /-- Left shift where shift distance `>= bit_width` is immediate UB
      (`ShlUnchecked`). -/
  | shlUnchecked : BinOp
  /-- Right shift (`Shr`). -/
  | shr : BinOp
  /-- Right shift where shift distance `>= bit_width` is immediate UB
      (`ShrUnchecked`). -/
  | shrUnchecked : BinOp
  /-- Equality comparison (`Eq`). -/
  | eq : BinOp
  /-- Less-than comparison (`Lt`). -/
  | lt : BinOp
  /-- Less-than-or-equal comparison (`Le`). -/
  | le : BinOp
  /-- Inequality comparison (`Ne`). -/
  | ne : BinOp
  /-- Greater-than-or-equal comparison (`Ge`). -/
  | ge : BinOp
  /-- Greater-than comparison (`Gt`). -/
  | gt : BinOp
  /-- Three-way comparison returning `Ordering` (`Cmp`). -/
  | cmp : BinOp
  /-- In-bounds pointer offset (`Offset`). -/
  | offset : BinOp

/--
Unary MIR operators, modeling `rustc_middle::mir::UnOp`.

Constructors `.not`, `.neg`, and `.ptrMetadata` correspond 1-to-1 to
`UnOp::Not`, `UnOp::Neg`, and `UnOp::PtrMetadata`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617>

> "pub enum UnOp {
>     /// The `!` operator for logical inversion
>     Not,
>     /// The `-` operator for negation
>     Neg,
>     /// Gets the metadata of a pointer (the length of a slice, or the vtable of a trait object, or
>     /// `()` for a thin pointer).
>     PtrMetadata,
> }"
-/
inductive UnOp : Type where
  /-- Bitwise or logical negation (`Not`). -/
  | not : UnOp
  /-- Arithmetic negation (`Neg`). -/
  | neg : UnOp
  /-- Metadata extraction from a wide pointer or reference (`PtrMetadata`). -/
  | ptrMetadata : UnOp

/--
Nullary type-query and runtime-check operators, modeling
`rustc_middle::mir::RuntimeChecks` (`Rvalue::NullaryOp`) and layout queries
(`size_of`, `align_of`, `offset_of!`).

Constructors `.ubChecks` and `.contractChecks` correspond to
`RuntimeChecks::UbChecks` and `RuntimeChecks::ContractChecks` in
`Rvalue::NullaryOp`, while `.sizeOf`, `.alignOf`, and `.offsetOf` model compile-
or runtime-evaluated layout queries parameterized by a concrete `Ty`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1579-L1589>

> "pub enum RuntimeChecks {
>     /// Returns whether `#[cfg(ub_checks)]` is enabled.
>     UbChecks,
>     /// Returns whether `#[cfg(contract_checks)]` is enabled.
>     ContractChecks,
>     /// Returns whether `#[cfg(overflow_checks)]` is enabled.
>     OverflowChecks,
> }"

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an array with that item type including alignment padding. The size of a value is always a multiple of its alignment."
-/
inductive NullOp : Type where
  /-- `core::mem::size_of::<T>()` (`NullOp::SizeOf`). -/
  | sizeOf : NullOp
  /-- `core::mem::align_of::<T>()` (`NullOp::AlignOf`). -/
  | alignOf : NullOp
  /-- `core::mem::offset_of!(T, fields)` (`NullOp::OffsetOf`). -/
  | offsetOf (fields : List (VariantIdx × FieldIdx)) : NullOp
  /-- `ub_checks` runtime flag query (`NullOp::UbChecks`). -/
  | ubChecks : NullOp
  /-- `contract_checks` runtime flag query (`NullOp::ContractChecks`). -/
  | contractChecks : NullOp

/--
Borrow flavor for `Rvalue::Ref`, modeling `rustc_middle::mir::BorrowKind` in
`Runtime(PostCleanup)` MIR.

Constructor `.shared` corresponds to `BorrowKind::Shared` and `.mut` corresponds
to `BorrowKind::Mut { kind }` (carrying `allowTwoPhaseBorrow` when `kind` is
`MutBorrowKind::TwoPhaseBorrow`). Note that `BorrowKind::Fake` is disallowed in
`Runtime` MIR and eliminated prior to `Runtime(PostCleanup)`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L149-L176>

> "pub enum BorrowKind {
>     /// Data must be immutable and is aliasable.
>     Shared,
>
>     /// The immediately borrowed place must be immutable, but projections from
>     /// it don't need to be. For example, a shallow borrow of `a.b` doesn't
>     /// conflict with a mutable borrow of `a.b.c`.
>     ///
>     /// This is used when lowering matches: when matching on a place we want to
>     /// ensure that place have the same value from the start of the match until
>     /// an arm is selected. This prevents this code from compiling:
>     ...
>     /// This can't be a shared borrow because mutably borrowing `(*x).1` should
>     /// not prevent `if let None = x`, for example, because the mutating `(*x).1`
>     /// can't affect the discriminant of `x`.
>     /// Disallowed in runtime MIR.
>     Fake(FakeBorrowKind),
>
>     /// Data is mutable and not aliasable.
>     Mut { kind: MutBorrowKind },
> }"
-/
inductive BorrowKind : Type where
  /-- Shared reference (`&place`). -/
  | shared : BorrowKind
  /-- Mutable reference (`&mut place`, with `allowTwoPhaseBorrow`). -/
  | mut (allowTwoPhaseBorrow : Bool) : BorrowKind

/--
Type cast flavor in `Rvalue::Cast`, modeling `rustc_middle::mir::CastKind`.

Constructors `.pointerExposeProvenance`, `.pointerWithExposedProvenance`,
`.pointerCoercion`, `.intToInt`, `.floatToInt`, `.floatToFloat`, `.intToFloat`,
`.ptrToPtr`, `.fnPtrToPtr`, `.transmute`, and `.subtype` correspond 1-to-1 to
the eleven variants of `rustc_middle::mir::CastKind`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532>

> "pub enum CastKind {
>     /// An exposing pointer to address cast. A cast between a pointer and an integer type, or
>     /// between a function pointer and an integer type.
>     /// See the docs on `expose_provenance` for more details.
>     PointerExposeProvenance,
>     /// An address-to-pointer cast that picks up an exposed provenance.
>     /// See the docs on `with_exposed_provenance` for more details.
>     PointerWithExposedProvenance,
>     /// Pointer related casts that are done by coercions. Note that reference-to-raw-ptr casts are
>     /// translated into `&raw mut/const *r`, i.e., they are not actually casts.
>     PointerCoercion(PointerCoercion, CoercionSource),
>     IntToInt,
>     FloatToInt,
>     FloatToFloat,
>     IntToFloat,
>     PtrToPtr,
>     FnPtrToPtr,
>     /// Reinterpret the bits of the input as a different type.
>     ///
>     /// This is only allowed in runtime MIR, and is subject to the same soundness requirements as
>     /// the `transmute` intrinsic (most notably, reading a value at the wrong type is UB if the bit
>     /// pattern is not valid for the target type). Furthermore, the two types must have the same
>     /// size.
>     Transmute,
>     /// Create a subtype of the input type. This is only allowed in analysis MIR; in runtime MIR,
>     /// subtypes are erased so this would be a no-op.
>     Subtype,
> }"
-/
inductive CastKind : Type where
  /-- Pointer-to-expose-provenance cast
      (`CastKind::PointerExposeProvenance`). -/
  | pointerExposeProvenance : CastKind
  /-- Provenance-capturing address-to-pointer cast
      (`CastKind::PointerWithExposedProvenance`). -/
  | pointerWithExposedProvenance : CastKind
  /-- Pointer coercion such as unsizing or fn-item-to-fn-ptr
      (`CastKind::PointerCoercion`). -/
  | pointerCoercion (coercionKind : String) : CastKind
  /-- Integer-to-integer cast (`CastKind::IntToInt`). -/
  | intToInt : CastKind
  /-- Float-to-integer cast (`CastKind::FloatToInt`). -/
  | floatToInt : CastKind
  /-- Float-to-float cast (`CastKind::FloatToFloat`). -/
  | floatToFloat : CastKind
  /-- Integer-to-float cast (`CastKind::IntToFloat`). -/
  | intToFloat : CastKind
  /-- Pointer-to-pointer cast (`CastKind::PtrToPtr`). -/
  | ptrToPtr : CastKind
  /-- Function-pointer-to-pointer cast (`CastKind::FnPtrToPtr`). -/
  | fnPtrToPtr : CastKind
  /-- Bitwise reinterpretation (`CastKind::Transmute`). -/
  | transmute : CastKind
  /-- Subtype cast (`CastKind::Subtype`). -/
  | subtype : CastKind

/--
Composite value construction kind in `Rvalue::Aggregate`, modeling
`rustc_middle::mir::AggregateKind`.

Constructors `.array`, `.tuple`, `.adt`, `.closure`, `.coroutine`, and `.rawPtr`
correspond to the variants of `rustc_middle::mir::AggregateKind`. For unions,
`.adt` carries `activeField = .some fieldIdx` to identify the initialized union
field.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1546-L1576>

> "pub enum AggregateKind<'tcx> {
>     /// The type is of the element
>     Array(Ty<'tcx>),
>     Tuple,
>
>     /// The second field is the variant index. It's equal to 0 for structs
>     /// and unions. The last field is the active field number and is present
>     /// only for unions -- each union aggregate expression only initializes one
>     /// field.
>     Adt(DefId, VariantIdx, GenericArgsRef<'tcx>, Option<UserTypeAnnotationIndex>, Option<FieldIdx>),
>
>     Closure(DefId, GenericArgsRef<'tcx>),
>     Coroutine(DefId, GenericArgsRef<'tcx>),
>     CoroutineClosure(DefId, GenericArgsRef<'tcx>),
>
>     /// Construct a raw pointer from the data pointer and metadata.
>     ///
>     /// The `Ty` is the type of the pointee, NOT the pointer type itself!
>     RawPtr(Ty<'tcx>, Mutability),
> }"
-/
inductive AggregateKind : Type where
  /-- Homogeneous array `[e_0, ..., e_{n-1}]` with element type `elemTy`. -/
  | array (elemTy : Ty) : AggregateKind
  /-- Tuple `(e_0, ..., e_{n-1})`. -/
  | tuple : AggregateKind
  /-- Algebraic data type value (struct, enum variant `variantIdx`, or union
      with active field `activeField`). -/
  | adt (defPath : DefPath) (variantIdx : VariantIdx) (activeField : Option FieldIdx) : AggregateKind
  /-- Closure environment value for `defPath`. -/
  | closure (defPath : DefPath) : AggregateKind
  /-- Coroutine state value for `defPath`. -/
  | coroutine (defPath : DefPath) : AggregateKind
  /-- Raw pointer construction from data pointer and metadata
      (`AggregateKind::RawPtr`). -/
  | rawPtr (pointeeTy : Ty) (mutability : Mutability) : AggregateKind

/--
Right-hand side expression of a MIR assignment (`StatementKind::Assign`),
modeling `rustc_middle::mir::Rvalue`.

Each constructor of `Rvalue` corresponds 1-to-1 to the variant of
`rustc_middle::mir::Rvalue` with the same name:
- `.use`: direct operand load (`Rvalue::Use`).
- `.repeat`: array repetition `[op; count]` (`Rvalue::Repeat`).
- `.ref`: shared or mutable borrow `&place` / `&mut place` (`Rvalue::Ref`).
- `.threadLocalRef`: reference to a thread-local static
  (`Rvalue::ThreadLocalRef`).
- `.rawPtr`: raw address-of `&raw const place` / `&raw mut place`
  (`Rvalue::RawPtr`).
- `.len`: array or slice element length (`Rvalue::Len`).
- `.cast`: value cast (`Rvalue::Cast`).
- `.binaryOp`: binary arithmetic, comparison, or pointer offset
  (`Rvalue::BinaryOp`).
- `.nullaryOp`: nullary type/check query (`Rvalue::NullaryOp`).
- `.unaryOp`: unary negation, logical inversion, or pointer metadata extraction
  (`Rvalue::UnaryOp`).
- `.discriminant`: read the discriminant of an enum or ADT place
  (`Rvalue::Discriminant`).
- `.aggregate`: construct a composite value from a list of operands
  (`Rvalue::Aggregate`).
- `.shallowInitBox`: initialize a `Box<T>` wrapper around a raw allocation
  pointer (`Rvalue::ShallowInitBox`).
- `.copyForDeref`: compiler-inserted copy before dereferencing
  (`Rvalue::CopyForDeref`).
- `.wrapUnsafeBinder`: wrap a value into an unsafe binder
  (`Rvalue::WrapUnsafeBinder`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488>

> "pub enum Rvalue<'tcx> {
>     /// Yields the operand unchanged
>     Use(Operand<'tcx>),
>
>     /// Creates an array where each element is the value of the operand.
>     ...
>     Repeat(Operand<'tcx>, ty::Const<'tcx>),
>
>     /// Creates a reference of the indicated kind to the place.
>     ...
>     Ref(Region<'tcx>, BorrowKind, Place<'tcx>),
>
>     /// Creates a pointer/reference to the given thread local.
>     ...
>     ThreadLocalRef(DefId),
>
>     /// Creates a pointer with the indicated mutability to the place.
>     ...
>     RawPtr(RawPtrKind, Place<'tcx>),
>
>     /// Yields the length of the place, as a `usize`.
>     ...
>     Len(Place<'tcx>),
>
>     /// Casts a value to the given type.
>     ...
>     Cast(CastKind, Operand<'tcx>, Ty<'tcx>),
>
>     BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>),
>     NullaryOp(RuntimeChecks, Ty<'tcx>),
>     UnaryOp(UnOp, Operand<'tcx>),
>
>     /// Read the discriminant of an ADT.
>     ...
>     Discriminant(Place<'tcx>),
>
>     /// Creates an aggregate value, like a tuple or struct.
>     ...
>     Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>),
>
>     /// Transmutes a `*mut u8` into a shallow-initialized `Box<T>`.
>     ...
>     ShallowInitBox(Operand<'tcx>, Ty<'tcx>),
>
>     /// Exactly like `Use(Operand::Copy(place))`, except that the `place` is guaranteed to not be
>     /// mutated for the lifespan of the borrow that it is used to create.
>     ...
>     CopyForDeref(Place<'tcx>),
>
>     /// Wrap a value in an unsafe binder, i.e. `T -> unsafe<'a> T`.
>     WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>),
> }"
-/
inductive Rvalue : Type where
  /-- Direct use of an operand (`Rvalue::Use`). -/
  | use (op : Operand) : Rvalue
  /-- Array repeat `[op; count]` (`Rvalue::Repeat`). -/
  | repeat (op : Operand) (count : Nat) : Rvalue
  /-- Create a reference `&place` or `&mut place` (`Rvalue::Ref`). -/
  | ref (borrowKind : BorrowKind) (place : Place) : Rvalue
  /-- Reference to a thread-local static (`Rvalue::ThreadLocalRef`). -/
  | threadLocalRef (defPath : DefPath) : Rvalue
  /-- Raw borrow `&raw const place` or `&raw mut place` (`Rvalue::RawPtr`). -/
  | rawPtr (mutability : Mutability) (place : Place) : Rvalue
  /-- Slice or array length (`Rvalue::Len`). -/
  | len (place : Place) : Rvalue
  /-- Type cast (`Rvalue::Cast`). -/
  | cast (kind : CastKind) (op : Operand) (targetTy : Ty) : Rvalue
  /-- Binary operation (`Rvalue::BinaryOp`). -/
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand) : Rvalue
  /-- Nullary operation (`Rvalue::NullaryOp`). -/
  | nullaryOp (op : NullOp) (ty : Ty) : Rvalue
  /-- Unary operation (`Rvalue::UnaryOp`). -/
  | unaryOp (op : UnOp) (val : Operand) : Rvalue
  /-- Read enum discriminant of `place` (`Rvalue::Discriminant`). -/
  | discriminant (place : Place) : Rvalue
  /-- Construct an aggregate value from `operands` (`Rvalue::Aggregate`). -/
  | aggregate (kind : AggregateKind) (operands : List Operand) : Rvalue
  /-- Shallow box initialization (`Rvalue::ShallowInitBox`). -/
  | shallowInitBox (op : Operand) (contentTy : Ty) : Rvalue
  /-- Built-in deref copy (`Rvalue::CopyForDeref`). -/
  | copyForDeref (place : Place) : Rvalue
  /-- Wrap value in an unsafe binder (`Rvalue::WrapUnsafeBinder`). -/
  | wrapUnsafeBinder (op : Operand) (targetTy : Ty) : Rvalue

end Trusted.Rustc.V2026_06_01.MirAst
