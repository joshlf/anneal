import Trusted.Rustc.V2026_06_01.Layout

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR primitive and composite types,
scalars, provenance pointers, constants, phase tags, and contract roles for
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#99`, `#101`, `#103`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1-L4>

> "//! This defines the syntax of MIR, i.e., the set of available MIR operations, and other definitions
> //! closely related to MIR semantics.
> //! This is in a dedicated file so that changes to this file can be reviewed more carefully.
> //! The intention is that this file only contains datatype declarations, no code."
-/

/--
Identifier of a global or constant memory allocation, modeling
`rustc_middle::mir::interpret::AllocId`.

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L21-L27>

> "pub struct ConstAlloc<'tcx> {
>     /// The value lives here, at offset 0, and that allocation definitely is an `AllocKind::Memory`
>     /// (so you can use `AllocMap::unwrap_memory`).
>     pub alloc_id: AllocId,
>     pub ty: Ty<'tcx>,
> }"
-/
abbrev AllocId : Type := Nat

/--
0-based index into a captured compilation unit's `LayoutTable.entries`
(`R-TY-01`).
-/
abbrev LayoutIdx : Type := Nat

/--
Canonical crate-qualified item path (`tcx.def_path_str(def_id)`) identifying a
Rust definition across MIR bodies and specification contracts.
-/
abbrev DefPath : Type := String

/--
Unsigned integer width, modeling `rustc_middle::ty::UintTy`.

Constructors `.u8`, `.u16`, `.u32`, `.u64`, `.u128`, and `.usize` correspond
1-to-1 to the six unsigned integer types of the Rust language.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The unsigned integer types consist of:
>
> Type   Minimum   Maximum
> u8     0         2^8-1
> u16    0         2^16-1
> u32    0         2^32-1
> u64    0         2^64-1
> u128   0         2^128-1
> usize  0         2^32-1 or 2^64-1"
>
> "The usize type is an unsigned integer type with the same number of bits as the platform’s pointer type. It can represent every memory address in the process."
-/
inductive UintTy : Type where
  /-- 8-bit unsigned integer (`u8`). -/
  | u8 : UintTy
  /-- 16-bit unsigned integer (`u16`). -/
  | u16 : UintTy
  /-- 32-bit unsigned integer (`u32`). -/
  | u32 : UintTy
  /-- 64-bit unsigned integer (`u64`). -/
  | u64 : UintTy
  /-- 128-bit unsigned integer (`u128`). -/
  | u128 : UintTy
  /-- Pointer-sized unsigned integer (`usize`). -/
  | usize : UintTy

/--
Signed two's-complement integer width, modeling `rustc_middle::ty::IntTy`.

Constructors `.i8`, `.i16`, `.i32`, `.i64`, `.i128`, and `.isize` correspond
1-to-1 to the six signed two's-complement integer types of the Rust language.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of:
>
> Type   Minimum            Maximum
> i8     -(2^7)             2^7-1
> i16    -(2^15)            2^15-1
> i32    -(2^31)            2^31-1
> i64    -(2^63)            2^63-1
> i128   -(2^127)           2^127-1
> isize  -(2^31) or -(2^63) 2^31-1 or 2^63-1"
>
> "The isize type is a signed two’s complement integer type with the same number of bits as the platform’s pointer type."
-/
inductive IntTy : Type where
  /-- 8-bit signed integer (`i8`). -/
  | i8 : IntTy
  /-- 16-bit signed integer (`i16`). -/
  | i16 : IntTy
  /-- 32-bit signed integer (`i32`). -/
  | i32 : IntTy
  /-- 64-bit signed integer (`i64`). -/
  | i64 : IntTy
  /-- 128-bit signed integer (`i128`). -/
  | i128 : IntTy
  /-- Pointer-sized signed integer (`isize`). -/
  | isize : IntTy

/--
Return the width in bits of an unsigned integer type `UintTy` on a target whose
pointer bit-width is `ptrBits`.
-/
def UintTy.bitWidth (ptrBits : Nat) : UintTy → Nat
  | .u8 => 8
  | .u16 => 16
  | .u32 => 32
  | .u64 => 64
  | .u128 => 128
  | .usize => ptrBits

/--
Return the width in bits of a signed integer type `IntTy` on a target whose
pointer bit-width is `ptrBits`.
-/
def IntTy.bitWidth (ptrBits : Nat) : IntTy → Nat
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .i64 => 64
  | .i128 => 128
  | .isize => ptrBits

/--
Return the width in bytes of an unsigned integer type `UintTy` on a target whose
pointer bit-width is `ptrBits`.
-/
def UintTy.byteWidth (ptrBits : Nat) (ty : UintTy) : Nat :=
  Nat.div (UintTy.bitWidth ptrBits ty) 8

/--
Return the width in bytes of a signed integer type `IntTy` on a target whose
pointer bit-width is `ptrBits`.
-/
def IntTy.byteWidth (ptrBits : Nat) (ty : IntTy) : Nat :=
  Nat.div (IntTy.bitWidth ptrBits ty) 8

/--
IEEE-754 floating-point width, modeling `rustc_middle::ty::FloatTy`.

Constructors `.f32` and `.f64` correspond to standard Rust `f32` and `f64`
types, while `.f16` and `.f128` correspond to nightly IEEE-754 half- and
quad-precision floating-point types in `rustc_middle::ty::FloatTy`.

Reference (The Rust Reference, "Floating-Point Types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and f64, respectively."
-/
inductive FloatTy : Type where
  /-- 16-bit binary floating-point (`f16`). -/
  | f16 : FloatTy
  /-- 32-bit binary floating-point (`f32`). -/
  | f32 : FloatTy
  /-- 64-bit binary floating-point (`f64`). -/
  | f64 : FloatTy
  /-- 128-bit binary floating-point (`f128`). -/
  | f128 : FloatTy

/--
Mutability qualifier of a local binding, reference, raw pointer, or static
allocation, modeling `rustc_ast::Mutability` (re-exported in
`rustc_middle::ty`).

Constructor `.not` models shared/immutable access (`&T`, `*const T`, immutable
local) and `.mut` models mutable access (`&mut T`, `*mut T`, `mut` local).

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Shared references point to memory which is owned by some other value. When a shared reference to a value is created, it prevents direct mutation of the value."
>
> "Mutable references point to memory which is owned by some other value. A mutable reference type is written &mut type or &'a mut type."
-/
inductive Mutability : Type where
  /-- Shared / immutable (`Mutability::Not`). -/
  | not : Mutability
  /-- Mutable (`Mutability::Mut`). -/
  | mut : Mutability

/--
Function or function-pointer safety qualifier, modeling `rustc_hir::Safety`.

Constructor `.safe` models safe Rust functions and `.unsafe_` models `unsafe fn`
items and `unsafe fn(...)` pointers.

Reference (The Rust Reference, "The unsafe keyword"):
<https://doc.rust-lang.org/1.98.0/reference/unsafe-keyword.html>

> "Unsafe functions are functions that are not safe in all contexts and/or for all possible inputs."
-/
inductive Safety : Type where
  /-- Safe Rust function or operation (`Safety::Safe`). -/
  | safe : Safety
  /-- Unsafe function or operation (`Safety::Unsafe`). -/
  | unsafe_ : Safety

/--
Structural representation of a Rust type in captured `Runtime(PostCleanup)` MIR
after lifetime-region erasure, modeling `rustc_middle::ty::TyKind` (supporting
both concrete monomorphized types and polymorphic generic type parameters and
associated type aliases).

The constructors of `RigidTy` correspond to the `TyKind` variants that appear in
post-cleanup MIR:
- `.param`: generic type parameter `T` at index `idx` (`TyKind::Param`).
- `.alias`: unnormalized associated type projection `<T as Trait>::Assoc`
  (`TyKind::Alias`).
- `.bool`, `.char`, `.int`, `.uint`, `.float`, `.never`, `.str`: primitive and
  textual types (`TyKind::Bool`, `Char`, `Int`, `Uint`, `Float`, `Never`,
  `Str`).
- `.tuple`, `.array`, `.slice`: structural sequence and product types
  (`TyKind::Tuple`, `Array`, `Slice`).
- `.ref`, `.rawPtr`: reference (`&T`, `&mut T`) and raw pointer (`*const T`,
  `*mut T`) types (`TyKind::Ref`, `RawPtr`).
- `.adt`: structs, enums, and unions (`TyKind::Adt`) identified by canonical
  `DefPath` and type arguments.
- `.fnDef`, `.fnPtr`, `.closure`: callable types (`TyKind::FnDef`, `FnPtr`,
  `Closure`).
- `.dynamic`, `.foreign`: trait objects (`dyn Trait`, `TyKind::Dynamic`) and
  extern foreign types (`TyKind::Foreign`).
- `.other`: fallback preserving the rendered type string for any remaining
  compiler-internal type so syntax capture is total.

Reference (`compiler/rustc_middle/src/ty/sty.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/sty.rs#L36-L46>

> "pub struct ParamTy {
>     pub index: u32,
>     pub name: Symbol,
> }"

Reference (The Rust Reference, "Types"):
<https://doc.rust-lang.org/1.98.0/reference/types.html>

> "Every variable, item, and value in a Rust program has a type. The type of a value defines the interpretation of the memory holding it and the operations that may be performed on the value."

Reference (The Rust Reference, "Boolean type", "Textual types", "Never type",
"Tuple types", "Array types", "Slice types"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>
<https://doc.rust-lang.org/1.98.0/reference/types/char.html>
<https://doc.rust-lang.org/1.98.0/reference/types/never.html>

> "The boolean type has values true and false. The bool type has a size and alignment of 1 each. The value false has the bit pattern 0x00 and the value true has the bit pattern 0x01."
>
> "A value of type char is a Unicode scalar value (i.e. a code point that is not a surrogate), represented as a 32-bit unsigned word in the 0x0000 to 0xD7FF or 0xE000 to 0x10FFFF range."
>
> "The never type ! is a type with no values, representing the result of computations that never complete."

Modeling choice: Every `RigidTy` is paired in `Ty` with a `LayoutIdx` pointing
into `LayoutTable.entries` (`R-TY-01`), so operational semantics never guesses a
type's size, alignment, or field offsets from `RigidTy` alone.
-/
inductive RigidTy : Type where
  /-- Generic type parameter `T` at index `idx` (`ty::Param`). -/
  | param (idx : Nat) (name : String) : RigidTy
  /-- Associated type alias `<T as Trait>::Assoc` (`ty::Alias`). -/
  | alias (defPath : DefPath) (args : List RigidTy) : RigidTy
  /-- Boolean (`bool`). -/
  | bool : RigidTy
  /-- Unicode scalar value (`char`). -/
  | char : RigidTy
  /-- Signed two's-complement integer (`i8`..`i128`, `isize`). -/
  | int (w : IntTy) : RigidTy
  /-- Unsigned integer (`u8`..`u128`, `usize`). -/
  | uint (w : UintTy) : RigidTy
  /-- Floating-point type (`f16`..`f128`). -/
  | float (w : FloatTy) : RigidTy
  /-- Never type (`!`). -/
  | never : RigidTy
  /-- UTF-8 string slice (`str`). -/
  | str : RigidTy
  /-- Tuple of element types `(T_0, ..., T_{n-1})`. -/
  | tuple (fields : List RigidTy) : RigidTy
  /-- Fixed-length array `[T; len]`. -/
  | array (elem : RigidTy) (len : Nat) : RigidTy
  /-- Dynamically-sized slice `[T]`. -/
  | slice (elem : RigidTy) : RigidTy
  /-- Reference `&T` or `&mut T`. -/
  | ref (mutability : Mutability) (pointee : RigidTy) : RigidTy
  /-- Raw pointer `*const T` or `*mut T`. -/
  | rawPtr (mutability : Mutability) (pointee : RigidTy) : RigidTy
  /-- Algebraic data type (struct, enum, or union) identified by `defPath` and
      monomorphized type arguments `args`. -/
  | adt (defPath : DefPath) (args : List RigidTy) : RigidTy
  /-- Zero-sized function item type for `defPath`. -/
  | fnDef (defPath : DefPath) (args : List RigidTy) : RigidTy
  /-- Function pointer `fn(A_0, ...) -> R`. -/
  | fnPtr (inputs : List RigidTy) (output : RigidTy) (safety : Safety) (abi : CallConv) : RigidTy
  /-- Monomorphized closure type identified by `defPath`. -/
  | closure (defPath : DefPath) (upvars : List RigidTy) : RigidTy
  /-- Trait object `dyn Trait`. -/
  | dynamic (traitPath : DefPath) : RigidTy
  /-- Extern `foreign` type. -/
  | foreign (defPath : DefPath) : RigidTy
  /-- Fallback for unindexed compiler-internal types, carrying the rendered
      type string so syntax capture remains total. -/
  | other (rendered : String) : RigidTy

/--
A captured monomorphized type paired with its index in the compilation unit's
`LayoutTable`, modeling `rustc_middle::ty::Ty` together with its queried
`tcx.layout_of(...)` entry (`R-TY-01`).

Field `kind` records the structural `RigidTy` and `layoutIdx` indexes into
`CapturedMir.layouts.entries`.
-/
structure Ty : Type where
  /-- Structural type representation. -/
  kind : RigidTy
  /-- Index of the compiler-computed `TypeLayout` in `LayoutTable.entries`. -/
  layoutIdx : LayoutIdx

/--
Raw machine scalar bit pattern and byte width, modeling
`rustc_middle::mir::interpret::ScalarInt`.

Field `bits` stores the unsigned bit pattern in `[0, 2^(sizeBytes * 8))` and
`sizeBytes` stores the scalar byte width (`1, 2, 4, 8, 16`).

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L35-L42>

> "/// A constant value that can be represented by a single \"scalar\" value.
> /// This includes integers, floats, pointers, `bool`, `char`.
> /// Does *not* include ZSTs, those use `ConstValue::ZeroSized`.
> Scalar(Scalar),"
-/
structure ScalarInt : Type where
  /-- Unsigned two's-complement bit representation in
      `[0, 2^(sizeBytes * 8))`. -/
  bits : Nat
  /-- Width in bytes (`1, 2, 4, 8, 16`). -/
  sizeBytes : Nat

/--
Test whether the unsigned bit pattern `s.bits` falls within the inclusive
possibly-wrapping range `r`, modeling `rustc_abi::WrappingRange::contains`.

When `r.start <= r.end_`, the range is non-wrapping and requires
`r.start <= s.bits <= r.end_`. When `r.start > r.end_`, the range wraps around
zero and requires `s.bits >= r.start` or `s.bits <= r.end_`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1440-L1448>

> "pub fn contains(&self, v: u128) -> bool {
>     if self.start <= self.end {
>         self.start <= v && v <= self.end
>     } else {
>         self.start <= v || v <= self.end
>     }
> }"
-/
def ScalarInt.inRange (s : ScalarInt) (r : WrappingRange) : Bool :=
  match Nat.ble r.start r.end_ with
  | true => Bool.and (Nat.ble r.start s.bits) (Nat.ble s.bits r.end_)
  | false => Bool.or (Nat.ble r.start s.bits) (Nat.ble s.bits r.end_)

/--
Pointer provenance and byte offset for a compile-time or runtime pointer,
modeling `rustc_middle::mir::interpret::Pointer<AllocId>`.

Field `allocId` identifies the target allocation (`AllocId`) and `offsetBytes`
gives the byte offset within that allocation.

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L61-L70>

> "Indirect {
>     /// The backing memory of the value. This may contain more memory than needed for just the
>     /// constant if this points into a larger ConstAlloc.
>     alloc_id: AllocId,
>     /// The offset into `alloc_id` where the value starts.
>     offset: Size,
> },"
-/
structure ProvenancePtr : Type where
  /-- Target global or stack allocation identifier. -/
  allocId : AllocId
  /-- Byte offset within `allocId`. -/
  offsetBytes : Nat

/--
Return the borrow-table provenance tag carried by `p`.

In `MirSem`, references (`Rvalue.ref`) and raw pointers (`Rvalue.rawPtr`) to
stack locals record their unique Tree Borrows provenance tag in `p.allocId`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1118-L1120>

> "1. The address in memory that the place refers to.
>  2. The provenance with which the place is being accessed."
-/
def ProvenancePtr.tag (p : ProvenancePtr) : Nat :=
  p.allocId

/--
Evaluated compile-time scalar or provenance-carrying pointer, modeling
`rustc_middle::mir::interpret::Scalar`.

Constructor `.int` models a pure bit-pattern scalar (`Scalar::Int`) and `.ptr`
models a pointer with allocation provenance (`Scalar::Ptr`) and pointer width
`sizeBytes`.

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L35-L42>

> "/// A constant value that can be represented by a single \"scalar\" value.
> /// This includes integers, floats, pointers, `bool`, `char`.
> /// Does *not* include ZSTs, those use `ConstValue::ZeroSized`.
> Scalar(Scalar),"
-/
inductive ConstScalar : Type where
  /-- Concrete bit-pattern scalar (`Scalar::Int`). -/
  | int (val : ScalarInt) : ConstScalar
  /-- Pointer with allocation provenance (`Scalar::Ptr`). -/
  | ptr (ptr : ProvenancePtr) (sizeBytes : Nat) : ConstScalar

/--
Evaluated or symbolic MIR constant value, modeling
`rustc_middle::mir::ConstValue` and `rustc_middle::mir::Const`.

Constructors `.zeroSized`, `.scalar`, `.slice`, and `.indirect` correspond
1-to-1 to the four variants of `rustc_middle::mir::ConstValue`, while
`.unevaluated` corresponds to `Const::Unevaluated` when a constant item is
referenced symbolically by `DefPath`.

Reference (`compiler/rustc_middle/src/mir/consts.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L34-L71>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/consts.rs#L210-L233>

> "pub enum ConstValue {
>     /// Used only for types with `layout::abi::Scalar` ABI and ZSTs.
>     ///
>     /// Not using the enum `Value` to encode that this must not be `Uninit`.
>     Scalar(Scalar),
>
>     /// Only for ZSTs.
>     ZeroSized,
>
>     /// Used for references to unsized types with slice tail.
>     ///
>     /// This is worth an optimized representation since Rust has literals of
>     /// type `&str` and `&[u8]`. Not having to indirect those through an
>     /// `AllocId` (or two, if we used `Indirect` here!) has shown measurable
>     /// performance improvements on stress tests. We then reuse this
>     /// optimization for slice-tail types more generally.
>     Slice {
>         /// The pointer to the slice contents.
>         alloc_id: AllocId,
>         /// The metadata field of the reference.
>         /// This is always a \"length\" so we use `u64` directly instead of `Scalar` or `usize`.
>         meta: u64,
>     },
>
>     /// A value not represented by any of the other variants; needs to be stored in-memory.
>     ///
>     /// Note that ZSTs can have an arbitrary representation, including `Indirect` with a dangling
>     ///(but aligned) pointer.
>     Indirect {
>         /// The backing memory of the value. This may contain more memory than needed for just the
>         /// constant if this points into a larger ConstAlloc.
>         alloc_id: AllocId,
>         /// The offset into `alloc_id` where the value starts.
>         offset: Size,
>     },
> }"
>
> "pub enum Const<'tcx> {
>     /// This constant came from the type system.
>     Ty(Ty<'tcx>, ty::Const<'tcx>),
>
>     /// An unevaluated mir constant which is not part of the type system.
>     Unevaluated(UnevaluatedConst<'tcx>, Ty<'tcx>),
>
>     /// This constant cannot go back into the type system, as it represents
>     /// something the type system cannot handle (e.g. pointers).
>     Val(ConstValue, Ty<'tcx>),
> }"
-/
inductive ConstValue : Type where
  /-- Zero-sized constant (`ConstValue::ZeroSized`). -/
  | zeroSized : ConstValue
  /-- Single scalar constant (`ConstValue::Scalar`). -/
  | scalar (s : ConstScalar) : ConstValue
  /-- Pair of scalars (`ConstValue::Slice`, e.g., `&str` or `&[T]` fat
      pointer). -/
  | slice (data : ConstScalar) (meta_ : Nat) : ConstValue
  /-- Indirect constant stored in global allocation `allocId` at
      `offsetBytes`. -/
  | indirect (allocId : AllocId) (offsetBytes : Nat) : ConstValue
  /-- Unevaluated or symbolic constant item `defPath`. -/
  | unevaluated (defPath : DefPath) : ConstValue

/--
Typed MIR constant operand, modeling `rustc_middle::mir::ConstOperand`.

Field `ty` stores the constant's monomorphized `Ty` and `val` stores its
`ConstValue`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1343-L1350>

> "pub struct ConstOperand<'tcx> {
>     pub span: Span,
>
>     /// Optional user-given type: for something like
>     /// `collect::<Vec<_>>`, this would be present and would
>     /// indicate that `Vec<_>` was explicitly specified.
>     pub user_ty: Option<UserTypeProjection>,
>
>     pub const_: Const<'tcx>,
> }"
-/
structure ConstOperand : Type where
  /-- Type of the constant. -/
  ty : Ty
  /-- Evaluated constant value. -/
  val : ConstValue

/--
Recorded dialect and phase of a captured MIR body, modeling
`rustc_middle::mir::MirPhase` and `rustc_middle::mir::RuntimePhase`.

Anneal's verification boundary targets `Runtime(PostCleanup)` MIR
(`MirPhase::Runtime(RuntimePhase::PostCleanup)`, `.runtimePostCleanup`, `#99`
§2). Constructor `.runtimeOptimized` models
`MirPhase::Runtime(RuntimePhase::Optimized)`, and `.other` records any other
phase name for diagnostics (`CapturedMir.wellFormed` and
`MirSemantics.WellFormedCapture` require `.runtimePostCleanup`).

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L92-L102>

> "impl MirPhase {
>     pub fn name(&self) -> &'static str {
>         match *self {
>             MirPhase::Built => \"built\",
>             MirPhase::Analysis(AnalysisPhase::Initial) => \"analysis-initial\",
>             MirPhase::Analysis(AnalysisPhase::PostCleanup) => \"analysis-post-cleanup\",
>             MirPhase::Runtime(RuntimePhase::Initial) => \"runtime-initial\",
>             MirPhase::Runtime(RuntimePhase::PostCleanup) => \"runtime-post-cleanup\",
>             MirPhase::Runtime(RuntimePhase::Optimized) => \"runtime-optimized\",
>         }
>     }
> }"
-/
inductive MirPhaseTag : Type where
  /-- `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`#99` §2). -/
  | runtimePostCleanup : MirPhaseTag
  /-- `MirPhase::Runtime(RuntimePhase::Optimized)`. -/
  | runtimeOptimized : MirPhaseTag
  /-- Other phase tag recorded for diagnostics (rejected by `WellFormedCapture`
      if not a supported runtime phase). -/
  | other (name : String) : MirPhaseTag

/--
Role of a captured MIR body in Anneal's specification pipeline (`#103` §3.2).

Constructors `.subject`, `.requires`, `.ensures`, `.externalSpec`, and `.model`
distinguish the Rust function under verification (`.subject`) from Anodized
synthetic precondition/postcondition check functions (`.requires`, `.ensures`),
external specification stubs (`.externalSpec`), and pure specification models
(`.model`).
-/
inductive ContractRole : Type where
  /-- Subject Rust function being verified. -/
  | subject : ContractRole
  /-- Synthetic precondition body (`__anodized_fn_requires_*`). -/
  | requires (subjectDefPath : DefPath) : ContractRole
  /-- Synthetic postcondition body (`__anodized_fn_ensures_*`). -/
  | ensures (subjectDefPath : DefPath) : ContractRole
  /-- External sidecar specification body (`#[anneal::external_spec]`). -/
  | externalSpec (subjectDefPath : DefPath) : ContractRole
  /-- Pure specification model function (`#[anneal::model]`). -/
  | model : ContractRole


/--
Generic type parameter declaration on a polymorphic MIR body, modeling
`rustc_middle::ty::GenericParamDef` (`GenericParamDefKind::Type`).

Reference (`compiler/rustc_middle/src/ty/generics.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/generics.rs#L17-L26>

> "pub struct GenericParamDef {
>     pub name: Symbol,
>     pub def_id: DefId,
>     pub index: u32,
>     pub pure_wrt_drop: bool,
>     pub kind: GenericParamDefKind,
> }"
-/
structure GenericParamDef : Type where
  /-- 0-based index of the generic type parameter (`GenericParamDef::index`). -/
  idx : Nat
  /-- Source identifier of the generic parameter (`GenericParamDef::name`). -/
  name : String

/--
Trait reference `<T_0 as Trait<T_1, ...>>`, modeling
`rustc_middle::ty::TraitRef`.

Reference (`compiler/rustc_middle/src/ty/structural_impls.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/sty.rs#L96-L102>

> "pub struct TraitRef<'tcx> {
>     pub def_id: DefId,
>     pub args: GenericArgsRef<'tcx>,
> }"
-/
structure TraitRef : Type where
  /-- Canonical path of the trait definition (`TraitRef::def_id`). -/
  defPath : DefPath
  /-- Type arguments to the trait (`TraitRef::args`, with `Self` at index `0`). -/
  args : List RigidTy

/--
Captured trait implementation entry associating a `TraitRef` with its concrete
`impl` block or resolved associated item path (`implPath`).
-/
structure TraitImplEntry : Type where
  /-- Implemented trait reference (`tcx.impl_trait_ref(impl_def_id)`). -/
  traitRef : TraitRef
  /-- Canonical path of the `impl` block or resolved implementation item. -/
  implPath : DefPath

/--
Concrete type-and-layout substitution list mapping generic parameter index `idx`
to `(substRigidTy, substTypeLayout)`.
-/
abbrev TypeSubst : Type := List (RigidTy × TypeLayout)

/--
Look up the `(RigidTy × TypeLayout)` entry at 0-based generic parameter index
`idx` in `args` by structural recursion on `args`.

Matching on `args` first ensures `TypeSubst.lookup .nil idx = .none` reduces
definitionally (`rfl`) even when `idx` is a symbolic `Nat` variable.
-/
@[reducible]
def TypeSubst.lookup : TypeSubst → Nat → Option (RigidTy × TypeLayout)
  | .nil, _ => .none
  | entry :: _, .zero => .some entry
  | _ :: rest, .succ idx => TypeSubst.lookup rest idx

/--
Extract the ordered list of concrete `TypeLayout` entries from `args`.
-/
@[reducible]
def TypeSubst.layouts : TypeSubst → List TypeLayout
  | .nil => .nil
  | (_, l) :: rest => l :: TypeSubst.layouts rest

/--
Number of type-parameter entries in `args`.
-/
@[reducible]
def TypeSubst.length : TypeSubst → Nat
  | .nil => 0
  | _ :: rest => Nat.succ (TypeSubst.length rest)

/--
Two-argument congruence lemma in `Init.Core`.
-/
theorem congrArg2
    {α β γ : Type}
    (f : α → β → γ)
    {a₁ a₂ : α}
    {b₁ b₂ : β}
    (ha : a₁ = a₂)
    (hb : b₁ = b₂) :
    f a₁ b₁ = f a₂ b₂ := by
  subst ha
  subst hb
  rfl

mutual
/--
Instantiate a `RigidTy` by structurally substituting every `.param idx name`
resolved in `args` across all nested type constructors (`.alias`, `.tuple`,
`.array`, `.slice`, `.ref`, `.rawPtr`, `.adt`, `.fnDef`, `.fnPtr`, `.closure`).
-/
@[reducible]
def RigidTy.instantiate (args : TypeSubst) : RigidTy → RigidTy
  | .param idx name =>
    match TypeSubst.lookup args idx with
    | .some (t, _) => t
    | .none => .param idx name
  | .alias p a => .alias p (RigidTy.instantiateList args a)
  | .bool => .bool
  | .char => .char
  | .int w => .int w
  | .uint w => .uint w
  | .float w => .float w
  | .never => .never
  | .str => .str
  | .tuple fields => .tuple (RigidTy.instantiateList args fields)
  | .array elem len => .array (RigidTy.instantiate args elem) len
  | .slice elem => .slice (RigidTy.instantiate args elem)
  | .ref mutability pointee => .ref mutability (RigidTy.instantiate args pointee)
  | .rawPtr mutability pointee => .rawPtr mutability (RigidTy.instantiate args pointee)
  | .adt p a => .adt p (RigidTy.instantiateList args a)
  | .fnDef p a => .fnDef p (RigidTy.instantiateList args a)
  | .fnPtr inputs output safety abi =>
    .fnPtr (RigidTy.instantiateList args inputs) (RigidTy.instantiate args output) safety abi
  | .closure p upvars => .closure p (RigidTy.instantiateList args upvars)
  | .dynamic traitPath => .dynamic traitPath
  | .foreign defPath => .foreign defPath
  | .other rendered => .other rendered

/--
Structurally instantiate a list of `RigidTy` arguments.
-/
@[reducible]
def RigidTy.instantiateList (args : TypeSubst) : List RigidTy → List RigidTy
  | .nil => .nil
  | t :: ts => RigidTy.instantiate args t :: RigidTy.instantiateList args ts
end

mutual
/--
Universal identity theorem for `RigidTy.instantiate` under the empty
substitution `.nil`.
-/
@[simp]
theorem RigidTy.instantiate_nil :
    (k : RigidTy) → RigidTy.instantiate .nil k = k
  | .param _ _ => rfl
  | .alias p a => congrArg (RigidTy.alias p) (RigidTy.instantiateList_nil a)
  | .bool => rfl
  | .char => rfl
  | .int _ => rfl
  | .uint _ => rfl
  | .float _ => rfl
  | .never => rfl
  | .str => rfl
  | .tuple fields => congrArg RigidTy.tuple (RigidTy.instantiateList_nil fields)
  | .array elem len => congrArg (RigidTy.array · len) (RigidTy.instantiate_nil elem)
  | .slice elem => congrArg RigidTy.slice (RigidTy.instantiate_nil elem)
  | .ref m pointee => congrArg (RigidTy.ref m) (RigidTy.instantiate_nil pointee)
  | .rawPtr m pointee => congrArg (RigidTy.rawPtr m) (RigidTy.instantiate_nil pointee)
  | .adt p a => congrArg (RigidTy.adt p) (RigidTy.instantiateList_nil a)
  | .fnDef p a => congrArg (RigidTy.fnDef p) (RigidTy.instantiateList_nil a)
  | .fnPtr inputs output safety abi =>
    congrArg2 (RigidTy.fnPtr · · safety abi)
      (RigidTy.instantiateList_nil inputs)
      (RigidTy.instantiate_nil output)
  | .closure p upvars => congrArg (RigidTy.closure p) (RigidTy.instantiateList_nil upvars)
  | .dynamic _ => rfl
  | .foreign _ => rfl
  | .other _ => rfl

/--
Universal identity theorem for `RigidTy.instantiateList` on `.nil`.
-/
@[simp]
theorem RigidTy.instantiateList_nil :
    (ks : List RigidTy) → RigidTy.instantiateList .nil ks = ks
  | .nil => rfl
  | k :: ks =>
    congrArg2 List.cons (RigidTy.instantiate_nil k) (RigidTy.instantiateList_nil ks)
end

/--
Alias for `RigidTy.instantiateList_nil`.
-/
@[simp]
theorem RigidTy.instantiateList_nil_eq (ks : List RigidTy) :
    RigidTy.instantiateList .nil ks = ks :=
  RigidTy.instantiateList_nil ks

/--
Alias for `RigidTy.instantiate_nil`.
-/
@[simp]
theorem RigidTy.instantiate_empty_id (k : RigidTy) :
    RigidTy.instantiate .nil k = k :=
  RigidTy.instantiate_nil k

mutual
/--
Test whether `k : RigidTy` contains any `.param idx _` resolved by `args`.
-/
@[reducible]
def RigidTy.hasSubstParam (args : TypeSubst) : RigidTy → Bool
  | .param idx _ =>
    match TypeSubst.lookup args idx with
    | .some _ => true
    | .none => false
  | .alias _ a => RigidTy.hasSubstParamList args a
  | .tuple fields => RigidTy.hasSubstParamList args fields
  | .array elem _ => RigidTy.hasSubstParam args elem
  | .slice elem => RigidTy.hasSubstParam args elem
  | .ref _ pointee => RigidTy.hasSubstParam args pointee
  | .rawPtr _ pointee => RigidTy.hasSubstParam args pointee
  | .adt _ a => RigidTy.hasSubstParamList args a
  | .fnDef _ a => RigidTy.hasSubstParamList args a
  | .fnPtr inputs output _ _ =>
    Bool.or
      (RigidTy.hasSubstParamList args inputs)
      (RigidTy.hasSubstParam args output)
  | .closure _ upvars => RigidTy.hasSubstParamList args upvars
  | .bool => false
  | .char => false
  | .int _ => false
  | .uint _ => false
  | .float _ => false
  | .never => false
  | .str => false
  | .dynamic _ => false
  | .foreign _ => false
  | .other _ => false

/--
Test whether any `RigidTy` in a list contains a resolved `.param`.
-/
@[reducible]
def RigidTy.hasSubstParamList (args : TypeSubst) : List RigidTy → Bool
  | .nil => false
  | t :: ts =>
    Bool.or (RigidTy.hasSubstParam args t) (RigidTy.hasSubstParamList args ts)
end

/--
Test whether `k : RigidTy` is a non-`.param` compound type that contains at
least one `.param idx _` resolved by `args`.
-/
@[reducible]
def RigidTy.isCompoundSubstParam (args : TypeSubst) : RigidTy → Bool
  | .param _ _ => false
  | k => RigidTy.hasSubstParam args k

/--
Left projection for `Bool.or a b = false`.
-/
theorem bool_or_eq_false_left {a b : Bool} (h : Bool.or a b = false) :
    a = false := by
  cases a with
  | false => rfl
  | true => cases h

/--
Right projection for `Bool.or a b = false`.
-/
theorem bool_or_eq_false_right {a b : Bool} (h : Bool.or a b = false) :
    b = false := by
  cases a with
  | false => exact h
  | true => cases h

mutual
/--
When `RigidTy.hasSubstParam args k = false`, `RigidTy.instantiate args k = k`.
-/
@[simp]
theorem RigidTy.instantiate_of_hasSubstParam_false (args : TypeSubst) :
    (k : RigidTy) → RigidTy.hasSubstParam args k = false →
    RigidTy.instantiate args k = k
  | .param idx _, h => by
    dsimp [RigidTy.hasSubstParam, RigidTy.instantiate] at h ⊢
    cases hLook : TypeSubst.lookup args idx with
    | none => rfl
    | some _ => rw [hLook] at h; cases h
  | .alias defPath a, h =>
    congrArg (RigidTy.alias defPath)
      (RigidTy.instantiateList_of_hasSubstParamList_false args a h)
  | .bool, _ => rfl
  | .char, _ => rfl
  | .int _, _ => rfl
  | .uint _, _ => rfl
  | .float _, _ => rfl
  | .never, _ => rfl
  | .str, _ => rfl
  | .tuple fields, h =>
    congrArg RigidTy.tuple
      (RigidTy.instantiateList_of_hasSubstParamList_false args fields h)
  | .array elem len, h =>
    congrArg (RigidTy.array · len)
      (RigidTy.instantiate_of_hasSubstParam_false args elem h)
  | .slice elem, h =>
    congrArg RigidTy.slice
      (RigidTy.instantiate_of_hasSubstParam_false args elem h)
  | .ref mutability pointee, h =>
    congrArg (RigidTy.ref mutability)
      (RigidTy.instantiate_of_hasSubstParam_false args pointee h)
  | .rawPtr mutability pointee, h =>
    congrArg (RigidTy.rawPtr mutability)
      (RigidTy.instantiate_of_hasSubstParam_false args pointee h)
  | .adt defPath a, h =>
    congrArg (RigidTy.adt defPath)
      (RigidTy.instantiateList_of_hasSubstParamList_false args a h)
  | .fnDef defPath a, h =>
    congrArg (RigidTy.fnDef defPath)
      (RigidTy.instantiateList_of_hasSubstParamList_false args a h)
  | .fnPtr inputs output _ _, h => by
    dsimp [RigidTy.instantiate]
    rw [RigidTy.instantiateList_of_hasSubstParamList_false args inputs
          (bool_or_eq_false_left h),
        RigidTy.instantiate_of_hasSubstParam_false args output
          (bool_or_eq_false_right h)]
  | .closure defPath upvars, h =>
    congrArg (RigidTy.closure defPath)
      (RigidTy.instantiateList_of_hasSubstParamList_false args upvars h)
  | .dynamic _, _ => rfl
  | .foreign _, _ => rfl
  | .other _, _ => rfl

/--
When `RigidTy.hasSubstParamList args ks = false`,
`RigidTy.instantiateList args ks = ks`.
-/
@[simp]
theorem RigidTy.instantiateList_of_hasSubstParamList_false (args : TypeSubst) :
    (ks : List RigidTy) → RigidTy.hasSubstParamList args ks = false →
    RigidTy.instantiateList args ks = ks
  | .nil, _ => rfl
  | k :: ks, h =>
    congrArg2 List.cons
      (RigidTy.instantiate_of_hasSubstParam_false args k
        (bool_or_eq_false_left h))
      (RigidTy.instantiateList_of_hasSubstParamList_false args ks
        (bool_or_eq_false_right h))
end

mutual
/--
Universal theorem that no `RigidTy` has a substituted parameter under `.nil`.
-/
@[simp]
theorem RigidTy.hasSubstParam_nil :
    (k : RigidTy) → RigidTy.hasSubstParam .nil k = false
  | .param _ _ => rfl
  | .alias _ a => RigidTy.hasSubstParamList_nil a
  | .bool => rfl
  | .char => rfl
  | .int _ => rfl
  | .uint _ => rfl
  | .float _ => rfl
  | .never => rfl
  | .str => rfl
  | .tuple fields => RigidTy.hasSubstParamList_nil fields
  | .array elem _ => RigidTy.hasSubstParam_nil elem
  | .slice elem => RigidTy.hasSubstParam_nil elem
  | .ref _ pointee => RigidTy.hasSubstParam_nil pointee
  | .rawPtr _ pointee => RigidTy.hasSubstParam_nil pointee
  | .adt _ a => RigidTy.hasSubstParamList_nil a
  | .fnDef _ a => RigidTy.hasSubstParamList_nil a
  | .fnPtr inputs output _ _ => by
    dsimp [RigidTy.hasSubstParam]
    rw [RigidTy.hasSubstParamList_nil inputs, RigidTy.hasSubstParam_nil output]
    rfl
  | .closure _ upvars => RigidTy.hasSubstParamList_nil upvars
  | .dynamic _ => rfl
  | .foreign _ => rfl
  | .other _ => rfl

/--
Universal theorem that no list of `RigidTy` has a substituted parameter under
`.nil`.
-/
@[simp]
theorem RigidTy.hasSubstParamList_nil :
    (ks : List RigidTy) → RigidTy.hasSubstParamList .nil ks = false
  | .nil => rfl
  | k :: ks => by
    dsimp [RigidTy.hasSubstParamList]
    rw [RigidTy.hasSubstParam_nil k, RigidTy.hasSubstParamList_nil ks]
    rfl
end

/--
Compute `2^k` in `Init.Core` for scalar valid-range bounds.
-/
@[reducible]
def pow2Nat : Nat → Nat
  | .zero => 1
  | .succ k => Nat.mul 2 (pow2Nat k)

/--
Byte width of a `FloatTy` (`2, 4, 8, 16`).
-/
@[reducible]
def FloatTy.byteWidth : FloatTy → Nat
  | .f16 => 2
  | .f32 => 4
  | .f64 => 8
  | .f128 => 16

mutual
/--
Synthesize or recompute the concrete `TypeLayout` of a `RigidTy` under `args` on
a target with pointer bit-width `ptrBits`, using `origLayout` for variant/field
metadata on ADTs when available.
-/
@[reducible]
def RigidTy.computeLayout
    (ptrBits : Nat)
    (extEntries : List TypeLayout)
    (args : TypeSubst)
    (origLayout : Option TypeLayout) :
    RigidTy → Option TypeLayout
  | .param idx _ =>
    match TypeSubst.lookup args idx with
    | .some (_, l) => .some l
    | .none => origLayout
  | .bool =>
    .some
      { size := ⟨1⟩
        align := ⟨1⟩
        backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .char =>
    .some
      { size := ⟨4⟩
        align := ⟨4⟩
        backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 1114111⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .uint w =>
    let effPtrBits := match Nat.beq ptrBits 0 with | true => 64 | false => ptrBits
    let sz := maxNat 1 (UintTy.byteWidth effPtrBits w)
    let bits := Nat.mul sz 8
    .some
      { size := ⟨sz⟩
        align := ⟨sz⟩
        backendRepr :=
          .scalar (.initialized (.int bits false) ⟨0, Nat.sub (pow2Nat bits) 1⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .int w =>
    let effPtrBits := match Nat.beq ptrBits 0 with | true => 64 | false => ptrBits
    let sz := maxNat 1 (IntTy.byteWidth effPtrBits w)
    let bits := Nat.mul sz 8
    .some
      { size := ⟨sz⟩
        align := ⟨sz⟩
        backendRepr :=
          .scalar (.initialized (.int bits true) ⟨0, Nat.sub (pow2Nat bits) 1⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .float w =>
    let sz := FloatTy.byteWidth w
    let bits := Nat.mul sz 8
    .some
      { size := ⟨sz⟩
        align := ⟨sz⟩
        backendRepr :=
          .scalar (.initialized (.float bits) ⟨0, Nat.sub (pow2Nat bits) 1⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .never =>
    .some
      { size := ⟨0⟩
        align := ⟨1⟩
        backendRepr := .memory
        fields := .primitive
        variants := .empty
        isUninhabited := true }
  | .fnDef _ _ =>
    .some
      { size := ⟨0⟩
        align := ⟨1⟩
        backendRepr := .memory
        fields := .arbitrary .nil .nil
        variants := .single 0
        isUninhabited := false }
  | .fnPtr _ _ _ _ =>
    let effPtrBits := match Nat.beq ptrBits 0 with | true => 64 | false => ptrBits
    let ptrBytes := maxNat 1 (Nat.div effPtrBits 8)
    let maxVal := Nat.sub (pow2Nat (Nat.mul ptrBytes 8)) 1
    .some
      { size := ⟨ptrBytes⟩
        align := ⟨ptrBytes⟩
        backendRepr := .scalar (.initialized (.pointer 0) ⟨1, maxVal⟩)
        fields := .primitive
        variants := .single 0
        isUninhabited := false }
  | .ref _ pointee =>
    let effPtrBits := match Nat.beq ptrBits 0 with | true => 64 | false => ptrBits
    let ptrBytes := maxNat 1 (Nat.div effPtrBits 8)
    let bits := Nat.mul ptrBytes 8
    let maxVal := Nat.sub (pow2Nat bits) 1
    let ptrScalar : ScalarLayout := .initialized (.pointer 0) ⟨1, maxVal⟩
    match RigidTy.instantiate args pointee with
    | .slice _ | .str | .dynamic _ =>
      let metaScalar : ScalarLayout := .initialized (.int bits false) ⟨0, maxVal⟩
      .some
        { size := ⟨Nat.mul ptrBytes 2⟩
          align := ⟨ptrBytes⟩
          backendRepr := .scalarPair ptrScalar metaScalar
          fields := .arbitrary (⟨0⟩ :: ⟨ptrBytes⟩ :: .nil) (0 :: 1 :: .nil)
          variants := .single 0
          isUninhabited := false }
    | _ =>
      .some
        { size := ⟨ptrBytes⟩
          align := ⟨ptrBytes⟩
          backendRepr := .scalar ptrScalar
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
  | .rawPtr _ pointee =>
    let effPtrBits := match Nat.beq ptrBits 0 with | true => 64 | false => ptrBits
    let ptrBytes := maxNat 1 (Nat.div effPtrBits 8)
    let bits := Nat.mul ptrBytes 8
    let maxVal := Nat.sub (pow2Nat bits) 1
    let ptrScalar : ScalarLayout := .initialized (.pointer 0) ⟨0, maxVal⟩
    match RigidTy.instantiate args pointee with
    | .slice _ | .str | .dynamic _ =>
      let metaScalar : ScalarLayout := .initialized (.int bits false) ⟨0, maxVal⟩
      .some
        { size := ⟨Nat.mul ptrBytes 2⟩
          align := ⟨ptrBytes⟩
          backendRepr := .scalarPair ptrScalar metaScalar
          fields := .arbitrary (⟨0⟩ :: ⟨ptrBytes⟩ :: .nil) (0 :: 1 :: .nil)
          variants := .single 0
          isUninhabited := false }
    | _ =>
      .some
        { size := ⟨ptrBytes⟩
          align := ⟨ptrBytes⟩
          backendRepr := .scalar ptrScalar
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
  | .array elem len =>
    match RigidTy.computeLayout ptrBits extEntries args .none elem with
    | .none => origLayout
    | .some elemFl =>
      let eAlign := maxNat 1 elemFl.align.bytes
      let strideBytes := alignUp elemFl.size.bytes eAlign
      .some
        { size := ⟨Nat.mul strideBytes len⟩
          align := ⟨eAlign⟩
          backendRepr := .memory
          fields := .array ⟨strideBytes⟩ len
          variants := .single 0
          isUninhabited :=
            Bool.and (Bool.not (Nat.beq len 0)) elemFl.isUninhabited }
  | .tuple fields =>
    match RigidTy.computeLayoutList ptrBits extEntries args fields with
    | .none => origLayout
    | .some fls =>
      let (offsets, memIdx, totalSz, maxAl, uninh) :=
        computeArbitraryFieldsAux 0 1 0 fls
      .some
        { size := ⟨totalSz⟩
          align := ⟨maxAl⟩
          backendRepr := computeAggregateBackendRepr totalSz fls
          fields := .arbitrary offsets memIdx
          variants := .single 0
          isUninhabited := uninh }
  | .adt _ adtArgs =>
    match origLayout with
    | .some origL =>
      match origL.fieldLayouts with
      | _ :: _ => .some (TypeLayout.recomputeFromFieldLayouts extEntries origL)
      | .nil =>
        match RigidTy.computeLayoutList ptrBits extEntries args adtArgs with
        | .none => .some origL
        | .some fls =>
          match origL.variants with
          | .empty => .some origL
          | .single vIdx =>
            let (offsets, memIdx, totalSz, maxAl, uninh) :=
              computeArbitraryFieldsAux 0 1 0 fls
            .some
              { origL with
                size := ⟨totalSz⟩
                align := ⟨maxAl⟩
                backendRepr := computeAggregateBackendRepr totalSz fls
                fields := .arbitrary offsets memIdx
                variants := .single vIdx
                isUninhabited := uninh }
          | .multiple tag tagField variantShapes =>
            let tagBytes := tagScalarByteWidth tag
            let (shapes', maxSz, maxAl) :=
              recomputeVariantShapesAux tagBytes variantShapes fls
            .some
              { origL with
                size := ⟨alignUp maxSz maxAl⟩
                align := ⟨maxAl⟩
                variants := .multiple tag tagField shapes' }
    | .none =>
      match RigidTy.computeLayoutList ptrBits extEntries args adtArgs with
      | .none => .none
      | .some fls =>
        let (offsets, memIdx, totalSz, maxAl, uninh) :=
          computeArbitraryFieldsAux 0 1 0 fls
        .some
          { size := ⟨totalSz⟩
            align := ⟨maxAl⟩
            backendRepr := computeAggregateBackendRepr totalSz fls
            fields := .arbitrary offsets memIdx
            variants := .single 0
            isUninhabited := uninh }
  | .closure _ upvars =>
    match RigidTy.computeLayoutList ptrBits extEntries args upvars with
    | .none => origLayout
    | .some fls =>
      let (offsets, memIdx, totalSz, maxAl, uninh) :=
        computeArbitraryFieldsAux 0 1 0 fls
      .some
        { size := ⟨totalSz⟩
          align := ⟨maxAl⟩
          backendRepr := computeAggregateBackendRepr totalSz fls
          fields := .arbitrary offsets memIdx
          variants := .single 0
          isUninhabited := uninh }
  | .slice _ => origLayout
  | .str => origLayout
  | .dynamic _ => origLayout
  | .alias _ _ => origLayout
  | .foreign _ => origLayout
  | .other _ => origLayout

/--
Compute concrete `TypeLayout`s for a list of `RigidTy` elements.
-/
@[reducible]
def RigidTy.computeLayoutList
    (ptrBits : Nat)
    (extEntries : List TypeLayout)
    (args : TypeSubst) :
    List RigidTy → Option (List TypeLayout)
  | .nil => .some .nil
  | k :: ks =>
    match
      RigidTy.computeLayout ptrBits extEntries args .none k,
      RigidTy.computeLayoutList ptrBits extEntries args ks
    with
    | .some fl, .some fls => .some (fl :: fls)
    | _, _ => .none
end

/--
Instantiate a `LayoutTable` with `args : TypeSubst`, substituting parametric
placeholder slots, appending the concrete parameter layouts from `args`, and
recomputing dependent `TypeLayout` entries.
-/
@[reducible]
def _root_.Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    LayoutTable :=
  LayoutTable.appendParamLayouts tbl (TypeSubst.layouts args)

/--
Alias for `LayoutTable.instantiate` inside the `MirAst` namespace.
-/
@[reducible]
def LayoutTable.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst) :
    LayoutTable :=
  _root_.Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate tbl args

/--
Universal identity theorem for `LayoutTable.instantiate` on `.nil`.
-/
@[simp]
theorem _root_.Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate_nil
    (tbl : LayoutTable) :
    tbl.instantiate .nil = tbl := by
  exact LayoutTable.appendParamLayouts_nil tbl

/--
Universal identity theorem for `LayoutTable.instantiate` on `.nil` in `MirAst`.
-/
@[simp]
theorem LayoutTable.instantiate_nil (tbl : LayoutTable) :
    LayoutTable.instantiate tbl .nil = tbl := by
  exact LayoutTable.appendParamLayouts_nil tbl

/--
Alias for `LayoutTable.instantiate_nil`.
-/
@[simp]
theorem LayoutTable.instantiate_empty_id (tbl : LayoutTable) :
    LayoutTable.instantiate tbl .nil = tbl :=
  LayoutTable.instantiate_nil tbl

/--
Instantiate a `Ty` by structurally substituting `.param` occurrences in
`ty.kind` and updating `ty.layoutIdx` to the appended layout slot
`tbl.entries.length + idx` when `ty.kind` is `.param idx _` and resolved in
`args`.
-/
@[reducible]
def Ty.instantiate (tbl : LayoutTable) (args : TypeSubst) (ty : Ty) : Ty :=
  let layoutIdx' :=
    match ty.kind with
    | .param idx _ =>
      match TypeSubst.lookup args idx with
      | .some _ => Nat.add (Trusted.Sequence.length tbl.entries) idx
      | .none => ty.layoutIdx
    | _ => ty.layoutIdx
  { kind := RigidTy.instantiate args ty.kind, layoutIdx := layoutIdx' }

/--
Universal identity theorem for `Ty.instantiate` under the empty substitution
`.nil`.
-/
@[simp]
theorem Ty.instantiate_nil (tbl : LayoutTable) (ty : Ty) :
    Ty.instantiate tbl .nil ty = ty := by
  cases ty with
  | mk kind layoutIdx =>
    have hKind : RigidTy.instantiate .nil kind = kind := RigidTy.instantiate_nil kind
    cases kind <;> dsimp [Ty.instantiate, TypeSubst.lookup] <;> rw [hKind]

/--
Alias for `Ty.instantiate_nil`.
-/
@[simp]
theorem Ty.instantiate_empty_id (tbl : LayoutTable) (ty : Ty) :
    Ty.instantiate tbl .nil ty = ty :=
  Ty.instantiate_nil tbl ty

/--
When `RigidTy.hasSubstParam args ty.kind = false`, `Ty.instantiate tbl args ty = ty`.
-/
@[simp]
theorem Ty.instantiate_of_hasSubstParam_false
    (tbl : LayoutTable)
    (args : TypeSubst)
    (ty : Ty)
    (h : RigidTy.hasSubstParam args ty.kind = false) :
    Ty.instantiate tbl args ty = ty := by
  cases ty with
  | mk kind layoutIdx =>
    dsimp at h
    have hKind : RigidTy.instantiate args kind = kind :=
      RigidTy.instantiate_of_hasSubstParam_false args kind h
    dsimp [Ty.instantiate]
    rw [hKind]
    clear hKind
    cases kind with
    | param idx name =>
      dsimp [RigidTy.hasSubstParam] at h ⊢
      cases hLook : TypeSubst.lookup args idx with
      | none => rfl
      | some _ => rw [hLook] at h; cases h
    | _ => rfl

/--
Instantiate a `ConstOperand` by instantiating its `ty` field.
-/
@[reducible]
def ConstOperand.instantiate
    (tbl : LayoutTable)
    (args : TypeSubst)
    (c : ConstOperand) :
    ConstOperand :=
  { c with ty := Ty.instantiate tbl args c.ty }

/--
Universal identity theorem for `ConstOperand.instantiate` on `.nil`.
-/
@[simp]
theorem ConstOperand.instantiate_nil (tbl : LayoutTable) (c : ConstOperand) :
    ConstOperand.instantiate tbl .nil c = c := by
  cases c
  simp [ConstOperand.instantiate]

/--
Instantiate a `TraitRef` by structurally instantiating its `args` type list.
-/
@[reducible]
def TraitRef.instantiate (args : TypeSubst) (tr : TraitRef) : TraitRef :=
  { tr with args := RigidTy.instantiateList args tr.args }

/--
Universal identity theorem for `TraitRef.instantiate` on `.nil`.
-/
@[simp]
theorem TraitRef.instantiate_nil (tr : TraitRef) :
    TraitRef.instantiate .nil tr = tr := by
  cases tr
  simp [TraitRef.instantiate]

/--
Instantiate a `TraitImplEntry` by instantiating its `traitRef`.
-/
@[reducible]
def TraitImplEntry.instantiate
    (args : TypeSubst)
    (e : TraitImplEntry) :
    TraitImplEntry :=
  { e with traitRef := TraitRef.instantiate args e.traitRef }

/--
Structurally instantiate a list of `TraitImplEntry` records.
-/
@[reducible]
def TraitImplEntry.instantiateList
    (args : TypeSubst) :
    List TraitImplEntry → List TraitImplEntry
  | .nil => .nil
  | e :: es =>
    TraitImplEntry.instantiate args e :: TraitImplEntry.instantiateList args es

/--
Universal identity theorem for `TraitImplEntry.instantiate` on `.nil`.
-/
@[simp]
theorem TraitImplEntry.instantiate_nil (e : TraitImplEntry) :
    TraitImplEntry.instantiate .nil e = e := by
  cases e
  simp [TraitImplEntry.instantiate]

/--
Universal identity theorem for `TraitImplEntry.instantiateList` on `.nil`.
-/
@[simp]
theorem TraitImplEntry.instantiateList_nil :
    (es : List TraitImplEntry) →
    TraitImplEntry.instantiateList .nil es = es
  | .nil => rfl
  | e :: es =>
    congrArg2 List.cons
      (TraitImplEntry.instantiate_nil e)
      (TraitImplEntry.instantiateList_nil es)

end Trusted.Rustc.V2026_06_01.MirAst
