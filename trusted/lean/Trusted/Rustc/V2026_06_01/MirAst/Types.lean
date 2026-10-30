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
Structural representation of a monomorphized Rust type after region and
type-parameter erasure, modeling `rustc_middle::ty::TyKind`.

In `Runtime(PostCleanup)` MIR for monomorphic items, type parameters are
instantiated and lifetime regions are erased for codegen. The constructors of
`RigidTy` correspond to the concrete `TyKind` variants that appear in
post-cleanup MIR:
- `.bool`, `.char`, `.int`, `.uint`, `.float`, `.never`, `.str`: primitive and
  textual types (`TyKind::Bool`, `Char`, `Int`, `Uint`, `Float`, `Never`,
  `Str`).
- `.tuple`, `.array`, `.slice`: structural sequence and product types
  (`TyKind::Tuple`, `Array`, `Slice`).
- `.ref`, `.rawPtr`: reference (`&T`, `&mut T`) and raw pointer (`*const T`,
  `*mut T`) types (`TyKind::Ref`, `RawPtr`).
- `.adt`: structs, enums, and unions (`TyKind::Adt`) identified by canonical
  `DefPath` and monomorphized type arguments.
- `.fnDef`, `.fnPtr`, `.closure`: callable types (`TyKind::FnDef`, `FnPtr`,
  `Closure`).
- `.dynamic`, `.foreign`: trait objects (`dyn Trait`, `TyKind::Dynamic`) and
  extern foreign types (`TyKind::Foreign`).
- `.other`: fallback preserving the rendered type string for any remaining
  compiler-internal type so syntax capture is total.

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

end Trusted.Rustc.V2026_06_01.MirAst
