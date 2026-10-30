import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types

namespace Trusted.Rustc.V2026_06_01.MirAst

open Trusted.Rustc.V2026_06_01.Layout

/-!
1-to-1 syntax of `Runtime(PostCleanup)` MIR local indices, field/variant
indices, projections, places, and operands for `rustc 1.98.0-nightly`
(`14210df0e 2026-05-31`, `#99`, `#101`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1334>

> "pub struct Place<'tcx> {
>     pub local: Local,
>
>     /// projection out of a place (access a field, deref a pointer, etc)
>     pub projection: &'tcx List<PlaceElem<'tcx>>,
> }"
-/

/--
0-based index of a MIR local variable, modeling `rustc_middle::mir::Local`.

Index `0` always denotes `RETURN_PLACE` (`_0`), indices `1..=argCount` denote
the function's incoming arguments, and higher indices denote user variables and
compiler-generated temporaries.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L861-L869>

> "rustc_index::newtype_index! {
>     #[derive(HashStable)]
>     #[encodable]
>     #[orderable]
>     #[debug_format = \"_{}\"]
>     pub struct Local {
>         const RETURN_PLACE = 0;
>     }
> }"
-/
abbrev Local : Type := Nat

/--
0-based source-order index of a field in a struct, tuple, union, or enum
variant, modeling `rustc_abi::FieldIdx`.

Reference (`compiler/rustc_abi/src/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/layout.rs#L28-L37>

> "rustc_index::newtype_index! {
>     /// The *source-order* index of a field in a variant.
>     ///
>     /// This is how most code after type checking refers to fields, rather than
>     /// using names (as names have hygiene complications and more complex lookup).
>     ///
>     /// Particularly for `repr(Rust)` types, this may not be the same as *layout* order.
>     /// (It is for `repr(C)` `struct`s, however.) For example, in the following types,
>     /// `FieldIdx::ZERO` is the `a` field, and `FieldIdx::from_u32(1)` is the `b` field,
>     /// even though `rustc` will typically reorder the `bool` after the `u32` in memory:"
-/
abbrev FieldIdx : Type := Nat

/--
0-based source-order index of a variant in an enum or algebraic data type,
modeling `rustc_abi::VariantIdx`.

Reference (`compiler/rustc_abi/src/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/layout.rs#L64-L82>

> "rustc_index::newtype_index! {
>     /// The *source-order* index of a variant in a type.
>     ///
>     /// For enums, this is `(0..variants.len()).map(VariantIdx::from_usize)`.
>     /// Note that the variant's *discriminant* may be different from its
>     /// `VariantIdx`, if it uses explicit discriminants (`enum Foo { A = 42 }`)
>     /// or niche encoding.
>     ///
>     /// Single-variant types (such as structs and tuples, though notably *not*
>     /// single-variant `enum`s) always use `FIRST_VARIANT` (which is `0`).
>     #[derive(HashStable_Generic)]
>     #[encodable]
>     #[orderable]
>     #[debug_format = \"VariantIdx({})\""]
>     pub struct VariantIdx {
>         /// Equivalent to `VariantIdx(0)`.
>         const FIRST_VARIANT = 0;
>     }
> }"
-/
abbrev VariantIdx : Type := Nat

/--
Single step in a MIR place projection path, modeling
`rustc_middle::mir::ProjectionElem` (`PlaceElem`).

Constructors `.deref`, `.field`, `.index`, `.constantIndex`, `.subslice`,
`.downcast`, `.opaqueCast`, and `.unwrapUnsafeBinder` correspond 1-to-1 to the
runtime-relevant variants of `rustc_middle::mir::ProjectionElem` (note that
`Subtype` only appears in analysis MIR prior to `Runtime(PostCleanup)`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L114-L115>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1279>

> "Furthermore, `Deref` projections must be the first projection within any place (if they
> appear at all)"
>
> "pub enum ProjectionElem<V, T> {
>     Deref,
>
>     /// A field (e.g., `f` in `_1.f`) is one variant of [`ProjectionElem`]. Conceptually,
>     /// rustc can identify that a field projection refers to either two different regions of memory
>     /// or the same one between base and projectedmir type.
>     /// Reading from or writing to the projected place reads or writes the subset of bytes of the
>     /// base place described by the layout of the base place's type (adjusted by active
>     /// `Downcast` projection if any).
>     Field(FieldIdx, T),
>
>     /// Index into a slice/array.
>     ...
>     Index(V),
>
>     /// These indices are generated by slice patterns. Easiest to explain
>     /// by example:
>     ///
>     /// ```ignore (illustrative)
>     /// [X, _, .._, _, _] => { offset: 0, min_length: 4, from_end: false },
>     /// [_, X, .._, _, _] => { offset: 1, min_length: 4, from_end: false },
>     /// [_, _, .._, X, _] => { offset: 2, min_length: 4, from_end: true },
>     /// [_, _, .._, _, X] => { offset: 1, min_length: 4, from_end: true },
>     /// ```
>     ConstantIndex {
>         /// index or -index (in Python terms), depending onfrom_end
>         offset: u64,
>         /// The thing being indexed must be at least this long. For arrays this
>         /// is always the exact length.
>         min_length: u64,
>         /// Counting backwards from end? This is always false when indexing an
>         /// array.
>         from_end: bool,
>     },
>
>     /// These indices are generated by slice patterns.
>     ///
>     /// If `from_end` is true `slice[from..slice.len() - to]`.
>     /// Otherwise `array[from..to]`.
>     Subslice {
>         from: u64,
>         to: u64,
>         from_end: bool,
>     },
>
>     /// \"Downcast\" to a variant of an enum or a coroutine.
>     ...
>     Downcast(Option<Symbol>, VariantIdx),
>
>     /// Like an explicit cast from an opaque type to a concrete type, but without
>     /// requiring an intermediate variable.
>     ...
>     OpaqueCast(T),
>
>     /// Unwrap an unsafe binder, i.e. `unsafe<'a> T -> T`.
>     UnwrapUnsafeBinder(T),
> }"
-/
inductive ProjectionElem : Type where
  /-- Dereference a pointer or reference (`*p`). -/
  | deref : ProjectionElem
  /-- Project field `field` (`p.field`) with concrete field type `ty`. -/
  | field (field : FieldIdx) (ty : Ty) : ProjectionElem
  /-- Index into an array or slice by local variable `idx` (`p[_idx]`). -/
  | index (idx : Local) : ProjectionElem
  /-- Constant array/slice index (`offset` from start or end of `minLength`). -/
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool) : ProjectionElem
  /-- Subslice projection `p[from..to]`. -/
  | subslice (fromIdx : Nat) (toIdx : Nat) (fromEnd : Bool) : ProjectionElem
  /-- Downcast an enum place to variant `variant` (`(p as Variant)`). -/
  | downcast (variantName : Option String) (variant : VariantIdx) : ProjectionElem
  /-- Project out of an `OpaqueCast` or subtype wrapper
      (`ProjectionElem::OpaqueCast`). -/
  | opaqueCast (ty : Ty) : ProjectionElem
  /-- Unwrap an unsafe binder (`ProjectionElem::UnwrapUnsafeBinder`). -/
  | unwrapUnsafeBinder (ty : Ty) : ProjectionElem

/--
A memory location rooted at a MIR `Local` followed by zero or more projections,
modeling `rustc_middle::mir::Place`.

Field `local_` corresponds to `Place::local` and `projection` corresponds to
`Place::projection`, applied left-to-right starting from `local_`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1190>

> "pub struct Place<'tcx> {
>     pub local: Local,
>
>     /// projection out of a place (access a field, deref a pointer, etc)
>     pub projection: &'tcx List<PlaceElem<'tcx>>,
> }"

Modeling choice: Because `local` is a reserved keyword in Lean 4, the root local
field is named `local_`.
-/
structure Place : Type where
  /-- Root local variable (`_0`, `_1`, ...). -/
  local_ : Local
  /-- Ordered sequence of projections applied left-to-right to `local_`. -/
  projection : List ProjectionElem

/--
Argument to a MIR rvalue or terminator, modeling `rustc_middle::mir::Operand`.

Constructors `.copy`, `.move`, and `.constant` correspond 1-to-1 to
`Operand::Copy`, `Operand::Move`, and `Operand::Constant`. In `Runtime` MIR,
evaluating `.move` leaves the source `Place` deinitialized (unless its type is
zero-sized), whereas `.copy` preserves the source `Place`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1334>

> "pub enum Operand<'tcx> {
>     /// Creates a value by loading the given place.
>     ///
>     ///Before drop elaboration, the type of the place must be `Copy`. After drop elaboration,
>     /// calling `Copy` on a non-`Copy` type is allowed, and does a bitwise copy without running any
>     /// `Clone` code.
>     Copy(Place<'tcx>),
>
>     /// Creates a value by performing loading the place, just like the `Copy` operand.
>     ///
>     /// Furthermore, in runtime MIR, this marks the place as deinitialized (i.e. writes `uninit` to
>     /// all bytes of the place). In analysis MIR, this acts as a signal to borrowck that the place
>     /// has been moved out of, and thus cannot be used again until it is reinitialized.
>     Move(Place<'tcx>),
>
>     /// Constants are already semantically values, and remain unchanged.
>     Constant(Box<ConstOperand<'tcx>>),
> }"
-/
inductive Operand : Type where
  /-- Copy the value at `place` (`Operand::Copy`). -/
  | copy (place : Place) : Operand
  /-- Move the value out of `place` (`Operand::Move`). -/
  | move (place : Place) : Operand
  /-- Compile-time constant (`Operand::Constant`). -/
  | constant (c : ConstOperand) : Operand

end Trusted.Rustc.V2026_06_01.MirAst
