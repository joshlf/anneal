/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import MiniRustSpec.Interp

/-!
# From Anneal MIR to MiniRust syntax: the program relation

The correspondence theorem relates an Anneal `CapturedMir` body to a MiniRust
`Function`. This module defines that relation as a *translation function*,
`translateFn`, that transcribes upstream MiniRust's own MIR-to-MiniRust
translator, `minimize`. The quoted `minimize` code is vendored (but not
translated) under
`minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/`,
and `crates/anneal-minirust-gen/tests/quotes.rs` checks every quotation
against it. Following `minimize` keeps the program relation on MiniRust's side
of the fence: we do not choose a MiniRust program "that behaves like Anneal";
we choose the program that MiniRust's tooling would produce.

The translation is defined only on the fragment checked by `inFragment`:

* the body is `Runtime(PostCleanup)` MIR and declares the return place, the
  arguments, and any number of temporaries (`argCount + 1 ≤ localDecls.length <
  2^31`); the return place `_0` has scalar fragment type (`Int`, `bool`,
  `core::cmp::Ordering`, or `(Int, bool)` 2-tuple), each temporary
  (`argCount < i`) has scalar fragment type or thin raw pointer type
  (`*const T` / `*mut T` for integer `T`), and each argument local (`1 ≤ i ≤
  argCount`) has scalar fragment type, homogeneous 1D integer array type
  `[T; N]` whose byte size `N * size_of::<T>()` fits in signed 64-bit `isize`
  (`< 2^63`), or well-formed tuple / single-variant struct type (`RigidTy.tuple`
  or `RigidTy.adt`) with explicit layout offsets and padding
  (`FieldsShape.arbitrary`, `VariantsShape.single 0`);
* statements are:
  - scalar assignments `dst = rv` to an integer place `dst` (`_i`, array
    element `_i[proj]`, tuple/struct scalar field chain `_i.f1...fk`, or mutable
    raw pointer dereference `*_p`), where
    `rv` is `Use(a)`, `UnaryOp(uop, a)` (`uop ∈ {Neg, Not}`),
    `BinaryOp(op, a, b)` (`op` among the 15 integer `BinOp` variants, with `b`
    of `dst`'s integer type `it` or of any integer type `rhsIt` for the shift
    operators `Shl, Shr, ShlUnchecked, ShrUnchecked`),
    `Cast(IntToInt, a, targetTy)` (from any integer type `srcIt` or `bool`),
    `Len(_j)` of an array local `_j` (into a `usize` destination), or on root
    destinations `_i = copy/move (*_p)` reading through a thin raw pointer `_p`;
  - thin raw pointer assignments `_i = rv` to a raw pointer local `_i`, where
    `rv` is `Use(copy/move _p)`, `&raw const q` / `&raw mut q` of a parameter
    scalar/array-element/struct-field place `q` (`ptrTargetOk`),
    `Cast(PtrToPtr, copy/move _p, castTy)` preserving pointee integer type and
    not upgrading `*const` to `*mut`, or zero-offset `BinaryOp(Offset,
    copy/move _p, const 0)` (`ptrRvalueOk`), subject to the static non-aliasing
    write discipline `ptrAliasingOk`;
  - `bool`, `Ordering`, and `(it, bool)` 2-tuple assignments `_i = rv` to a root
    local `_i` (`boolNot`, `boolBitOp`, comparisons `Eq | Ne | Lt | Le | Gt | Ge`,
    three-way `Cmp`, `AddWithOverflow | SubWithOverflow | MulWithOverflow`,
    `Aggregate(Tuple, [a, b])`, and `Use(a)`);
  - array assignments `_i = rv` to an unprojected array local `_i : [T; N]`,
    where `rv` is `Use(copy _j)`, `Aggregate(Array(T), [op_0, .., op_{N-1}])`,
    or `Repeat(op, N)` with `N > 0` (or `N = 0` when `op` is a constant);
  - tuple and single-variant struct assignments `dst = rv` to `_i` or a nested
    field chain `_i.f1...fk`, where `rv` is `Use(copy p)` or
    `Aggregate(Tuple | Adt(_, 0, None), [op_0, .., op_{M-1}])`;
  - `PlaceMention(p)` on `_i`, `(it, bool)` fields `_i.0` / `_i.1`, or
    tuple/struct field chains `_i.f1...fk`;
  - `StorageLive(_i)`, `StorageDead(_i)` of a temporary (`argCount < i`), and
    `Deinit(_i)` on scalar-family or thin raw pointer root locals;
* terminators are `Goto`, `SwitchInt` on an integer or `bool` fragment operand,
  `Unreachable`, or `Return`, and every jump target is a block of the body;
* no block is a cleanup block;
* no moved-from local is read before it is re-initialized (`movesOk`), and
  every temporary the body mentions has explicit storage markers
  (`mentionsOk`); see below.

`minimize` has no MiniRust Boolean operator to use: it writes `!b` as a
transmute of `1 - b` back to `bool` (`boolNot`), `a & b` / `a | b` / `a ^ b` as
integer `BitAnd` / `BitOr` / `BitXor` on the `u8` views transmuted back to
`bool` (`boolBitOp`), `b as Int` via `boolToU8` followed by `CastOp::IntToInt`,
and switches on a `bool` through a transmute to `u8` (`boolToU8`). All of these
use `CastOp::Transmute`, which MiniRust evaluates by encoding at the old type
and decoding at the new one (`MiniRustSpec.Interp.transmute`). MIR's three-way
comparison `Cmp` returns `core::cmp::Ordering`, while MiniRust's `RelOp::Cmp`
returns an `i8`; `minimize` transmutes that `i8` to its translation of the
`Ordering` enum (`orderingTy`, `translateCmp`), so an `Ordering` local is a
one-byte `Type::Enum` whose byte must be a valid tag (`-1`, `0`, or `1`).

`Operand::Move` needs care. `minimize` translates it exactly like `Copy`
("smir::Operand::Move(place) => ValueExpr::Load { .. }"), so MiniRust leaves
the moved-from bytes in place, while Anneal's MIR semantics de-initializes a
local that a projection-free `move _j` reads. The two models disagree exactly
on a later read of the moved-from local before it is written again, which
`rustc` itself forbids ("You should not emit MIR that may attempt a
subsequent second load of this place without first re-initializing it",
`Operand::Move` in `compiler/rustc_middle/src/mir/syntax.rs`). The fragment
therefore admits `move` only where a CFG dataflow check, `movesOk`, proves
that no such read happens: entry to `bb0` starts with no moved-out locals
(apart from any propagated along back-edges to `bb0`), a root `move _j` marks
`_j` as moved out, writing `_j` (assignment, `StorageLive`, `StorageDead`, or
`Deinit`) clears the mark, control-flow edges (`Goto` and `SwitchInt`)
propagate moved-out locals to successor blocks (`movedAtEntry`), and no
operand and no `Return` may read a marked local.

`minimize`'s init block allocates every temporary without storage markers
(`rs::always_storage_live_locals`), whereas Anneal starts every temporary
dead (`initLocals`); Anneal's capture
(`trusted/rustc-capture/src/rustc_2026_06_01/mir_lower.rs`) materializes a
`StorageLive` for every such temporary that the body references. The fragment
check `mentionsOk` makes that guarantee explicit: the temporaries that
`initBlock` allocates are never mentioned by a statement or terminator, so
they are dead in Anneal and allocated but untouched in MiniRust until the
frame is torn down.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirSemantics (LocalSlot)
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-- MIR local `_i` as a MiniRust `LocalName`: `minimize` names locals by index,
"let local_name = self.fresh_local_name();" with names `0, 1, ..` in
`local_decls` order. -/
def localName (i : Nat) : Gen.LocalName := ⟨⟨i⟩⟩

/-- MIR block `bbi` as a MiniRust `BbName`: `minimize` names the MIR blocks
`0..n` in index order ("for bb_id in self.body.basic_blocks.indices() {
let bb_name = self.fresh_bb_name(); .. }"). -/
def bbName (i : Nat) : Gen.BbName := ⟨⟨i⟩⟩

/-- Byte size of a MIR integer type on Anneal's pinned target (`x86_64`,
`pointerBits = 64`). -/
def intTyBytes : MirAst.RigidTy → Option (LibSpecr.Signedness × Nat)
  | .uint .u8 => some (.Unsigned, 1)
  | .uint .u16 => some (.Unsigned, 2)
  | .uint .u32 => some (.Unsigned, 4)
  | .uint .u64 => some (.Unsigned, 8)
  | .uint .u128 => some (.Unsigned, 16)
  | .uint .usize => some (.Unsigned, 8)
  | .int .i8 => some (.Signed, 1)
  | .int .i16 => some (.Signed, 2)
  | .int .i32 => some (.Signed, 4)
  | .int .i64 => some (.Signed, 8)
  | .int .i128 => some (.Signed, 16)
  | .int .isize => some (.Signed, 8)
  | _ => none

/-- `minimize`'s type translation for integers (`tooling/minimize/src/ty.rs`):
`rs::TyKind::Int(t)`/`Uint(t)` become `Type::Int(IntType { signed, size })`
with the size from the layout. -/
def intTypeOf (t : MirAst.Ty) : Option Gen.IntType :=
  (intTyBytes t.kind).map (fun (s, n) => ⟨s, ⟨n⟩⟩)

/-- `u8`, as MiniRust's tooling writes it (`<u8>::get_type()`, an unsigned
one-byte `IntType`). `minimize` transmutes a `bool` to `u8` before switching
on it or doing arithmetic on it, and a fragment `bool` local occupies the same
storage as a `u8` local (one byte, alignment one). -/
def u8Ty : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- Whether a MIR type is `bool` (`rs::TyKind::Bool`). -/
def isBoolTy (t : MirAst.Ty) : Bool :=
  match t.kind with
  | .bool => true
  | _ => false

/-- Whether a MIR type is `core::cmp::Ordering`, the result type of MIR's
three-way comparison `BinOp::Cmp` (`self.tcx.ty_ordering_enum(..)` in
`minimize`). Like Anneal's own recognition of `UnsafeCell`, both the `core`
and the `std` path are accepted. -/
def isOrderingTy (t : MirAst.Ty) : Bool :=
  match t.kind with
  | .adt p [] => decide (p = "core::cmp::Ordering") || decide (p = "std::cmp::Ordering")
  | _ => false

/-- The type of the data of each `Ordering` variant. `minimize` gives every
variant of an enum the type `build::tuple_ty(&fields, size, align)` of its
fields, with the size and alignment of the whole enum
(`tooling/minimize/src/enums.rs`):
> "let variant = Variant {
>     ty: build::tuple_ty(
>         &fields.iter().collect::<Vec<_>>(),
>         size,
>         align,
>     ),
>     tagger,
> };"
where `tuple_ty` builds a tuple type with no unsized tail whose sized head
ends at `size` (MiniRust's `tooling/miniutil/src/build/ty.rs`, lines 63-69 at
the pinned commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/ty.rs#L63-L69>):
```rust
pub fn tuple_ty(f: &[(Offset, Type)], size: Size, align: Align) -> Type {
    Type::Tuple {
        sized_fields: f.iter().copied().collect(),
        sized_head_layout: TupleHeadLayout { end: size, align, packed_align: None },
        unsized_field: GcCow::new(None),
    }
}
```
`Ordering`'s variants have no fields, and the enum has size and alignment 1
(see `orderingTy`). -/
def orderingVariantTy : Gen.Type := .Tuple [] ⟨⟨1⟩, ⟨1⟩, none⟩ none

/-- `minimize`'s translation of `core::cmp::Ordering`. In `core`
(`library/core/src/cmp.rs`, lines 403-415 at Rust 1.98.0,
<https://github.com/rust-lang/rust/blob/1.98.0/library/core/src/cmp.rs#L403-L415>,
doc comments and stability attributes elided):
```rust
#[lang = "Ordering"]
#[repr(i8)]
pub enum Ordering {
    Less = -1,
    Equal = 0,
    Greater = 1,
}
```
so rustc lays it out with size and alignment 1 and a directly encoded `i8`
tag at offset 0 (`TagEncoding::Direct`), and its discriminant type is `i8`.
For such a layout, `translate_enum` (`tooling/minimize/src/enums.rs`) tags
every variant with its own discriminant and branches on the tag, rejecting
every other tag value:
> "rs::TagEncoding::Direct => {
>     // direct tagging places the discriminant in the tag for all variants
>     let tagger = [(tag_offset, (tag_ty, discr_int))]
>         .into_iter()
>         .collect::<Map<Offset, (IntType, Int)>>();
>     ..
>     translated_variants.insert(discr_int, variant);
>     discriminator_branches.insert(
>         (discr_int, discr_int + Int::ONE),
>         Discriminator::Known(discr_int),
>     );
> }"
> "rs::TagEncoding::Direct => GcCow::new(Discriminator::Invalid),"
> "let discriminator = Discriminator::Branch {
>     offset: tag_offset,
>     value_type: tag_ty,
>     fallback,
>     children: discriminator_branches,
> };"
> "Type::Enum { variants, discriminator, discriminant_ty, size, align }"
-/
def orderingTy : Gen.Type :=
  .Enum ⟨[(-1, ⟨orderingVariantTy, ⟨[(⟨0⟩, (IntType.I8, -1))]⟩⟩),
          (0, ⟨orderingVariantTy, ⟨[(⟨0⟩, (IntType.I8, 0))]⟩⟩),
          (1, ⟨orderingVariantTy, ⟨[(⟨0⟩, (IntType.I8, 1))]⟩⟩)]⟩
    IntType.I8
    (.Branch ⟨0⟩ IntType.I8 .Invalid
      ⟨[((-1, 0), .Known (-1)), ((0, 1), .Known 0), ((1, 2), .Known 1)]⟩)
    ⟨1⟩ ⟨1⟩

/-- Whether a MIR type is a 2-tuple `(Int, bool)` (`rs::TyKind::Tuple` of an
integer type and `bool`), returning the integer type of field 0. -/
def intBoolTupleOf (t : MirAst.Ty) : Option Gen.IntType :=
  match t.kind with
  | .tuple [t0, .bool] => (intTyBytes t0).map (fun (s, n) => ⟨s, ⟨n⟩⟩)
  | _ => none

/-- `minimize`'s translation of a 2-tuple `(Int, bool)` where field 0 has
integer type `it` (`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Tuple(..) => {
>      let layout = self.rs_layout_of(ty);
>      self.tuple_from_layout(layout, span)
>  }"
with `tuple_from_layout` (`tooling/minimize/src/ty.rs`):
> "fn tuple_from_layout(&mut self, layout: rs::TyAndLayout<'tcx>, span: rs::Span) -> Type {
>      let size = translate_size(layout.size);
>      let align = translate_align(layout.align.abi);
>      let fields: Vec<(Size, Type)> = (0..layout.fields.count())
>          .map(|i| {
>              let ty = layout.field(self, i).ty;
>              let ty = self.translate_ty(ty, span);
>              let offset = layout.fields.offset(i);
>              let offset = translate_size(offset);
>              (offset, ty)
>          })
>          .collect();
>      build::tuple_ty(&fields, size, align)
>  }"
For `(it, bool)` on `x86_64`, field 0 (`Type::Int(it)`) is at offset `0`,
field 1 (`Type::Bool`) is at offset `it.size`, the overall alignment is
`it.size.bytes` (a power of two), and the overall size is rounded up to the
alignment (`2 * it.size.bytes`), matching `IntType::with_overflow`
(`MiniRustSpec.Interp.IntType.with_overflow`). -/
def intBoolTupleTy (it : Gen.IntType) : Gen.Type :=
  .Tuple [(⟨0⟩, .Int it), (it.size, .Bool)] ⟨⟨it.size.bytes + it.size.bytes⟩, ⟨it.size.bytes⟩, none⟩ none

/-- `minimize`'s type translation for the fragment's types
(`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Bool => Type::Bool,
>  rs::TyKind::Int(t) => {
>      let sz = rs::abi::Integer::from_int_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Signed })
>  }
>  rs::TyKind::Uint(t) => {
>      let sz = rs::abi::Integer::from_uint_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Unsigned })
>  }"
`core::cmp::Ordering`, whose translation is `orderingTy`, and 2-tuples
`(Int, bool)`, whose translation is `intBoolTupleTy`. -/
def scalarTypeOf (t : MirAst.Ty) : Option Gen.Type :=
  if isBoolTy t then some .Bool
  else if isOrderingTy t then some orderingTy
  else
    match intBoolTupleOf t with
    | some it => some (intBoolTupleTy it)
    | none => (intTypeOf t).map .Int

/-- MiniRust `usize` integer type on `x86_64` (`Unsigned`, 8 bytes). -/
def usizeIt : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩

/-- Element integer type and length of a homogeneous 1D array type `[T; N]`. -/
def arrayTypeOf (t : MirAst.Ty) : Option (Gen.IntType × Nat) :=
  match t.kind with
  | .array elemKind count =>
    (intTyBytes elemKind).map (fun (s, n) => (⟨s, ⟨n⟩⟩, count))
  | _ => none

/-- Whether `n` is a valid scalar/tuple alignment in bytes on `x86_64`
(`1, 2, 4, 8, 16`). -/
def goodAlignBytes (n : Nat) : Bool :=
  decide (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16)

/-- Structural descriptor of a scalar integer or a (possibly nested) padded
tuple or single-variant struct type in the correspondence fragment. -/
inductive TupleSpec : Type where
  | scalar (it : Gen.IntType) : TupleSpec
  | tuple (fields : List (Nat × TupleSpec)) (size : Nat) (align : Nat) : TupleSpec

mutual

/-- Boolean equality on `TupleSpec`. -/
def TupleSpec.beq : TupleSpec → TupleSpec → Bool
  | .scalar it1, .scalar it2 => decide (it1 = it2)
  | .tuple fs1 sz1 al1, .tuple fs2 sz2 al2 =>
    decide (sz1 = sz2) && decide (al1 = al2) && TupleSpec.fieldsBeq fs1 fs2
  | _, _ => false

/-- Pointwise Boolean equality on `List (Nat × TupleSpec)`. -/
def TupleSpec.fieldsBeq : List (Nat × TupleSpec) → List (Nat × TupleSpec) → Bool
  | [], [] => true
  | (o1, s1) :: r1, (o2, s2) :: r2 =>
    decide (o1 = o2) && s1.beq s2 && TupleSpec.fieldsBeq r1 r2
  | _, _ => false

end

mutual

theorem TupleSpec.beq_iff : ∀ (a b : TupleSpec), a.beq b = true ↔ a = b
  | .scalar it1, .scalar it2 => by simp [TupleSpec.beq]
  | .scalar _, .tuple _ _ _ => by simp [TupleSpec.beq]
  | .tuple _ _ _, .scalar _ => by simp [TupleSpec.beq]
  | .tuple fs1 sz1 al1, .tuple fs2 sz2 al2 => by
    simp only [TupleSpec.beq, Bool.and_eq_true, decide_eq_true_eq,
      TupleSpec.fieldsBeq_iff, TupleSpec.tuple.injEq]
    exact ⟨fun ⟨⟨hsz, hal⟩, hfs⟩ => ⟨hfs, hsz, hal⟩, fun ⟨hfs, hsz, hal⟩ => ⟨⟨hsz, hal⟩, hfs⟩⟩

theorem TupleSpec.fieldsBeq_iff :
    ∀ (xs ys : List (Nat × TupleSpec)), TupleSpec.fieldsBeq xs ys = true ↔ xs = ys
  | [], [] => by simp [TupleSpec.fieldsBeq]
  | [], _ :: _ => by simp [TupleSpec.fieldsBeq]
  | _ :: _, [] => by simp [TupleSpec.fieldsBeq]
  | (o1, s1) :: r1, (o2, s2) :: r2 => by
    simp [TupleSpec.fieldsBeq, TupleSpec.beq_iff, TupleSpec.fieldsBeq_iff, and_assoc]

end

instance : DecidableEq TupleSpec := fun a b =>
  if h : a.beq b = true then isTrue ((TupleSpec.beq_iff a b).mp h)
  else isFalse (fun heq => h ((TupleSpec.beq_iff a b).mpr heq))

/-- Byte size of a `TupleSpec`. -/
def TupleSpec.size : TupleSpec → Nat
  | .scalar it => it.size.bytes
  | .tuple _ size _ => size

/-- Alignment in bytes of a `TupleSpec`. -/
def TupleSpec.align : TupleSpec → Nat
  | .scalar it => it.size.bytes
  | .tuple _ _ align => align

mutual

/-- Lower a `TupleSpec` to a MiniRust `Gen.Type`:
`build::tuple_ty(&fields, size, align)` (`tooling/minimize/src/ty.rs`) builds
`Type::Tuple { sized_fields, sized_head_layout: TupleHeadLayout { end: size, align, packed_align: None }, unsized_field: None }`. -/
def TupleSpec.toMiniRustTy : TupleSpec → Gen.Type
  | .scalar it => .Int it
  | .tuple fields size align =>
    .Tuple (TupleSpec.fieldsToMiniRust fields)
      { «end» := ⟨size⟩, align := ⟨align⟩, packed_align := none } none

/-- Lower a list of `(offset, TupleSpec)` fields to MiniRust `Fields`. -/
def TupleSpec.fieldsToMiniRust : List (Nat × TupleSpec) → List (Gen.Offset × Gen.Type)
  | [] => []
  | (off, s) :: rest => (⟨off⟩, s.toMiniRustTy) :: TupleSpec.fieldsToMiniRust rest

end

mutual

/-- Well-formedness of a `TupleSpec`: valid alignment in `{1, 2, 4, 8, 16}`,
`size` a multiple of `align` fitting in signed 64-bit `isize` (`< 2^63`), and
pairwise non-overlapping aligned fields within `[0, size)`. -/
def TupleSpec.wf : TupleSpec → Bool
  | .scalar it => goodAlignBytes it.size.bytes
  | .tuple fields size align =>
    goodAlignBytes align &&
    decide (size % align = 0) &&
    decide (size < 2 ^ 63) &&
    TupleSpec.fieldsWf size align fields

/-- Well-formedness of the fields of a tuple/struct of given `size` and `align`. -/
def TupleSpec.fieldsWf (size align : Nat) : List (Nat × TupleSpec) → Bool
  | [] => true
  | (off, s) :: rest =>
    s.wf &&
    decide (off + s.size ≤ size) &&
    decide (off % s.align = 0) &&
    decide (s.align ≤ align) &&
    rest.all (fun p => decide (off + s.size ≤ p.1 ∨ p.1 + p.2.size ≤ off)) &&
    TupleSpec.fieldsWf size align rest

end

mutual

/-- `minimize`'s tuple and struct layout extraction (`tooling/minimize/src/ty.rs`):
> "fn tuple_from_layout(&mut self, layout: rs::TyAndLayout<'tcx>, span: rs::Span) -> Type {
>      let size = translate_size(layout.size);
>      let align = translate_align(layout.align.abi);
>
>      let fields: Vec<(Size, Type)> = (0..layout.fields.count())
>          .map(|i| {
>              let ty = layout.field(self, i).ty;
>              let ty = self.translate_ty(ty, span);
>              let offset = layout.fields.offset(i);
>              let offset = translate_size(offset);
>              (offset, ty)
>          })
>          .collect();
>
>      build::tuple_ty(&fields, size, align)
>  }
>  ..
>  fn translate_non_enum_adt(
>      &mut self,
>      ty: rs::Ty<'tcx>,
>      adt_def: rs::AdtDef<'tcx>,
>      sref: rs::GenericArgsRef<'tcx>,
>      span: rs::Span,
>  ) -> (Fields, Size, Align) {
>      let layout = self.rs_layout_of(ty).layout;
>      let fields = self.translate_adt_variant_fields(
>          Some(layout.fields()),
>          adt_def.non_enum_variant(),
>          sref,
>          span,
>      );
>      let size = translate_size(layout.size());
>      let align = translate_align(layout.align().abi);
>
>      (fields, size, align)
>  }" -/
def specOfRigidTy (layouts : Layout.LayoutTable) : MirAst.RigidTy → Nat → Option TupleSpec
  | .uint w, _ => (intTyBytes (.uint w)).map (fun (s, n) => .scalar ⟨s, ⟨n⟩⟩)
  | .int w, _ => (intTyBytes (.int w)).map (fun (s, n) => .scalar ⟨s, ⟨n⟩⟩)
  | .tuple fieldKinds, layoutIdx => do
    let l ← Layout.LayoutTable.lookup layouts layoutIdx
    match l.variants, l.isUninhabited, l.fields with
    | .single 0, false, .arbitrary offsets _ =>
      if offsets.length = fieldKinds.length then do
        let fields ← specOfFieldList layouts offsets fieldKinds l.fieldLayouts
        pure (.tuple fields l.size.bytes l.align.bytes)
      else none
    | _, _, _ => none
  | .adt _ fieldKinds, layoutIdx => do
    let l ← Layout.LayoutTable.lookup layouts layoutIdx
    match l.variants, l.isUninhabited, l.fields with
    | .single 0, false, .arbitrary offsets _ =>
      if offsets.length = fieldKinds.length then do
        let fields ← specOfFieldList layouts offsets fieldKinds l.fieldLayouts
        pure (.tuple fields l.size.bytes l.align.bytes)
      else none
    | _, _, _ => none
  | _, _ => none

/-- Extract the `(offset, TupleSpec)` list for each field of a tuple or
single-variant struct in source field order. -/
def specOfFieldList (layouts : Layout.LayoutTable) :
    List Layout.Size → List MirAst.RigidTy → List Nat → Option (List (Nat × TupleSpec))
  | [], [], _ => some []
  | off :: offs, fk :: fks, fls => do
    let fIdx := fls.head?.getD 0
    let fSpec ← specOfRigidTy layouts fk fIdx
    let rest ← specOfFieldList layouts offs fks (fls.tailD [])
    pure ((off.bytes, fSpec) :: rest)
  | _, _, _ => none

end

/-- Extract the `(fields, size, align)` tuple/struct descriptor of `t` when `t`
is a tuple (`RigidTy.tuple`) or single-variant struct (`RigidTy.adt`) outside
`scalarTypeOf` (`core::cmp::Ordering` and `(Int, bool)` 2-tuples are handled by
`scalarTypeOf`). -/
def tupleTypeOf (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (t : MirAst.Ty) :
    Option (List (Nat × TupleSpec) × Nat × Nat) :=
  if isOrderingTy t || (intBoolTupleOf t).isSome then none
  else
    match t.kind with
    | .tuple _ | .adt _ _ =>
      match specOfRigidTy layouts t.kind t.layoutIdx with
      | some (.tuple fields size align) => some (fields, size, align)
      | _ => none
    | _ => none

/-- The metadata kind of a raw pointer to `pointee`, as `minimize` computes it
from the pointee's layout (`pointee_info_of(..).layout.meta_kind()`): no
metadata (`PointerMetaKind::None`) for sized pointees, and an element count
(`PointerMetaKind::ElementCount`) for slices and `str`. Unsized trait objects
and extern foreign types are outside the translation. -/
def rawPtrMetaKind : MirAst.RigidTy → Option Gen.PointerMetaKind
  | .bool | .char | .int _ | .uint _ | .float _ | .never
  | .tuple _ | .array _ _ | .ref _ _ | .rawPtr _ _ | .adt _ _
  | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _ => some .None
  | .slice _ | .str => some .ElementCount
  | .dynamic _ | .foreign _ | .other _ => none

/-- Metadata kind of a raw pointer `MirAst.Ty` (`rawPtrMetaKind`). -/
def rawPtrMetaOf (t : MirAst.Ty) : Option Gen.PointerMetaKind :=
  match t.kind with
  | .rawPtr _ pointee => rawPtrMetaKind pointee
  | _ => none

/-- `minimize`'s translation of raw pointer types `*const T` and `*mut T`
(`tooling/minimize/src/ty.rs`), which records only the pointee's metadata
kind (`rawPtrMetaKind`):
> "rs::TyKind::RawPtr(ty, _mutbl) => {
>     let pointee = self.pointee_info_of(*ty, span);
>     Type::Ptr(PtrType::Raw { meta_kind: pointee.layout.meta_kind() })
> }" -/
def rawPtrTypeOf (t : MirAst.Ty) : Option Gen.Type :=
  (rawPtrMetaOf t).map (fun k => .Ptr (.Raw k))

/-- `minimize`'s type translation across the fragment (`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Bool => Type::Bool,
>  rs::TyKind::Int(t) => {
>      let sz = rs::abi::Integer::from_int_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Signed })
>  }
>  rs::TyKind::Uint(t) => {
>      let sz = rs::abi::Integer::from_uint_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Unsigned })
>  }
>  ..
>  rs::TyKind::Tuple(..) => {
>      let layout = self.rs_layout_of(ty);
>      self.tuple_from_layout(layout, span)
>  }
>  ..
>  rs::TyKind::Adt(adt_def, sref) if adt_def.is_struct() => {
>      let (fields, size, align) = self.translate_non_enum_adt(ty, *adt_def, sref, span);
>      build::tuple_ty(&fields.iter().collect::<Vec<_>>(), size, align)
>  }
>  ..
>  rs::TyKind::Array(ty, c) => {
>      let count = Int::from(c.try_to_target_usize(self.tcx).unwrap());
>      let elem = GcCow::new(self.translate_ty(*ty, span));
>      Type::Array { elem, count }
>  }" -/
def translateTy (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (t : MirAst.Ty) :
    Option Gen.Type :=
  match scalarTypeOf t with
  | some ty => some ty
  | none =>
    match arrayTypeOf t with
    | some (elemIt, count) => some (.Array (.Int elemIt) (Int.ofNat count))
    | none =>
      match tupleTypeOf layouts t with
      | some (fields, size, align) =>
        some ((TupleSpec.tuple fields size align).toMiniRustTy)
      | none => rawPtrTypeOf t

instance : DecidableEq MirAst.Mutability
  | .not, .not => isTrue rfl
  | .mut, .mut => isTrue rfl
  | .not, .mut => isFalse (by intro h; cases h)
  | .mut, .not => isFalse (by intro h; cases h)

/-- The pointee integer type of a thin raw pointer type `*const T` or `*mut T`
whose pointee `T` is an integer type, with the pointer's mutability. The
correspondence fragment admits raw pointers only to integer pointees (see
`ptrDeclOk`). -/
def ptrPointeeOf (t : MirAst.Ty) : Option (MirAst.Mutability × Gen.IntType) :=
  match t.kind with
  | .rawPtr mutbl pointee => (intTyBytes pointee).map (fun (s, n) => (mutbl, ⟨s, ⟨n⟩⟩))
  | _ => none

/-- Whether a MIR type is a thin raw pointer to an integer (`ptrPointeeOf`). -/
def isPtrTy (t : MirAst.Ty) : Bool := (ptrPointeeOf t).isSome

/-- The MiniRust type of a thin raw pointer: `rawPtrTypeOf` of a pointer to a
sized pointee, `Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })`. -/
def thinRawPtrTy : Gen.Type := .Ptr (.Raw .None)

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- Translation of a `RigidTy` pointee without needing a layout-table entry:
`bool`, integers, `core::cmp::Ordering`, `(Int, bool)` 2-tuples, homogeneous 1D
integer arrays `[Int; N]`, and nested raw pointers `*const U` / `*mut U`. -/
def translatePointeeRigidTy : MirAst.RigidTy → Option Gen.Type
  | .bool => some .Bool
  | .adt "core::cmp::Ordering" [] => some orderingTy
  | .tuple [elem, .bool] => (intTyBytes elem).map (fun (s, n) => intBoolTupleTy ⟨s, ⟨n⟩⟩)
  | .array elem count =>
    (intTyBytes elem).map (fun (s, n) => .Array (.Int ⟨s, ⟨n⟩⟩) (Int.ofNat count))
  | .rawPtr _ inner => (rawPtrMetaKind inner).map (fun k => .Ptr (.Raw k))
  | pointee => (intTyBytes pointee).map (fun (s, n) => .Int ⟨s, ⟨n⟩⟩)

/-- The translation of the pointee type of a raw pointer type, the type at
which `minimize` dereferences it (`translate_ty_smir(this_ty, ..)` in
`translatePlace`). -/
def derefPointeeTy (t : MirAst.Ty) : Option Gen.Type :=
  match t.kind with
  | .rawPtr _ pointee => translatePointeeRigidTy pointee
  | _ => none

/-- Left-to-right fold translating a chain of `ProjectionElem.field` projections
into nested `PlaceExpr.Field` expressions (`tooling/minimize/src/rvalue.rs`):
> "smir::ProjectionElem::Field(f, _ty) => {
>      let indirected = GcCow::new(expr);
>      PlaceExpr::Field { root: indirected, field: (*f).into() }
>  }" -/
def translateFieldPlace (root : Gen.PlaceExpr) :
    List MirAst.ProjectionElem → Option Gen.PlaceExpr
  | [] => some root
  | .field idx _ :: rest => translateFieldPlace (.Field root (idx : Int)) rest
  | _ => none

/-- `minimize`'s place translation for locals, field projections, array
indexing, and dereferences of raw pointers (`tooling/minimize/src/rvalue.rs`):
> "let expr = PlaceExpr::Local(self.local_name_map[&place.local.into()]);
>  let place_ty = self.locals_smir[place.local].ty;
>  // Fold over all projections
>  let (expr, _place_ty) =
>      place.projection.iter().fold((expr, place_ty), |(expr, place_ty), proj| {
>          let this_ty = proj.ty(place_ty).unwrap();
>          let this_expr = match proj {
>              smir::ProjectionElem::Field(f, _ty) => {
>                  let indirected = GcCow::new(expr);
>                  PlaceExpr::Field { root: indirected, field: (*f).into() }
>              }
>              smir::ProjectionElem::Deref => {
>                  let x = GcCow::new(expr);
>                  let x = ValueExpr::Load { source: x };
>                  let x = GcCow::new(x);
>
>                  let ty = self.translate_ty_smir(this_ty, span);
>
>                  PlaceExpr::Deref { operand: x, ty }
>              }
>              smir::ProjectionElem::Index(loc) => {
>                  let i = PlaceExpr::Local(self.local_name_map[&(*loc).into()]);
>                  let i = GcCow::new(i);
>                  let i = ValueExpr::Load { source: i };
>                  let i = GcCow::new(i);
>                  let root = GcCow::new(expr);
>                  PlaceExpr::Index { root, index: i }
>              }
>              ..
>              smir::ProjectionElem::ConstantIndex { .. }
>              | smir::ProjectionElem::Subslice { .. }
>              | smir::ProjectionElem::OpaqueCast(_) => {
>                  rs::span_bug!(span, \"Place Projection not supported: {:?}\", proj);
>              }"
Upstream `minimize` rejects `ProjectionElem::ConstantIndex`, so its lowering
here is an extension rather than a transcription: for
`ConstantIndex { offset, min_length, from_end }` on a fixed-size array
`[T; count]`, the index that MIR defines for the projection (`count - offset`
when `from_end` is true, or `offset` when `from_end` is false) becomes a
`usize` constant index expression of `PlaceExpr::Index`. A dereference
`*_j` (optionally followed by field projections `(*_j).f1...fk`) loads the
pointer local and dereferences it at the translation of the pointee type
`this_ty` (`derefPointeeTy`). -/
def translatePlace (decls : List MirAst.LocalDecl := []) : MirAst.Place → Option Gen.PlaceExpr
  | ⟨i, []⟩ => some (.Local (localName i))
  | ⟨i, .deref :: rest⟩ => do
    let d ← decls[i]?
    let ty ← derefPointeeTy d.ty
    translateFieldPlace (.Deref (.Load (.Local (localName i))) ty) rest
  | ⟨i, [.index idxLocal]⟩ =>
    some (.Index (.Local (localName i)) (.Load (.Local (localName idxLocal))))
  | ⟨i, [.constantIndex offset minLen fromEnd]⟩ =>
    match decls[i]? >>= (arrayTypeOf ·.ty) with
    | some (_, count) =>
      if minLen ≤ count ∧ (!fromEnd || (1 ≤ offset ∧ offset ≤ count)) then
        let idx := if fromEnd then count - offset else offset
        some (.Index (.Local (localName i)) (.Constant (.Int (Int.ofNat idx)) (.Int usizeIt)))
      else none
    | none => none
  | ⟨i, .field idx fieldTy :: rest⟩ =>
    translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest)
  | _ => none

/-- Follow a chain of `ProjectionElem.field` projections from `spec`, verifying
at each step that the projection's `fieldTy` translates to the selected field's
`TupleSpec`, and returning the accumulated byte offset and leaf `TupleSpec`. -/
def resolveFieldPath (layouts : Layout.LayoutTable) :
    TupleSpec → List MirAst.ProjectionElem → Option (Nat × TupleSpec)
  | spec, [] => some (0, spec)
  | .tuple fields _ _, .field idx fieldTy :: rest => do
    let (off, subSpec) ← fields[idx]?
    let expectedSpec ← specOfRigidTy layouts fieldTy.kind fieldTy.layoutIdx
    if subSpec = expectedSpec then do
      let (restOff, leafSpec) ← resolveFieldPath layouts subSpec rest
      pure (off + restOff, leafSpec)
    else none
  | _, _ => none

/-- Resolve the `MirAst.Ty` of a chain of `.field` projections from `baseTy`. -/
def resolveProjTy (baseTy : MirAst.Ty) : List MirAst.ProjectionElem → Option MirAst.Ty
  | [] => some baseTy
  | .field _ fieldTy :: rest => resolveProjTy fieldTy rest
  | _ => none

/-- Resolve the `MirAst.Ty` of a local or field-projected place. -/
def placeMirTy (decls : List MirAst.LocalDecl) (p : MirAst.Place) : Option MirAst.Ty := do
  let d ← decls[p.local_]?
  resolveProjTy d.ty p.projection

/-- Scalar integer type of a place (`_j`, `(it, bool)` field `_j.0`, `_j[idx]` /
`_j[constIdx]`, or `TupleSpec` scalar field chain `_j.f1...fk`). -/
def placeIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Place → Option Gen.IntType
  | ⟨j, []⟩ => decls[j]? >>= fun d => intTypeOf d.ty
  | ⟨j, [.index _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | ⟨j, [.constantIndex _ _ _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | ⟨j, .field idx fieldTy :: rest⟩ => do
    let d ← decls[j]?
    match intBoolTupleOf d.ty with
    | some it =>
      match idx, rest with
      | 0, [] =>
        let fIt ← intTypeOf fieldTy
        if fIt == it then some it else none
      | _, _ => none
    | none =>
      let (fields, size, align) ← tupleTypeOf layouts d.ty
      let (_, leafSpec) ←
        resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest)
      match leafSpec with
      | .scalar it => some it
      | .tuple _ _ _ => none
  | _ => none

/-- Integer type of a fragment operand: `copy p` has `p`'s resolved integer
type (`placeIntType`), and a constant carries its type. A `move` operand is
checked through `copyOp`. -/
def operandIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy p => placeIntType layouts decls p
  | .constant c => intTypeOf c.ty
  | _ => none

/-- MiniRust type of a fragment scalar-family operand (including `copy (_j.0)`
and `copy (_j.1)` on an `(it, bool)` local, array element projections, and
tuple/struct scalar field projections). -/
def operandType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.Type
  | .copy ⟨j, []⟩ => decls[j]? >>= fun d => scalarTypeOf d.ty
  | .copy ⟨j, [.field 1 fTy]⟩ =>
    match decls[j]? >>= fun d => intBoolTupleOf d.ty with
    | some _ => if isBoolTy fTy then some .Bool else none
    | none => (placeIntType layouts decls ⟨j, [.field 1 fTy]⟩).map .Int
  | .copy p => (placeIntType layouts decls p).map .Int
  | .constant c => scalarTypeOf c.ty
  | _ => none

/-- `minimize`'s operand translation (`tooling/minimize/src/rvalue.rs`):
> "smir::Operand::Constant(c) => self.translate_const_smir(&c.const_, span),
>  smir::Operand::Copy(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },
>  smir::Operand::Move(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },"
for places in the fragment (`PlaceExpr::Local`, `PlaceExpr::Field`, and
`PlaceExpr::Index`, see `translatePlace`) and scalar constants. For an integer
constant, `translate_const_val` (`tooling/minimize/src/constant.rs`) reads the
scalar at the constant's type, which is `Constant::Int(int_from_bits(..))`; for
a `bool` constant it reads a `bool`, which rustc's `Scalar::to_bool` accepts
only for the one-byte patterns `0` and `1`:
> "Type::Bool => {
>      let val = ecx.read_scalar(&val).unwrap().to_bool().unwrap();
>      ValueExpr::Constant(Constant::Bool(val), ty)
>  }" (`tooling/minimize/src/constant.rs`) -/
def translateOperand (decls : List MirAst.LocalDecl := []) : MirAst.Operand → Option Gen.ValueExpr
  | .copy p | .move p => (translatePlace decls p).map .Load
  | .constant c =>
    if isBoolTy c.ty then
      match c.val with
      | .scalar (.int ⟨bits, sz⟩) =>
        if sz = 1 ∧ bits < 2 then some (.Constant (.Bool (decide (bits = 1))) .Bool) else none
      | _ => none
    else
      match c.val, intTypeOf c.ty with
      | .scalar (.int ⟨bits, sz⟩), some it =>
        if sz = it.size.bytes ∧ bits < 2 ^ (8 * sz) then
          some (.Constant (.Int (intFromBits bits it)) (.Int it))
        else none
      | _, _ => none

/-- An operand with `move` replaced by `copy`. `minimize` translates the two
alike (`translateOperand`), and the type of `move p` is the type of `p`, just
as for `copy p` (`Operand::ty`), so every type-directed check and every
translation below inspects `copyOp op`. -/
def copyOp : MirAst.Operand → MirAst.Operand
  | .move p => .copy p
  | op => op

/-- An rvalue with every `move` operand replaced by `copy` (see `copyOp`). -/
def copyRv : MirAst.Rvalue → MirAst.Rvalue
  | .use op => .use (copyOp op)
  | .repeat op c => .repeat (copyOp op) c
  | .unaryOp uop op => .unaryOp uop (copyOp op)
  | .binaryOp bop a b => .binaryOp bop (copyOp a) (copyOp b)
  | .cast k op ty => .cast k (copyOp op) ty
  | .aggregate k ops => .aggregate k (ops.map copyOp)
  | rv => rv

theorem translateOperand_copyOp (decls : List MirAst.LocalDecl) (op : MirAst.Operand) :
    translateOperand decls (copyOp op) = translateOperand decls op := by
  cases op <;> rfl

/-- `minimize`'s unary-operator translation for integer operands
(`tooling/minimize/src/rvalue.rs`):
> "(Neg, Type::Int(_)) => build::neg(operand),
>  (Not, Type::Int(_)) => build::bit_not(operand),"
where `build::neg(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::Neg), operand: x }`
and `build::bit_not(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::BitNot), operand: x }`. -/
def translateUnOp : MirAst.UnOp → Option Gen.IntUnOp
  | .neg => some .Neg
  | .not => some .BitNot
  | _ => none

/-- `minimize`'s binary-operator translation for integer operands
(`tooling/minimize/src/rvalue.rs`):
> "(Add, Type::Int(_)) => build::add(l, r),
>  (Sub, Type::Int(_)) => build::sub(l, r),
>  (Mul, Type::Int(_)) => build::mul(l, r),
>  (Div, Type::Int(_)) => build::div(l, r),
>  (Rem, Type::Int(_)) => build::rem(l, r),
>  (Shl, Type::Int(_)) => build::shl(l, r),
>  (Shr, Type::Int(_)) => build::shr(l, r),
>  (BitAnd, Type::Int(_)) => build::bit_and(l, r),
>  (BitOr, Type::Int(_)) => build::bit_or(l, r),
>  (BitXor, Type::Int(_)) => build::bit_xor(l, r),
>  (AddUnchecked, Type::Int(_)) => build::add_unchecked(l, r),
>  (SubUnchecked, Type::Int(_)) => build::sub_unchecked(l, r),
>  (MulUnchecked, Type::Int(_)) => build::mul_unchecked(l, r),
>  (ShlUnchecked, Type::Int(_)) => build::shl_unchecked(l, r),
>  (ShrUnchecked, Type::Int(_)) => build::shr_unchecked(l, r),"
where `build::add(l, r)` is `ValueExpr::BinOp { operator: BinOp::Int(IntBinOp::Add), .. }`
(and analogously for the remaining 14 integer `BinOp` variants). -/
def translateBinOp : MirAst.BinOp → Option Gen.IntBinOp
  | .add => some .Add
  | .sub => some .Sub
  | .mul => some .Mul
  | .div => some .Div
  | .rem => some .Rem
  | .bitXor => some .BitXor
  | .bitAnd => some .BitAnd
  | .bitOr => some .BitOr
  | .shl => some .Shl
  | .shr => some .Shr
  | .addUnchecked => some .AddUnchecked
  | .subUnchecked => some .SubUnchecked
  | .mulUnchecked => some .MulUnchecked
  | .shlUnchecked => some .ShlUnchecked
  | .shrUnchecked => some .ShrUnchecked
  | _ => none

/-- `minimize`'s translation of the comparison operators, which it applies to
operands of any type (`tooling/minimize/src/rvalue.rs`):
> "(Lt, _) => build::lt(l, r),
>  (Le, _) => build::le(l, r),
>  (Gt, _) => build::gt(l, r),
>  (Ge, _) => build::ge(l, r),
>  (Eq, _) => build::eq(l, r),
>  (Ne, _) => build::ne(l, r),"
where each `build` helper is `rel_op(RelOp::_, l, r)`, which builds
`ValueExpr::BinOp { operator: BinOp::Rel(op), left, right }` (MiniRust's
`tooling/miniutil/src/build/expr.rs`, lines 209-235 at the pinned commit:
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L209-L235>).
MIR's three-way `Cmp` is translated separately (`translateCmp`), because
`minimize` transmutes its result to the `Ordering` enum. -/
def translateRelOp : MirAst.BinOp → Option Gen.RelOp
  | .lt => some .Lt
  | .le => some .Le
  | .gt => some .Gt
  | .ge => some .Ge
  | .eq => some .Eq
  | .ne => some .Ne
  | _ => none

/-- `build::bool_to_int::<u8>(v)`, which `minimize` uses to view a `bool` as
the integer `0` or `1`. It is a transmute to `u8`, with no further cast because
the target type already is `u8` (MiniRust's
`tooling/miniutil/src/build/expr.rs`, lines 101-107 at the pinned commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L101-L107>):
```rust
pub fn bool_to_int<T: TypeConv>(v: ValueExpr) -> ValueExpr {
    // First transmute to `u8`.
    let t_u8 = u8::get_type();
    let int = transmute(v, t_u8);
    // Then cast that to the desired integer type, if necessary.
    if T::get_type() == t_u8 { int } else { int_cast::<T>(int) }
}
```
with `transmute(v, t)` building
`ValueExpr::UnOp { operator: UnOp::Cast(CastOp::Transmute(t)), operand: v }`. -/
def boolToU8 (v : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Cast (.Transmute (.Int u8Ty))) v

/-- `build::not(v)`, `minimize`'s translation of `!b` on a `bool` operand
(`tooling/minimize/src/rvalue.rs`):
> "(Not, Type::Bool) => build::not(operand),"
MiniRust has no Boolean negation operator; `build::not` computes `1 - b` on
the `u8` view of `b` and transmutes the result back to `bool` (MiniRust's
`tooling/miniutil/src/build/expr.rs`, lines 109-112 at the pinned commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L109-L112>):
```rust
pub fn not(v: ValueExpr) -> ValueExpr {
    // `1 - v` is always 0 or 1, so safe to transmute back
    transmute(sub(const_int(1u8), bool_to_int::<u8>(v)), bool_ty())
}
```
where `const_int(1u8)` is `ValueExpr::Constant(Constant::Int(1), u8)`,
`sub(l, r)` is `BinOp::Int(IntBinOp::Sub)`, and `bool_ty()` is `Type::Bool`.
Both transmutes run through `Machine::transmute`, so the MiniRust side
re-validates the byte (`0` or `1`) at `bool`. -/
def boolNot (v : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Cast (.Transmute .Bool))
    (.BinOp (.Int .Sub) (.Constant (.Int 1) (.Int u8Ty)) (boolToU8 v))

/-- The integer bitwise operator underlying `minimize`'s `bool_and`,
`bool_or`, and `bool_xor` on `bool` operands (`tooling/minimize/src/rvalue.rs`):
> "(BitAnd, Type::Bool) => build::bool_and(l, r),
>  (BitOr, Type::Bool) => build::bool_or(l, r),
>  (BitXor, Type::Bool) => build::bool_xor(l, r)," -/
def translateBoolBitOp : MirAst.BinOp → Option Gen.IntBinOp
  | .bitAnd => some .BitAnd
  | .bitOr => some .BitOr
  | .bitXor => some .BitXor
  | _ => none

/-- `build::bool_and`, `build::bool_or`, and `build::bool_xor`: transmute both
`bool` operands to `u8` (`boolToU8`), apply `IntBinOp::{BitAnd, BitOr,
BitXor}`, and transmute the resulting `0` or `1` back to `bool` (MiniRust's
`tooling/miniutil/src/build/expr.rs`, lines 240-251 at the pinned commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L240-L251>):
```rust
pub fn bool_and(l: ValueExpr, r: ValueExpr) -> ValueExpr {
    // `l & r` is always 0 or 1, so safe to transmute back
    transmute(bit_and(bool_to_int::<u8>(l), bool_to_int::<u8>(r)), bool_ty())
}
pub fn bool_or(l: ValueExpr, r: ValueExpr) -> ValueExpr {
    // `l | r` is always 0 or 1, so safe to transmute back
    transmute(bit_or(bool_to_int::<u8>(l), bool_to_int::<u8>(r)), bool_ty())
}
pub fn bool_xor(l: ValueExpr, r: ValueExpr) -> ValueExpr {
    // `l ^ r` is always 0 or 1, so safe to transmute back
    transmute(bit_xor(bool_to_int::<u8>(l), bool_to_int::<u8>(r)), bool_ty())
}
```
All three transmutes run through `Machine::transmute`, so the MiniRust side
re-validates both input bytes and the output byte (`0` or `1`) at `bool`. -/
def boolBitOp (iop : Gen.IntBinOp) (l r : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Cast (.Transmute .Bool)) (.BinOp (.Int iop) (boolToU8 l) (boolToU8 r))

/-- `minimize`'s translation of MIR's three-way comparison `Cmp` of `l` and `r`
(`tooling/minimize/src/rvalue.rs`):
> "(Cmp, _) => {
>     let res = build::cmp(l, r);
>     // MiniRust expects an i8 for BinOp::Cmp but MIR uses an Ordering enum,
>     // so we have to transmute the result.
>     let ordering_ty: rs::Ty = self.tcx.ty_ordering_enum(rs::DUMMY_SP);
>     let ordering_ty: Type = self.translate_ty(ordering_ty, span);
>     build::transmute(res, ordering_ty)
> }"
where `build::cmp(l, r)` is
`ValueExpr::BinOp { operator: BinOp::Rel(RelOp::Cmp), left: l, right: r }`
(MiniRust's `tooling/miniutil/src/build/expr.rs`, lines 236-238 at the pinned
commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L236-L238>),
`build::transmute` is the `CastOp::Transmute` of `boolToU8`, and the
translation of `Ordering` is `orderingTy`. MiniRust thus computes the `i8`
`-1`, `0`, or `1` and re-validates its byte as a tag of `orderingTy`. -/
def translateCmp (l r : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Cast (.Transmute orderingTy)) (.BinOp (.Rel .Cmp) l r)

/-- `minimize`'s checked binary-operator translation for integer operands
(`tooling/minimize/src/rvalue.rs`):
> "smir::Rvalue::CheckedBinaryOp(op, l, r) => {
>      let l = GcCow::new(self.translate_operand_smir(l, span));
>      let r = GcCow::new(self.translate_operand_smir(r, span));
>      let op = match op {
>          smir::BinOp::Add => BinOp::IntWithOverflow(IntBinOpWithOverflow::Add),
>          smir::BinOp::Sub => BinOp::IntWithOverflow(IntBinOpWithOverflow::Sub),
>          smir::BinOp::Mul => BinOp::IntWithOverflow(IntBinOpWithOverflow::Mul),
>          x => panic!(\"CheckedBinaryOp {x:?} not supported.\"),
>      };
>      ValueExpr::BinOp { operator: op, left: l, right: r }
>  }"
In `stable_mir` / `rustc_public`, `CheckedBinaryOp(Add | Sub | Mul, l, r)` is
represented as `Rvalue::BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, l, r)`. -/
def translateCheckedBinOp : MirAst.BinOp → Option Gen.IntBinOpWithOverflow
  | .addWithOverflow => some .Add
  | .subWithOverflow => some .Sub
  | .mulWithOverflow => some .Mul
  | _ => none

/-- The pointee integer type (and the mutability) of a raw pointer operand
`copy _j` or `move _j`, from the declaration of `_j` (`ptrPointeeOf`). -/
def operandPtrPointee (decls : List MirAst.LocalDecl) :
    MirAst.Operand → Option (MirAst.Mutability × Gen.IntType)
  | .copy ⟨j, []⟩ | .move ⟨j, []⟩ => decls[j]? >>= fun d => ptrPointeeOf d.ty
  | _ => none

/-- Metadata kind of a raw pointer operand `copy _j` or `move _j` (`rawPtrMetaOf`). -/
def operandRawPtrMeta (decls : List MirAst.LocalDecl) :
    MirAst.Operand → Option Gen.PointerMetaKind
  | .copy ⟨j, []⟩ | .move ⟨j, []⟩ => decls[j]? >>= fun d => rawPtrMetaOf d.ty
  | _ => none

/-- `minimize`'s translation of MIR's pointer offset `Offset(l, r)`, which
counts in units of the pointee (`tooling/minimize/src/rvalue.rs`):
> "(Offset, Type::Ptr(_)) => {
>     // We have to convert the units.
>     let smir::TyKind::RigidTy(smir::RigidTy::RawPtr(pointee, _mutbl)) =
>         lty_smir.kind()
>     else {
>         unreachable!()
>     };
>     let pointee = self.rs_layout_of_smir(pointee);
>     assert!(pointee.is_sized());
>     let size = Int::from(pointee.size.bytes());
>     let size = ValueExpr::Constant(Constant::Int(size), rty);
>     let offset_bytes = build::mul_unchecked(r, size);
>     build::ptr_offset(l, offset_bytes, build::InBounds::Yes)
> }"
where `build::mul_unchecked(l, r)` is
`ValueExpr::BinOp { operator: BinOp::Int(IntBinOp::MulUnchecked), left: l, right: r }`
and `build::ptr_offset(l, r, InBounds::Yes)` is
`ValueExpr::BinOp { operator: BinOp::PtrOffset { inbounds: true }, left: l, right: r }`
(MiniRust's `tooling/miniutil/src/build/expr.rs` at the pinned commit). The
byte count is therefore checked for overflow at the count's type `rty` before
the in-bounds offset checks the whole byte range. `pointeeIt` is the pointee's
integer type, whose size is its layout size on `x86_64`. -/
def ptrOffsetExpr (l r : Gen.ValueExpr) (pointeeIt rIt : Gen.IntType) : Gen.ValueExpr :=
  .BinOp (.PtrOffset true) l
    (.BinOp (.Int .MulUnchecked) r (.Constant (.Int (pointeeIt.size.bytes : Int)) (.Int rIt)))

/-- `minimize`'s rvalue translation for `Use`, `UnaryOp(Neg | Not)` on
integers, `UnaryOp(Not)` on `bool`, integer `BinaryOp`s, checked integer
`BinaryOp`s (`AddWithOverflow | SubWithOverflow | MulWithOverflow`), `bool`
bitwise `BinaryOp`s (`BitAnd | BitOr | BitXor` via `boolBitOp`), the comparison
`BinaryOp`s (including the three-way `Cmp`, `translateCmp`),
`Aggregate(Tuple | Adt | Array)`, `Len`, `Repeat`, and
`Cast(CastKind::IntToInt)` on integers and `bool`
(`tooling/minimize/src/rvalue.rs`):
> "match rv {
>      smir::Rvalue::Use(operand) => self.translate_operand_smir(operand, span),
>      smir::Rvalue::BinaryOp(bin_op, l, r) => {
>          let lty_smir = l.ty(&self.locals_smir).unwrap();
>          let lty = self.translate_ty_smir(lty_smir, span);
>          ..
>          let l = self.translate_operand_smir(l, span);
>          let r = self.translate_operand_smir(r, span);
>          use smir::BinOp::*;
>          match (bin_op, lty) {
>              ..
>          }
>      }
>      ..
>      smir::Rvalue::UnaryOp(unop, operand) => {
>          let ty_smir = operand.ty(&self.locals_smir).unwrap();
>          let ty = self.translate_ty_smir(ty_smir, span);
>          let operand = self.translate_operand_smir(operand, span);
>          use smir::UnOp::*;
>          match (unop, ty) {
>              (Neg, Type::Int(_)) => build::neg(operand),
>              (Not, Type::Int(_)) => build::bit_not(operand),
>              (Not, Type::Bool) => build::not(operand),
>              ..
>          }
>      }
>      ..
>      smir::Rvalue::Aggregate(agg, operands) => {
>          let ty = rv.ty(&self.locals_smir).unwrap();
>          let ty = self.translate_ty_smir(ty, span);
>          match ty {
>              ..
>              Type::Tuple { .. } | Type::Array { .. } => {
>                  let ops: List<_> =
>                      operands.iter().map(|x| self.translate_operand_smir(x, span)).collect();
>                  ValueExpr::Tuple(ops, ty)
>              }
>              ..
>          }
>      }
>      ..
>      smir::Rvalue::Len(place) => {
>          let ty = place.ty(&self.locals_smir).unwrap();
>          match self.translate_ty_smir(ty, span) {
>              Type::Array { elem: _, count } => {
>                  ValueExpr::Constant(Constant::Int(count), <usize>::get_type())
>              }
>              ..
>          }
>      }
>      ..
>      smir::Rvalue::Repeat(op, c) => {
>          let c = c.eval_target_usize().unwrap();
>          let c = Int::from(c);
>          let elem_ty = op.ty(&self.locals_smir).unwrap();
>          let elem_ty = self.translate_ty_smir(elem_ty, span);
>          let op = self.translate_operand_smir(op, span);
>          let ty = Type::Array { elem: GcCow::new(elem_ty), count: c };
>          let ls = list![op; c];
>          ValueExpr::Tuple(ls, ty)
>      }
>      smir::Rvalue::Cast(cast_kind, operand, cast_ty) => {
>          match cast_kind {
>              smir::CastKind::IntToInt => {
>                  ..
>                  let operand = self.translate_operand_smir(operand, span);
>                  let Type::Int(int_ty) = self.translate_ty_smir(*cast_ty, span) else {
>                      rs::span_bug!(span, \"Attempting to IntToInt-Cast to non-int type!\");
>                  };
>                  let operand = match operand_ty {
>                      Type::Int(_) => operand,
>                      Type::Bool => build::transmute(operand, u8::get_type()),
>                      ..
>                  };
>                  ValueExpr::UnOp {
>                      operator: UnOp::Cast(CastOp::IntToInt(int_ty)),
>                      operand: GcCow::new(operand),
>                  }
>              }"
where `build::neg(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::Neg), operand: x }`
and `build::bit_not(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::BitNot), operand: x }`.
Like `minimize`, the translation dispatches on the operand type (`decls`
gives the types of locals): integer arithmetic needs an integer left operand,
`BitAnd | BitOr | BitXor` on a `bool` left operand becomes `build::bool_and`,
`build::bool_or`, or `build::bool_xor` (`boolBitOp`), `Not` means `build::not`
exactly when the operand is a `bool`, `IntToInt` casts a `bool` by first
transmuting to `u8` (`boolToU8`) and then applying `CastOp::IntToInt(int_ty)`,
and the comparisons apply to operands of any type.

For raw pointers, `&raw const p` and `&raw mut p` become `ValueExpr::AddrOf`
at the raw pointer type of the place's pointee, which is sized for every place
`translatePlace` accepts (`tooling/minimize/src/rvalue.rs`):
> "smir::Rvalue::AddressOf(_mutbl, place) => {
>     let ty = place.ty(&self.locals_smir).unwrap();
>     let place = self.translate_place_smir(place, span);
>     let target = GcCow::new(place);
>     let meta_kind = self.pointee_info_of_smir(ty, span).layout.meta_kind();
>
>     let ptr_ty = PtrType::Raw { meta_kind };
>
>     ValueExpr::AddrOf { target, ptr_ty }
> }"
a `PtrToPtr` cast preserves `operand` when `old_meta_kind == new_meta_kind` and
strips metadata via `UnOp::GetThinPointer` when casting to a thin pointer:
> "smir::CastKind::PtrToPtr => {
>     let operand_ty = operand.ty(&self.locals_smir).unwrap();
>     let Type::Ptr(PtrType::Raw { meta_kind: old_meta_kind }) =
>         self.translate_ty_smir(operand_ty, span)
>     else {
>         rs::span_bug!(span, \"ptr to ptr cast on non-raw-pointer\");
>     };
>     let Type::Ptr(PtrType::Raw { meta_kind: new_meta_kind }) =
>         self.translate_ty_smir(*cast_ty, span)
>     else {
>         rs::span_bug!(span, \"ptr to ptr cast to non-raw-pointer\");
>     };
>     let operand = self.translate_operand_smir(operand, span);
>     if old_meta_kind == new_meta_kind {
>         // Since raw pointers do only know care about the meta kind, no transmute is necessary here.
>         operand
>     } else if new_meta_kind == PointerMetaKind::None {
>         build::get_thin_pointer(operand)
>     } else {
>         ..
>     }
> }"
and `Offset(l, r)` becomes `ptrOffsetExpr`. -/
def translateRvalue (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty := none) :
    MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand decls op
  | .unaryOp uop op => do
    let e ← translateOperand decls op
    match operandType layouts decls op with
    | some (.Int _) => pure (.UnOp (.Int (← translateUnOp uop)) e)
    | some .Bool =>
      match uop with
      | .not => pure (boolNot e)
      | _ => none
    | _ => none
  | .binaryOp op l r => do
    let el ← translateOperand decls l
    let er ← translateOperand decls r
    match translateRelOp op with
    | some rel => pure (.BinOp (.Rel rel) el er)
    | none =>
      match translateBinOp op with
      | some iop =>
        match operandType layouts decls l with
        | some (.Int _) => pure (.BinOp (.Int iop) el er)
        | some .Bool => do
          let biop ← translateBoolBitOp op
          pure (boolBitOp biop el er)
        | _ => none
      | none =>
        match translateCheckedBinOp op with
        | some cop => pure (.BinOp (.IntWithOverflow cop) el er)
        | none =>
          match op with
          | .cmp => pure (translateCmp el er)
          | .offset => do
            let (_, pointeeIt) ← operandPtrPointee decls l
            let rIt ← operandIntType layouts decls r
            pure (ptrOffsetExpr el er pointeeIt rIt)
          | _ => none
  | .aggregate (.array elemTy) ops => do
    let elemIt ← intTypeOf elemTy
    let exprs ← ops.mapM (translateOperand decls)
    pure (.Tuple exprs (.Array (.Int elemIt) (Int.ofNat ops.length)))
  | .aggregate .tuple ops => do
    let exprs ← ops.mapM (translateOperand decls)
    match targetTy >>= intBoolTupleOf with
    | some it => pure (.Tuple exprs (intBoolTupleTy it))
    | none =>
      let dstTy ← targetTy
      let (fields, size, align) ← tupleTypeOf layouts dstTy
      pure (.Tuple exprs ((TupleSpec.tuple fields size align).toMiniRustTy))
  | .aggregate (.adt _ 0 none) ops => do
    let dstTy ← targetTy
    let (fields, size, align) ← tupleTypeOf layouts dstTy
    let exprs ← ops.mapM (translateOperand decls)
    pure (.Tuple exprs ((TupleSpec.tuple fields size align).toMiniRustTy))
  | .repeat op count => do
    let elemIt ← operandIntType layouts decls op
    let expr ← translateOperand decls op
    pure (.Tuple (List.replicate count expr) (.Array (.Int elemIt) (Int.ofNat count)))
  | .len ⟨j, []⟩ => do
    let (_, count) ← decls[j]? >>= (arrayTypeOf ·.ty)
    pure (.Constant (.Int (Int.ofNat count)) (.Int usizeIt))
  | .cast .intToInt op castTy => do
    let intTy ← intTypeOf castTy
    let operand ← translateOperand decls op
    match operandType layouts decls op with
    | some (.Int _) => pure (.UnOp (.Cast (.IntToInt intTy)) operand)
    | some .Bool => pure (.UnOp (.Cast (.IntToInt intTy)) (boolToU8 operand))
    | _ => none
  | .rawPtr _ place => do
    let target ← translatePlace decls place
    pure (.AddrOf target (.Raw .None))
  | .cast .ptrToPtr op castTy => do
    let operand ← translateOperand decls op
    let oldMeta ← operandRawPtrMeta decls op
    let newMeta ← rawPtrMetaOf castTy
    if oldMeta == newMeta then pure operand
    else if newMeta == .None then pure (.UnOp .GetThinPointer operand)
    else none
  | _ => none

/-- `minimize`'s statement translation for assignments, `StorageLive`,
`StorageDead`, and `PlaceMention` on a local or field-projected place
(`tooling/minimize/src/bb.rs`):
> "rs::StatementKind::Assign(operands) => {
>      let (place, rval) = &**operands;
>      let destination = self.translate_place(place, span);
>      ..
>      let source = self.translate_rvalue(rval, span);
>      Statement::Assign { destination, source }
>  }
>  rs::StatementKind::StorageLive(local) =>
>      Statement::StorageLive(self.local_name_map[&local]),
>  rs::StatementKind::StorageDead(local) =>
>      Statement::StorageDead(self.local_name_map[&local]),
>  ..
>  rs::StatementKind::PlaceMention(place) => {
>      let place = self.translate_place(place, span);
>      Statement::PlaceMention(place)
>  }"
where the elided part special-cases two pointer-provenance casts, which are
outside the fragment, and `PlaceMention` supports unprojected locals `⟨i, []⟩`
and field projection chains `⟨i, .field idx fieldTy :: rest⟩` (array
`Index`/`ConstantIndex` projections in `PlaceMention` are excluded because
Anneal's `.placeMention` checks only `place.local_`). The rvalue goes through
`copyRv` because `minimize` translates `move` and `copy` operands alike.
`minimize` at the pinned commit has no case for MIR's `StatementKind::Deinit`,
which Anneal's MIR does contain; we translate `Deinit(place)` to MiniRust's
`Statement::Deinit` of the translated place, the statement with the same
meaning ("This writes `uninit` bytes to the entire place",
`compiler/rustc_middle/src/mir/syntax.rs`; "This statement replaces the
contents of a place with `Uninit`", `spec/lang/step/statements.md`). -/
def translateStatement (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    Option Gen.Statement :=
  match s.kind with
  | .assign dst rv => do
    let destination ← translatePlace decls dst
    let source ← translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv)
    pure (.Assign destination source)
  | .placeMention ⟨i, []⟩ => some (.PlaceMention (.Local (localName i)))
  | .placeMention ⟨i, .field idx fieldTy :: rest⟩ =>
    (translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest)).map .PlaceMention
  | .storageLive i => some (.StorageLive (localName i))
  | .storageDead i => some (.StorageDead (localName i))
  | .deinit p => (translatePlace decls p).map .Deinit
  | _ => none

/-- `minimize`'s switch cases for a discriminant of type `it`
(`tooling/minimize/src/bb.rs`):
> "let cases = targets
>      .iter()
>      .map(|(value, target)| {
>          (int_from_bits(value, int_ty), self.bb_name_map[&target])
>      })
>      .collect();"
The fragment requires distinct values (see `terminatorOk`), so the order of
the association list is irrelevant. -/
def switchCases (it : Gen.IntType) (branches : List (Nat × Nat)) : Map Int Gen.BbName :=
  ⟨branches.map (fun p => (intFromBits p.1 it, bbName p.2))⟩

/-- The integer type `minimize` switches at for a fragment discriminant: the
discriminant's own type for an integer, and `u8` for a `bool`, which
`minimize` first transmutes to `u8` (see `translateTerminator`). -/
def switchIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (discr : MirAst.Operand) : Option Gen.IntType :=
  match operandType layouts decls discr with
  | some (.Int it) => some it
  | some .Bool => some u8Ty
  | _ => none

/-- `minimize`'s terminator translation (`tooling/minimize/src/bb.rs`):
> "rs::TerminatorKind::Return => Terminator::Return,
>  rs::TerminatorKind::Goto { target } => Terminator::Goto(self.bb_name_map[&target]),
>  ..
>  rs::TerminatorKind::SwitchInt { discr, targets } => {
>      let ty = discr.ty(&self.body, self.tcx);
>      let ty = self.translate_ty(ty, span);
>      let discr_op = self.translate_operand(discr, span);
>      let (value, int_ty) = match ty {
>          Type::Bool => {
>              // If the value is a boolean we need to cast it to an integer first as MiniRust switch only operates on ints.
>              let Type::Int(u8_inttype) = <u8>::get_type() else { unreachable!() };
>              (
>                  ValueExpr::UnOp {
>                      operator: UnOp::Cast(CastOp::Transmute(Type::Int(u8_inttype))),
>                      operand: GcCow::new(discr_op),
>                  },
>                  u8_inttype,
>              )
>          }
>          Type::Int(ity) => (discr_op, ity),
>          ..
>      };
>      let cases = targets .. .collect();
>      let fallback_block = targets.otherwise();
>      let fallback = self.bb_name_map[&fallback_block];
>      Terminator::Switch { value, cases, fallback }
>  }
>  rs::TerminatorKind::Unreachable => Terminator::Unreachable,"
restricted to integer and `bool` discriminants. For a `bool`, the
discriminant is transmuted to `u8` (`boolToU8`), so MiniRust re-validates the
byte at `bool` when it loads the local and then switches on the integer `0` or
`1`. A `move` discriminant goes through `copyOp`, like an rvalue operand. -/
def translateTerminator (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (t : MirAst.Terminator) :
    Option Gen.Terminator :=
  match t.kind with
  | .goto target => some (.Goto (bbName target))
  | .switchInt discr targets => do
    let discrOp ← translateOperand decls (copyOp discr)
    match operandType layouts decls (copyOp discr) with
    | some (.Int it) =>
      pure (.Switch discrOp (switchCases it targets.branches) (bbName targets.otherwise))
    | some .Bool =>
      pure (.Switch (boolToU8 discrOp) (switchCases u8Ty targets.branches) (bbName targets.otherwise))
    | _ => none
  | .unreachable => some .Unreachable
  | .return_ => some .Return
  | _ => none

/-- `minimize`'s basic-block translation; fragment blocks are not cleanup blocks,
so their kind is `BbKind::Regular`. -/
def translateBlock (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (bb : MirAst.BasicBlockData) :
    Option Gen.BasicBlock := do
  let stmts ← bb.statements.mapM (translateStatement decls · layouts)
  let term ← translateTerminator layouts decls bb.terminator
  pure ⟨stmts, term, .Regular⟩

/-- `minimize`'s local-type map, one entry per MIR local in index order
(`tooling/minimize/src/function.rs`):
> "for (id, local_name) in &self.local_name_map {
>      let local_decl = &self.body.local_decls[*id];
>      let span = local_decl.source_info.span;
>      let ty = self.cx.translate_ty(local_decl.ty, span);
>      self.locals.insert(*local_name, ty);
>  }" -/
def translateLocals (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    Nat → List MirAst.LocalDecl → Option (List (Gen.LocalName × Gen.Type))
  | _, [] => some []
  | i, d :: ds => do
    let ty ← translateTy layouts d.ty
    let rest ← translateLocals layouts (i + 1) ds
    pure ((localName i, ty) :: rest)

/-- `minimize`'s block map, one entry per MIR block in index order
("for (id, bb_name) in self.bb_name_map.clone() { .. self.translate_bb(bb_name, bb_data); }"). -/
def translateBlocks (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) :
    Nat → List MirAst.BasicBlockData → Option (List (Gen.BbName × Gen.BasicBlock))
  | _, [] => some []
  | i, bb :: bbs => do
    let b ← translateBlock layouts decls bb
    let rest ← translateBlocks layouts decls (i + 1) bbs
    pure ((bbName i, b) :: rest)

/-- Whether some statement of the body is `StorageLive(_loc)` or
`StorageDead(_loc)`. -/
def hasStorageMarker (body : MirAst.CapturedMir) (loc : Nat) : Bool :=
  body.basicBlocks.any fun bb =>
    bb.statements.any fun s =>
      match s.kind with
      | .storageLive l => l == loc
      | .storageDead l => l == loc
      | _ => false

/-- The locals that `minimize`'s init block marks live: the locals of
`rs::always_storage_live_locals(&self.body)`, which `rustc_mir_dataflow`
computes as the locals without any `StorageLive` or `StorageDead` statement
in the body, in increasing index order (the iteration order of its
`DenseBitSet`), minus the return place and the arguments (`.filter(|LocalName(i)|
i.get_internal() as usize >= free_argc)` with `free_argc = arg_count + 1`). -/
def alwaysStorageLiveLocals (body : MirAst.CapturedMir) : List Nat :=
  (List.range body.localDecls.length).filter fun loc =>
    decide (body.argCount + 1 ≤ loc) && !hasStorageMarker body loc

/-- The init block `minimize` prepends (see `translateFn`): `StorageLive` of
every local of `alwaysStorageLiveLocals`, then `Goto(bb0)`. -/
def initBlock (body : MirAst.CapturedMir) : Gen.BasicBlock :=
  ⟨(alwaysStorageLiveLocals body).map (fun loc => .StorageLive (localName loc)), .Goto (bbName 0),
    .Regular⟩

/-- `minimize`'s function translation (`tooling/minimize/src/function.rs`),
specialized to bodies without a spread argument (`spread_arg`, used only by
closures and the `rust-call` ABI):

> "for i in 1..=(self.body.arg_count) {
>      if Some(i) == spread_local_idx { .. } else {
>          args.push(LocalName(Name::from_internal(i as _)));
>      }
>  }
>  let free_argc = self.body.arg_count + 1;
>  // add init basic block
>  let init_bb = self.fresh_bb_name();
>  // this block allocates all \"always_storage_live_locals\",
>  // except for those which are implicitly storage live in Minirust;
>  // like the return local and function args.
>  init_statements.extend(rs::always_storage_live_locals(&self.body).iter()
>      .map(|loc| self.local_name_map[&loc])
>      .filter(|LocalName(i)| i.get_internal() as usize >= free_argc)
>      .map(Statement::StorageLive),);
>  let init_blk = BasicBlock { statements: init_statements.into_iter().collect(),
>      terminator: Terminator::Goto(self.bb_name_map[&rs::mir::START_BLOCK]),
>      kind: BbKind::Regular, };
>  self.blocks.insert(init_bb, init_blk);
>  ..
>  let ret = LocalName(Name::from_internal(0));
>  let f = Function { locals: self.locals, args, ret, blocks: self.blocks,
>      start: init_bb,
>      calling_convention: translate_calling_convention(self.abi.conv),
>      implicit_writes: self.implicit_writes, };"

Without a spread argument, `init_statements` holds exactly the `StorageLive`s
of `alwaysStorageLiveLocals` (`initBlock`). We take the calling convention to
be `Rust` and `implicit_writes` to be `true` (the `minimize` default absent
`#[rustc_no_writable]`); neither is read by the interpreted fragment. -/
def translateFn (body : MirAst.CapturedMir) : Option Gen.Function := do
  let locals ← translateLocals body.layouts 0 body.localDecls
  let blocks ← translateBlocks body.layouts body.localDecls 0 body.basicBlocks
  let n := body.basicBlocks.length
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨blocks ++ [(bbName n, initBlock body)]⟩
    start := bbName n
    implicit_writes := true
  }

/-- `minimize`'s `StatementResult` (`tooling/minimize/src/bb.rs`): a MIR
statement lowers either to a MiniRust `Statement` or to a block-splitting
`Terminator::Intrinsic` call (`PointerExposeProvenance` /
`PointerWithExposedProvenance`). -/
inductive StmtTranslation : Type where
  | stmt (s : Gen.Statement)
  | intrinsic (op : Gen.IntrinsicOp) (dst : Gen.PlaceExpr) (args : List Gen.ValueExpr)

/-- `minimize`'s statement translation including the integer-pointer provenance
casts (`tooling/minimize/src/bb.rs`):
> "match rval {
>     rs::Rvalue::Cast(rs::CastKind::PointerExposeProvenance, operand, _) => {
>         let operand = self.translate_operand(operand, span);
>         return StatementResult::Intrinsic {
>             intrinsic: IntrinsicOp::PointerExposeProvenance,
>             destination,
>             arguments: list![operand],
>         };
>     }
>     rs::Rvalue::Cast(rs::CastKind::PointerWithExposedProvenance, operand, _) => {
>         // TODO untested so far! (Can't test because of `predict`)
>         let operand = self.translate_operand(operand, span);
>         return StatementResult::Intrinsic {
>             intrinsic: IntrinsicOp::PointerWithExposedProvenance,
>             destination,
>             arguments: list![operand],
>         };
>     }
>     _ => {}
> }" -/
def translateStmtOrIntrinsic (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) :
    Option StmtTranslation :=
  match s.kind with
  | .assign dst (.cast .pointerExposeProvenance op _) => do
    let destination ← translatePlace decls dst
    let operand ← translateOperand decls op
    pure (.intrinsic .PointerExposeProvenance destination [operand])
  | .assign dst (.cast .pointerWithExposedProvenance op _) => do
    let destination ← translatePlace decls dst
    let operand ← translateOperand decls op
    pure (.intrinsic .PointerWithExposedProvenance destination [operand])
  | _ => (translateStatement decls s layouts).map .stmt

/-- Split a sequence of `StmtTranslation`s at `StmtTranslation.intrinsic`
boundaries (`FnCtxt::translate_bb`, `tooling/minimize/src/bb.rs`):
> "StatementResult::Intrinsic { intrinsic, destination, arguments } => {
>     // Generate a fresh bb name.
>     let next_bb = self.fresh_bb_name();
>     // End the current block by jumping to the next one.
>     let terminator = Terminator::Intrinsic {
>         intrinsic,
>         arguments,
>         ret: destination,
>         next_block: Some(next_bb),
>     };" -/
def splitBlockAtIntrinsics (curName : Gen.BbName) (accStmts : List Gen.Statement)
    (finalTerm : Gen.Terminator) (kind : Gen.BbKind) (nextFresh : Nat) :
    List StmtTranslation → List (Gen.BbName × Gen.BasicBlock) × Nat
  | [] => ([(curName, ⟨accStmts, finalTerm, kind⟩)], nextFresh)
  | .stmt st :: rest =>
    splitBlockAtIntrinsics curName (accStmts ++ [st]) finalTerm kind nextFresh rest
  | .intrinsic op dst args :: rest =>
    let nextBb := bbName nextFresh
    let curBlk : Gen.BasicBlock :=
      ⟨accStmts, .Intrinsic op args dst (some nextBb), kind⟩
    let (tailBlks, nextFresh') :=
      splitBlockAtIntrinsics nextBb [] finalTerm kind (nextFresh + 1) rest
    ((curName, curBlk) :: tailBlks, nextFresh')

/-- Translate basic blocks while splitting blocks at provenance-cast intrinsics,
allocating fresh `BbName`s above `nextFresh`. -/
def translateBlocksWithIntrinsics (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) :
    Nat → Nat → List MirAst.BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × Nat)
  | _, nextFresh, [] => some ([], nextFresh)
  | i, nextFresh, bb :: bbs => do
    let trs ← bb.statements.mapM (translateStmtOrIntrinsic decls · layouts)
    let term ← translateTerminator layouts decls bb.terminator
    let kind := if bb.isCleanup then Gen.BbKind.Cleanup else .Regular
    let (here, nextFresh') :=
      splitBlockAtIntrinsics (bbName i) [] term kind nextFresh trs
    let (rest, finalFresh) ←
      translateBlocksWithIntrinsics layouts decls (i + 1) nextFresh' bbs
    pure (here ++ rest, finalFresh)

/-- `minimize`'s function translation extended with block-splitting lowering of
`CastKind::PointerExposeProvenance` and `CastKind::PointerWithExposedProvenance`
into `Terminator::Intrinsic` blocks (used by ground-truth and divergence
witnesses outside `inFragment`). -/
def translateFnWithIntrinsics (body : MirAst.CapturedMir) : Option Gen.Function := do
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, initIdx) ←
    translateBlocksWithIntrinsics body.layouts body.localDecls 0 n body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨blocks ++ [(bbName initIdx, initBlock body)]⟩
    start := bbName initIdx
    implicit_writes := true
  }

/-! ## The fragment -/

/-- Well-formedness of a single array indexing projection (`Index` or
`ConstantIndex`) on an array of length `count`. -/
def projOk (decls : List MirAst.LocalDecl) (count : Nat) : MirAst.ProjectionElem → Bool
  | .index idxLocal =>
    decide (idxLocal < decls.length) &&
    match decls[idxLocal]? >>= (intTypeOf ·.ty) with
    | some idxIt =>
      decide (idxIt.signed = .Unsigned ∨ count ≤ 2 ^ (8 * idxIt.size.bytes - 1))
    | none => false
  | .constantIndex offset minLen fromEnd =>
    decide (minLen ≤ count) &&
    decide (offset < 2 ^ 63) &&
    if fromEnd then decide (1 ≤ offset ∧ offset ≤ count) else true
  | _ => false

/-- A scalar place of integer type `it`: an unprojected integer local `_j`,
field `0` (`_j.0`) of an `(it, bool)` local, a (possibly nested) field
projection `_j.f1...fk` on a `TupleSpec` local, or an indexed element `_j[proj]`
of a homogeneous array local. -/
def placeOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Place → Bool
  | ⟨j, []⟩ =>
    decide (j < decls.length) && decide ((decls[j]? >>= (intTypeOf ·.ty)) = some it)
  | ⟨j, .field idx fieldTy :: rest⟩ =>
    decide (j < decls.length) &&
    match decls[j]? with
    | none => false
    | some d =>
      match intBoolTupleOf d.ty with
      | some tupIt =>
        match idx, rest, intTypeOf fieldTy with
        | 0, [], some fIt => decide (fIt = tupIt) && decide (tupIt = it)
        | _, _, _ => false
      | none =>
        match tupleTypeOf layouts d.ty with
        | some (fields, size, align) =>
          match resolveFieldPath layouts (.tuple fields size align)
              (.field idx fieldTy :: rest) with
          | some (_, .scalar leafIt) => decide (leafIt = it)
          | _ => false
        | none => false
  | ⟨j, [proj]⟩ =>
    decide (j < decls.length) &&
    match decls[j]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) => decide (elemIt = it) && projOk decls count proj
    | none => false
  | _ => false

/-- A fragment integer operand of type `it`: `copy p` of an integer place `p`,
or an integer constant. A `move` operand is checked through `copyOp`. -/
def operandOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy p => placeOk layouts decls it p && (translateOperand decls op).isSome
  | .constant _ =>
    decide (operandIntType layouts decls op = some it) && (translateOperand decls op).isSome
  | _ => false

/-- Whether an `IntBinOp` is a shift operator, which in MiniRust (as in MIR)
allows the right-hand shift amount to have an integer type unequal to the
left-hand operand's type (`spec/lang/well-formed.md`):
> "// Shift operators allow unequal left and right type
>  if !matches!(int_op, Shl | Shr | ShlUnchecked | ShrUnchecked) {
>      ensure_wf(left == right, \"BinOp:Int: right and left type are not equal\")?;
>  }" -/
def isShiftIntBinOp : Gen.IntBinOp → Bool
  | .Shl | .Shr | .ShlUnchecked | .ShrUnchecked => true
  | _ => false

/-- Whether a fragment operand has MiniRust type `Type::Bool`. -/
def operandIsBool (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  match operandType layouts decls op with
  | some .Bool => true
  | _ => false

/-- A fragment `bool` operand: a `bool` local `copy _j`, field 1 `copy (_j.1)`
of an `(Int, bool)` tuple local, or a `bool` constant that `minimize` can read
(`0` or `1`). -/
def operandOkB (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ => decide (j < decls.length) && operandIsBool layouts decls op
  | .copy ⟨j, [.field 1 fTy]⟩ =>
    decide (j < decls.length) &&
    match decls[j]? >>= fun d => intBoolTupleOf d.ty with
    | some _ => isBoolTy fTy
    | none => false
  | .constant _ => operandIsBool layouts decls op && (translateOperand decls op).isSome
  | _ => false

/-- Fragment rvalues of integer type `it`. -/
def rvalueOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use op => operandOk layouts decls it op
  | .unaryOp uop op => (translateUnOp uop).isSome && operandOk layouts decls it op
  | .binaryOp op a b =>
    match translateBinOp op with
    | none => false
    | some iop =>
      operandOk layouts decls it a &&
      if isShiftIntBinOp iop then
        match operandIntType layouts decls b with
        | some rhsIt => operandOk layouts decls rhsIt b
        | none => false
      else
        operandOk layouts decls it b
  | .cast .intToInt op targetTy =>
    decide (intTypeOf targetTy = some it) &&
    match operandIntType layouts decls op with
    | some srcIt => operandOk layouts decls srcIt op
    | none => operandOkB layouts decls op
  | .len ⟨j, []⟩ =>
    decide (it = usizeIt) &&
    decide (j < decls.length) &&
    (decls[j]? >>= (arrayTypeOf ·.ty)).isSome
  | _ => false

/-- The operands of a fragment comparison: both integers of one type, or both
`bool`s (MiniRust requires both operands of `BinOp::Rel` to have the same
type, `spec/lang/well-formed.md`:
> "ensure_wf(right == left, \"BinOp::Rel: invalid right type\")?;"
and MIR's comparisons are homogeneous as well). -/
def relOperandsOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (a b : MirAst.Operand) : Bool :=
  match operandType layouts decls a with
  | some (.Int it) => operandOk layouts decls it a && operandOk layouts decls it b
  | some .Bool => operandOkB layouts decls a && operandOkB layouts decls b
  | _ => false

/-- Fragment rvalues of type `bool`: a `bool` operand, `!b` on a `bool`
operand, `BitAnd | BitOr | BitXor` on two `bool` operands, or a comparison
(`==`, `!=`, `<`, `<=`, `>`, `>=`) of two integers of one type or of two
`bool`s. -/
def rvalueOkB (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Bool
  | .use op => operandOkB layouts decls op
  | .unaryOp .not op => operandOkB layouts decls op
  | .binaryOp op a b =>
    if (translateRelOp op).isSome then relOperandsOk layouts decls a b
    else (translateBoolBitOp op).isSome && operandOkB layouts decls a && operandOkB layouts decls b
  | _ => false

/-- Whether a fragment operand has MiniRust type `orderingTy`. -/
def operandIsOrdering (decls : List MirAst.LocalDecl) : MirAst.Operand → Bool
  | .copy ⟨j, []⟩ => match decls[j]? with | some d => isOrderingTy d.ty | none => false
  | .constant c => isOrderingTy c.ty
  | _ => false

/-- A projection-free `Ordering` operand: an `Ordering` local (`Ordering`
constants are rejected by `translateOperand`; see
`translateOperand_ordering_const`). -/
def operandOkO (decls : List MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ => decide (j < decls.length) && operandIsOrdering decls op
  | .constant _ => operandIsOrdering decls op && (translateOperand decls op).isSome
  | _ => false

/-- Fragment rvalues of type `core::cmp::Ordering`: an `Ordering` operand or
a three-way comparison `Cmp` of two integers of one type or of two `bool`s. -/
def rvalueOkO (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Bool
  | .use op => operandOkO decls op
  | .binaryOp .cmp a b => relOperandsOk layouts decls a b
  | _ => false

/-- Field-0 integer type of a projection-free `(Int, bool)` 2-tuple operand. -/
def operandTupleIntType (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy ⟨j, []⟩ => decls[j]? >>= fun d => intBoolTupleOf d.ty
  | _ => none

/-- A projection-free `(Int, bool)` 2-tuple operand of field-0 integer type `it`. -/
def operandOkTuple (decls : List MirAst.LocalDecl) (it : Gen.IntType) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ =>
    decide (j < decls.length) && decide (operandTupleIntType decls op = some it)
  | _ => false

/-- Fragment rvalues of 2-tuple type `(it, bool)`: a 2-tuple operand, a
checked binary operation `AddWithOverflow | SubWithOverflow | MulWithOverflow`
on two integer operands of type `it`, or a 2-tuple aggregate `(a, b)` of an
integer operand of type `it` and a `bool` operand. -/
def rvalueOkTuple (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use op => operandOkTuple decls it op
  | .binaryOp op a b =>
    (translateCheckedBinOp op).isSome && operandOk layouts decls it a && operandOk layouts decls it b
  | .aggregate .tuple [a, b] => operandOk layouts decls it a && operandOkB layouts decls b
  | _ => false

/-- Fragment rvalues producing a homogeneous array `[elemIt; count]`. -/
def arrayRvalueOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (elemIt : Gen.IntType) (count : Nat) :
    MirAst.Rvalue → Bool
  | .use (.copy ⟨j, []⟩) =>
    decide (j < decls.length) &&
    decide ((decls[j]? >>= (arrayTypeOf ·.ty)) = some (elemIt, count))
  | .aggregate (.array elemTy) ops =>
    decide (intTypeOf elemTy = some elemIt) &&
    decide (ops.length = count) &&
    ops.all (operandOk layouts decls elemIt)
  | .repeat op n =>
    decide (n = count) &&
    (decide (0 < count) || match op with | .constant _ => true | _ => false) &&
    operandOk layouts decls elemIt op
  | _ => false

/-- Resolved `(fields, size, align)` descriptor of a tuple/struct place (either
an unprojected tuple/struct local `_j` or a field projection chain `_j.f1...fk`
whose target is a nested tuple/struct). -/
def tuplePlaceSpec (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) :
    MirAst.Place → Option (List (Nat × TupleSpec) × Nat × Nat)
  | ⟨j, []⟩ =>
    if j < decls.length then decls[j]? >>= (tupleTypeOf layouts ·.ty) else none
  | ⟨j, .field idx fieldTy :: rest⟩ =>
    if j < decls.length then do
      let d ← decls[j]?
      let (fields, size, align) ← tupleTypeOf layouts d.ty
      let (_, leafSpec) ←
        resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest)
      match leafSpec with
      | .tuple subFields subSize subAlign => some (subFields, subSize, subAlign)
      | .scalar _ => none
    else none
  | _ => none

/-- Well-formedness of an operand producing a value of `TupleSpec` `spec`
(either a scalar operand of type `it` when `spec = .scalar it`, or a `copy p`
of a tuple/struct place when `spec = .tuple fields size align`). -/
def specOperandOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (spec : TupleSpec) (op : MirAst.Operand) : Bool :=
  match spec with
  | .scalar it => operandOk layouts decls it op
  | .tuple fields size align =>
    match op with
    | .copy p =>
      decide (tuplePlaceSpec layouts decls p = some (fields, size, align)) &&
      (translateOperand decls op).isSome
    | _ => false

/-- Pointwise well-formedness of aggregate field operands against `fields`. -/
def tupleFieldsOperandOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) :
    List (Nat × TupleSpec) → List MirAst.Operand → Bool
  | [], [] => true
  | (_, fSpec) :: restF, op :: restOps =>
    specOperandOk layouts decls fSpec op && tupleFieldsOperandOk layouts decls restF restOps
  | _, _ => false

/-- Whether `AggregateKind` `agg` matches the destination's `RigidTy`
(`.tuple` for `RigidTy.tuple`, `.adt defPath 0 none` for `RigidTy.adt defPath _`). -/
def aggKindMatchesTy : MirAst.AggregateKind → MirAst.RigidTy → Bool
  | .tuple, .tuple _ => true
  | .adt defPath 0 none, .adt defPath' _ => decide (defPath = defPath')
  | _, _ => false

/-- Fragment rvalues producing a tuple or single-variant struct of spec
`(fields, size, align)` and destination type `dstTy`. -/
def tupleRvalueOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (dstTy : MirAst.Ty)
    (fields : List (Nat × TupleSpec)) (size align : Nat) : MirAst.Rvalue → Bool
  | .use (.copy p) =>
    decide (tuplePlaceSpec layouts decls p = some (fields, size, align)) &&
    (translatePlace decls p).isSome
  | .aggregate agg ops =>
    aggKindMatchesTy agg dstTy.kind &&
    decide (tupleTypeOf layouts dstTy = some (fields, size, align)) &&
    tupleFieldsOperandOk layouts decls fields ops
  | _ => false

/-- Resolve the pointee integer type and relative byte offset of an admissible
`&raw const` / `&raw mut` target place: an unprojected integer parameter local
`⟨k, []⟩`, an in-bounds `ConstantIndex` element `⟨k, [.constantIndex ..]⟩` of an
array parameter `[T; count]`, or a scalar field chain `⟨k, .field ..⟩` of a
`TupleSpec` parameter (`1 ≤ k`). -/
def ptrTargetSpec (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Place → Option (Gen.IntType × Nat)
  | ⟨k, []⟩ =>
    if 1 ≤ k ∧ k < decls.length then
      (decls[k]? >>= (intTypeOf ·.ty)).map (·, 0)
    else none
  | ⟨k, [.constantIndex offset minLen fromEnd]⟩ =>
    if 1 ≤ k ∧ k < decls.length then
      match decls[k]? >>= (arrayTypeOf ·.ty) with
      | some (elemIt, count) =>
        if minLen ≤ count ∧ (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count) then
          let idx := if fromEnd then count - offset else offset
          some (elemIt, idx * elemIt.size.bytes)
        else none
      | none => none
    else none
  | ⟨k, .field idx fieldTy :: rest⟩ =>
    if 1 ≤ k ∧ k < decls.length then do
      let d ← decls[k]?
      let (fields, size, align) ← tupleTypeOf layouts d.ty
      let (relOff, leafSpec) ←
        resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest)
      match leafSpec with
      | .scalar leafIt => some (leafIt, relOff)
      | .tuple _ _ _ => none
    else none
  | _ => none

/-- Whether `place` is an admissible `&raw` target of pointee integer type `pointeeIt`. -/
def ptrTargetOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (pointeeIt : Gen.IntType) (place : MirAst.Place) : Bool :=
  match ptrTargetSpec layouts decls place with
  | some (it, _) => decide (it = pointeeIt)
  | none => false

/-- Whether `c` is an integer constant encoding `0` (`Offset(p, 0)`). -/
def zeroOffsetConstOk (c : MirAst.ConstOperand) : Bool :=
  match c.val, intTypeOf c.ty with
  | .scalar (.int ⟨0, sz⟩), some rIt => decide (sz = rIt.size.bytes)
  | _, _ => false

/-- Fragment rvalues producing a thin raw pointer of mutability `mutbl` and
pointee integer type `pointeeIt` (inspected after `copyRv`). -/
def ptrRvalueOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) :
    MirAst.Rvalue → Bool
  | .use (.copy ⟨p, []⟩) =>
    decide (p < decls.length) &&
    decide ((decls[p]? >>= (ptrPointeeOf ·.ty)) = some (mutbl, pointeeIt))
  | .rawPtr m place =>
    decide (m = mutbl) && ptrTargetOk layouts decls pointeeIt place
  | .cast .ptrToPtr (.copy ⟨p, []⟩) castTy =>
    decide (p < decls.length) &&
    decide (ptrPointeeOf castTy = some (mutbl, pointeeIt)) &&
    match decls[p]? >>= (ptrPointeeOf ·.ty) with
    | some (srcMutbl, srcIt) =>
      decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
    | none => false
  | .binaryOp .offset (.copy ⟨p, []⟩) (.constant c) =>
    decide (p < decls.length) &&
    decide ((decls[p]? >>= (ptrPointeeOf ·.ty)) = some (mutbl, pointeeIt)) &&
    zeroOffsetConstOk c
  | _ => false

/-- Whether `rv` (after `copyRv`) is a dereference read `*_p` of a thin raw
pointer to integer type `it`. -/
def ptrDerefReadOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use (.copy ⟨p, [.deref]⟩) =>
    decide (p < decls.length) &&
    match decls[p]? >>= (ptrPointeeOf ·.ty) with
    | some (_, pointeeIt) => decide (pointeeIt = it)
    | none => false
  | _ => false

/-- Places admissible in `PlaceMention`: an unprojected local `_i`, field `0`
or `1` of an `(Int, bool)` local, or a valid field projection chain `_i.f1...fk`
on a `TupleSpec` local. -/
def mentionPlaceOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Place → Bool
  | ⟨i, []⟩ => decide (i < decls.length)
  | ⟨i, .field idx fieldTy :: rest⟩ =>
    decide (i < decls.length) &&
    match decls[i]? with
    | none => false
    | some d =>
      match intBoolTupleOf d.ty with
      | some it =>
        match idx, rest with
        | 0, [] => decide (intTypeOf fieldTy = some it)
        | 1, [] => isBoolTy fieldTy
        | _, _ => false
      | none =>
        match tupleTypeOf layouts d.ty with
        | some (fields, size, align) =>
          (resolveFieldPath layouts (.tuple fields size align)
            (.field idx fieldTy :: rest)).isSome
        | none => false
  | _ => false

/-- Fragment statements, type-checked against the destination's type:
scalar-family root assignments (`bool`, `Ordering`, `(it, bool)`, and `Int`,
including raw-pointer dereference reads `*_p`) check `copyRv rv`; thin raw
pointer root assignments check `ptrRvalueOk` on `copyRv rv`; array root
assignments check `arrayRvalueOk`; `TupleSpec` root and field assignments check
`tupleRvalueOk` / `rvalueOk`; mutable raw pointer dereference writes `(*_p) = rv`
check `rvalueOk`; array element assignments check `projOk` and `rvalueOk`;
`PlaceMention` checks `mentionPlaceOk`; and `StorageLive`, `StorageDead`, and
root `Deinit` take a declared scalar-family or thin raw pointer local
(`spec/lang/well-formed.md`:
> "Deinit { place } => {
>      let ty = place.check_wf::<T>(func.locals, prog)?;
>      ensure_wf(ty.layout::<T>().is_sized(), \"Statement::Deinit: unsized place\")?;
>  }
>  StorageLive(local) => {
>      ensure_wf(func.locals.contains_key(local), \"Statement::StorageLive: invalid local variable\")?;
>  }"
`Deinit` only without projections: Anneal's `Deinit` of a projected place reads
the projected value and leaves the slot initialized, whereas MiniRust's writes
`Uninit` to the projected bytes). `storageDeadOk` restricts `StorageDead`
further. -/
def statementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      if isBoolTy d.ty then rvalueOkB layouts decls (copyRv rv)
      else if isOrderingTy d.ty then rvalueOkO layouts decls (copyRv rv)
      else
        match intBoolTupleOf d.ty with
        | some it => rvalueOkTuple layouts decls it (copyRv rv)
        | none =>
          match intTypeOf d.ty with
          | some it => rvalueOk layouts decls it (copyRv rv) || ptrDerefReadOk decls it (copyRv rv)
          | none =>
            match arrayTypeOf d.ty with
            | some (elemIt, count) => arrayRvalueOk layouts decls elemIt count rv
            | none =>
              match tupleTypeOf layouts d.ty with
              | some (fields, size, align) =>
                tupleRvalueOk layouts decls d.ty fields size align rv
              | none =>
                match ptrPointeeOf d.ty with
                | some (mutbl, pointeeIt) =>
                  ptrRvalueOk layouts decls mutbl pointeeIt (copyRv rv)
                | none => false
  | .assign ⟨i, .field idx fieldTy :: rest⟩ rv =>
    (decls[i]? >>= (tupleTypeOf layouts ·.ty)).isSome &&
    match placeIntType layouts decls ⟨i, .field idx fieldTy :: rest⟩ with
    | some it =>
      placeOk layouts decls it ⟨i, .field idx fieldTy :: rest⟩ &&
      rvalueOk layouts decls it rv
    | none =>
      match tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: rest⟩,
            placeMirTy decls ⟨i, .field idx fieldTy :: rest⟩ with
      | some (fields, size, align), some dstTy =>
        tupleRvalueOk layouts decls dstTy fields size align rv
      | _, _ => false
  | .assign ⟨i, [.deref]⟩ rv =>
    decide (i < decls.length) &&
    match decls[i]? >>= (ptrPointeeOf ·.ty) with
    | some (.mut, pointeeIt) => rvalueOk layouts decls pointeeIt rv
    | _ => false
  | .assign ⟨i, [proj]⟩ rv =>
    match decls[i]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) =>
      projOk decls count proj && rvalueOk layouts decls elemIt rv
    | none => false
  | .placeMention p => mentionPlaceOk layouts decls p
  | .storageLive i | .storageDead i =>
    decide (i < decls.length) &&
    match decls[i]? with
    | some d => (scalarTypeOf d.ty).isSome || isPtrTy d.ty
    | none => false
  | .deinit ⟨i, []⟩ =>
    decide (i < decls.length) &&
    match decls[i]? with
    | some d => (scalarTypeOf d.ty).isSome || isPtrTy d.ty
    | none => false
  | _ => false

/-- A fragment `switchInt` discriminant: an integer operand of its type, or a
`bool` operand. -/
def discrOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (discr : MirAst.Operand) : Bool :=
  match operandType layouts decls discr with
  | some (.Int it) => operandOk layouts decls it discr
  | some .Bool => operandOkB layouts decls discr
  | _ => false

/-- Fragment terminators; jump targets must be blocks of the body and
`switchInt` values must be distinct in-range bit patterns of the type
`minimize` switches at (`switchIntType`: the discriminant's integer type, or
`u8` for a `bool`). The discriminant is checked through `copyOp`. -/
def terminatorOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match switchIntType layouts decls (copyOp discr) with
    | some it =>
      discrOk layouts decls (copyOp discr) &&
      targets.branches.all (fun p => decide (p.1 < 2 ^ (8 * it.size.bytes)) && decide (p.2 < nblocks)) &&
      (targets.branches.map Prod.fst).Nodup &&
      decide (targets.otherwise < nblocks)
    | none => false
  | .unreachable => true
  | .return_ => true
  | _ => false

/-- `StorageDead` only of temporaries: MiniRust's well-formedness check
(`spec/lang/well-formed.md`) rejects it for the return place and the
arguments:
> "StorageDead(local) => {
>      ensure_wf(func.locals.contains_key(local), \"Statement::StorageDead: invalid local variable\")?;
>      if local == func.ret || func.args.any(|arg_name| local == arg_name) {
>          throw_ill_formed!(\"Statement::StorageDead: trying to mark argument or return local as dead\");
>      }
>  }" -/
def storageDeadOk (body : MirAst.CapturedMir) : Bool :=
  body.basicBlocks.all fun bb =>
    bb.statements.all fun s =>
      match s.kind with
      | .storageDead i => decide (body.argCount < i)
      | _ => true

/-! ### Moved-out locals

The CFG dataflow check `movesOk` described in the module docs. Forward
propagation across `Goto` and `SwitchInt` edges computes the set of locals
`movedAtEntry body blk` that may be moved out on entry to each block `blk`,
and `movesOk` verifies both intra-block safety (`blockMovesOk`) and edge
closure across every control-flow transition. -/

/-- The local that a fragment operand moves out of: Anneal's `evalOperand`
sets the slot of `_j` to `.uninit` when it reads `move _j` ("reading a root
local via `Operand.move` transitions its slot to `.uninit`"), whereas a
projected `move (_j.f)` leaves `_j` initialized. -/
def opMoved : MirAst.Operand → Option Nat
  | .move ⟨j, []⟩ => some j
  | _ => none

/-- The root local of a fragment operand. -/
def opRead : MirAst.Operand → Option Nat
  | .copy p | .move p => some p.local_
  | .constant _ => none

/-- All locals referenced by a place (its root local, plus `idxLocal` for
`ProjectionElem.index idxLocal`). -/
def placeLocals : MirAst.Place → List Nat
  | ⟨j, [.index k]⟩ => [j, k]
  | ⟨j, _⟩ => [j]

/-- All locals read when evaluating an operand (`placeLocals` for `copy`/`move`,
none for constants). -/
def opLocals : MirAst.Operand → List Nat
  | .copy p | .move p => placeLocals p
  | .constant _ => []

/-- Whether every projection element in `projs` is `ProjectionElem.field`. -/
def allFields : List MirAst.ProjectionElem → Bool
  | [] => true
  | .field _ _ :: rest => allFields rest
  | _ => false

/-- Projection lists admitted on fragment operands: field chains, `[.index _]`,
or `[.constantIndex _ _ _]`. -/
def simpleProj : List MirAst.ProjectionElem → Bool
  | [.index _] | [.constantIndex _ _ _] => true
  | projs => allFields projs

/-- Whether an operand is a constant or a `copy`/`move` of a `simpleProj`
place: the operand shapes that `statementOk` and `terminatorOk` admit. Reading
one reads at most `opLocals op`. -/
def simpleOp : MirAst.Operand → Bool
  | .constant _ => true
  | .copy ⟨_, projs⟩ | .move ⟨_, projs⟩ => simpleProj projs

/-- The operands of an rvalue in the order in which Anneal's `evalRvalue`
evaluates them (left to right). -/
def rvOperands : MirAst.Rvalue → List MirAst.Operand
  | .use op | .repeat op _ | .unaryOp _ op | .cast _ op _ => [op]
  | .len p => [.copy p]
  | .binaryOp _ a b => [a, b]
  | .aggregate _ ops => ops
  | _ => []

/-- Mark the local that `op` moves out of. -/
def moveOut (mo : List Nat) (op : MirAst.Operand) : List Nat :=
  match opMoved op with
  | some j => j :: mo
  | none => mo

/-- Whether the operands `ops`, read in order with the moved-out locals `mo`,
are simple (`simpleOp`, which the other checks already imply) and avoid every
moved-out local, including those that earlier operands move out of. -/
def readsOk : List Nat → List MirAst.Operand → Bool
  | _, [] => true
  | mo, op :: ops =>
    (simpleOp op && (opLocals op).all (fun j => !mo.contains j)) &&
    readsOk (moveOut mo op) ops

/-- The moved-out locals after statement `s`: those its operands move out of,
minus the root local it writes (a root assignment's destination, or the local of
`StorageLive`, `StorageDead`, or root `Deinit`, after which both models agree
that the local is unallocated or holds the same bytes; a projected assignment
records its operand moves without clearing the destination root local). -/
def stmtMoved (mo : List Nat) (s : MirAst.Statement) : List Nat :=
  match s.kind with
  | .assign ⟨i, []⟩ rv => ((rvOperands rv).foldl moveOut mo).filter (· != i)
  | .assign ⟨_, _ :: _⟩ rv => (rvOperands rv).foldl moveOut mo
  | .storageLive i | .storageDead i | .deinit ⟨i, []⟩ => mo.filter (· != i)
  | _ => mo

/-- Whether statement `s` reads no moved-out local (including `_p` on a raw
pointer dereference read `*_p`, `idxLocal` on an indexed destination
`_i[_k] = rv`, and the destination root `_i` on a projected assignment
`_i.proj = rv` / `(*_p) = rv`). -/
def stmtReadsOk (mo : List Nat) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨_, []⟩ (.use (.copy ⟨p, .deref :: _⟩))
  | .assign ⟨_, []⟩ (.use (.move ⟨p, .deref :: _⟩)) => !mo.contains p
  | .assign ⟨_, []⟩ rv => readsOk mo (rvOperands rv)
  | .assign p@⟨_, _ :: _⟩ rv =>
    readsOk mo (rvOperands rv) &&
    let mo' := (rvOperands rv).foldl moveOut mo
    (placeLocals p).all (fun j => !mo'.contains j)
  | _ => true

/-- Whether terminator `t` reads no moved-out local (`Return` reads `_0`). -/
def termReadsOk (mo : List Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .switchInt discr _ => readsOk mo [discr]
  | .return_ => !mo.contains 0
  | _ => true

/-- The moved-out locals after terminator `t` reads its operand. -/
def termMoved (mo : List Nat) (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => moveOut mo discr
  | _ => mo

/-- The successor block indices of terminator `t`. -/
def termTargets (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .goto target => [target]
  | .switchInt _ targets => targets.otherwise :: targets.branches.map Prod.snd
  | _ => []

/-- Add elements of `xs` not already present in `acc`. -/
def unionLocals (acc xs : List Nat) : List Nat :=
  xs.foldl (fun a j => if a.contains j then a else j :: a) acc

/-- One forward CFG pass propagating moved-out locals from every block's exit
to its successor blocks' entries. -/
def stepMovedEntries (bbs : List MirAst.BasicBlockData) (entries : List (List Nat)) :
    List (List Nat) :=
  (List.range bbs.length).map fun dst =>
    (List.range bbs.length).foldl (fun acc src =>
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let mo := entries.getD src []
          let exitMo := termMoved (bb.statements.foldl stmtMoved mo) bb.terminator
          unionLocals acc exitMo
        else acc
      | none => acc) (entries.getD dst [])

/-- Iterate forward moved-out propagation up to `fuel` passes, stopping early
as soon as the per-block entry sets stabilize. -/
def iterMovedEntries : Nat → List MirAst.BasicBlockData → List (List Nat) → List (List Nat)
  | 0, _, entries => entries
  | n + 1, bbs, entries =>
    let entries' := stepMovedEntries bbs entries
    if entries' == entries then entries
    else iterMovedEntries n bbs entries'

/-- The locals that may be moved out on entry to block `blk`. For `N ≥ 1`
blocks whose moved-out local indices lie below `L = body.localDecls.length`,
one pass expands `[]` to `N` entry lists and at most `N * L` further passes add
distinct moved-out locals `< L`, so `1 + N * L ≤ N * (L + 1)` passes always
reach a fixed point (`iterMovedEntries_stabilizes`). -/
def movedAtEntry (body : MirAst.CapturedMir) (blk : Nat) : List Nat :=
  let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
  (iterMovedEntries fuel body.basicBlocks []).getD blk []

/-- The locals that may be moved out before statement `stmt` of block `blk`. -/
def movedBefore (body : MirAst.CapturedMir) (blk stmt : Nat) : List Nat :=
  match body.basicBlocks[blk]? with
  | some bb => (bb.statements.take stmt).foldl stmtMoved (movedAtEntry body blk)
  | none => movedAtEntry body blk

/-- Whether a block whose statements are `ss` and whose terminator is `t`,
entered with the moved-out locals `mo`, never reads a moved-out local. -/
def blockMovesOk (mo : List Nat) : List MirAst.Statement → MirAst.Terminator → Bool
  | [], t => termReadsOk mo t
  | s :: ss, t => stmtReadsOk mo s && blockMovesOk (stmtMoved mo s) ss t

/-- No moved-from local is read before it is re-initialized along any CFG path. -/
def movesOk (body : MirAst.CapturedMir) : Bool :=
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      let mo := movedAtEntry body blk
      let exitMo := termMoved (bb.statements.foldl stmtMoved mo) bb.terminator
      blockMovesOk mo bb.statements bb.terminator &&
      (termTargets bb.terminator).all (fun t =>
        exitMo.all (fun j => (movedAtEntry body t).contains j))
    | none => true

/-! ### Locals mentioned by the body -/

/-- The locals a statement mentions. -/
def stmtLocals (s : MirAst.Statement) : List Nat :=
  match s.kind with
  | .assign p (.rawPtr _ q) => placeLocals p ++ placeLocals q
  | .assign p rv => placeLocals p ++ (rvOperands rv).flatMap opLocals
  | .placeMention p | .deinit p => placeLocals p
  | .storageLive i | .storageDead i => [i]
  | _ => []

/-- The locals a terminator mentions (`Return` reads `_0`). -/
def termLocals (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => opLocals discr
  | .return_ => [0]
  | _ => []

/-- No statement or terminator mentions a local that `initBlock` allocates. -/
def mentionsOk (body : MirAst.CapturedMir) : Bool :=
  body.basicBlocks.all fun bb =>
    bb.statements.all (fun s => (stmtLocals s).all (fun j => !(alwaysStorageLiveLocals body).contains j)) &&
    (termLocals bb.terminator).all (fun j => !(alwaysStorageLiveLocals body).contains j)

/-! ### Raw-pointer borrow discipline -/

/-- All locals `k` whose address is taken via `.rawPtr _ ⟨k, _⟩` anywhere in `body`. -/
def bodyAddrTakenLocals (body : MirAst.CapturedMir) : List Nat :=
  body.basicBlocks.flatMap fun bb =>
    bb.statements.filterMap fun s =>
      match s.kind with
      | .assign _ (.rawPtr _ q) => some q.local_
      | _ => none

/-- All locals `k` whose mutable address is taken via `.rawPtr .mut ⟨k, _⟩` in `body`. -/
def bodyMutAddrTakenLocals (body : MirAst.CapturedMir) : List Nat :=
  body.basicBlocks.flatMap fun bb =>
    bb.statements.filterMap fun s =>
      match s.kind with
      | .assign _ (.rawPtr .mut q) => some q.local_
      | _ => none

/-- Whether `s` neither directly writes/deinits/changes storage of any local in
`addrLocals` nor moves out any local in `addrLocals`. -/
def stmtPreservesAddrTaken (addrLocals : List Nat) (s : MirAst.Statement) : Bool :=
  let moveFree (ops : List MirAst.Operand) : Bool :=
    ops.all fun op =>
      match opMoved op with
      | some j => !addrLocals.contains j
      | none => true
  match s.kind with
  | .assign dst rv => !addrLocals.contains dst.local_ && moveFree (rvOperands rv)
  | .deinit p => !addrLocals.contains p.local_
  | .storageLive i | .storageDead i => !addrLocals.contains i
  | _ => true

/-- Whether `t` moves out no local in `addrLocals`. -/
def termPreservesAddrTaken (addrLocals : List Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .switchInt discr _ =>
    match opMoved discr with
    | some j => !addrLocals.contains j
    | none => true
  | _ => true

/-- Pairwise projection disjointness of `&raw` borrows of locals in `mutLocals`
within an acyclic entry block. -/
def rawPtrListDisjoint (mutLocals : List Nat) : List MirAst.Statement → Bool
  | [] => true
  | s :: rest =>
    (match s.kind with
      | .assign _ (.rawPtr _ ⟨k, projs1⟩) =>
        if mutLocals.contains k then
          rest.all fun s' =>
            match s'.kind with
            | .assign _ (.rawPtr _ ⟨k', projs2⟩) =>
              decide (k ≠ k') ||
              (!MirSemantics.projectionsOverlap projs1 projs2 &&
               !MirSemantics.projectionsOverlap projs2 projs1)
            | _ => true
        else true
      | _ => true) &&
    rawPtrListDisjoint mutLocals rest

/-- Whether no statement in `stmts` takes a `&raw` borrow of a local in `mutLocals`. -/
def noMutAddrOfInStmts (mutLocals : List Nat) (stmts : List MirAst.Statement) : Bool :=
  stmts.all fun s =>
    match s.kind with
    | .assign _ (.rawPtr _ ⟨k, _⟩) => !mutLocals.contains k
    | _ => true

/-- Static aliasing discipline aligning Anneal's per-borrow Tree Borrows tags
with MiniRust's flat byte-level `BasicMemory` (where `retag_ptr` is the
identity):
1. Every address-taken local `k` is a parameter (`1 ≤ k ≤ body.argCount`) that
   is never directly assigned, deinited, storage-cycled, or moved out.
2. Whenever a local `k` has at least one mutable raw borrow (`&raw mut`), `bb0`
   has no incoming CFG edges, all `&raw` borrows of `k` occur in `bb0`, and
   distinct `&raw` borrows of `k` in `bb0` target pairwise non-overlapping
   projections (`projectionsOverlap = false`), so writes through any `*mut`
   pointer never disable another live borrow tag in Anneal. -/
def ptrAliasingOk (body : MirAst.CapturedMir) : Bool :=
  let addrLocals := bodyAddrTakenLocals body
  let mutLocals := bodyMutAddrTakenLocals body
  addrLocals.all (fun k => decide (1 ≤ k ∧ k ≤ body.argCount)) &&
  body.basicBlocks.all (fun bb =>
    bb.statements.all (stmtPreservesAddrTaken addrLocals) &&
    termPreservesAddrTaken addrLocals bb.terminator) &&
  (mutLocals.isEmpty ||
    (body.basicBlocks.all (fun bb => !(termTargets bb.terminator).contains 0) &&
     (match body.basicBlocks with
      | [] => true
      | bb0 :: restBbs =>
        rawPtrListDisjoint mutLocals bb0.statements &&
        restBbs.all (fun bb => noMutAddrOfInStmts mutLocals bb.statements))))

/-- Well-formedness of a local declaration in the fragment: a scalar-family
type (`scalarTypeOf`), a thin raw pointer to an integer (`isPtrTy`), a
homogeneous 1D integer array whose byte size fits in signed 64-bit `isize`
(`< 2 ^ 63`), or a well-formed tuple / single-variant struct (`TupleSpec.wf`). -/
def localDeclOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (d : MirAst.LocalDecl) : Bool :=
  (scalarTypeOf d.ty).isSome || isPtrTy d.ty ||
  match arrayTypeOf d.ty with
  | some (elemIt, count) => decide (count * elemIt.size.bytes < 2 ^ 63)
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (fields, size, align) => (TupleSpec.tuple fields size align).wf
    | none => false

/-- The decidable fragment on which the correspondence theorem is stated. The
condition `argCount + 1 ≤ localDecls.length` ensures that `_0` (`f.ret`) and
`_1 .. _argCount` (`f.args`) are distinct declared keys of `f.locals`, matching
`Function::check_wf` (`spec/lang/well-formed.md`):
> "let mut start_live: Set<LocalName> = Set::new();
>  for arg in self.args {
>      ensure_wf(self.locals.contains_key(arg),
>          \"Function: argument local does not exist\")?;
>      if start_live.try_insert(arg).is_err() {
>          throw_ill_formed!(
>              \"Function: two arguments refer to the same local\");
>      };
>  }
>  ensure_wf(self.locals.contains_key(self.ret),
>      \"Function: return local does not exist\")?;
>  if start_live.try_insert(self.ret).is_err() {
>      throw_ill_formed!(
>          \"Function: return local is also used for an argument\");
>  };"
The bound `localDecls.length < 2^31` keeps the first-fit candidate addresses of
`BM.pickAddr` that the callee's locals can occupy below `2^63`. -/
def inFragment (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  (body.localDecls[0]? >>= (scalarTypeOf ·.ty)).isSome &&
  body.localDecls.all (localDeclOk body.layouts) &&
  ((body.localDecls.drop 1).take body.argCount).all (fun d => !isPtrTy d.ty) &&
  (body.localDecls.drop (body.argCount + 1)).all
    (fun d => (scalarTypeOf d.ty).isSome || isPtrTy d.ty) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.localDecls · body.layouts) &&
    terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator) &&
  storageDeadOk body && movesOk body && mentionsOk body && ptrAliasingOk body &&
  (translateFn body).isSome

end MiniRustSpec.Correspondence
