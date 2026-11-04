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

* the body declares exactly the return place and the arguments
  (`localDecls.length = argCount + 1`), all of integer, `bool`,
  `core::cmp::Ordering`, or `(Int, bool)` 2-tuple type;
* statements are `_i = Use(copy _j)`, `_i = Use(copy (_j.0))`, `_i = Use(const c)`,
  `_i = UnaryOp(uop, a)` with `uop ∈ {Neg, Not}`,
  `_i = BinaryOp(op, a, b)` with
  `op ∈ {Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr, Shl, Shr, AddUnchecked, SubUnchecked, MulUnchecked, ShlUnchecked, ShrUnchecked}`
  (`a` of `_i`'s integer type `it`, and `b` of `it` for homogeneous binary
  operators or of any integer type `rhsIt` for the shift operators
  `Shl, Shr, ShlUnchecked, ShrUnchecked`),
  `_i = Cast(IntToInt, a, targetTy)` (casting an operand `a` of any integer
  type `srcIt` or `bool` to the destination local's integer type `it`), all
  for an integer `_i`; and, for a `bool` `_i`, `_i = Use(a)`, `_i =
  UnaryOp(Not, a)` (`boolNot`), and `_i = BinaryOp(BitAnd | BitOr | BitXor, a,
  b)` (`boolBitOp`) with `bool` operands, and the comparisons
  `_i = BinaryOp(Eq | Ne | Lt | Le | Gt | Ge, a, b)` of two integer operands
  of one type or of two `bool` operands; for an `Ordering` `_i`, `_i =
  Use(copy _j)` of an `Ordering` local and the three-way comparison
  `_i = BinaryOp(Cmp, a, b)` of such operands; for an `(it, bool)` 2-tuple `_i`,
  `_i = Use(copy _j)` of an `(it, bool)` local, the checked integer operations
  `_i = BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, a, b)` of
  two integer operands of type `it`, and `_i = Aggregate(Tuple, [a, b])` of an
  integer operand `a` of type `it` and a `bool` operand `b`; every operand is
  `copy _j`, a 2-tuple field projection `copy (_j.0)` or `copy (_j.1)`, or a
  scalar constant; or `PlaceMention(_i)`;
* terminators are `Goto`, `SwitchInt` on an integer or `bool` operand
  (`copy _j` or constant), `Unreachable`, or `Return`, and every jump target is
  a block of the body;
* no block is a cleanup block.

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

`Operand::Move` is excluded on purpose: `minimize` translates it exactly like
`Copy` ("smir::Operand::Move(place) => ValueExpr::Load { .. }"), while Anneal's
MIR semantics de-initializes the moved-from place. The two models genuinely
disagree on later reads of a moved-from local, so `Move` cannot be in a
lock-step fragment; `minirust/README.md` lists this and the other gaps.
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

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- `minimize`'s place translation for locals and single-level field
projections (`tooling/minimize/src/rvalue.rs`):
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
>              }" -/
def translatePlace : MirAst.Place → Option Gen.PlaceExpr
  | ⟨j, []⟩ => some (.Local (localName j))
  | ⟨j, [.field f _]⟩ => some (.Field (.Local (localName j)) (f : Int))
  | _ => none

/-- Integer type of a fragment operand: `copy _j` has `_j`'s declared type,
`copy (_j.0)` on an `(it, bool)` local has type `it`, and a constant carries
its type. -/
def operandIntType (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy ⟨j, []⟩ => decls[j]? >>= fun d => intTypeOf d.ty
  | .copy ⟨j, [.field 0 fTy]⟩ => do
    let d ← decls[j]?
    let it ← intBoolTupleOf d.ty
    let fIt ← intTypeOf fTy
    if fIt == it then some it else none
  | .constant c => intTypeOf c.ty
  | _ => none

/-- MiniRust type of a fragment operand (including `copy (_j.0)` and
`copy (_j.1)` field projections on an `(it, bool)` tuple local). -/
def operandType (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.Type
  | .copy ⟨j, []⟩ => decls[j]? >>= fun d => scalarTypeOf d.ty
  | .copy ⟨j, [.field 0 fTy]⟩ => do
    let d ← decls[j]?
    let it ← intBoolTupleOf d.ty
    let fIt ← intTypeOf fTy
    if fIt == it then some (.Int it) else none
  | .copy ⟨j, [.field 1 fTy]⟩ => do
    let d ← decls[j]?
    let _ ← intBoolTupleOf d.ty
    if isBoolTy fTy then some .Bool else none
  | .constant c => scalarTypeOf c.ty
  | _ => none

/-- `minimize`'s operand translation (`tooling/minimize/src/rvalue.rs`):
> "smir::Operand::Constant(c) => self.translate_const_smir(&c.const_, span),
>  smir::Operand::Copy(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },"
restricted to fragment places (`PlaceExpr::Local` and `PlaceExpr::Field`, see
`translatePlace`) and scalar constants. For an integer constant,
`translate_const_val` (`tooling/minimize/src/constant.rs`) reads the scalar at
the constant's type, which is `Constant::Int(int_from_bits(..))`; for a `bool`
constant it reads a `bool`, which rustc's `Scalar::to_bool` accepts only for
the one-byte patterns `0` and `1`:
> "Type::Bool => {
>      let val = ecx.read_scalar(&val).unwrap().to_bool().unwrap();
>      ValueExpr::Constant(Constant::Bool(val), ty)
>  }" (`tooling/minimize/src/constant.rs`) -/
def translateOperand : MirAst.Operand → Option Gen.ValueExpr
  | .copy p => (translatePlace p).map .Load
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
  | _ => none

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

/-- `minimize`'s rvalue translation for `Use`, `UnaryOp(Neg | Not)` on
integers, `UnaryOp(Not)` on `bool`, integer `BinaryOp`s, checked integer
`BinaryOp`s (`AddWithOverflow | SubWithOverflow | MulWithOverflow`), `bool`
bitwise `BinaryOp`s (`BitAnd | BitOr | BitXor` via `boolBitOp`), the comparison
`BinaryOp`s (including the three-way `Cmp`, `translateCmp`), `Aggregate` on
2-tuples `(Int, bool)`, and `Cast(CastKind::IntToInt)` on integers and `bool`
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
and the comparisons apply to operands of any type. -/
def translateRvalue (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand op
  | .unaryOp uop op => do
    let e ← translateOperand op
    match operandType decls op with
    | some (.Int _) => pure (.UnOp (.Int (← translateUnOp uop)) e)
    | some .Bool =>
      match uop with
      | .not => pure (boolNot e)
      | _ => none
    | _ => none
  | .binaryOp op l r => do
    let el ← translateOperand l
    let er ← translateOperand r
    match translateRelOp op with
    | some rel => pure (.BinOp (.Rel rel) el er)
    | none =>
      match translateBinOp op with
      | some iop =>
        match operandType decls l with
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
          | _ => none
  | .aggregate .tuple [op0, op1] => do
    let e0 ← translateOperand op0
    let e1 ← translateOperand op1
    let it ← operandIntType decls op0
    pure (.Tuple [e0, e1] (intBoolTupleTy it))
  | .cast .intToInt op targetTy => do
    let intTy ← intTypeOf targetTy
    let operand ← translateOperand op
    match operandType decls op with
    | some (.Int _) => pure (.UnOp (.Cast (.IntToInt intTy)) operand)
    | some .Bool => pure (.UnOp (.Cast (.IntToInt intTy)) (boolToU8 operand))
    | _ => none
  | _ => none

/-- `minimize`'s statement translation for assignments to projection-free locals
and `PlaceMention` on a fragment place (`_i`, `_i.0`, or `_i.1`,
`tooling/minimize/src/bb.rs`):
> "rs::StatementKind::Assign(operands) => {
>      let (place, rval) = &**operands;
>      let destination = self.translate_place(place, span);
>      ..
>      let source = self.translate_rvalue(rval, span);
>      Statement::Assign { destination, source }
>  }
>  ..
>  rs::StatementKind::PlaceMention(place) => {
>      let place = self.translate_place(place, span);
>      Statement::PlaceMention(place)
>  }"
where the elided part special-cases two pointer-provenance casts, which are
outside the fragment. -/
def translateStatement (decls : List MirAst.LocalDecl) (s : MirAst.Statement) :
    Option Gen.Statement :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    (translateRvalue decls rv).map (fun src => .Assign (.Local (localName i)) src)
  | .placeMention p => (translatePlace p).map .PlaceMention
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
def switchIntType (decls : List MirAst.LocalDecl) (discr : MirAst.Operand) : Option Gen.IntType :=
  match operandType decls discr with
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
`1`. -/
def translateTerminator (decls : List MirAst.LocalDecl) (t : MirAst.Terminator) :
    Option Gen.Terminator :=
  match t.kind with
  | .goto target => some (.Goto (bbName target))
  | .switchInt discr targets => do
    let discrOp ← translateOperand discr
    match operandType decls discr with
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
def translateBlock (decls : List MirAst.LocalDecl) (bb : MirAst.BasicBlockData) :
    Option Gen.BasicBlock := do
  let stmts ← bb.statements.mapM (translateStatement decls)
  let term ← translateTerminator decls bb.terminator
  pure ⟨stmts, term, .Regular⟩

/-- `minimize`'s local-type map, one entry per MIR local in index order
(`tooling/minimize/src/function.rs`):
> "for (id, local_name) in &self.local_name_map {
>      let local_decl = &self.body.local_decls[*id];
>      let span = local_decl.source_info.span;
>      let ty = self.cx.translate_ty(local_decl.ty, span);
>      self.locals.insert(*local_name, ty);
>  }" -/
def translateLocals : Nat → List MirAst.LocalDecl → Option (List (Gen.LocalName × Gen.Type))
  | _, [] => some []
  | i, d :: ds => do
    let ty ← scalarTypeOf d.ty
    let rest ← translateLocals (i + 1) ds
    pure ((localName i, ty) :: rest)

/-- `minimize`'s block map, one entry per MIR block in index order
("for (id, bb_name) in self.bb_name_map.clone() { .. self.translate_bb(bb_name, bb_data); }"). -/
def translateBlocks (decls : List MirAst.LocalDecl) :
    Nat → List MirAst.BasicBlockData → Option (List (Gen.BbName × Gen.BasicBlock))
  | _, [] => some []
  | i, bb :: bbs => do
    let b ← translateBlock decls bb
    let rest ← translateBlocks decls (i + 1) bbs
    pure ((bbName i, b) :: rest)

/-- The init block `minimize` prepends (see `translateFn`). -/
def initBlock : Gen.BasicBlock := ⟨[], .Goto (bbName 0), .Regular⟩

/-- `minimize`'s function translation (`tooling/minimize/src/function.rs`),
specialized to bodies whose only locals are the return place and the arguments:

> "// add init basic block
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
>  ..
>  let ret = LocalName(Name::from_internal(0));
>  let f = Function { locals: self.locals, args, ret, blocks: self.blocks, start: init_bb,
>      calling_convention: translate_calling_convention(self.abi.conv),
>      implicit_writes: self.implicit_writes, };"

With no locals beyond the return place and arguments, the `filter` leaves no
`StorageLive`, so the init block is a lone `Goto(bb0)`. We take the
calling convention to be `Rust` and `implicit_writes` to be `true` (the
`minimize` default absent `#[rustc_no_writable]`); neither is read by the
interpreted fragment. -/
def translateFn (body : MirAst.CapturedMir) : Option Gen.Function := do
  let locals ← translateLocals 0 body.localDecls
  let blocks ← translateBlocks body.localDecls 0 body.basicBlocks
  let n := body.basicBlocks.length
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨blocks ++ [(bbName n, initBlock)]⟩
    start := bbName n
    implicit_writes := true
  }

/-! ## The fragment -/

/-- A fragment integer operand of type `it`: an integer local `copy _j`, field
0 `copy (_j.0)` of an `(it, bool)` tuple local, or an integer constant. -/
def operandOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ | .copy ⟨j, [.field 0 _]⟩ =>
    decide (j < decls.length) && decide (operandIntType decls op = some it)
  | .constant _ =>
    decide (operandIntType decls op = some it) && (translateOperand op).isSome
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
def operandIsBool (decls : List MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  match operandType decls op with
  | some .Bool => true
  | _ => false

/-- A fragment `bool` operand: a `bool` local `copy _j`, field 1 `copy (_j.1)`
of an `(Int, bool)` tuple local, or a `bool` constant that `minimize` can read
(`0` or `1`). -/
def operandOkB (decls : List MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ | .copy ⟨j, [.field 1 _]⟩ =>
    decide (j < decls.length) && operandIsBool decls op
  | .constant _ => operandIsBool decls op && (translateOperand op).isSome
  | _ => false

/-- Fragment rvalues of integer type `it`. -/
def rvalueOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use op => operandOk decls it op
  | .unaryOp uop op => (translateUnOp uop).isSome && operandOk decls it op
  | .binaryOp op a b =>
    match translateBinOp op with
    | none => false
    | some iop =>
      operandOk decls it a &&
      if isShiftIntBinOp iop then
        match operandIntType decls b with
        | some rhsIt => operandOk decls rhsIt b
        | none => false
      else
        operandOk decls it b
  | .cast .intToInt op targetTy =>
    decide (intTypeOf targetTy = some it) &&
    match operandIntType decls op with
    | some srcIt => operandOk decls srcIt op
    | none => operandOkB decls op
  | _ => false

/-- The operands of a fragment comparison: both integers of one type, or both
`bool`s (MiniRust requires both operands of `BinOp::Rel` to have the same
type, `spec/lang/well-formed.md`:
> "ensure_wf(right == left, \"BinOp::Rel: invalid right type\")?;"
and MIR's comparisons are homogeneous as well). -/
def relOperandsOk (decls : List MirAst.LocalDecl) (a b : MirAst.Operand) : Bool :=
  match operandType decls a with
  | some (.Int it) => operandOk decls it a && operandOk decls it b
  | some .Bool => operandOkB decls a && operandOkB decls b
  | _ => false

/-- Fragment rvalues of type `bool`: a `bool` operand, `!b` on a `bool`
operand, `BitAnd | BitOr | BitXor` on two `bool` operands, or a comparison
(`==`, `!=`, `<`, `<=`, `>`, `>=`) of two integers of one type or of two
`bool`s. -/
def rvalueOkB (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Bool
  | .use op => operandOkB decls op
  | .unaryOp .not op => operandOkB decls op
  | .binaryOp op a b =>
    if (translateRelOp op).isSome then relOperandsOk decls a b
    else (translateBoolBitOp op).isSome && operandOkB decls a && operandOkB decls b
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
  | .constant _ => operandIsOrdering decls op && (translateOperand op).isSome
  | _ => false

/-- Fragment rvalues of type `core::cmp::Ordering`: an `Ordering` operand or
a three-way comparison `Cmp` of two integers of one type or of two `bool`s. -/
def rvalueOkO (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Bool
  | .use op => operandOkO decls op
  | .binaryOp .cmp a b => relOperandsOk decls a b
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
def rvalueOkTuple (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use op => operandOkTuple decls it op
  | .binaryOp op a b =>
    (translateCheckedBinOp op).isSome && operandOk decls it a && operandOk decls it b
  | .aggregate .tuple [a, b] => operandOk decls it a && operandOkB decls b
  | _ => false

/-- A fragment place: a local `_i`, field `0` (`_i.0`) of an `(Int, bool)`
tuple local, or field `1` (`_i.1`) of an `(Int, bool)` tuple local. -/
def placeOk (decls : List MirAst.LocalDecl) : MirAst.Place → Bool
  | ⟨i, []⟩ => decide (i < decls.length)
  | ⟨i, [.field 0 fieldTy]⟩ =>
    decide (i < decls.length) &&
    match decls[i]? with
    | some d =>
      match intBoolTupleOf d.ty, intTypeOf fieldTy with
      | some it, some fit => decide (fit = it)
      | _, _ => false
    | none => false
  | ⟨i, [.field 1 fieldTy]⟩ =>
    decide (i < decls.length) &&
    match decls[i]? with
    | some d => (intBoolTupleOf d.ty).isSome && isBoolTy fieldTy
    | none => false
  | _ => false

/-- Fragment statements, type-checked against the destination's type: an
integer destination takes an integer rvalue (`rvalueOk`), a `bool`
destination takes a `bool` rvalue (`rvalueOkB`), an `Ordering` destination
takes a three-way comparison (`rvalueOkO`), an `(it, bool)` 2-tuple
destination takes a 2-tuple rvalue (`rvalueOkTuple`), and `PlaceMention` takes
any fragment place (`placeOk`). -/
def statementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      if isBoolTy d.ty then rvalueOkB decls rv
      else if isOrderingTy d.ty then rvalueOkO decls rv
      else
        match intBoolTupleOf d.ty with
        | some it => rvalueOkTuple decls it rv
        | none =>
          match intTypeOf d.ty with
          | none => false
          | some it => rvalueOk decls it rv
  | .placeMention p => placeOk decls p
  | _ => false

/-- A fragment `switchInt` discriminant: an integer operand of its type, or a
`bool` operand. -/
def discrOk (decls : List MirAst.LocalDecl) (discr : MirAst.Operand) : Bool :=
  match operandType decls discr with
  | some (.Int it) => operandOk decls it discr
  | some .Bool => operandOkB decls discr
  | _ => false

/-- Fragment terminators; jump targets must be blocks of the body and
`switchInt` values must be distinct in-range bit patterns of the type
`minimize` switches at (`switchIntType`: the discriminant's integer type, or
`u8` for a `bool`). -/
def terminatorOk (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match switchIntType decls discr with
    | some it =>
      discrOk decls discr &&
      targets.branches.all (fun p => decide (p.1 < 2 ^ (8 * it.size.bytes)) && decide (p.2 < nblocks)) &&
      (targets.branches.map Prod.fst).Nodup &&
      decide (targets.otherwise < nblocks)
    | none => false
  | .unreachable => true
  | .return_ => true
  | _ => false

/-- The decidable fragment on which the correspondence theorem is stated. -/
def inFragment (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.localDecls.length = body.argCount + 1) &&
  body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.localDecls) &&
    terminatorOk body.localDecls body.basicBlocks.length bb.terminator) &&
  (translateFn body).isSome

end MiniRustSpec.Correspondence
