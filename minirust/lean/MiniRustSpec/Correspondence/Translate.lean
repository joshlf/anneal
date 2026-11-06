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

* the body declares the return place, the arguments, and any number of
  temporaries (`argCount + 1 ≤ localDecls.length < 2^31`), all of integer,
  `bool`, `core::cmp::Ordering`, or `(Int, bool)` 2-tuple type;
* statements are `_i = Use(a)`,
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
  of one type or of two `bool` operands; for an `Ordering` `_i`, `_i = Use(a)`
  of an `Ordering` local (`copy _j` or `move _j`) and the three-way comparison
  `_i = BinaryOp(Cmp, a, b)` of integer or `bool` operands; for an `(it, bool)`
  2-tuple `_i`, `_i = Use(a)` of an `(it, bool)` local (`copy _j` or `move _j`),
  the checked integer operations
  `_i = BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, a, b)` of
  two integer operands of type `it`, and `_i = Aggregate(Tuple, [a, b])` of an
  integer operand `a` of type `it` and a `bool` operand `b`; every operand is
  `copy _j` or `move _j`, a 2-tuple field projection `copy (_j.0)`,
  `copy (_j.1)`, `move (_j.0)`, or `move (_j.1)`, or a scalar constant;
  `PlaceMention(p)` of a fragment place; `StorageLive(_i)` of any local,
  `StorageDead(_i)` of a temporary (`_i` with `argCount < i`), and
  `Deinit(_i)` of a root local;
* terminators are `Goto`, `SwitchInt` on an integer or `bool` fragment operand
  (`copy _j`, `move _j`, 2-tuple field projection, or constant), `Unreachable`,
  `Return`, or (in `progInFragment`) direct monomorphic `Call`s to fragment
  callees, and every jump or call return target is a block of the body;
* no block in the source MIR body is a cleanup block (`translateUnwindAction`
  synthesizes MiniRust cleanup blocks for call unwind edges);
* no moved-from local is read before it is re-initialized (`movesOk`), call
  return places are must-live and disjoint from call arguments (`livenessOk`,
  `tupleInitOk`, `callTerminatorOk`), and every temporary the body mentions has
  explicit storage markers (`mentionsOk`); see below.

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
its type. A `move` operand is checked through `copyOp`. -/
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
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },
>  smir::Operand::Move(place) =>
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
  | .copy p | .move p => (translatePlace p).map .Load
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
  | .unaryOp uop op => .unaryOp uop (copyOp op)
  | .binaryOp bop a b => .binaryOp bop (copyOp a) (copyOp b)
  | .cast k op ty => .cast k (copyOp op) ty
  | .aggregate k ops => .aggregate k (ops.map copyOp)
  | rv => rv

theorem translateOperand_copyOp (op : MirAst.Operand) :
    translateOperand (copyOp op) = translateOperand op := by
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

/-- `minimize`'s statement translation for assignments to projection-free locals,
`StorageLive`, `StorageDead`, and `PlaceMention` on a fragment place (`_i`,
`_i.0`, or `_i.1`, `tooling/minimize/src/bb.rs`):
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
outside the fragment. The rvalue goes through `copyRv` because `minimize`
translates `move` and `copy` operands alike. `minimize` at the pinned commit
has no case for MIR's `StatementKind::Deinit`, which Anneal's MIR does
contain; we translate `Deinit(place)` to MiniRust's `Statement::Deinit` of the
translated place, the statement with the same meaning ("This writes `uninit`
bytes to the entire place", `compiler/rustc_middle/src/mir/syntax.rs`;
"This statement replaces the contents of a place with `Uninit`",
`spec/lang/step/statements.md`). -/
def translateStatement (decls : List MirAst.LocalDecl) (s : MirAst.Statement) :
    Option Gen.Statement :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    (translateRvalue decls (copyRv rv)).map (fun src => .Assign (.Local (localName i)) src)
  | .placeMention p => (translatePlace p).map .PlaceMention
  | .storageLive i => some (.StorageLive (localName i))
  | .storageDead i => some (.StorageDead (localName i))
  | .deinit p => (translatePlace p).map .Deinit
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
`1`. A `move` discriminant goes through `copyOp`, like an rvalue operand. -/
def translateTerminator (decls : List MirAst.LocalDecl) (t : MirAst.Terminator) :
    Option Gen.Terminator :=
  match t.kind with
  | .goto target => some (.Goto (bbName target))
  | .switchInt discr targets => do
    let discrOp ← translateOperand (copyOp discr)
    match operandType decls (copyOp discr) with
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
  let locals ← translateLocals 0 body.localDecls
  let blocks ← translateBlocks body.localDecls 0 body.basicBlocks
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

/-! ### Multi-function program translation (`Terminator::Call`) -/

/-- Monomorphic function index `idx` as a MiniRust `FnName`
(`tooling/minimize/src/program.rs`):
> "pub fn get_fn_name(&mut self, key: rs::Instance<'tcx>) -> FnName {
>      // Used as the fn name if it is not named yet.
>      let len = self.fn_name_map.len();
>
>      *self.fn_name_map.entry(key).or_insert_with(|| FnName(Name::from_internal(len as _)))
>  }" -/
def fnName (idx : Nat) : Gen.FnName :=
  ⟨⟨idx⟩⟩

@[simp]
theorem fnName_inj {i j : Nat} : fnName i = fnName j ↔ i = j := by
  simp [fnName]

/-- `build::fn_ptr(fn_name)`, which `minimize` emits for direct monomorphic
calls (`tooling/minimize/src/bb.rs`, line 874; `tooling/miniutil/src/build/expr.rs`,
lines 46-48 at the pinned commit:
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L46-L48>):
`ValueExpr::Constant(Constant::FnPointer(fn_name), Type::Ptr(PtrType::FnPtr))`. -/
def fnPtrExpr (fn : Gen.FnName) : Gen.ValueExpr :=
  .Constant (.FnPointer fn) (.Ptr .FnPtr)

/-- Extract the canonical `DefPath` from a constant monomorphic function-item
operand (`TyKind::FnDef`), matching `minimize`'s direct-call resolution
(`tooling/minimize/src/bb.rs`):
> "let fn_ty = func.ty(&self.body, self.tcx);
>  let (f, substs_ref) = match *fn_ty.kind() {
>      rs::TyKind::FnDef(id, substs) => (id, substs)," -/
def extractFnDefPath : MirAst.Operand → Option String
  | .constant c =>
    match c.ty.kind with
    | .fnDef defPath _ => some defPath
    | _ => none
  | _ => none

/-- Look up the `FnName` assigned to `defPath` in `fnMap`. -/
def lookupFnName : List (String × Gen.FnName) → String → Option Gen.FnName
  | [], _ => none
  | (dp, fn) :: rest, target =>
    if dp == target then some fn else lookupFnName rest target

/-- Assign `FnName(0)` to `entry` and `FnName(1), FnName(2), ..` to `callees`
in list order, matching `Ctxt::translate` and `Ctxt::get_fn_name`
(`tooling/minimize/src/program.rs`):
> "let entry_name = FnName(Name::from_internal(0));
>
>  self.fn_name_map.insert(entry_instance, entry_name);" -/
def fnNameMap (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir) :
    List (String × Gen.FnName) :=
  (entry :: callees).zipIdx.map fun (b, idx) => (b.defPath, fnName idx)

/-- `minimize`'s call-argument translation (`tooling/minimize/src/bb.rs`):
> "match &x.node {
>      rs::Operand::Move(place) =>
>          ArgumentExpr::InPlace(self.translate_place(&place, x.span)),
>      op => ArgumentExpr::ByValue(self.translate_operand(op, x.span)),
>  }"
Unlike statement rvalues (where `minimize` translates `Operand::Move` as
`ValueExpr::Load`), call arguments translate `Operand::Move(place)` as
`ArgumentExpr::InPlace`, so MiniRust's `eval_argument` calls
`prepare_for_inplace_passing` and writes `Uninit` bytes to the moved place. -/
def translateCallArg : MirAst.Operand → Option Gen.ArgumentExpr
  | .move p => (translatePlace p).map .InPlace
  | op => (translateOperand op).map .ByValue

/-- MiniRust's unit type `()`, used by `build::unit_place()` and `mk_start_fn`. -/
def unitTy : Gen.Type :=
  .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- `build::unit_place()`, a dangling aligned raw-pointer dereference of unit
type (`tooling/miniutil/src/build/expr.rs`, lines 55-65 at the pinned commit:
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs#L55-L65>). -/
def buildUnitPlace : Gen.PlaceExpr :=
  .Deref (.Constant (.PointerWithoutProvenance 1) (.Ptr (.Raw .None))) unitTy

/-- `build::abort()`, `Terminator::Intrinsic { intrinsic: IntrinsicOp::Abort, .. }`
(`tooling/miniutil/src/build/bb.rs`, lines 28-35 at the pinned commit:
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/bb.rs#L28-L35>). -/
def buildAbort : Gen.Terminator :=
  .Intrinsic .Abort [] buildUnitPlace none

/-- `minimize`'s translation of a call's `UnwindAction` in a non-cleanup basic
block (`tooling/minimize/src/bb.rs`):
> "rs::UnwindAction::Continue => {
>      // UnwindAction::Continue must only be used by a call in a regular block,
>      // therefore the unwind block should be a cleanup block.
>      assert!(
>          !bb.is_cleanup,
>          \"A call in a cleanup block cannot use UnwindAction::Continue\"
>      );
>      let block_kind = BbKind::Cleanup;
>      let unwind_bb_name = self.fresh_bb_name();
>      let unwind_bb = BasicBlock {
>          statements: list![],
>          terminator: Terminator::ResumeUnwind,
>          kind: block_kind,
>      };
>      self.blocks.insert(unwind_bb_name, unwind_bb);
>      unwind_bb_name
>  }
>  rs::UnwindAction::Unreachable => {
>      let block_kind = if bb.is_cleanup { BbKind::Terminate } else { BbKind::Cleanup };
>      let unwind_bb_name = self.fresh_bb_name();
>      let unwind_bb = BasicBlock {
>          statements: list![],
>          terminator: Terminator::Unreachable,
>          kind: block_kind,
>      };
>      self.blocks.insert(unwind_bb_name, unwind_bb);
>      unwind_bb_name
>  }
>  rs::UnwindAction::Terminate(_) => {
>      // FIXME: do not ignore UnwindTerminateReason
>      let block_kind = if bb.is_cleanup { BbKind::Terminate } else { BbKind::Cleanup };
>      let unwind_bb_name = self.fresh_bb_name();
>      let unwind_bb = BasicBlock {
>          statements: list![],
>          terminator: build::abort(),
>          kind: block_kind,
>      };
>      self.blocks.insert(unwind_bb_name, unwind_bb);
>      unwind_bb_name
>  }
>  rs::UnwindAction::Cleanup(cleanup_block) => self.bb_name_map[&cleanup_block],"
Returns `(unwindBb, nextCleanup', extraBlocks)`. -/
def translateUnwindAction (nextCleanup : Nat) :
    MirAst.UnwindAction → Gen.BbName × Nat × List (Gen.BbName × Gen.BasicBlock)
  | .continue_ =>
    let b := bbName nextCleanup
    (b, nextCleanup + 1, [(b, ⟨[], .ResumeUnwind, .Cleanup⟩)])
  | .unreachable =>
    let b := bbName nextCleanup
    (b, nextCleanup + 1, [(b, ⟨[], .Unreachable, .Cleanup⟩)])
  | .terminate =>
    let b := bbName nextCleanup
    (b, nextCleanup + 1, [(b, ⟨[], buildAbort, .Cleanup⟩)])
  | .cleanup cb =>
    (bbName cb, nextCleanup, [])

/-- `minimize`'s terminator translation extended with direct monomorphic calls
(`tooling/minimize/src/bb.rs`):
> "let unwind_block = Some(self.translate_unwind_action(unwind, bb));
>  ..
>  let callee = if let rs::InstanceKind::Virtual(_trait, method) = instance.def {
>      ..
>  } else {
>      build::fn_ptr(self.cx.get_fn_name(instance))
>  };
>
>  Terminator::Call {
>      callee,
>      calling_convention: conv,
>      arguments: args,
>      ret: self.translate_place(&destination, span),
>      next_block: target.as_ref().map(|t| self.bb_name_map[t]),
>      unwind_block,
>  }"
with `CallingConvention::Rust` (matching `translateFn`). Non-call terminators
delegate directly to `translateTerminator` and synthesize no extra cleanup
blocks. -/
def translateTerminatorInProg (fnMap : List (String × Gen.FnName))
    (decls : List MirAst.LocalDecl) (nextCleanup : Nat) (t : MirAst.Terminator) :
    Option (Gen.Terminator × Nat × List (Gen.BbName × Gen.BasicBlock)) :=
  match t.kind with
  | .call func argOps destination target unwind => do
    let defPath ← extractFnDefPath func
    let fn ← lookupFnName fnMap defPath
    let args ← argOps.mapM translateCallArg
    let retPlace ← translatePlace destination
    let (unwindBb, nextCleanup', extra) := translateUnwindAction nextCleanup unwind
    pure (.Call (fnPtrExpr fn) .Rust args retPlace (target.map bbName) (some unwindBb),
      nextCleanup', extra)
  | _ => do
    let term ← translateTerminator decls t
    pure (term, nextCleanup, [])

/-- Translate basic blocks in index order while threading `nextCleanup`
(starting at `body.basicBlocks.length + 1`, after `init_bb = bbName n` in
`FnCtxt::translate`) for any synthesized call unwind blocks. -/
def translateBlocksInProg (fnMap : List (String × Gen.FnName))
    (decls : List MirAst.LocalDecl) :
    Nat → Nat → List MirAst.BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock))
  | _, _, [] => some ([], [])
  | i, nextCleanup, bb :: bbs => do
    let stmts ← bb.statements.mapM (translateStatement decls)
    let (term, nextCleanup', extra1) ←
      translateTerminatorInProg fnMap decls nextCleanup bb.terminator
    let (rest, extraRest) ← translateBlocksInProg fnMap decls (i + 1) nextCleanup' bbs
    pure ((bbName i, ⟨stmts, term, .Regular⟩) :: rest, extra1 ++ extraRest)

/-- `FnCtxt::translate` for a function in a multi-function program: `init_bb`
takes `bbName n` (`n = body.basicBlocks.length`), and any cleanup blocks
synthesized by `translate_unwind_action` during block translation take
`bbName (n + 1), bbName (n + 2), ..` (`tooling/minimize/src/function.rs`). When
`body` contains no `Call` terminators, `extra` is empty and `translateFnInProg`
produces the exact same `Gen.Function` as `translateFn`. -/
def translateFnInProg (fnMap : List (String × Gen.FnName))
    (body : MirAst.CapturedMir) : Option Gen.Function := do
  let locals ← translateLocals 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, extra) ← translateBlocksInProg fnMap body.localDecls 0 (n + 1) body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := .Rust
    blocks := ⟨blocks ++ [(bbName n, initBlock body)] ++ extra⟩
    start := bbName n
    implicit_writes := true
  }

/-- `minimize`'s synthesized program-entry wrapper `mk_start_fn`
(`tooling/minimize/src/program.rs`):
> "fn mk_start_fn(entry: u32) -> Function {
>      let b0_name = BbName(Name::from_internal(0));
>      let b1_name = BbName(Name::from_internal(1));
>      let b2_name = BbName(Name::from_internal(2));
>      let l0_name = LocalName(Name::from_internal(0));" -/
def mkStartFn (entryIdx : Nat) : Gen.Function :=
  let b0Name := bbName 0
  let b1Name := bbName 1
  let b2Name := bbName 2
  let l0Name := localName 0
  let b0 : Gen.BasicBlock :=
    ⟨[], .Call (fnPtrExpr (fnName entryIdx)) .Rust [] buildUnitPlace (some b1Name) (some b2Name),
      .Regular⟩
  let b1 : Gen.BasicBlock :=
    ⟨[], .Intrinsic .Exit [] buildUnitPlace none, .Regular⟩
  let b2 : Gen.BasicBlock :=
    ⟨[], buildAbort, .Catch⟩
  { locals := ⟨[(l0Name, unitTy)]⟩
    args := []
    ret := l0Name
    blocks := ⟨[(b0Name, b0), (b1Name, b1), (b2Name, b2)]⟩
    start := b0Name
    calling_convention := .C
    implicit_writes := true }

/-- Translate `(entry :: callees)` in index order against `fnMap`. -/
def translateProgFns (fnMap : List (String × Gen.FnName)) :
    Nat → List MirAst.CapturedMir → Option (List (Gen.FnName × Gen.Function))
  | _, [] => some []
  | idx, b :: bs => do
    let f ← translateFnInProg fnMap b
    let rest ← translateProgFns fnMap (idx + 1) bs
    pure ((fnName idx, f) :: rest)

/-- `Ctxt::translate` for a multi-function MIR environment (`entry` + `callees`,
`tooling/minimize/src/program.rs`):
> "let number_of_fns = self.fn_name_map.len();
>
>  // add a `start` function, which calls `entry`.
>  let start = FnName(Name::from_internal(number_of_fns as _));
>  self.functions.insert(start, mk_start_fn(0));
>
>  Program {
>      start,
>      functions: self.functions,
>      globals: self.globals,
>      vtables: self.vtables,
>      traits: self.traits,
>  }" -/
def translateProg (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir) :
    Option Gen.Program := do
  let fnMap := fnNameMap entry callees
  let fns ← translateProgFns fnMap 0 (entry :: callees)
  let startFn := fnName (1 + callees.length)
  pure {
    functions := ⟨fns ++ [(startFn, mkStartFn 0)]⟩
    start := startFn
    globals := ⟨[]⟩
    vtables := ⟨[]⟩
    traits := ⟨[]⟩
  }

/-! ## The fragment -/

/-- A fragment integer operand of type `it`: an integer local `copy _j`, field
0 `copy (_j.0)` of an `(it, bool)` tuple local, or an integer constant. A
`move` operand is checked through `copyOp`. -/
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
takes a three-way comparison (`rvalueOkO`), and an `(it, bool)` 2-tuple
destination takes a 2-tuple rvalue (`rvalueOkTuple`), each checked through
`copyRv`; `PlaceMention` takes any fragment place (`placeOk`);
`StorageLive`, `StorageDead`, and `Deinit` take a declared local (fragment
locals have sized layout, and `Deinit` and `StorageLive` are well-formed in
`spec/lang/well-formed.md`:
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
def statementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      if isBoolTy d.ty then rvalueOkB decls (copyRv rv)
      else if isOrderingTy d.ty then rvalueOkO decls (copyRv rv)
      else
        match intBoolTupleOf d.ty with
        | some it => rvalueOkTuple decls it (copyRv rv)
        | none =>
          match intTypeOf d.ty with
          | none => false
          | some it => rvalueOk decls it (copyRv rv)
  | .placeMention p => placeOk decls p
  | .storageLive i | .storageDead i => decide (i < decls.length)
  | .deinit ⟨i, []⟩ => decide (i < decls.length)
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
`u8` for a `bool`). The discriminant is checked through `copyOp`. -/
def terminatorOk (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match switchIntType decls (copyOp discr) with
    | some it =>
      discrOk decls (copyOp discr) &&
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

/-- The local that a fragment operand reads. -/
def opRead : MirAst.Operand → Option Nat
  | .copy p | .move p => some p.local_
  | .constant _ => none

/-- Whether an operand is a constant, a local, or a field of a local: the
operand shapes that `statementOk` and `terminatorOk` admit. Reading one reads
at most the slot of its local. -/
def simpleOp : MirAst.Operand → Bool
  | .constant _ => true
  | .copy ⟨_, []⟩ | .move ⟨_, []⟩ => true
  | .copy ⟨_, [.field _ _]⟩ | .move ⟨_, [.field _ _]⟩ => true
  | _ => false

/-- The operands of an rvalue in the order in which Anneal's `evalRvalue`
evaluates them (left to right). -/
def rvOperands : MirAst.Rvalue → List MirAst.Operand
  | .use op | .unaryOp _ op | .cast _ op _ => [op]
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
    (simpleOp op &&
     match opRead op with
     | some j => !mo.contains j
     | none => true) && readsOk (moveOut mo op) ops

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

/-- Whether statement `s` reads no moved-out local. -/
def stmtReadsOk (mo : List Nat) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign _ rv => readsOk mo (rvOperands rv)
  | _ => true

/-- Whether terminator `t` reads no local in `mo`. For `Call`:
* MiniRust's `Terminator::Call` runs `prepare_for_inplace_passing(ret_place)`
  (writing `Uninit` to `ret_place`) *before* evaluating `arguments`, so
  `readsOk (dst :: mo) argOps` forbids `argOps` from reading either a stale
  local in `mo` or `dst`;
* a root destination `⟨dst, []⟩` overwrites `_dst` completely without reading
  its prior value (so `_dst = callee(..)` may re-initialize a moved-out local),
  whereas a projected destination `⟨dst, _ :: _⟩` (`_dst.f = callee(..)`)
  preserves the sibling field of `_dst` and requires `!mo.contains dst`. -/
def termReadsOk (mo : List Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .switchInt discr _ => readsOk mo [discr]
  | .return_ => !mo.contains 0
  | .call _ argOps ⟨dst, []⟩ _ _ => readsOk (dst :: mo) argOps
  | .call _ argOps ⟨dst, _ :: _⟩ _ _ => !mo.contains dst && readsOk (dst :: mo) argOps
  | _ => true

/-- The stale moved-out locals after terminator `t`: `SwitchInt` marks a moved
discriminant (lowered via `ValueExpr::Load`, which leaves initialized bytes in
MiniRust), whereas `Call` clears a root destination `_dst` on its `some target`
edge and does NOT add `Move` call arguments to `mo` (`callArgOk` restricts
`Call` `Move` arguments to root locals `⟨j, []⟩`, which `translateCallArg`
lowers to `ArgumentExpr::InPlace`, writing `Uninit` bytes in MiniRust too so
`_j` is uninitialized in both semantics rather than stale; `termTupleInit`
separately drops moved tuple locals via `dropMovedFrom`). -/
def termMoved (mo : List Nat) (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => moveOut mo discr
  | .call _ _ ⟨dst, []⟩ (some _) _ => mo.filter (· != dst)
  | _ => mo

/-- The successor block indices of terminator `t`. -/
def termTargets (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .goto target => [target]
  | .switchInt _ targets => targets.otherwise :: targets.branches.map Prod.snd
  | .call _ _ _ (some target) _ => [target]
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
  | .assign p rv => p.local_ :: (rvOperands rv).filterMap opRead
  | .placeMention p | .deinit p => [p.local_]
  | .storageLive i | .storageDead i => [i]
  | _ => []

/-- The locals a terminator mentions (`Return` reads `_0`; `Call` mentions its
destination local and all locals read by its arguments). -/
def termLocals (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => (opRead discr).toList
  | .return_ => [0]
  | .call _ argOps dst _ _ => dst.local_ :: argOps.filterMap opRead
  | _ => []

/-- No statement or terminator mentions a local that `initBlock` allocates. -/
def mentionsOk (body : MirAst.CapturedMir) : Bool :=
  body.basicBlocks.all fun bb =>
    bb.statements.all (fun s => (stmtLocals s).all (fun j => !(alwaysStorageLiveLocals body).contains j)) &&
    (termLocals bb.terminator).all (fun j => !(alwaysStorageLiveLocals body).contains j)

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
  body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.localDecls) &&
    terminatorOk body.localDecls body.basicBlocks.length bb.terminator) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  (translateFn body).isSome

/-! ### Multi-function fragment (`progInFragment`)

In MiniRust's `Terminator::Call` (`spec/lang/step/terminators.md`), the caller
evaluates `ret` and runs `prepare_for_inplace_passing(ret_place, ret_ty)`
(which checks liveness/alignment and writes `Uninit` bytes to `ret_place`)
*before* evaluating `arguments` and pushing the callee frame, whereas Anneal's
`TerminatorKind.call` evaluates `argOps` first, pushes the callee frame, and
writes `destination` via `writePlaceValue` when the callee returns:

1. `livenessOk` computes the greatest fixed point `liveAtEntry` of must-live
   locals across the CFG (`_0 .. _argCount` live at `bb0` entry, `StorageLive`
   adds a local, `StorageDead` removes it, CFG joins intersect) so every call's
   `destination.local_` is guaranteed live when `Terminator::Call` runs.
2. `tupleInitOk` computes the greatest fixed point `tupleInitAtEntry` of
   must-initialized `(Int, bool)` 2-tuple locals across the CFG so that when a
   call writes into a projected tuple field (`_dst.0` or `_dst.1`), `_dst` is
   already an initialized 2-tuple in Anneal (matching `writePlaceValue` on
   `Return`) while MiniRust's `prepare_for_inplace_passing` deinitializes only
   the target field's bytes and preserves the sibling field.
3. `callTerminatorOk` checks callee resolution in `callees`, parameter count and
   type compatibility across all four fragment types, root-only `Operand::Move`
   on call arguments (projected `move (_j.f)` leaves `_j` initialized in Anneal
   but writes `Uninit` via `ArgumentExpr::InPlace` in MiniRust), return-place
   liveness/type compatibility, and disjointness of `destination.local_` from
   all locals read by `argOps` (so `prepare_for_inplace_passing` on `ret`
   cannot clobber any argument before `eval_argument` reads it). -/

/-- Must-live transfer of statement `s` on a list of live local indices. -/
def stmtMustLive (lv : List Nat) (s : MirAst.Statement) : List Nat :=
  match s.kind with
  | .storageLive i => if lv.contains i then lv else i :: lv
  | .storageDead i => lv.filter (· != i)
  | _ => lv

/-- Initial per-block must-live sets before iteration: `_0 .. _argCount` at
`bb0`, and all declared locals `0 .. L - 1` at `blk > 0` (top of the
intersection lattice). -/
def initLiveEntries (body : MirAst.CapturedMir) : List (List Nat) :=
  (List.range body.basicBlocks.length).map fun blk =>
    if blk == 0 then List.range (body.argCount + 1)
    else List.range body.localDecls.length

/-- One forward CFG intersection pass for must-live locals. -/
def stepLiveEntries (body : MirAst.CapturedMir) (entries : List (List Nat)) :
    List (List Nat) :=
  let bbs := body.basicBlocks
  (List.range bbs.length).map fun dst =>
    let initAcc :=
      if dst == 0 then List.range (body.argCount + 1)
      else entries.getD dst (List.range body.localDecls.length)
    (List.range bbs.length).foldl (fun acc src =>
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let exitLv := bb.statements.foldl stmtMustLive (entries.getD src [])
          acc.filter (fun i => exitLv.contains i)
        else acc
      | none => acc) initAcc

/-- Iterate forward must-live intersection up to `fuel` passes. -/
def iterLiveEntries : Nat → MirAst.CapturedMir → List (List Nat) → List (List Nat)
  | 0, _, entries => entries
  | n + 1, body, entries =>
    let entries' := stepLiveEntries body entries
    if entries' == entries then entries
    else iterLiveEntries n body entries'

/-- Locals guaranteed live on entry to block `blk`. -/
def liveAtEntry (body : MirAst.CapturedMir) (blk : Nat) : List Nat :=
  let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
  (iterLiveEntries fuel body (initLiveEntries body)).getD blk []

/-- Locals guaranteed live before statement `stmt` of block `blk`. -/
def mustLiveBefore (body : MirAst.CapturedMir) (blk stmt : Nat) : List Nat :=
  match body.basicBlocks[blk]? with
  | some bb => (bb.statements.take stmt).foldl stmtMustLive (liveAtEntry body blk)
  | none => liveAtEntry body blk

/-- Inductive verification that `liveAtEntry` is a valid post-fixed point:
every local in `liveAtEntry body 0` is in `0 .. argCount`, and every CFG edge
`blk → t` preserves every local in `liveAtEntry body t`. -/
def livenessOk (body : MirAst.CapturedMir) : Bool :=
  (liveAtEntry body 0).all (fun i => decide (i ≤ body.argCount)) &&
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      let exitLv := bb.statements.foldl stmtMustLive (liveAtEntry body blk)
      (termTargets bb.terminator).all (fun t =>
        (liveAtEntry body t).all (fun i => exitLv.contains i))
    | none => true

/-- Whether local `i` is declared with an `(Int, bool)` 2-tuple type. -/
def isTupleLocal (decls : List MirAst.LocalDecl) (i : Nat) : Bool :=
  match decls[i]? with
  | some d => (intBoolTupleOf d.ty).isSome
  | none => false

/-- Remove any root local moved out by `ops` from `ti`. -/
def dropMovedFrom (ti : List Nat) (ops : List MirAst.Operand) : List Nat :=
  ops.foldl (fun acc op =>
    match opMoved op with
    | some j => acc.filter (· != j)
    | none => acc) ti

/-- Must-initialized 2-tuple transfer of statement `s`. -/
def stmtTupleInit (decls : List MirAst.LocalDecl) (ti : List Nat)
    (s : MirAst.Statement) : List Nat :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    let ti' := dropMovedFrom ti (rvOperands rv)
    if isTupleLocal decls i then
      if ti'.contains i then ti' else i :: ti'
    else ti'.filter (· != i)
  | .assign ⟨_, _ :: _⟩ rv => dropMovedFrom ti (rvOperands rv)
  | .storageLive i | .storageDead i | .deinit ⟨i, []⟩ => ti.filter (· != i)
  | _ => ti

/-- Must-initialized 2-tuple transfer across terminator `t` to its normal
successor(s). -/
def termTupleInit (decls : List MirAst.LocalDecl) (ti : List Nat)
    (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => dropMovedFrom ti [discr]
  | .call _ argOps ⟨dst, []⟩ (some _) _ =>
    let ti' := dropMovedFrom ti argOps
    if isTupleLocal decls dst then
      if ti'.contains dst then ti' else dst :: ti'
    else ti'.filter (· != dst)
  | .call _ argOps ⟨_, _ :: _⟩ (some _) _ => dropMovedFrom ti argOps
  | _ => ti

/-- Initial per-block must-initialized 2-tuple sets: tuple parameters among
`1 .. argCount` at `bb0`, and all tuple locals at `blk > 0`. -/
def initTupleEntries (body : MirAst.CapturedMir) : List (List Nat) :=
  let allTuples := (List.range body.localDecls.length).filter (isTupleLocal body.localDecls)
  let paramTuples :=
    ((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls)
  (List.range body.basicBlocks.length).map fun blk =>
    if blk == 0 then paramTuples else allTuples

/-- One forward CFG intersection pass for must-initialized 2-tuple locals. -/
def stepTupleInitEntries (body : MirAst.CapturedMir) (entries : List (List Nat)) :
    List (List Nat) :=
  let bbs := body.basicBlocks
  let allTuples := (List.range body.localDecls.length).filter (isTupleLocal body.localDecls)
  let paramTuples :=
    ((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls)
  (List.range bbs.length).map fun dst =>
    let initAcc :=
      if dst == 0 then paramTuples
      else entries.getD dst allTuples
    (List.range bbs.length).foldl (fun acc src =>
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let midTi := bb.statements.foldl (stmtTupleInit body.localDecls) (entries.getD src [])
          let exitTi := termTupleInit body.localDecls midTi bb.terminator
          acc.filter (fun i => exitTi.contains i)
        else acc
      | none => acc) initAcc

/-- Iterate forward must-initialized 2-tuple intersection up to `fuel` passes. -/
def iterTupleInitEntries : Nat → MirAst.CapturedMir → List (List Nat) → List (List Nat)
  | 0, _, entries => entries
  | n + 1, body, entries =>
    let entries' := stepTupleInitEntries body entries
    if entries' == entries then entries
    else iterTupleInitEntries n body entries'

/-- 2-tuple locals guaranteed initialized on entry to block `blk`. -/
def tupleInitAtEntry (body : MirAst.CapturedMir) (blk : Nat) : List Nat :=
  let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
  (iterTupleInitEntries fuel body (initTupleEntries body)).getD blk []

/-- 2-tuple locals guaranteed initialized before statement `stmt` of block `blk`. -/
def tupleInitBefore (body : MirAst.CapturedMir) (blk stmt : Nat) : List Nat :=
  match body.basicBlocks[blk]? with
  | some bb =>
    (bb.statements.take stmt).foldl (stmtTupleInit body.localDecls) (tupleInitAtEntry body blk)
  | none => tupleInitAtEntry body blk

/-- Inductive verification that `tupleInitAtEntry` is a valid post-fixed point. -/
def tupleInitOk (body : MirAst.CapturedMir) : Bool :=
  (tupleInitAtEntry body 0).all (fun i =>
    decide (1 ≤ i ∧ i ≤ body.argCount) && isTupleLocal body.localDecls i) &&
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      let midTi :=
        bb.statements.foldl (stmtTupleInit body.localDecls) (tupleInitAtEntry body blk)
      let exitTi := termTupleInit body.localDecls midTi bb.terminator
      (termTargets bb.terminator).all (fun t =>
        (tupleInitAtEntry body t).all (fun i => exitTi.contains i))
    | none => true

/-- Whether a call argument `op` in a caller with declarations `decls` is a
well-typed fragment argument for callee parameter declaration `paramDecl`.
`Operand::Move` is restricted to root locals (`move _j`), because projected
`move (_j.f)` leaves `_j` initialized in Anneal (`evalOperand`) while MiniRust's
`ArgumentExpr::InPlace` writes `Uninit` to field `f`. -/
def callArgOk (decls : List MirAst.LocalDecl) (paramDecl : MirAst.LocalDecl)
    (op : MirAst.Operand) : Bool :=
  let shapeOk :=
    match op with
    | .move ⟨_, []⟩ => true
    | .move _ => false
    | _ => true
  shapeOk &&
  if isBoolTy paramDecl.ty then operandOkB decls (copyOp op)
  else if isOrderingTy paramDecl.ty then operandOkO decls (copyOp op)
  else
    match intBoolTupleOf paramDecl.ty with
    | some it => operandOkTuple decls it (copyOp op)
    | none =>
      match intTypeOf paramDecl.ty with
      | some it => operandOk decls it (copyOp op)
      | none => false

/-- Check every call argument against the callee's parameter declarations
`_1 .. _argCount`. -/
def callArgsOk (decls : List MirAst.LocalDecl) :
    List MirAst.LocalDecl → List MirAst.Operand → Bool
  | [], [] => true
  | pd :: pds, op :: ops => callArgOk decls pd op && callArgsOk decls pds ops
  | _, _ => false

/-- Whether two MIR types translate to the same fragment MiniRust type. -/
def sameFragmentTy (t1 t2 : MirAst.Ty) : Bool :=
  (isBoolTy t1 && isBoolTy t2) ||
  (isOrderingTy t1 && isOrderingTy t2) ||
  (match intBoolTupleOf t1, intBoolTupleOf t2 with
   | some it1, some it2 => decide (it1 = it2)
   | _, _ => false) ||
  (match intTypeOf t1, intTypeOf t2 with
   | some it1, some it2 => decide (it1 = it2)
   | _, _ => false)

/-- Whether `destination` in the caller (with must-live set `lv` and
must-initialized tuple set `ti` at the terminator) is a valid return place for a
callee with return declaration `calleeRetDecl`:
* root local `_dst`: `_dst` is must-live and has the same MiniRust type as
  `calleeRetDecl`;
* projected tuple field `_dst.0` or `_dst.1`: `_dst` is both must-live and
  must-initialized as an `(it, bool)` 2-tuple, and the projected field has the
  same MiniRust type as `calleeRetDecl`. -/
def callDestOk (decls : List MirAst.LocalDecl) (lv ti : List Nat)
    (calleeRetDecl : MirAst.LocalDecl) (destination : MirAst.Place) : Bool :=
  match destination with
  | ⟨dst, []⟩ =>
    decide (dst < decls.length) && lv.contains dst &&
    match decls[dst]? with
    | some d => sameFragmentTy d.ty calleeRetDecl.ty
    | none => false
  | ⟨dst, [.field 0 fTy]⟩ =>
    decide (dst < decls.length) && lv.contains dst && ti.contains dst &&
    match decls[dst]? with
    | some d =>
      match intBoolTupleOf d.ty, intTypeOf fTy, intTypeOf calleeRetDecl.ty with
      | some it, some fit, some rit => decide (fit = it) && decide (rit = it)
      | _, _, _ => false
    | none => false
  | ⟨dst, [.field 1 fTy]⟩ =>
    decide (dst < decls.length) && lv.contains dst && ti.contains dst &&
    match decls[dst]? with
    | some d =>
      (intBoolTupleOf d.ty).isSome && isBoolTy fTy && isBoolTy calleeRetDecl.ty
    | none => false
  | _ => false

/-- Whether `unwind` is one of the non-cleanup call `UnwindAction`s (`Continue`,
`Unreachable`, or `Terminate`; fragment basic blocks have `!bb.isCleanup`). -/
def callUnwindOk : MirAst.UnwindAction → Bool
  | .continue_ | .unreachable | .terminate => true
  | .cleanup _ => false

/-- Whether a `TerminatorKind.call` at the end of block `blk` in `body` is in
the multi-function fragment relative to `callees`. -/
def callTerminatorOk (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir)
    (blk : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind, body.basicBlocks[blk]? with
  | .call func argOps destination (some targetBb) unwind, some bb =>
    match extractFnDefPath func with
    | none => false
    | some defPath =>
      match MirSemantics.findCallee? callees defPath with
      | none => false
      | some callee =>
        match callee.localDecls with
        | [] => false
        | retDecl :: restDecls =>
          let lv := mustLiveBefore body blk bb.statements.length
          let ti := tupleInitBefore body blk bb.statements.length
          decide (targetBb < body.basicBlocks.length) &&
          callUnwindOk unwind &&
          decide (argOps.length = callee.argCount) &&
          decide (callee.argCount ≤ restDecls.length) &&
          callArgsOk body.localDecls (restDecls.take callee.argCount) argOps &&
          callDestOk body.localDecls lv ti retDecl destination &&
          argOps.all (fun op => opRead op != some destination.local_)
  | _, _ => false

/-- Block terminator check in a multi-function program: either a single-body
fragment terminator (`terminatorOk`) or a fragment direct call
(`callTerminatorOk`). -/
def terminatorInProgOk (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir)
    (blk : Nat) (t : MirAst.Terminator) : Bool :=
  terminatorOk body.localDecls body.basicBlocks.length t ||
  callTerminatorOk callees body blk t

/-- Per-function fragment check within a multi-function program `(fnMap, callees)`. -/
def bodyInProgFragment (fnMap : List (String × Gen.FnName))
    (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) &&
  decide (body.basicBlocks ≠ []) &&
  (List.range body.basicBlocks.length).all (fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      !bb.isCleanup &&
      bb.statements.all (statementOk body.localDecls) &&
      terminatorInProgOk callees body blk bb.terminator
    | none => true) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  livenessOk body && tupleInitOk body &&
  (translateFnInProg fnMap body).isSome

/-- All callee `DefPath`s syntactically referenced by `Call` terminators in
`body`. -/
def callCalleesOf (body : MirAst.CapturedMir) : List String :=
  body.basicBlocks.filterMap fun bb =>
    match bb.terminator.kind with
    | .call func _ _ _ _ => extractFnDefPath func
    | _ => none

/-- Fuel-bounded worst-case sum of `localDecls.length` along any static call
chain rooted at `body`. Returns `none` if the call graph has a cycle or exceeds
`fuel` frames. -/
def maxStackLocalsAux : Nat → List MirAst.CapturedMir → MirAst.CapturedMir → Option Nat
  | 0, _, _ => none
  | fuel + 1, callees, body => do
    let subBounds ← (callCalleesOf body).mapM fun dp => do
      let callee ← MirSemantics.findCallee? callees dp
      maxStackLocalsAux fuel callees callee
    pure (body.localDecls.length + subBounds.foldl Nat.max 0)

/-- Worst-case total `localDecls.length` across any call stack rooted at `entry`
within `callees` (`fuel = callees.length + 1` suffices for every acyclic call
graph over `callees`). -/
def maxStackLocals (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir) :
    Option Nat :=
  maxStackLocalsAux (callees.length + 1) callees entry

/-- Decidable multi-function fragment check for `entry` together with `callees`:
1. `entry` and all `callees` have distinct `defPath`s;
2. `entry` and every callee in `callees` satisfy `bodyInProgFragment`;
3. the call graph rooted at `entry` is acyclic and its worst-case stack-local
   budget `maxStackLocals entry callees` is strictly below `2^31` (keeping
   `BM.pickAddr` first-fit stack candidate addresses below `2^63` across all
   simultaneously live frames);
4. `translateProg entry callees` succeeds. -/
def progInFragment (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir) : Bool :=
  let fnMap := fnNameMap entry callees
  ((entry :: callees).map (·.defPath)).Nodup &&
  (entry :: callees).all (bodyInProgFragment fnMap callees) &&
  (match maxStackLocals entry callees with
   | some bound => decide (bound < 2 ^ 31)
   | none => false) &&
  (translateProg entry callees).isSome

end MiniRustSpec.Correspondence
