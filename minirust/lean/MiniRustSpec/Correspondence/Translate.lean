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
  (`argCount < i`) has scalar fragment type, thin raw pointer type
  (`*const T` / `*mut T` for integer `T`), or reference type (`&T` / `&mut T`
  for integer `T`), and each argument local (`1 ≤ i ≤ argCount`) has scalar
  fragment type, homogeneous 1D integer array type `[T; N]` whose byte size
  `N * size_of::<T>()` fits in signed 64-bit `isize` (`< 2^63`), or well-formed
  tuple / single-variant struct type (`RigidTy.tuple` or `RigidTy.adt`) with
  explicit layout offsets and padding (`FieldsShape.arbitrary`,
  `VariantsShape.single 0`);
* statements are:
  - scalar assignments `dst = rv` to an integer place `dst` (`_i`, array
    element `_i[proj]`, tuple/struct scalar field chain `_i.f1...fk`, or mutable
    pointer/reference dereference `*_p`), where
    `rv` is `Use(a)`, `CopyForDeref(p)`, `UnaryOp(uop, a)` (`uop ∈ {Neg, Not}`),
    `BinaryOp(op, a, b)` (`op` among the 15 integer `BinOp` variants, with `b`
    of `dst`'s integer type `it` or of any integer type `rhsIt` for the shift
    operators `Shl, Shr, ShlUnchecked, ShrUnchecked`),
    `Cast(IntToInt, a, targetTy)` (from any integer type `srcIt` or `bool`),
    `Len(_j)` of an array local `_j` (into a `usize` destination), or dereference
    reads `copy/move (*_r)` / `CopyForDeref(*_r)` through a thin raw pointer or
    reference `_r` into either a root destination `_i` or a mutable pointer /
    reference dereference `(*_w)` (`ptrDerefReadOk`);
  - thin raw pointer and reference assignments `_i = rv` to a pointer or
    reference local `_i`, where `rv` is `Use(copy/move _p)`, `CopyForDeref(_p)`,
    direct borrows (`&raw const q`, `&raw mut q`, `&q`, `&mut q`) of a parameter
    scalar/array-element/struct-field place `q` (`ptrTargetOk`), reborrows
    (`&raw const *_p`, `&raw mut *_p`, `&*_p`, `&mut *_p`), `Cast(PtrToPtr,
    copy/move _p, castTy)` preserving pointee integer type and not upgrading
    `*const` to `*mut`, or zero-offset `BinaryOp(Offset, copy/move _p, const 0)`
    (`ptrRvalueOk`), subject to the flow-sensitive CFG borrow/aliasing
    discipline `ptrAliasingOk`;
  - `bool`, `Ordering`, and `(it, bool)` 2-tuple assignments `_i = rv` to a root
    local `_i` (`boolNot`, `boolBitOp`, comparisons `Eq | Ne | Lt | Le | Gt | Ge`,
    three-way `Cmp`, `AddWithOverflow | SubWithOverflow | MulWithOverflow`,
    `Aggregate(Tuple, [a, b])`, `CopyForDeref(p)`, and `Use(a)`);
  - array assignments `_i = rv` to an unprojected array local `_i : [T; N]`,
    where `rv` is `Use(copy _j)`, `Aggregate(Array(T), [op_0, .., op_{N-1}])`,
    or `Repeat(op, N)` with `N > 0` (or `N = 0` when `op` is a constant);
  - tuple and single-variant struct assignments `dst = rv` to `_i` or a nested
    field chain `_i.f1...fk`, where `rv` is `Use(copy p)` or
    `Aggregate(Tuple | Adt(_, 0, None), [op_0, .., op_{M-1}])`;
  - `PlaceMention(p)` on `_i`, `(it, bool)` fields `_i.0` / `_i.1`, or
    tuple/struct field chains `_i.f1...fk`;
  - `StorageLive(_i)`, `StorageDead(_i)` of a temporary (`argCount < i`), and
    `Deinit(_i)` on scalar-family, thin raw pointer, or reference root locals;
* terminators are `Goto`, `SwitchInt` on an integer or `bool` fragment operand,
  `Unreachable`, or `Return`, and every jump target is a block of the body;
* no block is a cleanup block;
* no moved-from local is read before it is re-initialized (`movesOk`), and
  every temporary the body mentions has explicit storage markers
  (`mentionsOk`); see below.

The multi-function translation `translateProg` (`translateFnInProg`,
`Terminator::Call`) is defined on the fragment checked by `progInFragment`:

* the body declares the return place, the arguments, and any number of
  temporaries (`argCount + 1 ≤ localDecls.length < 2^31`), all of integer,
  `bool`, `core::cmp::Ordering`, or `(Int, bool)` 2-tuple type;
* statements are the scalar-family statements of `inFragment` above together
  with `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` on a
  `bool` fragment operand (`translateStmtResult`, `splitStmts`, `SegChain`,
  `SegPc`);
* terminators are `Goto`, `SwitchInt` on an integer or `bool` fragment operand
  (`copy _j`, `move _j`, 2-tuple field projection, or constant), `Unreachable`,
  `Return`, or direct monomorphic `Call`s to fragment callees, and every jump
  or call return target is a block of the body;
* no block in the source MIR body is a cleanup block (`translateUnwindAction`
  synthesizes MiniRust cleanup blocks for call unwind edges);
* no moved-from local is read before it is re-initialized (`movesOk`), call
  return places are must-live and disjoint from call arguments (`livenessOk`,
  `tupleInitOk`, `callTerminatorOk`), and every temporary the body mentions has
  explicit storage markers (`mentionsOk`); see below.

Both translations share `translateStatement`, `translatePlace`,
`translateOperand`, and `translateTerminator`, so a statement or terminator
lowers identically whichever function it appears in; the two fragment
predicates differ only in which bodies their correspondence proofs cover.

For `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))`,
`translateFnInProg` transcribes how `minimize` splits a MIR basic block: the
statement ends the current MiniRust block segment in a `Terminator::Intrinsic`
of `IntrinsicOp::Assume` on `op` with `ret = build::unit_place()` and a fresh
continuation block (`translateStmtResult`, `splitStmts`, `SegChain`, `SegPc`).
`translateFnWithIntrinsics` splits blocks in the same way at the provenance
casts `PointerExposeProvenance` and `PointerWithExposedProvenance`
(`translateStmtOrIntrinsic`, `splitBlockAtIntrinsics`).
`translateRsIntrinsic` also transcribes `minimize`'s lowering of compiler
intrinsic calls (`raw_eq`, `ctpop`, `exact_div`, `cold_path`, `abort`).

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

/-- Canonical zero-initialized `MirSemantics.Value` of shape `TupleSpec`,
matching the runtime `.aggregate 0 vals` arities of `TupleSpec.valOk`. -/
def TupleSpec.zeroVal : TupleSpec → MirSemantics.Value
  | .scalar it => .scalar ⟨0, it.size.bytes⟩
  | .tuple fields _ _ => .aggregate 0 (TupleSpec.zeroFieldVals fields)

/-- Pointwise `TupleSpec.zeroVal` across tuple/struct fields. -/
def TupleSpec.zeroFieldVals : List (Nat × TupleSpec) → List MirSemantics.Value
  | [] => []
  | (_, s) :: rest => s.zeroVal :: TupleSpec.zeroFieldVals rest

end

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

/-- Whether a captured `TypeLayout` has non-union `FieldsShape` (`minimize` and
`TupleSpec` only translate single-variant structs `FieldsShape.arbitrary`, never
unions `FieldsShape.union`). -/
def isNonUnionTypeLayout (l : Layout.TypeLayout) : Bool :=
  match l.fields with
  | .union _ => false
  | _ => true

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
      if offsets.length = fieldKinds.length && layouts.entries.all isNonUnionTypeLayout then do
        let fields ← specOfFieldList layouts offsets fieldKinds l.fieldLayouts
        pure (.tuple fields l.size.bytes l.align.bytes)
      else none
    | _, _, _ => none
  | .adt _ fieldKinds, layoutIdx => do
    let l ← Layout.LayoutTable.lookup layouts layoutIdx
    match l.variants, l.isUninhabited, l.fields with
    | .single 0, false, .arbitrary offsets _ =>
      if offsets.length = fieldKinds.length && layouts.entries.all isNonUnionTypeLayout then do
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

mutual

/-- Whether `t` is free of unmonomorphized generic type parameters
(`RigidTy.param`, `ty::Param`) and unnormalized associated-type projections
(`RigidTy.alias`, `ty::Alias`), including inside recursive container types
(`tuple`, `array`, `slice`, `adt`, `rawPtr`, `ref`, `fnDef`, `fnPtr`,
`closure`). MiniRust and `minimize` operate strictly over fully monomorphized
`rustc` types (`rs_layout_of` panics on `ty::Param` or `ty::Alias` anywhere
inside a type). -/
def isMonoRigidTy : MirAst.RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .str | .never => true
  | .tuple elems | .adt _ elems | .fnDef _ elems | .closure _ elems =>
    isMonoRigidTyList elems
  | .array elem _ | .slice elem | .rawPtr _ elem | .ref _ elem =>
    isMonoRigidTy elem
  | .fnPtr inputs output _ _ =>
    isMonoRigidTyList inputs && isMonoRigidTy output
  | .dynamic _ | .foreign _ | .other _ => true
  | .param _ _ | .alias _ _ => false

/-- Pointwise `isMonoRigidTy` across a list of `RigidTy` arguments or fields. -/
def isMonoRigidTyList : List MirAst.RigidTy → Bool
  | [] => true
  | t :: ts => isMonoRigidTy t && isMonoRigidTyList ts

end

/-- The metadata kind of a raw pointer to `pointee`, as `minimize` computes it
from the pointee's layout (`pointee_info_of(..).layout.meta_kind()`): no
metadata (`PointerMetaKind::None`) for sized pointees, and an element count
(`PointerMetaKind::ElementCount`) for slices and `str`. Unsized trait objects
and extern foreign types are outside the translation.

MiniRust (and `minimize`) only ever sees fully monomorphized types, so an
unsubstituted generic parameter (`RigidTy.param`, `ty::Param`) or an
unnormalized associated-type projection (`RigidTy.alias`, `ty::Alias`) — either
directly or nested inside a container type (`tuple`, `array`, `slice`, `adt`,
`rawPtr`, `ref`, `fnDef`, `fnPtr`, `closure`) — has no layout from which a
metadata kind could be read: all unmonomorphized pointees fail closed (`none`),
which keeps every pointer to such a pointee out of the translation. -/
def rawPtrMetaKind : MirAst.RigidTy → Option Gen.PointerMetaKind
  | .bool | .char | .int _ | .uint _ | .float _ | .never => some .None
  | .tuple elems | .adt _ elems | .fnDef _ elems | .closure _ elems =>
    if isMonoRigidTyList elems then some .None else none
  | .array elem _ | .ref _ elem | .rawPtr _ elem =>
    if isMonoRigidTy elem then some .None else none
  | .fnPtr inputs output _ _ =>
    if isMonoRigidTyList inputs && isMonoRigidTy output then some .None else none
  | .slice elem =>
    if isMonoRigidTy elem then some .ElementCount else none
  | .str => some .ElementCount
  | .dynamic _ | .foreign _ | .other _ => none
  | .param _ _ | .alias _ _ => none

/-- Metadata kind of a raw pointer `MirAst.Ty` (`rawPtrMetaKind`). -/
def rawPtrMetaOf (t : MirAst.Ty) : Option Gen.PointerMetaKind :=
  match t.kind with
  | .rawPtr _ pointee => rawPtrMetaKind pointee
  | _ => none

/-- `minimize`'s mutability translation (`tooling/minimize/src/ty.rs`):
> "pub fn translate_mutbl_smir(mutbl: smir::Mutability) -> Mutability {
>     match mutbl {
>         smir::Mutability::Mut => Mutability::Mutable,
>         smir::Mutability::Not => Mutability::Immutable,
>     }
> }" -/
def translateMutbl : MirAst.Mutability → LibSpecr.Mutability
  | .mut => .Mutable
  | .not => .Immutable

/-- `BorrowKind::to_mutable_lossy`: shared borrows map to `Mutability.not` and
mutable borrows (including two-phase borrows) map to `Mutability.mut`. -/
def borrowKindMutbl : MirAst.BorrowKind → MirAst.Mutability
  | .shared => .not
  | .mut _ => .mut

/-- `minimize`'s `pointee_info_of` for a sized, inhabited, `Freeze`, `Unpin`
integer type `it` (`tooling/minimize/src/ty.rs`):
> "pub fn pointee_info_of(&mut self, ty: rs::Ty<'tcx>, span: rs::Span) -> PointeeInfo {
>     let layout = self.rs_layout_of(ty).layout;
>     let inhabited = !layout.is_uninhabited();
>     let freeze = ty.is_freeze(self.tcx, self.typing_env());
>     let unpin = ty.is_unpin(self.tcx, self.typing_env());
>
>     if layout.is_sized() {
>         let size = translate_size(layout.size());
>         let align = translate_align(layout.align().abi);
>         let layout = LayoutStrategy::Sized(size, align);
>         ..
>         return PointeeInfo {
>             layout,
>             inhabited,
>             unsafe_cells: UnsafeCellStrategy::Sized { cells },
>             freeze,
>             unpin,
>         };
>     }" -/
def intPointeeInfo (it : Gen.IntType) : Gen.PointeeInfo :=
  { layout := .Sized it.size ⟨it.size.bytes⟩
    inhabited := true
    unsafe_cells := .Sized []
    freeze := true
    unpin := true }

/-- Whether `defPath` names `core::cell::UnsafeCell` or `std::cell::UnsafeCell`. -/
def isUnsafeCellPath (defPath : String) : Bool :=
  decide (defPath = "core::cell::UnsafeCell" ∨ defPath = "std::cell::UnsafeCell")

/-- Whether `defPath` names `alloc::boxed::Box` or `std::boxed::Box`. -/
def isBoxPath (defPath : String) : Bool :=
  decide (defPath = "alloc::boxed::Box" ∨ defPath = "std::boxed::Box")

/-- Equal-width integer 2-tuple `(T0, T1)` (`size_of::<T0>() == size_of::<T1>() == n`),
whose Rust/MiniRust layout is unambiguously `size = 2 * n`, `align = n` with fields
at offsets `0` and `n` even when no `LayoutIdx` is attached (e.g. inside `RigidTy.ref`
or `RigidTy.rawPtr`). -/
def eqAlignIntPairOf : MirAst.RigidTy → Option (Gen.IntType × Gen.IntType)
  | .tuple [t0, t1] => do
    let (s0, n0) ← intTyBytes t0
    let (s1, n1) ← intTyBytes t1
    if n0 = n1 then some (⟨s0, ⟨n0⟩⟩, ⟨s1, ⟨n1⟩⟩) else none
  | _ => none

/-- `minimize`'s `pointee_info_of` + `cells_in_sized_ty` across sized pointee
`RigidTy`s whose layout and `UnsafeCell` ranges are determined without a
`LayoutTable` entry (`tooling/minimize/src/ty.rs`):
> "pub fn cells_in_sized_ty(&mut self, ty: rs::Ty<'tcx>, span: rs::Span) -> Vec<(Offset, Size)> {
>     match ty.kind() {
>         rs::TyKind::Bool => Vec::new(),
>         rs::TyKind::Int(_) => Vec::new(),
>         rs::TyKind::Uint(_) => Vec::new(),
>         rs::TyKind::Char => Vec::new(),
>         rs::TyKind::RawPtr(..) => Vec::new(),
>         rs::TyKind::Ref(..) => Vec::new(),
>         rs::TyKind::Adt(adt_def, _) if adt_def.is_box() => Vec::new(),
>         ..
>         rs::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => {
>             let layout = self.rs_layout_of(ty);
>             let size = translate_size(layout.size);
>             vec![(Size::ZERO, size)]
>         }"
For integer pointees, `pointeeInfoOfRigidTy` reduces directly to `intPointeeInfo`. -/
def pointeeInfoOfRigidTyAux : Nat → MirAst.RigidTy → Option Gen.PointeeInfo
  | 0, _ => none
  | fuel + 1, pointee =>
    match intTyBytes pointee with
    | some (s, n) => some (intPointeeInfo ⟨s, ⟨n⟩⟩)
    | none =>
      match pointee with
      | .bool =>
        some { layout := .Sized ⟨1⟩ ⟨1⟩, inhabited := true,
               unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .adt defPath (inner :: rest) =>
        if !isMonoRigidTyList rest then none
        else if isUnsafeCellPath defPath then do
          let innerInfo ← pointeeInfoOfRigidTyAux fuel inner
          match innerInfo.layout with
          | .Sized sz al =>
            some { layout := .Sized sz al, inhabited := innerInfo.inhabited,
                   unsafe_cells := .Sized [(⟨0⟩, sz)], freeze := false,
                   unpin := innerInfo.unpin }
          | _ => none
        else if isBoxPath defPath then
          match rawPtrMetaKind inner with
          | some .None =>
            some { layout := .Sized ⟨8⟩ ⟨8⟩, inhabited := true,
                   unsafe_cells := .Sized [], freeze := true, unpin := true }
          | _ => none
        else none
      | .adt "core::cmp::Ordering" [] | .adt "std::cmp::Ordering" [] =>
        some { layout := .Sized ⟨1⟩ ⟨1⟩, inhabited := true,
               unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .tuple [] =>
        some { layout := .Sized ⟨0⟩ ⟨1⟩, inhabited := true,
               unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .tuple [elem, .bool] =>
        (intTyBytes elem).map fun (_, n) =>
          { layout := .Sized ⟨n + n⟩ ⟨n⟩, inhabited := true,
            unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .tuple [t0, t1] =>
        (eqAlignIntPairOf (.tuple [t0, t1])).map fun (it0, _) =>
          let n := it0.size.bytes
          { layout := .Sized ⟨n + n⟩ ⟨n⟩, inhabited := true,
            unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .array elem count =>
        (intTyBytes elem).map fun (_, n) =>
          { layout := .Sized ⟨count * n⟩ ⟨n⟩, inhabited := true,
            unsafe_cells := .Sized [], freeze := true, unpin := true }
      | .rawPtr _ inner =>
        match rawPtrMetaKind inner with
        | some .None =>
          some { layout := .Sized ⟨8⟩ ⟨8⟩, inhabited := true,
                 unsafe_cells := .Sized [], freeze := true, unpin := true }
        | _ => none
      | .ref _ inner =>
        (pointeeInfoOfRigidTyAux fuel inner).map fun _ =>
          { layout := .Sized ⟨8⟩ ⟨8⟩, inhabited := true,
            unsafe_cells := .Sized [], freeze := true, unpin := true }
      | _ => none

/-- `PointeeInfo` for a sized `RigidTy` pointee (`pointeeInfoOfRigidTyAux 16`). -/
def pointeeInfoOfRigidTy (pointee : MirAst.RigidTy) : Option Gen.PointeeInfo :=
  pointeeInfoOfRigidTyAux 16 pointee

/-- `PtrType::Ref` for a reference to an integer type `it` (`tooling/minimize/src/ty.rs`). -/
def refPtrType (mutbl : MirAst.Mutability) (it : Gen.IntType) : Gen.PtrType :=
  .Ref (translateMutbl mutbl) (intPointeeInfo it)

/-- `Type::Ptr(PtrType::Ref { .. })` for a reference to an integer type `it`
(`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Ref(_, ty, mutbl) => {
>     let pointee = self.pointee_info_of(*ty, span);
>     let mutbl = translate_mutbl(*mutbl);
>     Type::Ptr(PtrType::Ref { pointee, mutbl })
> }" -/
def refTy (mutbl : MirAst.Mutability) (it : Gen.IntType) : Gen.Type :=
  .Ptr (refPtrType mutbl it)

/-- `minimize`'s translation of reference types `&T` and `&mut T` across sized
pointee types (`intTyBytes` fast-pathed to `refTy`, falling back to
`pointeeInfoOfRigidTy` for `bool`, `Ordering`, `UnsafeCell<T>`, tuples, arrays,
thin pointers, and nested references). -/
def refTypeOf (t : MirAst.Ty) : Option Gen.Type :=
  match t.kind with
  | .ref mutbl pointee =>
    match intTyBytes pointee with
    | some (s, n) => some (refTy mutbl ⟨s, ⟨n⟩⟩)
    | none =>
      (pointeeInfoOfRigidTy pointee).map fun info =>
        .Ptr (.Ref (translateMutbl mutbl) info)
  | _ => none

/-- `minimize`'s translation of `Box<T>` (`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Adt(adt_def, _) if adt_def.is_box() => {
>     let ty = ty.expect_boxed_ty();
>     let pointee = self.pointee_info_of(ty, span);
>     Type::Ptr(PtrType::Box { pointee })
> }" -/
def boxTypeOf (t : MirAst.Ty) : Option Gen.Type :=
  match t.kind with
  | .adt defPath (pointee :: rest) =>
    if isMonoRigidTyList rest && isBoxPath defPath then
      (pointeeInfoOfRigidTy pointee).map fun info => .Ptr (.Box info)
    else none
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
>  rs::TyKind::Ref(_, ty, mutbl) => {
>      let pointee = self.pointee_info_of(*ty, span);
>      let mutbl = translate_mutbl(*mutbl);
>      Type::Ptr(PtrType::Ref { pointee, mutbl })
>  }
>  rs::TyKind::RawPtr(ty, _mutbl) => {
>      let pointee = self.pointee_info_of(*ty, span);
>      Type::Ptr(PtrType::Raw { meta_kind: pointee.layout.meta_kind() })
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
      | none =>
        match rawPtrTypeOf t with
        | some ty => some ty
        | none =>
          match refTypeOf t with
          | some ty => some ty
          | none => boxTypeOf t

instance : DecidableEq MirAst.Mutability
  | .not, .not => isTrue rfl
  | .mut, .mut => isTrue rfl
  | .not, .mut => isFalse (by intro h; cases h)
  | .mut, .not => isFalse (by intro h; cases h)

instance : DecidableEq MirAst.BorrowKind
  | .shared, .shared => isTrue rfl
  | .mut b1, .mut b2 =>
    match decEq b1 b2 with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro heq; injection heq with hb; exact h hb)
  | .shared, .mut _ => isFalse (by intro h; cases h)
  | .mut _, .shared => isFalse (by intro h; cases h)

/-- The pointee integer type and mutability of a thin raw pointer type `*const T`
or `*mut T` to an integer `T`. -/
def rawPtrPointeeOf (t : MirAst.Ty) : Option (MirAst.Mutability × Gen.IntType) :=
  match t.kind with
  | .rawPtr mutbl pointee => (intTyBytes pointee).map (fun (s, n) => (mutbl, ⟨s, ⟨n⟩⟩))
  | _ => none

/-- The pointee integer type and mutability of a reference type `&T` or `&mut T`
to an integer `T`. -/
def refPointeeOf (t : MirAst.Ty) : Option (MirAst.Mutability × Gen.IntType) :=
  match t.kind with
  | .ref mutbl pointee => (intTyBytes pointee).map (fun (s, n) => (mutbl, ⟨s, ⟨n⟩⟩))
  | _ => none

/-- The pointee integer type of a thin raw pointer type (`*const T`, `*mut T`) or
reference type (`&T`, `&mut T`) whose pointee `T` is an integer type, with the
pointer's mutability. -/
def ptrPointeeOf (t : MirAst.Ty) : Option (MirAst.Mutability × Gen.IntType) :=
  match t.kind with
  | .rawPtr mutbl pointee | .ref mutbl pointee =>
    (intTyBytes pointee).map (fun (s, n) => (mutbl, ⟨s, ⟨n⟩⟩))
  | _ => none

/-- Whether a MIR type is a thin raw pointer to an integer (`rawPtrPointeeOf`). -/
def isRawPtrTy (t : MirAst.Ty) : Bool := (rawPtrPointeeOf t).isSome

/-- Whether a MIR type is a reference to an integer (`refPointeeOf`). -/
def isRefTy (t : MirAst.Ty) : Bool := (refPointeeOf t).isSome

/-- Whether a MIR type is a thin raw pointer or reference to an integer (`ptrPointeeOf`). -/
def isPtrTy (t : MirAst.Ty) : Bool := (ptrPointeeOf t).isSome

/-- The MiniRust type of a thin raw pointer: `rawPtrTypeOf` of a pointer to a
sized pointee, `Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })`. -/
def thinRawPtrTy : Gen.Type := .Ptr (.Raw .None)

/-- The MiniRust pointer type of a pointer or reference local declaration `t`:
`refTy mutbl it` for `&T` / `&mut T` and `thinRawPtrTy` for `*const T` / `*mut T`. -/
def declPtrTy (t : MirAst.Ty) : Gen.Type :=
  match t.kind with
  | .ref mutbl pointee =>
    match intTyBytes pointee with
    | some (s, n) => refTy mutbl ⟨s, ⟨n⟩⟩
    | none => thinRawPtrTy
  | _ => thinRawPtrTy

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- Translation of a `RigidTy` pointee without needing a layout-table entry:
`bool`, integers, `core::cmp::Ordering` / `std::cmp::Ordering`, `UnsafeCell<T>`
(translated as a single-field `#[repr(transparent)]` tuple struct `[(0, inner)]`),
`Box<T>`, unit `()`, `(Int, bool)` 2-tuples, equal-width integer 2-tuples `(T0, T1)`,
homogeneous 1D integer arrays `[Int; N]`, nested raw pointers `*const U` / `*mut U`,
and nested references `&U` / `&mut U`. -/
def translatePointeeRigidTyAux : Nat → MirAst.RigidTy → Option Gen.Type
  | 0, _ => none
  | fuel + 1, pointee =>
    match intTyBytes pointee with
    | some (s, n) => some (.Int ⟨s, ⟨n⟩⟩)
    | none =>
      match pointee with
      | .bool => some .Bool
      | .adt defPath (inner :: rest) =>
        if !isMonoRigidTyList rest then none
        else if isUnsafeCellPath defPath then do
          let innerTy ← translatePointeeRigidTyAux fuel inner
          let innerInfo ← pointeeInfoOfRigidTy inner
          match innerInfo.layout with
          | .Sized sz al =>
            some (.Tuple [(⟨0⟩, innerTy)] { «end» := sz, align := al, packed_align := none } none)
          | _ => none
        else if isBoxPath defPath then
          (pointeeInfoOfRigidTy inner).map fun info => .Ptr (.Box info)
        else none
      | .adt "core::cmp::Ordering" [] | .adt "std::cmp::Ordering" [] => some orderingTy
      | .tuple [] =>
        some (.Tuple [] { «end» := ⟨0⟩, align := ⟨1⟩, packed_align := none } none)
      | .tuple [elem, .bool] => (intTyBytes elem).map (fun (s, n) => intBoolTupleTy ⟨s, ⟨n⟩⟩)
      | .tuple [t0, t1] =>
        (eqAlignIntPairOf (.tuple [t0, t1])).map fun (it0, it1) =>
          let n := it0.size.bytes
          .Tuple [(⟨0⟩, .Int it0), (⟨n⟩, .Int it1)]
            { «end» := ⟨n + n⟩, align := ⟨n⟩, packed_align := none } none
      | .array elem count =>
        (intTyBytes elem).map (fun (s, n) => .Array (.Int ⟨s, ⟨n⟩⟩) (Int.ofNat count))
      | .rawPtr _ inner => (rawPtrMetaKind inner).map (fun k => .Ptr (.Raw k))
      | .ref mutbl inner =>
        match intTyBytes inner with
        | some (s, n) => some (refTy mutbl ⟨s, ⟨n⟩⟩)
        | none =>
          (pointeeInfoOfRigidTy inner).map fun info =>
            .Ptr (.Ref (translateMutbl mutbl) info)
      | _ => none

/-- Translation of a `RigidTy` pointee (`translatePointeeRigidTyAux 16`). -/
def translatePointeeRigidTy (pointee : MirAst.RigidTy) : Option Gen.Type :=
  translatePointeeRigidTyAux 16 pointee

/-- The translation of the pointee type of a raw pointer, reference, or `Box`
type, the type at which `minimize` dereferences it (`translate_ty_smir(this_ty, ..)`
in `translatePlace`). -/
def derefPointeeTy (t : MirAst.Ty) : Option Gen.Type :=
  match t.kind with
  | .rawPtr _ pointee | .ref _ pointee => translatePointeeRigidTy pointee
  | .adt defPath (pointee :: rest) =>
    if isMonoRigidTyList rest && isBoxPath defPath then translatePointeeRigidTy pointee else none
  | _ => none

/-! ### Unmonomorphized types fail closed

`MirAst.RigidTy` now also represents generic type parameters (`RigidTy.param`,
`ty::Param`) and unnormalized associated-type projections (`RigidTy.alias`,
`ty::Alias`). MiniRust, like `minimize`, only translates fully monomorphized
types, so neither has a translation: every type-directed helper of the
translation returns `none` on them, also when they occur as the pointee of a raw
pointer or reference, so no fragment local, operand, cast target, or pointer
target can have such a type. -/

theorem intTyBytes_param (idx : Nat) (name : String) :
    intTyBytes (.param idx name) = none := rfl

theorem intTyBytes_alias (p : MirAst.DefPath) (args : List MirAst.RigidTy) :
    intTyBytes (.alias p args) = none := rfl

theorem rawPtrMetaKind_param (idx : Nat) (name : String) :
    rawPtrMetaKind (.param idx name) = none := rfl

theorem rawPtrMetaKind_alias (p : MirAst.DefPath) (args : List MirAst.RigidTy) :
    rawPtrMetaKind (.alias p args) = none := rfl

theorem specOfRigidTy_param (layouts : Layout.LayoutTable) (idx : Nat) (name : String)
    (layoutIdx : Nat) : specOfRigidTy layouts (.param idx name) layoutIdx = none := by
  simp [specOfRigidTy]

theorem specOfRigidTy_alias (layouts : Layout.LayoutTable) (p : MirAst.DefPath)
    (args : List MirAst.RigidTy) (layoutIdx : Nat) :
    specOfRigidTy layouts (.alias p args) layoutIdx = none := by
  simp [specOfRigidTy]

theorem pointeeInfoOfRigidTy_param (idx : Nat) (name : String) :
    pointeeInfoOfRigidTy (.param idx name) = none := rfl

theorem pointeeInfoOfRigidTy_alias (p : MirAst.DefPath) (args : List MirAst.RigidTy) :
    pointeeInfoOfRigidTy (.alias p args) = none := rfl

theorem translatePointeeRigidTy_param (idx : Nat) (name : String) :
    translatePointeeRigidTy (.param idx name) = none := rfl

theorem translatePointeeRigidTy_alias (p : MirAst.DefPath) (args : List MirAst.RigidTy) :
    translatePointeeRigidTy (.alias p args) = none := rfl

theorem scalarTypeOf_param (idx : Nat) (name : String) (layoutIdx : Nat) :
    scalarTypeOf ⟨.param idx name, layoutIdx⟩ = none := rfl

theorem scalarTypeOf_alias (p : MirAst.DefPath) (args : List MirAst.RigidTy)
    (layoutIdx : Nat) : scalarTypeOf ⟨.alias p args, layoutIdx⟩ = none := rfl

theorem translateTy_param (layouts : Layout.LayoutTable) (idx : Nat) (name : String)
    (layoutIdx : Nat) : translateTy layouts ⟨.param idx name, layoutIdx⟩ = none := rfl

theorem translateTy_alias (layouts : Layout.LayoutTable) (p : MirAst.DefPath)
    (args : List MirAst.RigidTy) (layoutIdx : Nat) :
    translateTy layouts ⟨.alias p args, layoutIdx⟩ = none := rfl

/-- A raw pointer or reference whose pointee is a generic parameter has no
translation either (`rawPtrMetaKind`, `pointeeInfoOfRigidTy`), and neither has
its dereferenced pointee (`derefPointeeTy`). -/
theorem translateTy_ptr_param (layouts : Layout.LayoutTable) (m : MirAst.Mutability)
    (idx : Nat) (name : String) (layoutIdx : Nat) :
    translateTy layouts ⟨.rawPtr m (.param idx name), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.ref m (.param idx name), layoutIdx⟩ = none ∧
    derefPointeeTy ⟨.rawPtr m (.param idx name), layoutIdx⟩ = none ∧
    derefPointeeTy ⟨.ref m (.param idx name), layoutIdx⟩ = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A raw pointer or reference whose pointee is an associated-type projection has
no translation, and neither has its dereferenced pointee (`derefPointeeTy`). -/
theorem translateTy_ptr_alias (layouts : Layout.LayoutTable) (m : MirAst.Mutability)
    (p : MirAst.DefPath) (args : List MirAst.RigidTy) (layoutIdx : Nat) :
    translateTy layouts ⟨.rawPtr m (.alias p args), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.ref m (.alias p args), layoutIdx⟩ = none ∧
    derefPointeeTy ⟨.rawPtr m (.alias p args), layoutIdx⟩ = none ∧
    derefPointeeTy ⟨.ref m (.alias p args), layoutIdx⟩ = none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem isMonoRigidTy_of_intTyBytes {k : MirAst.RigidTy} {p : LibSpecr.Signedness × Nat}
    (h : intTyBytes k = some p) : isMonoRigidTy k = true := by
  cases k <;> first | rfl | simp [intTyBytes] at h

theorem intTyBytes_eq_none_of_not_isMonoRigidTy {k : MirAst.RigidTy}
    (h : isMonoRigidTy k = false) : intTyBytes k = none := by
  cases hb : intTyBytes k with
  | none => rfl
  | some p => rw [isMonoRigidTy_of_intTyBytes hb] at h; cases h

theorem rawPtrMetaKind_eq_none_of_not_isMonoRigidTy {k : MirAst.RigidTy}
    (h : isMonoRigidTy k = false) : rawPtrMetaKind k = none := by
  cases k <;> simp_all [isMonoRigidTy, rawPtrMetaKind]

theorem isMonoRigidTyList_eq_false_of_mem {k : MirAst.RigidTy} {ks : List MirAst.RigidTy}
    (hmem : k ∈ ks) (hk : isMonoRigidTy k = false) : isMonoRigidTyList ks = false := by
  induction ks with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp [isMonoRigidTyList, hk]
    · simp [isMonoRigidTyList, ih htl]

mutual

theorem specOfRigidTy_eq_none_of_not_isMonoRigidTy (layouts : Layout.LayoutTable) :
    ∀ (k : MirAst.RigidTy) (layoutIdx : Nat),
      isMonoRigidTy k = false → specOfRigidTy layouts k layoutIdx = none
  | .bool, _, h | .char, _, h | .int _, _, h | .uint _, _, h | .float _, _, h
  | .str, _, h | .never, _, h | .dynamic _, _, h | .foreign _, _, h
  | .other _, _, h => by simp [isMonoRigidTy] at h
  | .param _ _, _, _ | .alias _ _, _, _
  | .array _ _, _, _ | .slice _, _, _ | .rawPtr _ _, _, _ | .ref _ _, _, _
  | .fnDef _ _, _, _ | .fnPtr _ _ _ _, _, _ | .closure _ _, _, _ => by
    simp [specOfRigidTy]
  | .tuple fieldKinds, layoutIdx, h => by
    simp only [isMonoRigidTy] at h
    unfold specOfRigidTy
    cases Layout.LayoutTable.lookup layouts layoutIdx with
    | none => rfl
    | some l =>
      dsimp only [Option.bind_eq_bind, Option.bind]
      split
      · split
        · rw [specOfFieldList_eq_none_of_not_isMonoRigidTyList layouts _ fieldKinds l.fieldLayouts h]
        · rfl
      · rfl
  | .adt defPath fieldKinds, layoutIdx, h => by
    simp only [isMonoRigidTy] at h
    unfold specOfRigidTy
    cases Layout.LayoutTable.lookup layouts layoutIdx with
    | none => rfl
    | some l =>
      dsimp only [Option.bind_eq_bind, Option.bind]
      split
      · split
        · rw [specOfFieldList_eq_none_of_not_isMonoRigidTyList layouts _ fieldKinds l.fieldLayouts h]
        · rfl
      · rfl

theorem specOfFieldList_eq_none_of_not_isMonoRigidTyList (layouts : Layout.LayoutTable) :
    ∀ (offs : List Layout.Size) (fks : List MirAst.RigidTy) (fls : List Nat),
      isMonoRigidTyList fks = false → specOfFieldList layouts offs fks fls = none
  | _, [], _, h => by simp [isMonoRigidTyList] at h
  | [], _ :: _, _, _ => rfl
  | off :: offs, fk :: fks, fls, h => by
    simp only [isMonoRigidTyList, Bool.and_eq_false_iff] at h
    unfold specOfFieldList
    dsimp only [Option.bind_eq_bind, Option.bind]
    rcases h with hfk | hfks
    · rw [specOfRigidTy_eq_none_of_not_isMonoRigidTy layouts fk (fls.head?.getD 0) hfk]
    · cases specOfRigidTy layouts fk (fls.head?.getD 0) with
      | none => rfl
      | some fSpec =>
        dsimp only
        rw [specOfFieldList_eq_none_of_not_isMonoRigidTyList layouts offs fks (fls.tailD []) hfks]

end

theorem eqAlignIntPairOf_eq_none_of_not_isMonoRigidTy {k : MirAst.RigidTy}
    (h : isMonoRigidTy k = false) : eqAlignIntPairOf k = none := by
  unfold eqAlignIntPairOf
  split
  · rename_i t0 t1
    simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_true, Bool.and_eq_false_iff] at h
    rcases h with h0 | h1
    · rw [intTyBytes_eq_none_of_not_isMonoRigidTy h0]; rfl
    · cases intTyBytes t0 with
      | none => rfl
      | some p0 => rw [intTyBytes_eq_none_of_not_isMonoRigidTy h1]; rfl
  · rfl

theorem pointeeInfoOfRigidTyAux_eq_none_of_not_isMonoRigidTy :
    ∀ (fuel : Nat) (k : MirAst.RigidTy),
      isMonoRigidTy k = false → pointeeInfoOfRigidTyAux fuel k = none
  | 0, _, _ => rfl
  | fuel + 1, k, h => by
    unfold pointeeInfoOfRigidTyAux
    rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]
    dsimp only
    cases k with
    | bool | char | int _ | uint _ | float _ | str | never
    | dynamic _ | foreign _ | other _ => simp [isMonoRigidTy] at h
    | param _ _ | alias _ _ | slice _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ _ => rfl
    | adt defPath args =>
      cases args with
      | nil => simp [isMonoRigidTy, isMonoRigidTyList] at h
      | cons inner rest =>
        simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_eq_false_iff] at h
        dsimp only
        cases hrest : isMonoRigidTyList rest with
        | false => rfl
        | true =>
          have hinner : isMonoRigidTy inner = false := h.resolve_right (by simp [hrest])
          rw [pointeeInfoOfRigidTyAux_eq_none_of_not_isMonoRigidTy fuel inner hinner,
            rawPtrMetaKind_eq_none_of_not_isMonoRigidTy hinner]
          cases isUnsafeCellPath defPath <;> cases isBoxPath defPath <;> rfl
    | tuple elems =>
      rcases elems with _ | ⟨e0, _ | ⟨e1, rest⟩⟩
      · simp [isMonoRigidTy, isMonoRigidTyList] at h
      · rfl
      · cases rest with
        | cons _ _ => cases e1 <;> rfl
        | nil =>
          have hp := eqAlignIntPairOf_eq_none_of_not_isMonoRigidTy h
          cases e1 <;> try (dsimp only; rw [hp]; rfl)
          simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_true] at h
          dsimp only
          rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
    | array elem count =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
    | rawPtr m inner =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [rawPtrMetaKind_eq_none_of_not_isMonoRigidTy h]
    | ref m inner =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [pointeeInfoOfRigidTyAux_eq_none_of_not_isMonoRigidTy fuel inner h]; rfl

theorem pointeeInfoOfRigidTy_eq_none_of_not_isMonoRigidTy {k : MirAst.RigidTy}
    (h : isMonoRigidTy k = false) : pointeeInfoOfRigidTy k = none :=
  pointeeInfoOfRigidTyAux_eq_none_of_not_isMonoRigidTy 16 k h

theorem translatePointeeRigidTyAux_eq_none_of_not_isMonoRigidTy :
    ∀ (fuel : Nat) (k : MirAst.RigidTy),
      isMonoRigidTy k = false → translatePointeeRigidTyAux fuel k = none
  | 0, _, _ => rfl
  | fuel + 1, k, h => by
    unfold translatePointeeRigidTyAux
    rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]
    dsimp only
    cases k with
    | bool | char | int _ | uint _ | float _ | str | never
    | dynamic _ | foreign _ | other _ => simp [isMonoRigidTy] at h
    | param _ _ | alias _ _ | slice _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ _ => rfl
    | adt defPath args =>
      cases args with
      | nil => simp [isMonoRigidTy, isMonoRigidTyList] at h
      | cons inner rest =>
        simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_eq_false_iff] at h
        dsimp only
        cases hrest : isMonoRigidTyList rest with
        | false => rfl
        | true =>
          have hinner : isMonoRigidTy inner = false := h.resolve_right (by simp [hrest])
          rw [translatePointeeRigidTyAux_eq_none_of_not_isMonoRigidTy fuel inner hinner,
            pointeeInfoOfRigidTy_eq_none_of_not_isMonoRigidTy hinner]
          cases isUnsafeCellPath defPath <;> cases isBoxPath defPath <;> rfl
    | tuple elems =>
      rcases elems with _ | ⟨e0, _ | ⟨e1, rest⟩⟩
      · simp [isMonoRigidTy, isMonoRigidTyList] at h
      · rfl
      · cases rest with
        | cons _ _ => cases e1 <;> rfl
        | nil =>
          have hp := eqAlignIntPairOf_eq_none_of_not_isMonoRigidTy h
          cases e1 <;> try (dsimp only; rw [hp]; rfl)
          simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_true] at h
          dsimp only
          rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
    | array elem count =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
    | rawPtr m inner =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [rawPtrMetaKind_eq_none_of_not_isMonoRigidTy h]; rfl
    | ref m inner =>
      simp only [isMonoRigidTy] at h
      dsimp only
      rw [intTyBytes_eq_none_of_not_isMonoRigidTy h,
        pointeeInfoOfRigidTy_eq_none_of_not_isMonoRigidTy h]; rfl

theorem translatePointeeRigidTy_eq_none_of_not_isMonoRigidTy {k : MirAst.RigidTy}
    (h : isMonoRigidTy k = false) : translatePointeeRigidTy k = none :=
  translatePointeeRigidTyAux_eq_none_of_not_isMonoRigidTy 16 k h

theorem intBoolTupleOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : intBoolTupleOf t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold intBoolTupleOf
  cases kind with
  | tuple elems =>
    dsimp only at h ⊢
    rcases elems with _ | ⟨e0, _ | ⟨e1, rest⟩⟩
    · rfl
    · rfl
    · cases rest with
      | cons _ _ => cases e1 <;> rfl
      | nil =>
        cases e1 <;> try rfl
        simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_true] at h
        dsimp only
        rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
  | _ => rfl

theorem scalarTypeOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : scalarTypeOf t = none := by
  have hb : isBoolTy t = false := by
    unfold isBoolTy; cases hk : t.kind <;> first | rfl | (rw [hk] at h; simp [isMonoRigidTy] at h)
  have ho : isOrderingTy t = false := by
    unfold isOrderingTy
    cases hk : t.kind with
    | adt dp args =>
      cases args with
      | nil => rw [hk] at h; simp [isMonoRigidTy, isMonoRigidTyList] at h
      | cons _ _ => rfl
    | _ => rfl
  have hibt := intBoolTupleOf_eq_none_of_not_isMonoRigidTy h
  have hint : intTypeOf t = none := by
    simp [intTypeOf, intTyBytes_eq_none_of_not_isMonoRigidTy h]
  simp [scalarTypeOf, hb, ho, hibt, hint]

theorem arrayTypeOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : arrayTypeOf t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold arrayTypeOf
  cases kind with
  | array elem count =>
    simp only [isMonoRigidTy] at h
    dsimp only
    rw [intTyBytes_eq_none_of_not_isMonoRigidTy h]; rfl
  | _ => rfl

theorem tupleTypeOf_eq_none_of_not_isMonoRigidTy (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : tupleTypeOf layouts t = none := by
  unfold tupleTypeOf
  rw [specOfRigidTy_eq_none_of_not_isMonoRigidTy layouts t.kind t.layoutIdx h]
  split <;> first | rfl | (split <;> rfl)

theorem rawPtrTypeOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : rawPtrTypeOf t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold rawPtrTypeOf rawPtrMetaOf
  cases kind with
  | rawPtr m pointee =>
    simp only [isMonoRigidTy] at h
    dsimp only
    rw [rawPtrMetaKind_eq_none_of_not_isMonoRigidTy h]; rfl
  | _ => rfl

theorem refTypeOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : refTypeOf t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold refTypeOf
  cases kind with
  | ref m pointee =>
    simp only [isMonoRigidTy] at h
    dsimp only
    rw [intTyBytes_eq_none_of_not_isMonoRigidTy h,
      pointeeInfoOfRigidTy_eq_none_of_not_isMonoRigidTy h]; rfl
  | _ => rfl

theorem boxTypeOf_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : boxTypeOf t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold boxTypeOf
  cases kind with
  | adt defPath args =>
    cases args with
    | nil => rfl
    | cons pointee rest =>
      simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_eq_false_iff] at h
      dsimp only
      cases hrest : isMonoRigidTyList rest with
      | false => rfl
      | true =>
        have hpt : isMonoRigidTy pointee = false := h.resolve_right (by simp [hrest])
        rw [pointeeInfoOfRigidTy_eq_none_of_not_isMonoRigidTy hpt]
        split <;> rfl
  | _ => rfl

/-- Master monomorphization fail-closed theorem: any `MirAst.Ty` containing an
unsubstituted generic parameter (`RigidTy.param`) or unnormalized associated-type
projection (`RigidTy.alias`) anywhere in its `RigidTy` tree has no MiniRust type
translation (`translateTy layouts t = none`). -/
theorem translateTy_eq_none_of_not_isMonoRigidTy (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : translateTy layouts t = none := by
  simp [translateTy, scalarTypeOf_eq_none_of_not_isMonoRigidTy h,
    arrayTypeOf_eq_none_of_not_isMonoRigidTy h,
    tupleTypeOf_eq_none_of_not_isMonoRigidTy layouts h,
    rawPtrTypeOf_eq_none_of_not_isMonoRigidTy h,
    refTypeOf_eq_none_of_not_isMonoRigidTy h,
    boxTypeOf_eq_none_of_not_isMonoRigidTy h]

/-- Dereferencing any pointer, reference, or `Box` type that contains an
unmonomorphized `.param` or `.alias` fails closed (`derefPointeeTy t = none`). -/
theorem derefPointeeTy_eq_none_of_not_isMonoRigidTy {t : MirAst.Ty}
    (h : isMonoRigidTy t.kind = false) : derefPointeeTy t = none := by
  rcases t with ⟨kind, lidx⟩
  unfold derefPointeeTy
  cases kind with
  | rawPtr m pointee | ref m pointee =>
    simp only [isMonoRigidTy] at h
    exact translatePointeeRigidTy_eq_none_of_not_isMonoRigidTy h
  | adt defPath args =>
    cases args with
    | nil => rfl
    | cons pointee rest =>
      simp only [isMonoRigidTy, isMonoRigidTyList, Bool.and_eq_false_iff] at h
      dsimp only
      cases hrest : isMonoRigidTyList rest with
      | false => rfl
      | true =>
        have hpt : isMonoRigidTy pointee = false := h.resolve_right (by simp [hrest])
        rw [translatePointeeRigidTy_eq_none_of_not_isMonoRigidTy hpt]
        split <;> rfl
  | _ => rfl

/-- Concrete container fail-closed corollaries: arrays, tuples, structs, slices,
and raw pointers/references wrapping `.param` or `.alias` all fail closed in
`translateTy`. -/
theorem translateTy_container_param (layouts : Layout.LayoutTable) (m : MirAst.Mutability)
    (idx : Nat) (name : String) (count : Nat) (defPath : String) (layoutIdx : Nat) :
    translateTy layouts ⟨.array (.param idx name) count, layoutIdx⟩ = none ∧
    translateTy layouts ⟨.tuple [.param idx name], layoutIdx⟩ = none ∧
    translateTy layouts ⟨.adt defPath [.param idx name], layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.tuple [.param idx name]), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.array (.param idx name) count), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.slice (.param idx name)), layoutIdx⟩ = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact translateTy_eq_none_of_not_isMonoRigidTy layouts rfl

theorem translateTy_container_alias (layouts : Layout.LayoutTable) (m : MirAst.Mutability)
    (p : MirAst.DefPath) (args : List MirAst.RigidTy) (count : Nat) (defPath : String)
    (layoutIdx : Nat) :
    translateTy layouts ⟨.array (.alias p args) count, layoutIdx⟩ = none ∧
    translateTy layouts ⟨.tuple [.alias p args], layoutIdx⟩ = none ∧
    translateTy layouts ⟨.adt defPath [.alias p args], layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.tuple [.alias p args]), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.array (.alias p args) count), layoutIdx⟩ = none ∧
    translateTy layouts ⟨.rawPtr m (.slice (.alias p args)), layoutIdx⟩ = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact translateTy_eq_none_of_not_isMonoRigidTy layouts rfl

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

/-- Scalar integer type of a borrowed place (`placeIntType` for local or
projected places, or the pointee integer type `it` for a dereference `*_p` of a
raw pointer or reference local `_p`). -/
def borrowPlaceIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Place → Option Gen.IntType
  | ⟨p, [.deref]⟩ => (decls[p]? >>= (ptrPointeeOf ·.ty)).map Prod.snd
  | place => placeIntType layouts decls place

/-- `PointeeInfo` of a borrowed place (`Rvalue::Ref`): fast-paths all integer
borrows and integer dereference reborrows through `borrowPlaceIntType`
(`intPointeeInfo`), and extends reference creation to `bool`, `Ordering`,
`UnsafeCell<T>`, `TupleSpec` locals and sub-tuples (when `Freeze`), arrays, thin
pointers/references/`Box`, and projected dereference field paths `(*_p).f1...fk`
(`tooling/minimize/src/rvalue.rs`, `tooling/minimize/src/ty.rs`). -/
def borrowPlacePointeeInfo (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (place : MirAst.Place) : Option Gen.PointeeInfo :=
  match borrowPlaceIntType layouts decls place with
  | some it => some (intPointeeInfo it)
  | none =>
    match place with
    | ⟨j, []⟩ => do
      let d ← decls[j]?
      match pointeeInfoOfRigidTy d.ty.kind with
      | some info => some info
      | none =>
        let (_, size, align) ← tupleTypeOf layouts d.ty
        some { layout := .Sized ⟨size⟩ ⟨align⟩, inhabited := true,
               unsafe_cells := .Sized [], freeze := true, unpin := true }
    | ⟨j, .field idx fieldTy :: rest⟩ => do
      let d ← decls[j]?
      match intBoolTupleOf d.ty with
      | some _ =>
        match idx, rest with
        | 1, [] =>
          if isBoolTy fieldTy then
            some { layout := .Sized ⟨1⟩ ⟨1⟩, inhabited := true,
                   unsafe_cells := .Sized [], freeze := true, unpin := true }
          else none
        | _, _ => none
      | none =>
        let (fields, size, align) ← tupleTypeOf layouts d.ty
        let (_, leafSpec) ←
          resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest)
        match leafSpec with
        | .scalar it => some (intPointeeInfo it)
        | .tuple _ subSize subAlign =>
          some { layout := .Sized ⟨subSize⟩ ⟨subAlign⟩, inhabited := true,
                 unsafe_cells := .Sized [], freeze := true, unpin := true }
    | ⟨p, .deref :: rest⟩ => do
      let d ← decls[p]?
      let pointeeRt ← match d.ty.kind with
        | .rawPtr _ rt | .ref _ rt => some rt
        | .adt defPath (rt :: rest') =>
          if isMonoRigidTyList rest' && isBoxPath defPath then some rt else none
        | _ => none
      let leafRt ← match rest with
        | [] => some pointeeRt
        | .field _ fieldTy :: rest' => (resolveProjTy fieldTy rest').map (·.kind)
        | _ => none
      pointeeInfoOfRigidTy leafRt
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

/-- An rvalue with every `move` operand replaced by `copy` and `CopyForDeref(p)`
normalized to `Use(copy p)` (`minimize`'s `translate_rvalue_smir` translates
`CopyForDeref(p)` identically to `Use(copy p)`, and Anneal's `evalRvalue`
evaluates the two identically, including the dereference-read borrow freeze
`freezeDerefReadBorrowsAt`, except that only `Use(copy p)` applies typed-load
validation `validateLoadedValue`). -/
def copyRv : MirAst.Rvalue → MirAst.Rvalue
  | .use op => .use (copyOp op)
  | .copyForDeref p => .use (.copy p)
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

/-- The translation of MIR's `Rvalue::Discriminant(_j)` on an `Ordering` local
`_j`, given the `Load` `v` of `_j` at `orderingTy`. `minimize` lowers
`Rvalue::Discriminant` to MiniRust's `ValueExpr::GetDiscriminant`
(`tooling/minimize/src/rvalue.rs`):
> "smir::Rvalue::Discriminant(place) =>
>     ValueExpr::GetDiscriminant {
>         place: GcCow::new(self.translate_place_smir(place, span)),
>     },"
which reads only the bytes that the enum's discriminator touches and returns
the decoded discriminant at the enum's `discriminant_ty`
(`spec/lang/step/expressions.md`):
> "let Some(discriminant) = decode_discriminant::<M>(accessor, discriminator)? else {
>     throw_ub!(\"ValueExpr::GetDiscriminant encountered invalid discriminant.\");
> };
> ret((Value::Int(discriminant), Type::Int(discriminant_ty)))"
The executable interpretation `MiniRustSpec.Interp` does not implement
`GetDiscriminant`, so the correspondence lowers it, for `orderingTy` only, to
the `Load` of the place followed by `transmute::<i8>` (`build::transmute`, as
in `translateCmp`). `orderingTy` occupies exactly its one tag byte, which its
discriminator decodes at `i8` with the three branches `-1`, `0`, `1` (and
`Discriminator::Invalid` otherwise, see `orderingTy`), so both the `Load` at
`orderingTy` and `GetDiscriminant` read that one byte, raise UB unless it is
the tag `255`, `0`, or `1`, and otherwise produce `Value::Int` of the tag read
as an `i8` (`orderingDiscrExpr_eq_getDiscriminant` in
`MiniRustSpec.Correspondence.MiniRustEval` checks this on every byte). -/
def orderingDiscrExpr (v : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Cast (.Transmute (.Int IntType.I8))) v

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

/-- `minimize`'s rvalue translation for `Use`, `CopyForDeref`, `UnaryOp(Neg | Not)`
on integers, `UnaryOp(Not)` on `bool`, integer `BinaryOp`s, checked integer
`BinaryOp`s (`AddWithOverflow | SubWithOverflow | MulWithOverflow`), `bool`
bitwise `BinaryOp`s (`BitAnd | BitOr | BitXor` via `boolBitOp`), the comparison
`BinaryOp`s (including the three-way `Cmp`, `translateCmp`),
`Aggregate(Tuple | Adt | Array)`, `Len`, `Repeat`, `Discriminant` of an
`Ordering` local (`orderingDiscrExpr`), and
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
>      smir::Rvalue::CopyForDeref(place) =>
>          ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },
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

For references and raw pointers, `&p` / `&mut p` and `&raw const p` /
`&raw mut p` become `ValueExpr::AddrOf` at `PtrType::Ref` or `PtrType::Raw` of
the place's pointee, which is sized for every place `translatePlace` accepts
(`tooling/minimize/src/rvalue.rs`):
> "smir::Rvalue::Ref(_, bkind, place) => {
>     let ty = place.ty(&self.locals_smir).unwrap();
>     let pointee = self.pointee_info_of_smir(ty, span);
>
>     let place = self.translate_place_smir(place, span);
>     let target = GcCow::new(place);
>     let mutbl = translate_mutbl_smir(bkind.to_mutable_lossy());
>
>     let ptr_ty = PtrType::Ref { mutbl, pointee };
>
>     ValueExpr::AddrOf { target, ptr_ty }
> }
> smir::Rvalue::AddressOf(_mutbl, place) => {
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
a `Transmute` cast translates the operand and target type and wraps them in
`build::transmute` (`UnOp::Cast(CastOp::Transmute(ty))`):
> "smir::CastKind::Transmute
>  | smir::CastKind::FnPtrToPtr
>  | smir::CastKind::PointerCoercion(smir::PointerCoercion::UnsafeFnPointer) => {
>      let operand = self.translate_operand_smir(operand, span);
>      let ty = self.translate_ty_smir(*cast_ty, span);
>      build::transmute(operand, ty)
>  }"
and `Offset(l, r)` becomes `ptrOffsetExpr`. -/
def translateRvalue (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty := none) :
    MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand decls op
  | .copyForDeref p => .Load <$> translatePlace decls p
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
  | .discriminant ⟨j, []⟩ => do
    let d ← decls[j]?
    if isOrderingTy d.ty then pure (orderingDiscrExpr (.Load (.Local (localName j)))) else none
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
  | .ref bkind place => do
    let pointee ← borrowPlacePointeeInfo layouts decls place
    let target ← translatePlace decls place
    pure (.AddrOf target (.Ref (translateMutbl (borrowKindMutbl bkind)) pointee))
  | .cast .ptrToPtr op castTy => do
    let operand ← translateOperand decls op
    let oldMeta ← operandRawPtrMeta decls op
    let newMeta ← rawPtrMetaOf castTy
    if oldMeta == newMeta then pure operand
    else if newMeta == .None then pure (.UnOp .GetThinPointer operand)
    else none
  | .cast .transmute op castTy => do
    let operand ← translateOperand decls op
    let ty ← translateTy layouts castTy
    pure (.UnOp (.Cast (.Transmute ty)) operand)
  | _ => none

/-- Whether a MIR `RetagKind` is `RetagKind::FnEntry`
(`matches!(kind, rs::RetagKind::FnEntry)` in `tooling/minimize/src/bb.rs`). -/
def isRetagFnEntry : MirAst.RetagKind → Bool
  | .fnEntry => true
  | _ => false

/-- `minimize`'s statement translation for assignments, `StorageLive`,
`StorageDead`, `Retag`, and `PlaceMention` on a local or field-projected place
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
>  rs::StatementKind::Retag(kind, place) => {
>      let place = self.translate_place(place, span);
>      let fn_entry = matches!(kind, rs::RetagKind::FnEntry);
>      Statement::Validate { place, fn_entry }
>  }
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
  | .retag kind p => (translatePlace decls p).map (fun pe => .Validate pe (isRetagFnEntry kind))
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

/-- `minimize`'s calling-convention translation (`tooling/minimize/src/ty.rs`,
lines 348-354 at the pinned commit:
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/ty.rs#L348-L354>):
> "pub fn translate_calling_convention(conv: rs::CanonAbi) -> CallingConvention {
>      match conv {
>          rs::CanonAbi::C => CallingConvention::C,
>          rs::CanonAbi::Rust => CallingConvention::Rust,
>          ..
>      }
>  }" -/
def translateCallConv : Layout.CallConv → Option Gen.CallingConvention
  | .c => some .C
  | .rust => some .Rust
  | _ => none

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

Without a spread argument, `init_statements` holds exactly the
`StorageLive`s of `alwaysStorageLiveLocals` (`initBlock`). We translate the
calling convention from `body.fnAbi.conv` via `translateCallConv` and take
`implicit_writes` to be `true` (the `minimize` default absent
`#[rustc_no_writable]`). -/
def translateFn (body : MirAst.CapturedMir) : Option Gen.Function := do
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let blocks ← translateBlocks body.layouts body.localDecls 0 body.basicBlocks
  let n := body.basicBlocks.length
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
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

/-- `build::raw_void_ptr_ty()`, the thin raw pointer type with no metadata
(`Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })`). -/
def rawVoidPtrTy : Gen.Type := .Ptr (.Raw .None)

/-- `build::unit_ptr()`, `minimize`'s aligned dangling raw pointer constant
used as the dummy unwind payload and `unit_place` base (MiniRust's
`tooling/miniutil/src/build/expr.rs` at the pinned commit,
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/miniutil/src/build/expr.rs>):
`Constant::PointerWithoutProvenance(Address::from_bytes(1))` at
`raw_void_ptr_ty()`. -/
def unitPtr : Gen.ValueExpr :=
  .Constant (.PointerWithoutProvenance 1) rawVoidPtrTy

/-- `build::unit_place()`, `*unit_ptr()` at the zero-sized `()` tuple type
`Interp.unitType` (MiniRust's `tooling/miniutil/src/build/expr.rs` at the
pinned commit). `minimize` uses it as the destination of every intrinsic
that returns `()`, such as `Assume` (`StatementResult::Intrinsic`). -/
def unitPlace : Gen.PlaceExpr :=
  .Deref unitPtr Interp.unitType

/-- `build::abort()`, `minimize`'s abort terminator
(`tooling/minimize/src/bb.rs`):
> "Terminator::Intrinsic {
>      intrinsic: IntrinsicOp::Abort,
>      arguments: list![],
>      ret: unit_place(),
>      next_block: None,
>  }" -/
def abortTerminator : Gen.Terminator :=
  .Intrinsic .Abort [] unitPlace none

/-- MiniRust's unit type `()`, alias for `Interp.unitType` used by `mkStartFn`. -/
abbrev unitTy : Gen.Type := Interp.unitType

/-- `build::unit_place()`, alias for `unitPlace` used by `mkStartFn`. -/
abbrev buildUnitPlace : Gen.PlaceExpr := unitPlace

/-- `build::abort()`, alias for `abortTerminator` used by `mkStartFn` and
`translateUnwindAction`. -/
abbrev buildAbort : Gen.Terminator := abortTerminator

/-- Whether a MIR statement is
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_))`, which
`minimize` lowers to a block-ending `StatementResult::Intrinsic` with
`IntrinsicOp::Assume` and destination `unit_place()`. -/
def isAssume (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .intrinsic (.assume _) => true
  | _ => false

/-- `minimize`'s statement translation including `NonDivergingIntrinsic::Assume`
and the integer-pointer provenance casts (`tooling/minimize/src/bb.rs`):
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
  | .intrinsic (.assume op) => do
    let operand ← translateOperand decls op
    pure (.intrinsic .Assume unitPlace [operand])
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
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, initIdx) ←
    translateBlocksWithIntrinsics body.layouts body.localDecls 0 n body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
    blocks := ⟨blocks ++ [(bbName initIdx, initBlock body)]⟩
    start := bbName initIdx
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

/-- Program function-table mapping `defPath` to `(FnName, CallingConvention)`. -/
abbrev FnMap : Type := List (String × (Gen.FnName × Gen.CallingConvention))

/-- Look up the `FnName` assigned to `defPath` in `fnMap`. -/
def lookupFnName : FnMap → String → Option Gen.FnName
  | [], _ => none
  | (dp, (fn, _)) :: rest, target =>
    if dp == target then some fn else lookupFnName rest target

/-- Look up the `(FnName, CallingConvention)` target assigned to `defPath` in `fnMap`. -/
def lookupFnTarget : FnMap → String → Option (Gen.FnName × Gen.CallingConvention)
  | [], _ => none
  | (dp, entry) :: rest, target =>
    if dp == target then some entry else lookupFnTarget rest target

/-- Assign `FnName(0)` to `entry` and `FnName(1), FnName(2), ..` to `callees`
in list order along with each body's translated calling convention (defaulting
to `CallingConvention.Rust` if `translateCallConv` is `none`, so `fnNameMap`
remains total while `translateFnInProg` requires `translateCallConv` to return
`some`). `Ctxt::translate` names `entry` first
(`tooling/minimize/src/program.rs`):
> "let entry_name = FnName(Name::from_internal(0));
>
>  self.fn_name_map.insert(entry_instance, entry_name);"
and `Ctxt::get_fn_name` names every other function in the order in which
translation first references it:
> "pub fn get_fn_name(&mut self, key: rs::Instance<'tcx>) -> FnName {
>      // Used as the fn name if it is not named yet.
>      let len = self.fn_name_map.len();
>
>      *self.fn_name_map.entry(key).or_insert_with(|| FnName(Name::from_internal(len as _)))
>  }"
The two numberings therefore coincide when `callees` lists the callees in that
first-reference order, and otherwise differ only by a consistent renaming of
`FnName`s, which the fragment cannot observe: function names only index
`prog.functions` and `Machine::fn_ptrs`, and the fragment has no
pointer-to-integer casts or pointer comparisons. -/
def fnNameMap (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir) : FnMap :=
  (entry :: callees).zipIdx.map fun (b, idx) =>
    (b.defPath, (fnName idx, (translateCallConv b.fnAbi.conv).getD .Rust))

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
def translateCallArg (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.ArgumentExpr
  | .move p => (translatePlace decls p).map .InPlace
  | op => (translateOperand decls op).map .ByValue

/-- The `MR-4.1` spelling `buildUnitPlace` is `unitPlace`. -/
theorem unitPlace_eq_buildUnitPlace : unitPlace = buildUnitPlace := rfl

/-- The `MR-4.1` spelling `buildAbort` is `abortTerminator`. -/
theorem abortTerminator_eq_buildAbort : abortTerminator = buildAbort := rfl

/-- The `MR-4.1` spelling `unitTy` is the transcribed `unit_type()`. -/
theorem unitType_eq_unitTy : Interp.unitType = unitTy := rfl

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

/-- `minimize`'s per-statement translation result
(`tooling/minimize/src/bb.rs`):
> "/// A MIR statement becomes either a MiniRust statement or an intrinsic with some arguments, which
>  /// then starts a new basic block.
>  enum StatementResult {
>      Statement(Statement),
>      Intrinsic { intrinsic: IntrinsicOp, destination: PlaceExpr, arguments: List<ValueExpr> },
>  }" -/
inductive StatementResult : Type where
  | statement (s : Gen.Statement)
  | intrinsic (intrinsic : Gen.IntrinsicOp) (destination : Gen.PlaceExpr)
      (arguments : List Gen.ValueExpr)

/-- `minimize`'s per-terminator translation result
(`tooling/minimize/src/bb.rs`):
> "/// A MIR terminator becomes a MiniRust terminator, possibly preceded by a list
>  /// of statements to execute at the end of the previous basic block.
>  struct TerminatorResult {
>      stmts: List<Statement>,
>      terminator: Terminator,
>  }" -/
structure TerminatorResult where
  stmts : List Gen.Statement
  terminator : Gen.Terminator

/-- `build::count_ones(v)`, `ValueExpr::UnOp` with `IntUnOp::CountOnes`. -/
def buildCountOnes (v : Gen.ValueExpr) : Gen.ValueExpr :=
  .UnOp (.Int .CountOnes) v

/-- `build::div_exact(l, r)`, `ValueExpr::BinOp` with `IntBinOp::DivExact`. -/
def buildDivExact (l r : Gen.ValueExpr) : Gen.ValueExpr :=
  .BinOp (.Int .DivExact) l r

/-- `minimize`'s `translate_rs_intrinsic` (`tooling/minimize/src/bb.rs`) on the
intrinsic names whose arguments and destination require no `rustc` type-context
queries (`raw_eq`, `ctpop`, `exact_div`, `cold_path`, `abort`):
> "rs::sym::raw_eq =>
>      return TerminatorResult {
>          stmts: List::new(),
>          terminator: Terminator::Intrinsic {
>              intrinsic: IntrinsicOp::RawEq,
>              arguments: args
>                  .iter()
>                  .map(|x| self.translate_operand(&x.node, x.span))
>                  .collect(),
>              ret: self.translate_place(&destination, span),
>              next_block: target.as_ref().map(|t| self.bb_name_map[t]),
>          },
>      },"
> "rs::sym::ctpop => {
>      let v = self.translate_operand(&args[0].node, span);
>      let destination = self.translate_place(&destination, span);
>
>      let val = build::count_ones(v);
>      let stmt = Statement::Assign { destination, source: val };
>
>      let terminator = Terminator::Goto(self.bb_name_map[&target.unwrap()]);
>      return TerminatorResult { stmts: list![stmt], terminator };
>  }
>  rs::sym::exact_div => {
>      let l = self.translate_operand(&args[0].node, span);
>      let r = self.translate_operand(&args[1].node, span);
>      let destination = self.translate_place(&destination, span);
>
>      let val = build::div_exact(l, r);
>
>      let stmt = Statement::Assign { destination, source: val };
>      let terminator = Terminator::Goto(self.bb_name_map[&target.unwrap()]);
>
>      return TerminatorResult { stmts: list![stmt], terminator };
>  }"
> "rs::sym::cold_path => {
>      // Just a NOP for us.
>      let terminator = Terminator::Goto(self.bb_name_map[&target.unwrap()]);
>      return TerminatorResult { stmts: list![], terminator };
>  }"
> "rs::sym::abort => {
>      let terminator = build::abort();
>      TerminatorResult { stmts: list![], terminator }
>  }"
Other `translate_rs_intrinsic` arms (`assert_*_valid`, `arith_offset`,
`ptr_offset_from*`, `size_of_val`, `align_of_val`, `catch_unwind`) query `tcx`
layouts or synthesize catch blocks, and unsupported names hit `span_bug!`. -/
inductive RsIntrinsic
  | raw_eq
  | ctpop
  | exact_div
  | cold_path
  | abort
  | ub_checks
  deriving DecidableEq

def translateRsIntrinsic (decls : List MirAst.LocalDecl) (name : RsIntrinsic)
    (args : List MirAst.Operand) (destination : MirAst.Place) (target : Option Nat) :
    Option TerminatorResult :=
  match name with
  | .raw_eq => do
    let args' ← args.mapM (translateOperand decls)
    let ret' ← translatePlace decls destination
    pure ⟨[], .Intrinsic .RawEq args' ret' (target.map bbName)⟩
  | .ctpop =>
    match args, target with
    | [vOp], some t => do
      let v ← translateOperand decls vOp
      let dest ← translatePlace decls destination
      pure ⟨[.Assign dest (buildCountOnes v)], .Goto (bbName t)⟩
    | _, _ => none
  | .exact_div =>
    match args, target with
    | [lOp, rOp], some t => do
      let l ← translateOperand decls lOp
      let r ← translateOperand decls rOp
      let dest ← translatePlace decls destination
      pure ⟨[.Assign dest (buildDivExact l r)], .Goto (bbName t)⟩
    | _, _ => none
  | .cold_path =>
    match target with
    | some t => pure ⟨[], .Goto (bbName t)⟩
    | none => none
  | .abort => pure ⟨[], abortTerminator⟩
  | _ => none

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
where `minimize` computes the call edge's `conv` from the *callee instance's*
own ABI:
> "let abi = self
>      .cx
>      .tcx
>      .fn_abi_of_instance(self.typing_env().as_query_input((instance, rs::List::empty())))
>      .unwrap();
>  let conv = translate_calling_convention(abi.conv);"
so `lookupFnTarget` returns the callee's `translateCallConv callee.fnAbi.conv`,
which is exactly the `calling_convention` that `translateFnInProg` gives the
callee (and `create_frame`'s calling-convention check never fails on a
translated direct call). Non-call terminators delegate directly to
`translateTerminator` and synthesize no extra cleanup blocks. -/


def translateIntrinsicOrNone (decls : List MirAst.LocalDecl) (defPath : String)
    (argOps : List MirAst.Operand) (destination : MirAst.Place)
    (target : Option MirAst.BasicBlockIdx) : Option TerminatorResult :=
  match defPath.toList with
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','r','a','w','_','e','q'] =>
      translateRsIntrinsic decls .raw_eq argOps destination target
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','c','t','p','o','p'] =>
      translateRsIntrinsic decls .ctpop argOps destination target
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','e','x','a','c','t','_','d','i','v'] =>
      translateRsIntrinsic decls .exact_div argOps destination target
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','c','o','l','d','_','p','a','t','h'] =>
      translateRsIntrinsic decls .cold_path argOps destination target
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','a','b','o','r','t'] =>
      translateRsIntrinsic decls .abort argOps destination target
  | ['c','o','r','e',':',':','i','n','t','r','i','n','s','i','c','s',':',':','u','b','_','c','h','e','c','k','s'] =>
      translateRsIntrinsic decls .ub_checks argOps destination target
  | _ => none

def translateTerminatorInProg (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (nextCleanup : Nat) (t : MirAst.Terminator) :
    Option (Gen.Terminator × Nat × List (Gen.BbName × Gen.BasicBlock)) :=
  match t.kind with
  | .call func argOps destination target unwind => do
    let defPath ← extractFnDefPath func
    match translateIntrinsicOrNone decls defPath argOps destination target with
    | some res =>
      let b := bbName nextCleanup
      pure (.Goto b, nextCleanup + 1, [(b, ⟨res.stmts, res.terminator, .Regular⟩)])
    | none =>
      let (fn, conv) ← lookupFnTarget fnMap defPath
      let args ← argOps.mapM (translateCallArg decls)
      let retPlace ← translatePlace decls destination
      let (unwindBb, nextCleanup', extra) := translateUnwindAction nextCleanup unwind
      pure (.Call (fnPtrExpr fn) conv args retPlace (target.map bbName) (some unwindBb),
        nextCleanup', extra)
  | _ => do
    let term ← translateTerminator layouts decls t
    pure (term, nextCleanup, [])


/-- `minimize`'s `translate_stmt` (`tooling/minimize/src/bb.rs`) on the
fragment: `translateStatement` for the ordinary statements, and for
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))`
> "rs::StatementKind::Intrinsic(intrinsic) => {
>      match &**intrinsic {
>          rs::NonDivergingIntrinsic::Assume(op) => {
>              let op = self.translate_operand(op, span);
>              // Doesn't return anything, get us a dummy place.
>              let destination = build::unit_place();
>              return StatementResult::Intrinsic {
>                  intrinsic: IntrinsicOp::Assume,
>                  destination,
>                  arguments: list![op],
>              };
>          }
>          rs::NonDivergingIntrinsic::CopyNonOverlapping(_) =>
>              rs::span_bug!(span, \"NonDivergingIntrinsic not supported: {intrinsic:?}\"),
>      }
>  }"
`translate_operand` lowers `move p` like `copy p` (`translateOperand`).
`CopyNonOverlapping` is a `span_bug!` in `minimize` and stays untranslated. -/
def translateStmtResult (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Option StatementResult :=
  match s.kind with
  | .intrinsic (.assume op) =>
    (translateOperand decls op).map (fun op' => .intrinsic .Assume unitPlace [op'])
  | _ => (translateStatement decls s layouts).map .statement

/-- The statement loop of `minimize`'s `translate_bb`
(`tooling/minimize/src/bb.rs`):
> "for stmt in bb.statements.iter() {
>      match self.translate_stmt(stmt) {
>          StatementResult::Statement(stmt) => {
>              cur_block_statements.push(stmt);
>          }
>          StatementResult::Intrinsic { intrinsic, destination, arguments } => {
>              // Generate a fresh bb name.
>              let next_bb = self.fresh_bb_name();
>              // End the current block by jumping to the next one.
>              let terminator = Terminator::Intrinsic {
>                  intrinsic,
>                  arguments,
>                  ret: destination,
>                  next_block: Some(next_bb),
>              };
>              let cur_block = BasicBlock {
>                  statements: cur_block_statements,
>                  terminator,
>                  kind: block_kind,
>              };
>              let old = self.blocks.insert(cur_block_name, cur_block);
>              assert!(old.is_none()); // make sure we do not overwrite a bb
>              // Go on building the next block.
>              cur_block_name = next_bb;
>              cur_block_statements = List::new();
>          }
>      }
>  }"
Given the open block's name `cur` and statements `acc` and the next fresh
block index `nextBb`, returns the name and statements of the block that is
still open after the loop, the blocks the loop finished (in insertion order),
and the next fresh index. Fragment blocks are not cleanup blocks, so
`block_kind` is `BbKind::Regular`. -/
def splitStmts (cur : Gen.BbName) (acc : List Gen.Statement) (nextBb : Nat) :
    List StatementResult →
      Gen.BbName × List Gen.Statement × List (Gen.BbName × Gen.BasicBlock) × Nat
  | [] => (cur, acc, [], nextBb)
  | .statement s :: rest => splitStmts cur (acc ++ [s]) nextBb rest
  | .intrinsic op dest args :: rest =>
    let next := bbName nextBb
    let r := splitStmts next [] (nextBb + 1) rest
    (r.1, r.2.1, (cur, ⟨acc, .Intrinsic op args dest (some next), .Regular⟩) :: r.2.2.1, r.2.2.2)

/-- Translate basic blocks in index order while threading the fresh block
index `nextCleanup` (starting at `body.basicBlocks.length + 1`, after
`init_bb = bbName n` in `FnCtxt::translate`). `minimize`'s `translate_bb`
(`tooling/minimize/src/bb.rs`) first splits the block at every `Assume`
statement (`splitStmts`, taking fresh names in statement order) and then
translates the terminator into the block that is still open:
> "let TerminatorResult { stmts, terminator } = self.translate_terminator(bb);
>  for stmt in stmts.iter() {
>      cur_block_statements.push(stmt);
>  }
>  let cur_block =
>      BasicBlock { statements: cur_block_statements, terminator, kind: block_kind };
>  let old = self.blocks.insert(cur_block_name, cur_block);
>  assert!(old.is_none()); // make sure we do not overwrite a bb"
so any unwind block of the terminator takes a fresh name after the split
blocks. The first component lists every block that `translate_bb` inserts
for MIR blocks (the segment named after the MIR block comes first), and the
second component the synthesized cleanup blocks. -/
def translateBlocksInProg (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) :
    Nat → Nat → List MirAst.BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock))
  | _, _, [] => some ([], [])
  | i, nextCleanup, bb :: bbs => do
    let results ← bb.statements.mapM (translateStmtResult decls · layouts)
    let sp := splitStmts (bbName i) [] nextCleanup results
    let (term, nextCleanup', extra1) ←
      translateTerminatorInProg fnMap layouts decls sp.2.2.2 bb.terminator
    let (rest, extraRest) ← translateBlocksInProg fnMap layouts decls (i + 1) nextCleanup' bbs
    pure (sp.2.2.1 ++ [(sp.1, ⟨sp.2.1, term, .Regular⟩)] ++ rest, extra1 ++ extraRest)

/-- How `translate_bb` lays out MIR statements `ss`, followed by a terminator
that `translateTerminatorInProg` translated to `term`, from MiniRust block
`name` on, as seen through a block lookup `look` (`mapGet f.blocks`):
* `last`: no statement of `ss` is an `Assume`, and `name` holds the
  translations of `ss` followed by `term`;
* `split`: `ss = pre ++ s :: post` with `s` the first `Assume(op)`, `name`
  holds the translations of `pre` followed by `Terminator::Intrinsic` of
  `IntrinsicOp::Assume` on `op` with destination `unit_place()` and next block
  `next`, and `post` is laid out from `next` on (`splitStmts`).

A MIR program point `(blk, stmt)` therefore corresponds to a MiniRust program
point inside one of these segments (`PcAt` in `Correspondence.Relation`). -/
inductive SegChain (look : Gen.BbName → Option Gen.BasicBlock)
    (decls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable) (term : Gen.Terminator) :
    Gen.BbName → List MirAst.Statement → Prop where
  | last {name : Gen.BbName} {ss : List MirAst.Statement} {stmts : List Gen.Statement}
      (hlook : look name = some ⟨stmts, term, .Regular⟩)
      (htr : ss.mapM (translateStatement decls · layouts) = some stmts)
      (hna : ∀ s ∈ ss, isAssume s = false) :
      SegChain look decls layouts term name ss
  | split {name : Gen.BbName} {nextIdx : Nat} {pre post : List MirAst.Statement}
      {s : MirAst.Statement} {op : MirAst.Operand} {op' : Gen.ValueExpr}
      {stmts : List Gen.Statement}
      (hlook : look name =
        some ⟨stmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextIdx)), .Regular⟩)
      (htr : pre.mapM (translateStatement decls · layouts) = some stmts)
      (hna : ∀ s ∈ pre, isAssume s = false)
      (hs : s.kind = .intrinsic (.assume op))
      (hop : translateOperand decls op = some op')
      (hrest : SegChain look decls layouts term (bbName nextIdx) post) :
      SegChain look decls layouts term name (pre ++ s :: post)

/-- Active program-counter relation along a `SegChain` rooted at
`bbName entrySeg` for MIR statement list `ss` ending in `term`: MIR statement
index `stmtIdx` corresponds to MiniRust block `bbName curSeg` at statement
index `segStmt`. -/
inductive SegPc (look : Gen.BbName → Option Gen.BasicBlock)
    (decls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable) (term : Gen.Terminator) :
    Nat → List MirAst.Statement → Nat → Nat → Nat → Prop where
  | hereLast {curSeg segStmt : Nat} {ss : List MirAst.Statement}
      {stmts : List Gen.Statement}
      (hlook : look (bbName curSeg) = some ⟨stmts, term, .Regular⟩)
      (htr : ss.mapM (translateStatement decls · layouts) = some stmts)
      (hna : ∀ s ∈ ss, isAssume s = false)
      (hle : segStmt ≤ ss.length) :
      SegPc look decls layouts term curSeg ss segStmt curSeg segStmt
  | hereSplit {curSeg nextSeg segStmt : Nat} {pre post : List MirAst.Statement}
      {s : MirAst.Statement} {op : MirAst.Operand} {op' : Gen.ValueExpr}
      {stmts : List Gen.Statement}
      (hlook : look (bbName curSeg) =
        some ⟨stmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg)), .Regular⟩)
      (htr : pre.mapM (translateStatement decls · layouts) = some stmts)
      (hna : ∀ s ∈ pre, isAssume s = false)
      (hs : s.kind = .intrinsic (.assume op))
      (hop : translateOperand decls op = some op')
      (hrest : SegChain look decls layouts term (bbName nextSeg) post)
      (hle : segStmt ≤ pre.length) :
      SegPc look decls layouts term curSeg (pre ++ s :: post) segStmt curSeg segStmt
  | stepSplit {entrySeg nextSeg curSeg segStmt restIdx : Nat}
      {pre post : List MirAst.Statement}
      {s : MirAst.Statement} {op : MirAst.Operand} {op' : Gen.ValueExpr}
      {stmts : List Gen.Statement}
      (hlook : look (bbName entrySeg) =
        some ⟨stmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg)), .Regular⟩)
      (htr : pre.mapM (translateStatement decls · layouts) = some stmts)
      (hna : ∀ s ∈ pre, isAssume s = false)
      (hs : s.kind = .intrinsic (.assume op))
      (hop : translateOperand decls op = some op')
      (hrest : SegPc look decls layouts term nextSeg post restIdx curSeg segStmt) :
      SegPc look decls layouts term entrySeg (pre ++ s :: post) (pre.length + 1 + restIdx) curSeg segStmt

/-- `FnCtxt::translate` for a function in a multi-function program: `init_bb`
takes `bbName n` (`n = body.basicBlocks.length`), and the blocks that
`translate_bb` creates with `fresh_bb_name()` (the continuations after each
`Assume` statement, `splitStmts`, and the cleanup blocks synthesized by
`translate_unwind_action`) take `bbName (n + 1), bbName (n + 2), ..` in
allocation order (`tooling/minimize/src/function.rs`). When `body` contains no
`Call` terminators and no `Assume` statements, `extra` is empty, every MIR
block yields exactly one MiniRust block, and `translateFnInProg` produces the
exact same `Gen.Function` as `translateFn`. -/
def translateFnInProg (fnMap : FnMap)
    (body : MirAst.CapturedMir) : Option Gen.Function := do
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, extra) ←
    translateBlocksInProg fnMap body.layouts body.localDecls 0 (n + 1) body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
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
def translateProgFns (fnMap : FnMap) :
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

/-- Whether Anneal's `evalPlaceDiscriminant` (`Rvalue::Discriminant`) returns
the loaded scalar unchanged for every tag (`255`, `0`, `1`) of an `Ordering`
place of type `t`: the layout table has no entry at `t.layoutIdx` (then
`evalPlaceDiscriminant` checks the `core::cmp::Ordering` bit pattern itself),
or an inhabited entry whose variants are `Variants::Multiple` with either a
`union` tag (the same fallback) or an initialized tag whose valid range
contains the three tags. On an uninhabited entry, `Variants::Empty`, or
`Variants::Single` (which returns the 8-byte scalar `0`), or a valid range
excluding a tag, Anneal and MiniRust's `GetDiscriminant` (which reads the
`i8` tag) would disagree, so those layouts are outside the fragment. -/
def orderingDiscrLayoutOk (layouts : Layout.LayoutTable) (t : MirAst.Ty) : Bool :=
  match Layout.LayoutTable.lookup layouts t.layoutIdx with
  | none => true
  | some l =>
    !l.isUninhabited &&
    match l.variants with
    | .multiple (.initialized _ vr) _ _ =>
      MirAst.ScalarInt.inRange ⟨255, 1⟩ vr && MirAst.ScalarInt.inRange ⟨0, 1⟩ vr &&
        MirAst.ScalarInt.inRange ⟨1, 1⟩ vr
    | .multiple (.union _) _ _ => true
    | _ => false

/-- Fragment rvalues of integer type `it`. `Discriminant(_j)` of an
`Ordering` local `_j` has MiniRust type `Type::Int(i8)` (the `discriminant_ty`
of `orderingTy`), so it is an `i8` rvalue (`orderingDiscrLayoutOk` keeps
Anneal's result the loaded `i8` tag). -/
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
    ((decls[j]? >>= (arrayTypeOf ·.ty)).isSome &&
      -- Anneal's `evalPlaceLen` returns a `layoutPointerBytes layouts`-byte
      -- scalar, which is MiniRust's 8-byte `usize` only on a 64-bit layout table.
      decide (MirSemantics.layoutPointerBytes layouts = 8))
  | .discriminant ⟨j, []⟩ =>
    decide (it = IntType.I8) &&
    decide (j < decls.length) &&
    match decls[j]? with
    | some d => isOrderingTy d.ty && orderingDiscrLayoutOk layouts d.ty
    | none => false
  | _ => false

/-- `RigidTy.char` (`DIFF-AB`) is outside the MiniRust translation and integer
fragment (`intTyBytes .char = none`), so `char -> int` and `int -> char` casts
(`CastKind.intToInt`) fail closed in `translateTy`, `translateRvalue`, and
`rvalueOk`. -/
theorem intTyBytes_char : intTyBytes .char = none := rfl

theorem scalarTypeOf_char (layoutIdx : Nat) :
    scalarTypeOf ⟨.char, layoutIdx⟩ = none := rfl

theorem translateTy_char (layouts : Layout.LayoutTable) (layoutIdx : Nat) :
    translateTy layouts ⟨.char, layoutIdx⟩ = none := rfl

theorem translateRvalue_cast_intToInt_to_char_eq_none (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (op : MirAst.Operand) (layoutIdx : Nat) :
    translateRvalue layouts decls targetTy (.cast .intToInt op ⟨.char, layoutIdx⟩) = none := rfl

theorem rvalueOk_cast_intToInt_to_char_eq_false (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType)
    (op : MirAst.Operand) (layoutIdx : Nat) :
    rvalueOk layouts decls it (.cast .intToInt op ⟨.char, layoutIdx⟩) = false := rfl

theorem translateRvalue_cast_intToInt_from_char_const_eq_none (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (val : MirAst.ConstValue) (cLayoutIdx : Nat) (castTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy
      (.cast .intToInt (.constant ⟨⟨.char, cLayoutIdx⟩, val⟩) castTy) = none := by
  simp [translateRvalue, Option.bind_eq_bind, operandType, scalarTypeOf_char]

theorem rvalueOk_cast_intToInt_from_char_const_eq_false (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType)
    (val : MirAst.ConstValue) (cLayoutIdx : Nat) (castTy : MirAst.Ty) :
    rvalueOk layouts decls it
      (.cast .intToInt (.constant ⟨⟨.char, cLayoutIdx⟩, val⟩) castTy) = false := by
  simp [rvalueOk, operandIntType, intTypeOf, intTyBytes, operandOkB, operandIsBool, operandType,
    scalarTypeOf_char]

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

/-- Whether `c` is an 8-byte integer constant encoding `0` (`Offset(p, 0)`),
matching `MirSemantics.evalBinOpOffset`'s 64-bit offset width check. -/
def zeroOffsetConstOk (c : MirAst.ConstOperand) : Bool :=
  match c.val, intTypeOf c.ty with
  | .scalar (.int ⟨0, sz⟩), some rIt => decide (sz = 8 ∧ rIt.size.bytes = 8)
  | _, _ => false

theorem zeroOffsetConstOk_iff {c : MirAst.ConstOperand} :
    zeroOffsetConstOk c = true ↔
      ∃ rIt, c.val = .scalar (.int ⟨0, 8⟩) ∧ intTypeOf c.ty = some rIt ∧ rIt.size.bytes = 8 := by
  unfold zeroOffsetConstOk
  split
  · next sz rIt hval hit =>
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, hr⟩
      exact ⟨rIt, hval, hit, hr⟩
    · rintro ⟨rIt', hval', hit', hr⟩
      rw [hval] at hval'
      rw [hit] at hit'
      injection hval' with h1
      injection h1 with h2
      injection h2 with _ hsz
      injection hit' with hrIt
      subst hsz; subst hrIt
      exact ⟨rfl, hr⟩
  · next hne =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro rIt hval hit _
    exact hne 8 rIt hval hit

/-- Fragment rvalues producing a thin raw pointer (`isRef = false`) or reference
(`isRef = true`) of mutability `mutbl` and pointee integer type `pointeeIt`
(inspected after `copyRv`). Includes direct borrows (`&raw const q`, `&raw mut q`,
`&q`, `&mut q`, and two-phase `&two_phase mut q`), reborrows (`&raw const *_p`,
`&raw mut *_p`, `&*_p`, `&mut *_p`, and `&two_phase mut *_p`), pointer/reference
copies, `PtrToPtr` casts between raw pointers, `Transmute` casts between
compatible thin pointers and references (`*const T` / `*mut T` / `&T` / `&mut T`),
and zero-offset raw pointer arithmetic. -/
def ptrRvalueOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (isRef : Bool := false) : MirAst.Rvalue → Bool
  | .use (.copy ⟨p, []⟩) =>
    decide (p < decls.length) &&
    if isRef then
      decide ((decls[p]? >>= (refPointeeOf ·.ty)) = some (mutbl, pointeeIt))
    else
      decide ((decls[p]? >>= (rawPtrPointeeOf ·.ty)) = some (mutbl, pointeeIt))
  | .rawPtr m ⟨p, [.deref]⟩ =>
    !isRef &&
    decide (m = mutbl) &&
    decide (p < decls.length) &&
    match decls[p]? >>= (ptrPointeeOf ·.ty) with
    | some (srcMutbl, srcIt) =>
      decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
    | none => false
  | .rawPtr m place =>
    !isRef &&
    decide (m = mutbl) && ptrTargetOk layouts decls pointeeIt place
  | .ref bkind ⟨p, [.deref]⟩ =>
    isRef &&
    decide (borrowKindMutbl bkind = mutbl) &&
    decide (p < decls.length) &&
    match decls[p]? >>= (ptrPointeeOf ·.ty) with
    | some (srcMutbl, srcIt) =>
      decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
    | none => false
  | .ref bkind place =>
    isRef &&
    decide (borrowKindMutbl bkind = mutbl) &&
    ptrTargetOk layouts decls pointeeIt place
  | .cast .ptrToPtr (.copy ⟨p, []⟩) castTy =>
    !isRef &&
    decide (p < decls.length) &&
    decide (rawPtrPointeeOf castTy = some (mutbl, pointeeIt)) &&
    match decls[p]? >>= (rawPtrPointeeOf ·.ty) with
    | some (srcMutbl, srcIt) =>
      decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
    | none => false
  | .cast .transmute (.copy ⟨p, []⟩) castTy =>
    decide (p < decls.length) &&
    (if isRef then
       decide (refPointeeOf castTy = some (mutbl, pointeeIt))
     else
       decide (rawPtrPointeeOf castTy = some (mutbl, pointeeIt))) &&
    match decls[p]? >>= (ptrPointeeOf ·.ty) with
    | some (srcMutbl, srcIt) =>
      decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
    | none => false
  | .binaryOp .offset (.copy ⟨p, []⟩) (.constant c) =>
    !isRef &&
    decide (p < decls.length) &&
    decide ((decls[p]? >>= (rawPtrPointeeOf ·.ty)) = some (mutbl, pointeeIt)) &&
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

/-- Whether local `i` is declared with a thin raw pointer or reference type. -/
def isDeclPtrLocal (decls : List MirAst.LocalDecl) (i : Nat) : Bool :=
  match decls[i]? with
  | some d => isPtrTy d.ty
  | none => false

/-- Fragment statements, type-checked against the destination's type:
scalar-family root assignments (`bool`, `Ordering`, `(it, bool)`, and `Int`,
including raw-pointer and reference dereference reads `*_p`) check `copyRv rv`;
thin raw pointer and reference root assignments check `ptrRvalueOk` on `copyRv rv`;
array root assignments check `arrayRvalueOk`; `TupleSpec` root and field
assignments check `tupleRvalueOk` / `rvalueOk`; mutable raw pointer and `&mut`
reference dereference writes `(*_p) = rv` check `rvalueOk` on `copyRv rv` or
pointer-to-pointer dereference reads `ptrDerefReadOk` on `copyRv rv`; array
element assignments check `projOk` and `rvalueOk`;
`PlaceMention` checks `mentionPlaceOk`; and `StorageLive`, `StorageDead`, and
root `Deinit` take a declared scalar-family or thin pointer/reference local
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
                  ptrRvalueOk layouts decls mutbl pointeeIt (isRefTy d.ty) (copyRv rv)
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
    | some (.mut, pointeeIt) =>
      rvalueOk layouts decls pointeeIt (copyRv rv) ||
      ptrDerefReadOk decls pointeeIt (copyRv rv)
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
  | .retag kind ⟨i, []⟩ =>
    !isRetagFnEntry kind && decide (i < decls.length) && isDeclPtrLocal decls i
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
place: the operand shapes that `statementOk` and `terminatorOk` accept. Reading
one reads at most `opLocals op`. -/
def simpleOp : MirAst.Operand → Bool
  | .constant _ => true
  | .copy ⟨_, projs⟩ | .move ⟨_, projs⟩ => simpleProj projs

/-- The operands of an rvalue in the order in which Anneal's `evalRvalue`
evaluates them (left to right). `Discriminant(p)` reads `p` through
`evalOperand (.copy p)` before `evalPlaceDiscriminant` inspects the loaded
value, so its operand is `copy p`. -/
def rvOperands : MirAst.Rvalue → List MirAst.Operand
  | .use op | .repeat op _ | .unaryOp _ op | .cast _ op _ => [op]
  | .copyForDeref p | .len p | .discriminant p => [.copy p]
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

/-- The moved-out locals after statement `s`: those its operands move out of
(including `Assume(move _j)`, which `evalOperand` moves out in Anneal while
`translateOperand` lowers `move` via `ValueExpr::Load` in MiniRust), minus the
root local it writes (a root assignment's destination, or the local of
`StorageLive`, `StorageDead`, or root `Deinit`, after which both models agree
that the local is unallocated or holds the same bytes; a projected assignment
records its operand moves without clearing the destination root local). -/
def stmtMoved (mo : List Nat) (s : MirAst.Statement) : List Nat :=
  match s.kind with
  | .assign ⟨i, []⟩ rv => ((rvOperands rv).foldl moveOut mo).filter (· != i)
  | .assign ⟨_, _ :: _⟩ rv => (rvOperands rv).foldl moveOut mo
  | .intrinsic (.assume op) => moveOut mo op
  | .storageLive i | .storageDead i | .deinit ⟨i, []⟩ => mo.filter (· != i)
  | _ => mo

/-- Extract the pointer/reference local `p` of a dereference read rvalue
(`copy (*_p)`, `move (*_p)`, `CopyForDeref(*_p)`). -/
def ptrDerefReadSrc (rv : MirAst.Rvalue) : Option Nat :=
  match copyRv rv with
  | .use (.copy ⟨p, .deref :: _⟩) => some p
  | _ => none

/-- Whether statement `s` reads no moved-out local (including `_p` on a raw
pointer dereference read `*_p`, `idxLocal` on an indexed destination
`_i[_k] = rv`, and the destination root `_i` on a projected assignment
`_i.proj = rv` / `(*_p) = rv`). -/
def stmtReadsOk (mo : List Nat) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨_, []⟩ (.use (.copy ⟨p, .deref :: _⟩))
  | .assign ⟨_, []⟩ (.use (.move ⟨p, .deref :: _⟩))
  | .assign ⟨_, []⟩ (.copyForDeref ⟨p, .deref :: _⟩)
  | .assign ⟨_, []⟩ (.rawPtr _ ⟨p, .deref :: _⟩)
  | .assign ⟨_, []⟩ (.ref _ ⟨p, .deref :: _⟩) => !mo.contains p
  | .assign ⟨_, []⟩ rv => readsOk mo (rvOperands rv)
  | .assign p@⟨_, _ :: _⟩ rv =>
    match p, ptrDerefReadSrc rv with
    | ⟨w, [.deref]⟩, some r => !mo.contains r && !mo.contains w
    | _, _ =>
      readsOk mo (rvOperands rv) &&
      let mo' := (rvOperands rv).foldl moveOut mo
      (placeLocals p).all (fun j => !mo'.contains j)
  | .retag _ ⟨p, []⟩ => !mo.contains p
  | .intrinsic (.assume op) => readsOk mo [op]
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
  | .assign p (.rawPtr _ q) | .assign p (.ref _ q) => placeLocals p ++ placeLocals q
  | .assign p rv => placeLocals p ++ (rvOperands rv).flatMap opLocals
  | .intrinsic (.assume op) => opLocals op
  | .placeMention p | .deinit p | .retag _ p => placeLocals p
  | .storageLive i | .storageDead i => [i]
  | _ => []

/-- The locals a terminator mentions (`Return` reads `_0`; `Call` mentions its
destination local and all locals read by its arguments). -/
def termLocals (t : MirAst.Terminator) : List Nat :=
  match t.kind with
  | .switchInt discr _ => opLocals discr
  | .return_ => [0]
  | .call _ argOps dst _ _ => dst.local_ :: argOps.filterMap opRead
  | _ => []

/-- No statement or terminator mentions a local that `initBlock` allocates. -/
def mentionsOk (body : MirAst.CapturedMir) : Bool :=
  body.basicBlocks.all fun bb =>
    bb.statements.all (fun s => (stmtLocals s).all (fun j => !(alwaysStorageLiveLocals body).contains j)) &&
    (termLocals bb.terminator).all (fun j => !(alwaysStorageLiveLocals body).contains j)

/-! ### Pointer and reference borrow discipline -/

/-- Extract the mutability and target place of a direct (non-deref) `&raw` or
`&` / `&mut` borrow rvalue. Reborrows (`&*_p`, `&mut *_p`, `&raw const *_p`,
`&raw mut *_p`) borrow through an existing pointer or reference local `_p` whose
underlying target local was already borrowed at the root of the chain. -/
def directBorrowOf : MirAst.Rvalue → Option (MirAst.Mutability × MirAst.Place)
  | .rawPtr m ⟨k, []⟩ => some (m, ⟨k, []⟩)
  | .rawPtr _ ⟨_, .deref :: _⟩ => none
  | .rawPtr m ⟨k, projs⟩ => some (m, ⟨k, projs⟩)
  | .ref bk ⟨k, []⟩ => some (borrowKindMutbl bk, ⟨k, []⟩)
  | .ref _ ⟨_, .deref :: _⟩ => none
  | .ref bk ⟨k, projs⟩ => some (borrowKindMutbl bk, ⟨k, projs⟩)
  | _ => none

/-- All locals `k` whose address is directly taken via `.rawPtr` or `.ref`
anywhere in `body`. -/
def bodyAddrTakenLocals (body : MirAst.CapturedMir) : List Nat :=
  body.basicBlocks.flatMap fun bb =>
    bb.statements.filterMap fun s =>
      match s.kind with
      | .assign _ rv => (directBorrowOf rv).map (·.2.local_)
      | _ => none

/-- All places `q` directly borrowed via `.rawPtr` or `.ref` anywhere in `body`. -/
def bodyDirectBorrowPlaces (body : MirAst.CapturedMir) : List MirAst.Place :=
  body.basicBlocks.flatMap fun bb =>
    bb.statements.filterMap fun s =>
      match s.kind with
      | .assign _ rv => (directBorrowOf rv).map (·.2)
      | _ => none

/-- Canonical zero-initialized `MirSemantics.Value` for a fragment `LocalDecl`. -/
def canonicalDeclVal (layouts : Layout.LayoutTable) (d : MirAst.LocalDecl) : MirSemantics.Value :=
  match intTypeOf d.ty with
  | some it => .scalar ⟨0, it.size.bytes⟩
  | none =>
    match arrayTypeOf d.ty with
    | some (elemIt, count) => .aggregate 0 (List.replicate count (.scalar ⟨0, elemIt.size.bytes⟩))
    | none =>
      match tupleTypeOf layouts d.ty with
      | some (fields, size, align) => (TupleSpec.tuple fields size align).zeroVal
      | none => .unit

/-- Static consistency of `body.layouts` and `body.localDecls` with `minimize`'s
pointer, target-alignment, stride, and byte-offset rules across all pointer
locals and directly borrowed places in `body`. -/
def ptrDeclLayoutsOk (body : MirAst.CapturedMir) : Bool :=
  let decls := body.localDecls
  let layouts := body.layouts
  let canonLocals : List MirSemantics.LocalSlot :=
    decls.map (fun d => .init (canonicalDeclVal layouts d))
  let borrowPlaces := bodyDirectBorrowPlaces body
  (List.range decls.length).all (fun p =>
    match decls[p]? with
    | none => true
    | some dp =>
      match ptrPointeeOf dp.ty with
      | none => true
      | some (_, pointeeIt) =>
        match MirSemantics.placeTyResolved decls layouts ⟨p, [.deref]⟩ with
        | none => false
        | some pTy =>
          let rAccTy := MirSemantics.resolveTyWithLocalDecls decls layouts pTy
          decide (MirSemantics.tyScalarBytes rAccTy = some pointeeIt.size.bytes) &&
          decide (MirSemantics.tyByteSize decls layouts pTy = some pointeeIt.size.bytes) &&
          decide (MirSemantics.tyByteSize decls layouts rAccTy = some pointeeIt.size.bytes) &&
          (match rAccTy.kind with
           | .bool | .char | .never => false
           | _ => true) &&
          borrowPlaces.all (fun q =>
            match decls[q.local_]? with
            | none => true
            | some dk =>
              let qEntry : MirSemantics.BorrowEntry :=
                { tag := 0, targetLocal := q.local_, targetProjection := q.projection,
                  perm := .active }
              MirSemantics.checkTargetPlaceAlign decls layouts (some pTy)
                qEntry ⟨0, 0⟩ (some (canonicalDeclVal layouts dk)) &&
              MirSemantics.checkTargetPlaceAlign decls layouts (some rAccTy)
                qEntry ⟨0, 0⟩ (some (canonicalDeclVal layouts dk)))) &&
  borrowPlaces.all (fun q =>
    match decls[q.local_]?, ptrTargetSpec layouts decls q with
    | some dk, some (pointeeIt, relOff) =>
      let qEntry : MirSemantics.BorrowEntry :=
        { tag := 0, targetLocal := q.local_, targetProjection := q.projection, perm := .active }
      decide (MirSemantics.borrowPlaceByteOffset? canonLocals [] decls layouts qEntry =
        some relOff) &&
      match q.projection with
      | [] =>
        decide (MirSemantics.tyByteSize decls layouts
          (MirSemantics.resolveTyWithLocalDecls decls layouts dk.ty) = some pointeeIt.size.bytes)
      | [.constantIndex _ _ _] =>
        decide (MirSemantics.resolveSeqContainerElemByteStride decls layouts q.local_ [] [] =
          pointeeIt.size.bytes) &&
        match MirSemantics.placeTyResolved decls layouts q with
        | some projTy =>
          decide (MirSemantics.tyByteSize decls layouts projTy = some pointeeIt.size.bytes)
        | none => false
      | .field _ _ :: _ =>
        (match tupleTypeOf layouts dk.ty with
         | some (_, size, _) =>
           decide (MirSemantics.tyByteSize decls layouts
             (MirSemantics.resolveTyWithLocalDecls decls layouts dk.ty) = some size) &&
           decide (MirSemantics.projectionChainByteOffset? layouts
             (some (MirSemantics.resolveTyWithLocalDecls decls layouts dk.ty))
             (some (canonicalDeclVal layouts dk)) none 0 decls q.projection = some relOff)
         | none => false) &&
        match MirSemantics.placeTyResolved decls layouts q with
        | some projTy =>
          decide (MirSemantics.tyByteSize decls layouts projTy = some pointeeIt.size.bytes)
        | none => false
      | _ => true
    | _, _ => true)

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
  | .intrinsic (.assume op) => moveFree [op]
  | .deinit p => !addrLocals.contains p.local_
  | .storageLive i | .storageDead i => !addrLocals.contains i
  | _ => true

/-- Whether `t` moves out no local in `addrLocals` and (when `t` is a `Call`)
writes its return value to no local in `addrLocals`. -/
def termPreservesAddrTaken (addrLocals : List Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .switchInt discr _ =>
    match opMoved discr with
    | some j => !addrLocals.contains j
    | none => true
  | .call _ argOps dst _ _ =>
    !addrLocals.contains dst.local_ &&
    argOps.all fun op =>
      match opMoved op with
      | some j => !addrLocals.contains j
      | none => true
  | _ => true

theorem termPreservesAddrTaken_call_spec {addrLocals : List Nat}
    {fn : MirAst.Operand} {argOps : List MirAst.Operand} {dst : MirAst.Place}
    {target : Option Nat} {unwind : MirAst.UnwindAction} {span : String}
    (h : termPreservesAddrTaken addrLocals ⟨.call fn argOps dst target unwind, span⟩ = true) :
    addrLocals.contains dst.local_ = false ∧
      ∀ op ∈ argOps, ∀ j, opMoved op = some j → addrLocals.contains j = false := by
  simp only [termPreservesAddrTaken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  refine ⟨h.1, fun op hop j hmov => ?_⟩
  have hop' := h.2 op hop
  rw [hmov] at hop'
  simpa using hop'

/-- Decidable static summary of a non-transparent `ProjectionElem` step, erasing
type payloads so borrow targets have `DecidableEq` while matching
`MirSemantics.projectionsOverlap` exactly (`borrowProjOverlap_borrowProjSteps`). -/
inductive BorrowProjStep where
  | field (idx : Nat)
  | constantIndex (offset : Nat) (fromEnd : Bool)
  | downcast (variantIdx : Nat)
  | other
  deriving DecidableEq, Repr

/-- Convert a `ProjectionElem` path to `BorrowProjStep`s after stripping
transparent `.opaqueCast` and `.unwrapUnsafeBinder` steps, matching
`MirSemantics.stripTransparentProjections`. -/
def borrowProjSteps : List MirAst.ProjectionElem → List BorrowProjStep
  | [] => []
  | .opaqueCast _ :: rest => borrowProjSteps rest
  | .unwrapUnsafeBinder _ :: rest => borrowProjSteps rest
  | .field idx _ :: rest => .field idx :: borrowProjSteps rest
  | .constantIndex off _ fromEnd :: rest => .constantIndex off fromEnd :: borrowProjSteps rest
  | .downcast _ varIdx :: rest => .downcast varIdx :: borrowProjSteps rest
  | _ :: rest => .other :: borrowProjSteps rest

/-- Exact `BorrowProjStep` mirror of `MirSemantics.projectionsOverlapAux`. -/
def borrowProjOverlap : List BorrowProjStep → List BorrowProjStep → Bool
  | [], _ => true
  | _, [] => true
  | .field idxA :: restA, .field idxB :: restB =>
    if idxA == idxB then borrowProjOverlap restA restB else false
  | .constantIndex offA fromEndA :: restA, .constantIndex offB fromEndB :: restB =>
    if fromEndA == fromEndB then
      if offA == offB then borrowProjOverlap restA restB else false
    else
      borrowProjOverlap restA restB
  | .downcast varA :: restA, .downcast varB :: restB =>
    if varA == varB then borrowProjOverlap restA restB else false
  | _ :: _, _ :: _ => true

/-- Flow-sensitive abstract borrow state of a pointer or reference local `p`:
* `.empty` (`⊥`): `p` holds no initialized pointer (`.dead` or `.uninit`, or `p`
  is not a pointer/reference local);
* `.live target peers hot`: if `p` holds an initialized pointer `pv`, its Anneal
  `BorrowEntry` is not `.disabled`, is not `.active` whenever `hot = false`
  (two-phase borrows `&two_phase mut`, mutable reference reborrows `&mut *_p`,
  and shared borrows start `.reserved` or `.frozen`, which foreign reads leave
  unfrozen), is not `.frozen` when `p` is a mutable pointer/reference local,
  targets `target` (when `some`), and has a tag `pv.tag` in the Tree Borrows
  subtree of every initialized pointer/reference local in `peers` (the peers are
  `p`'s tag-sharing copies and its reborrow ancestors, `PtrLocalOk`), so a write
  or read through `p` is a local access for every peer;
* `.disabled` (`⊤`): `p`'s tag may have been invalidated by a dereference write
  through a distinct overlapping tag (or frozen on a hot mutable borrow by a
  foreign read), so dereferencing `p` is forbidden. -/
inductive PtrLocalState where
  | empty
  | live (target : Option (Nat × List BorrowProjStep)) (peers : List Nat) (hot : Bool := true)
  | disabled
  deriving DecidableEq, Repr

/-- Whether a fresh borrow or reborrow rvalue creates an immediately `.active`
entry (`&raw mut` or non-two-phase root `&mut`), as opposed to `.reserved` or
`.frozen` (`&two_phase mut`, reference reborrows `&mut *_p`, `&`, `&raw const`). -/
def borrowStartsHot : MirAst.Rvalue → Bool
  | .rawPtr .mut _ => true
  | .ref (.mut false) ⟨_, []⟩ => true
  | .ref (.mut false) ⟨_, .deref :: _⟩ => false
  | .ref (.mut false) ⟨_, _ :: _⟩ => true
  | _ => false

/-- Whether `st` may hold an `.active` Tree Borrows entry (which a foreign read
would freeze). -/
def isHotPtrState : PtrLocalState → Bool
  | .live _ _ hot => hot
  | _ => false

/-- Extract the parent local `p` of a reborrow rvalue (`&*_p`, `&mut *_p`,
`&raw const *_p`, `&raw mut *_p`). -/
def reborrowParentOf : MirAst.Rvalue → Option Nat
  | .rawPtr _ ⟨p, .deref :: _⟩ => some p
  | .ref _ ⟨p, .deref :: _⟩ => some p
  | _ => none

/-- Extract the source local `p` of a zero-offset pointer arithmetic rvalue
`Offset(copy _p, _)` / `Offset(move _p, _)`, which `evalPtrOffsetBinOp` faults
on when `_p`'s borrow tag is `.disabled`. -/
def ptrOffsetSrcOf (rv : MirAst.Rvalue) : Option Nat :=
  match copyRv rv with
  | .binaryOp .offset (.copy ⟨p, []⟩) _ => some p
  | _ => none

/-- Extract the source pointer/reference local `p` of a tag-preserving copy,
`CopyForDeref`, `PtrToPtr` cast, `Transmute` cast, or zero-offset `Offset`. -/
def ptrCopySrcOf (decls : List MirAst.LocalDecl) (rv : MirAst.Rvalue) : Option Nat :=
  match copyRv rv with
  | .use (.copy ⟨p, []⟩)
  | .cast .ptrToPtr (.copy ⟨p, []⟩) _
  | .cast .transmute (.copy ⟨p, []⟩) _
  | .binaryOp .offset (.copy ⟨p, []⟩) _ =>
    match decls[p]? with
    | some dp => if isPtrTy dp.ty then some p else none
    | none => none
  | _ => none

/-- Remove local `i` from a `PtrLocalState`'s peer set when `i` is overwritten. -/
def removePeerFromState (i : Nat) : PtrLocalState → PtrLocalState
  | .empty => .empty
  | .live t ps hot => .live t (ps.filter (· != i)) hot
  | .disabled => .disabled

/-- Add local `i` to a `.live` state's peer set. -/
def addPeerToState (i : Nat) : PtrLocalState → PtrLocalState
  | .empty => .empty
  | .live t ps hot => .live t (if ps.contains i then ps else i :: ps) hot
  | .disabled => .disabled

/-- Update local `i` to `st` while removing `i` from all other locals' peer sets. -/
def setPtrLocal (n : Nat) (env : List PtrLocalState) (i : Nat) (st : PtrLocalState) :
    List PtrLocalState :=
  (List.range n).map fun q =>
    if q == i then st else removePeerFromState i (env.getD q .disabled)

/-- Abstract transfer for a reborrow `_i = &*_p` / `&mut *_p` / `&raw *_p`,
which allocates a fresh child tag inheriting `p`'s borrow target, `p`'s
ancestor-local set (plus `i`), and initial hotness `hot`. -/
def stepReborrow (n : Nat) (env : List PtrLocalState) (i p : Nat) (hot : Bool) :
    List PtrLocalState :=
  let newSt :=
    match env.getD p .disabled with
    | .empty => .empty
    | .live target pPeers _ => .live target (i :: pPeers.filter (· != i)) hot
    | .disabled => .disabled
  setPtrLocal n env i newSt

/-- Abstract transfer for a tag-preserving pointer/reference copy `_i = _p`,
`PtrToPtr` cast, or zero-offset `Offset`. -/
def stepPtrCopy (n : Nat) (env : List PtrLocalState) (i p : Nat) : List PtrLocalState :=
  if i == p then
    (List.range n).map (fun q => env.getD q .disabled)
  else
    let srcSt := addPeerToState i (env.getD p .disabled)
    (List.range n).map fun q =>
      if q == i then srcSt
      else
        match removePeerFromState i (env.getD q .disabled) with
        | .live t ps qHot =>
          if ps.contains p then .live t (if ps.contains i then ps else i :: ps) qHot
          else .live t ps qHot
        | other => other

/-- Whether two static borrow targets are guaranteed not to overlap in Anneal's
`borrowEntryOverlapsWrite` (`k1 ≠ k2` or `borrowProjOverlap p1 p2 = false`). -/
def targetsDefinitelyDisjoint :
    Option (Nat × List BorrowProjStep) → Option (Nat × List BorrowProjStep) → Bool
  | some (k1, p1), some (k2, p2) =>
    decide (k1 ≠ k2) || !borrowProjOverlap p1 p2
  | _, _ => false

/-- Abstract transfer for a dereference write `(*_w) = rv`: every `.live` local
whose tag is an ancestor-or-self of `w`'s tag (`q ∈ wPeers`, a local write that
activates `.reserved` entries) or that targets a provably non-overlapping place
(`targetsDefinitelyDisjoint`) stays `.live` (conservatively marked `hot = true`),
and all other `.live` locals become `.disabled`. -/
def stepDerefWrite (n : Nat) (env : List PtrLocalState) (w : Nat) : List PtrLocalState :=
  match env.getD w .disabled with
  | .empty => (List.range n).map (fun q => env.getD q .disabled)
  | .disabled => (List.range n).map (fun _ => .disabled)
  | .live wTarget wPeers _ =>
    (List.range n).map fun q =>
      match env.getD q .disabled with
      | .empty => .empty
      | .disabled => .disabled
      | .live qTarget qPeers _ =>
        if wPeers.contains q || targetsDefinitelyDisjoint qTarget wTarget then
          .live qTarget qPeers true
        else
          .disabled

/-- Whether local `q` is declared as a mutable raw pointer or mutable reference
(`*mut T` / `&mut T`): the only pointer/reference locals through which the
fragment writes (`(*_q) = rv`) or reborrows mutably (`&mut *_q`, `&raw mut *_q`). -/
def isMutPtrLocal (decls : List MirAst.LocalDecl) (q : Nat) : Bool :=
  match decls[q]? >>= (ptrPointeeOf ·.ty) with
  | some (.mut, _) => true
  | _ => false

/-- Whether a Tree Borrows read through `r`'s tag provably leaves `q`'s abstract
state valid: `q` is `r` itself, `q` holds no pointer (`.empty`) or is already
`.disabled`, `r` holds no pointer (the read is UB), or both are `.live` and `q`'s
tag is an ancestor-or-self of `r`'s tag (`q ∈ rPeers`, so the read is local for
`q`) or `q` targets a place that cannot overlap `r`'s
target (`targetsDefinitelyDisjoint`). A `.disabled` reader keeps no `.live` `q`
(so that `stepForeignRead` is monotone). -/
def foreignReadKeeps (env : List PtrLocalState) (r q : Nat) : Bool :=
  q == r ||
  match env.getD r .disabled, env.getD q .disabled with
  | .empty, _ => true
  | _, .empty => true
  | _, .disabled => true
  | .live rTarget rPeers _, .live qTarget _ _ =>
    rPeers.contains q || targetsDefinitelyDisjoint qTarget rTarget
  | .disabled, .live _ _ _ => false

/-- Abstract transfer for a Tree Borrows read through `r`'s tag: a dereference
read `*_r` (`freezeDerefReadBorrowsAt`) or the initial read of a reborrow
`&*_r` / `&mut *_r` (`freezeTreeBorrowsOnReadAtProj`). Anneal freezes every
foreign `.active` entry overlapping the read (MiniRust
`PermissionUnprot::foreign_read`), leaving `.reserved` and `.frozen` entries
unchanged, so every hot (`isHotPtrState`) `.live` mutable pointer/reference local
(`isMutPtrLocal`) that the read may freeze (`foreignReadKeeps = false`) becomes
`.disabled`, while cold (`hot = false`) `.reserved` borrows and shared
pointer/reference locals stay `.live`. -/
def stepForeignRead (decls : List MirAst.LocalDecl) (n : Nat) (env : List PtrLocalState)
    (r : Nat) : List PtrLocalState :=
  (List.range n).map fun q =>
    if isMutPtrLocal decls q && isHotPtrState (env.getD q .disabled) && !foreignReadKeeps env r q then
      .disabled
    else env.getD q .disabled

/-- Extract the parent local `p` of a reference reborrow (`&*_p`, `&mut *_p`),
which, unlike a raw reborrow `&raw *_p`, performs an initial read through `p`'s
tag (`PermissionUnprot::init_access`). -/
def refReborrowParentOf : MirAst.Rvalue → Option Nat
  | .ref _ ⟨p, .deref :: _⟩ => some p
  | _ => none

/-- `stepForeignRead` for the initial read of a reference reborrow
(`refReborrowParentOf`); the identity on every other rvalue. -/
def stepReborrowRead (decls : List MirAst.LocalDecl) (n : Nat) (env : List PtrLocalState)
    (rv : MirAst.Rvalue) : List PtrLocalState :=
  match refReborrowParentOf rv with
  | some p => stepForeignRead decls n env p
  | none => env

/-- Whether statement `s` never dereferences (for reading, reborrowing, or
writing), offsets (`BinOp::Offset`), or retags (`StatementKind::Retag`) a
`.disabled` pointer or reference local. `.empty` (uninitialized or dead) is
permitted because both Anneal and MiniRust raise UB when loading or validating
an uninitialized or dead pointer local. A pointer-to-pointer copy
`(*_w) = copy (*_p)` additionally requires the read through `_p`, which Anneal
evaluates before the write, to keep `_w`'s entry unfrozen (`foreignReadKeeps`). -/
def ptrStmtOk (env : List PtrLocalState) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨_, []⟩ rv =>
    match ptrDerefReadSrc rv with
    | some p => env.getD p .disabled != .disabled
    | none =>
      match reborrowParentOf rv with
      | some p => env.getD p .disabled != .disabled
      | none =>
        match ptrOffsetSrcOf rv with
        | some p => env.getD p .disabled != .disabled
        | none => true
  | .assign ⟨w, [.deref]⟩ rv =>
    env.getD w .disabled != .disabled &&
    match ptrDerefReadSrc rv with
    | some p => env.getD p .disabled != .disabled && foreignReadKeeps env p w
    | none => true
  | .retag _ ⟨p, []⟩ => env.getD p .disabled != .disabled
  | _ => true

/-- Flow-sensitive abstract state transition of `s` on `env`. -/
def ptrStmtStep (decls : List MirAst.LocalDecl) (env : List PtrLocalState)
    (s : MirAst.Statement) : List PtrLocalState :=
  let n := decls.length
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    if isDeclPtrLocal decls i then
      match directBorrowOf rv with
      | some (_, ⟨k, projs⟩) =>
        setPtrLocal n env i (.live (some (k, borrowProjSteps projs)) [i] (borrowStartsHot rv))
      | none =>
        match reborrowParentOf rv with
        | some p => stepReborrow n (stepReborrowRead decls n env rv) i p (borrowStartsHot rv)
        | none =>
          match ptrCopySrcOf decls rv with
          | some p => stepPtrCopy n env i p
          | none => setPtrLocal n env i .disabled
    else
      match ptrDerefReadSrc rv with
      | some r => stepForeignRead decls n env r
      | none => (List.range n).map (fun q => env.getD q .disabled)
  | .assign ⟨w, [.deref]⟩ rv =>
    match ptrDerefReadSrc rv with
    | some r => stepDerefWrite n (stepForeignRead decls n env r) w
    | none => stepDerefWrite n env w
  | .storageLive i | .storageDead i | .deinit ⟨i, []⟩ =>
    if isDeclPtrLocal decls i then
      setPtrLocal n env i .empty
    else
      (List.range n).map (fun q => env.getD q .disabled)
  | _ => (List.range n).map (fun q => env.getD q .disabled)

/-- Whether every statement in `ss` satisfies `ptrStmtOk` along the abstract
execution starting from `env`. -/
def blockPtrAliasOk (decls : List MirAst.LocalDecl) (env : List PtrLocalState) :
    List MirAst.Statement → Bool
  | [] => true
  | s :: ss => ptrStmtOk env s && blockPtrAliasOk decls (ptrStmtStep decls env s) ss

/-- Least upper bound in the `PtrLocalState` join-semilattice (`.empty` is `⊥`,
`.disabled` is `⊤`). -/
def joinPtrLocalState : PtrLocalState → PtrLocalState → PtrLocalState
  | .empty, s => s
  | s, .empty => s
  | .live t1 ps1 h1, .live t2 ps2 h2 =>
    let t := if t1 == t2 then t1 else none
    let ps := ps1.filter (fun r => ps2.contains r)
    .live t ps (h1 || h2)
  | _, _ => .disabled

/-- Pointwise join of two `PtrLocalState` environments of width `n`. -/
def joinPtrEnv (n : Nat) (e1 e2 : List PtrLocalState) : List PtrLocalState :=
  (List.range n).map fun q =>
    joinPtrLocalState (e1.getD q .disabled) (e2.getD q .disabled)

/-- Partial order `s1 ≤ s2` on `PtrLocalState` (`PtrLocalOk ... s1` implies
`PtrLocalOk ... s2`). -/
def subsumesPtrLocalState : PtrLocalState → PtrLocalState → Bool
  | .empty, _ => true
  | _, .disabled => true
  | .live t1 ps1 h1, .live t2 ps2 h2 =>
    (!h1 || h2) &&
    (match t2 with
     | none => true
     | some q2 => decide (t1 = some q2)) &&
    ps2.all (fun r => ps1.contains r)
  | _, _ => false

/-- Pointwise subsumption `e1 ≤ e2` across locals `0 .. n - 1`. -/
def subsumesPtrEnv (n : Nat) (e1 e2 : List PtrLocalState) : Bool :=
  (List.range n).all fun q =>
    subsumesPtrLocalState (e1.getD q .disabled) (e2.getD q .disabled)

/-- Initial abstract environment (`⊥` on all `n` locals). -/
def initPtrEnv (n : Nat) : List PtrLocalState :=
  (List.range n).map (fun _ => .empty)

/-- Initial per-block entry table (`initPtrEnv n` at every block). -/
def initPtrEntries (bbsLen n : Nat) : List (List PtrLocalState) :=
  (List.range bbsLen).map (fun _ => initPtrEnv n)

/-- One forward CFG pass propagating exit `PtrLocalState` environments to
successor block entries via `joinPtrEnv`. -/
def stepPtrAliasEntries (decls : List MirAst.LocalDecl)
    (bbs : List MirAst.BasicBlockData)
    (entries : List (List PtrLocalState)) : List (List PtrLocalState) :=
  let n := decls.length
  (List.range bbs.length).map fun dst =>
    (List.range bbs.length).foldl (fun acc src =>
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let inEnv := entries.getD src (initPtrEnv n)
          let outEnv := bb.statements.foldl (ptrStmtStep decls) inEnv
          joinPtrEnv n acc outEnv
        else acc
      | none => acc) (entries.getD dst (initPtrEnv n))

/-- Iterate forward `PtrLocalState` propagation up to `fuel` passes, stopping
early as soon as the per-block entry environments stabilize. -/
def iterPtrAliasEntries :
    Nat → List MirAst.LocalDecl → List MirAst.BasicBlockData →
      List (List PtrLocalState) → List (List PtrLocalState)
  | 0, _, _, entries => entries
  | k + 1, decls, bbs, entries =>
    let entries' := stepPtrAliasEntries decls bbs entries
    if entries' == entries then entries
    else iterPtrAliasEntries k decls bbs entries'

/-- Abstract pointer/reference borrow state on entry to block `blk`. Each local's
lattice chain has height at most `n + 4`, so `B * n * (n + 4) + 1` passes suffice
to reach the least fixed point on any CFG. -/
def ptrEnvAtEntry (body : MirAst.CapturedMir) (blk : Nat) : List PtrLocalState :=
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  let fuel := b * n * (n + 4) + 1
  let init := initPtrEntries b n
  (iterPtrAliasEntries fuel body.localDecls body.basicBlocks init).getD blk (initPtrEnv n)

/-- Abstract pointer/reference borrow state immediately before statement `stmt`
of block `blk`. -/
def ptrEnvBefore (body : MirAst.CapturedMir) (blk stmt : Nat) : List PtrLocalState :=
  match body.basicBlocks[blk]? with
  | some bb =>
    (bb.statements.take stmt).foldl (ptrStmtStep body.localDecls) (ptrEnvAtEntry body blk)
  | none => ptrEnvAtEntry body blk

/-- Flow-sensitive CFG borrow and aliasing discipline aligning Anneal's
per-borrow Tree Borrows tags with MiniRust's flat byte-level `BasicMemory`
(where `retag_ptr` is the identity):
1. Every directly borrowed local `k` is a parameter (`1 ≤ k ≤ body.argCount`)
   that is never directly assigned, deinited, storage-cycled, or moved out.
2. Along every CFG path (`blockPtrAliasOk` + `subsumesPtrEnv` across all
   terminator edges), no dereference read, reborrow, or dereference write uses a
   pointer or reference local whose Anneal `BorrowEntry` may have been
   invalidated (`.disabled`) by an overlapping dereference write through a
   distinct tag. -/
def ptrAliasingOk (body : MirAst.CapturedMir) : Bool :=
  let addrLocals := bodyAddrTakenLocals body
  let n := body.localDecls.length
  ptrDeclLayoutsOk body &&
  addrLocals.all (fun k => decide (1 ≤ k ∧ k ≤ body.argCount)) &&
  body.basicBlocks.all (fun bb =>
    bb.statements.all (stmtPreservesAddrTaken addrLocals) &&
    termPreservesAddrTaken addrLocals bb.terminator) &&
  subsumesPtrEnv n (initPtrEnv n) (ptrEnvAtEntry body 0) &&
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      let inEnv := ptrEnvAtEntry body blk
      let exitEnv := bb.statements.foldl (ptrStmtStep body.localDecls) inEnv
      blockPtrAliasOk body.localDecls inEnv bb.statements &&
      (termTargets bb.terminator).all (fun t =>
        subsumesPtrEnv n exitEnv (ptrEnvAtEntry body t))
    | none => true

/-- Well-formedness of a local declaration in the fragment: a scalar-family
type (`scalarTypeOf`), a thin raw pointer or reference to an integer (`isPtrTy`),
a homogeneous 1D integer array whose byte size fits in signed 64-bit `isize`
(`< 2 ^ 63`), or a well-formed tuple / single-variant struct (`TupleSpec.wf`). -/
def localDeclOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (d : MirAst.LocalDecl) : Bool :=
  (scalarTypeOf d.ty).isSome ||
  (isPtrTy d.ty && decide (MirSemantics.layoutPointerBytes layouts = 8)) ||
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
`BM.pickAddr` that the callee's locals can occupy below `2^63`.

Note: `inFragment` checks `statementOk`, which rejects
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))`. The single-body
MR-1.x and MR-4.1 theorems (like `run_ub`) do not model block splitting.
`Assume` is only supported in multi-function proofs (`bodyInProgFragment`),
where `translateFnInProg` explicitly translates `Assume` into a block-splitting
`Terminator::Intrinsic` corresponding to `SegChain` and `SegPc`. -/
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

/-! ## Provenance-Cast In-Fragment Lowering & Block-Splitting Specifications (MR-3.3) -/

/-- Whether a MIR statement is an assignment of a provenance cast
(`CastKind::PointerExposeProvenance` or `CastKind::PointerWithExposedProvenance`). -/
def isProvCastStmt (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign _ (.cast .pointerExposeProvenance _ _) => true
  | .assign _ (.cast .pointerWithExposedProvenance _ _) => true
  | _ => false

/-- Fragment rvalue check for `CastKind::PointerExposeProvenance(op, targetTy)`
(inspected after `copyRv`) assigned to an integer local of type `it`:
`it` and `targetTy` must both be `usize` (`usizeIt`), and `op` must read a
declared thin pointer or reference local `⟨p, []⟩`. -/
def exposeCastOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .cast .pointerExposeProvenance (.copy ⟨p, []⟩) targetTy =>
    decide (it = usizeIt) &&
    decide (intTypeOf targetTy = some usizeIt) &&
    decide (p < decls.length) &&
    (decls[p]? >>= (rawPtrPointeeOf ·.ty)).isSome
  | _ => false

/-- Fragment rvalue check for `CastKind::PointerWithExposedProvenance(op, targetTy)`
(inspected after `copyRv`) assigned to a thin raw pointer local (`isRef = false`)
of mutability `mutbl` and pointee integer type `pointeeIt`:
`targetTy` must be a thin raw pointer of `(mutbl, pointeeIt)` and `op` must be a
valid `usize` operand (`operandOk layouts decls usizeIt op`). -/
def withExposedCastOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
    (isRef : Bool := false) : MirAst.Rvalue → Bool
  | .cast .pointerWithExposedProvenance op targetTy =>
    !isRef &&
    decide (rawPtrPointeeOf targetTy = some (mutbl, pointeeIt)) &&
    operandOk layouts decls usizeIt op
  | _ => false

/-- Well-formedness check for a root provenance-cast statement
`_i = Cast(PointerExposeProvenance, op, usize)` or
`_i = Cast(PointerWithExposedProvenance, op, *const T / *mut T)`. -/
def provCastStmtOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      match intTypeOf d.ty with
      | some it => exposeCastOk decls it (copyRv rv)
      | none =>
        match ptrPointeeOf d.ty with
        | some (mutbl, pointeeIt) =>
          withExposedCastOk layouts decls mutbl pointeeIt (isRefTy d.ty) (copyRv rv)
        | none => false
  | _ => false

/-- Statement check in a multi-function program (`progInFragment`) or
intrinsic-extended body (`statementOkWithIntrinsics`): either a
single-body fragment statement (`statementOk`) or
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` on a well-typed
`bool` fragment operand (`operandOkB decls (copyOp op)`), which `translate_bb`
splits into `Terminator::Intrinsic { intrinsic: IntrinsicOp::Assume, .. }`
jumping to a fresh continuation block (`splitStmts`, `splitBlockAtIntrinsics`). -/
def progStatementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  match s.kind with
  | .intrinsic (.assume op) => operandOkB layouts decls (copyOp op)
  | _ => statementOk decls s layouts

theorem progStatementOk_of_statementOk {decls : List MirAst.LocalDecl}
    {s : MirAst.Statement} {layouts : Layout.LayoutTable}
    (h : statementOk decls s layouts = true) :
    progStatementOk decls s layouts = true := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | intrinsic intr =>
    cases intr <;> simp [statementOk] at h
  | _ => exact h

/-- Statement well-formedness extended with `Assume` and provenance-cast
statements lowered to `Terminator::Intrinsic` blocks by
`translateStmtOrIntrinsic`. -/
def statementOkWithIntrinsics (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  progStatementOk decls s layouts || provCastStmtOk decls s layouts

/-! ### Provenance-cast data-flow and aliasing discipline

Anneal's MIR semantics (`trusted/lean/.../MirSemantics/Places.lean`) models
exposure with canonical addresses: `PointerExposeProvenance` returns the
canonical stack address `ptrAddress?` of the borrowed place (the same for every
tag borrowing that place) and records the tag in `Memory.exposedAllocIds`, and
`PointerWithExposedProvenance` recovers the highest-ranked live exposed stack
borrow covering the address (`recoverExposedPtrValue?`), or a provenance-less
address when none is exposed. MiniRust returns the pointer's address and
resolves the provenance of `int2ptr` angelically among the exposed provenances.
Under these semantics observing an exposed integer (`exposeTwice`: both return
`0`) and forging one (`int2ptrForgedTag`: both raise UB) agree
(`exposeTwice_three_way_agreement`, `int2ptrForgedTag_three_way_ub_agreement`),
but the fragment still admits only the flows whose step correspondence is
proved, i.e. an exposed integer used for nothing but casting it back:

* observing or forging exposed integers stays outside the fragment (the step
  simulation `ProvenanceRel.*_from_frameOk` covers only the
  expose-then-cast-back round trip);
* laundering mutability or pointee type through the integer (`*const u32` →
  `usize` → `*mut u32`) escapes `ptrRvalueOk`'s `PtrToPtr` rule;
* and a round-tripped pointer recovers the exposed pointer's borrow tag in
  Anneal (`AnnealExposeRoundTripOk`), so it must obey the same `ptrAliasingOk`
  borrow discipline.

`provCastFlowOk` and `ptrAliasingOk (provCastAliasView body)` enforce exactly
this. -/

/-- Whether some statement of `body` is a provenance cast. -/
def hasProvCast (body : MirAst.CapturedMir) : Bool :=
  body.basicBlocks.any fun bb => bb.statements.any isProvCastStmt

/-- The *exposed-address locals*: the root destinations of
`PointerExposeProvenance` casts. -/
def exposedIntLocals (body : MirAst.CapturedMir) : List Nat :=
  body.basicBlocks.flatMap fun bb => bb.statements.filterMap fun s =>
    match s.kind with
    | .assign ⟨e, []⟩ (.cast .pointerExposeProvenance _ _) => some e
    | _ => none

/-- `(mutability, pointee)` of the pointer local read by each
`PointerExposeProvenance` cast into local `e` (`none` for an operand that is
not a whole declared pointer local). -/
def exposeSourcesOf (body : MirAst.CapturedMir) (e : Nat) :
    List (Option (MirAst.Mutability × Gen.IntType)) :=
  body.basicBlocks.flatMap fun bb => bb.statements.filterMap fun s =>
    match s.kind with
    | .assign ⟨e', []⟩ (.cast .pointerExposeProvenance op _) =>
      if e' = e then
        some (match copyOp op with
          | .copy ⟨p, []⟩ => body.localDecls[p]? >>= (rawPtrPointeeOf ·.ty)
          | _ => none)
      else none
    | _ => none

/-- The exposed-address local read as a whole (`copy _e` / `move _e`) by a
`PointerWithExposedProvenance` operand. -/
def exposedIntOperand (E : List Nat) : MirAst.Operand → Option Nat
  | .copy ⟨e, []⟩ => if E.contains e then some e else none
  | .move ⟨e, []⟩ => if E.contains e then some e else none
  | _ => none

/-- An exposed source pointer may be reconstructed at `(mutbl, pointeeIt)`:
same pointee, and no `*const`/`&` to `*mut` upgrade (`ptrRvalueOk`'s
`PtrToPtr` rule). -/
def exposeSourceCompatible (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType) :
    Option (MirAst.Mutability × Gen.IntType) → Bool
  | some (srcMutbl, srcIt) =>
    decide (srcIt = pointeeIt) && (decide (srcMutbl = .mut) || decide (mutbl = .not))
  | none => false

/-- Per-statement data flow of exposed-address locals `E`: they are written
only by `PointerExposeProvenance`, read only (whole) by
`PointerWithExposedProvenance` at a compatible pointer type, and otherwise only
storage-cycled; no other statement mentions them. -/
def provCastStmtFlowOk (body : MirAst.CapturedMir) (E : List Nat) (s : MirAst.Statement) :
    Bool :=
  if isProvCastStmt s then
    match s.kind with
    | .assign ⟨_, []⟩ (.cast .pointerExposeProvenance op _) =>
      (opLocals op).all (fun j => !E.contains j)
    | .assign ⟨q, []⟩ (.cast .pointerWithExposedProvenance op targetTy) =>
      !E.contains q &&
      match exposedIntOperand E op, rawPtrPointeeOf targetTy with
      | some e, some (mutbl, pointeeIt) =>
        (exposeSourcesOf body e).all (exposeSourceCompatible mutbl pointeeIt)
      | _, _ => false
    | _ => false
  else
    match s.kind with
    | .storageLive _ | .storageDead _ => true
    | _ => (stmtLocals s).all (fun j => !E.contains j)

/-- Data-flow discipline for provenance casts: exposed-address locals are
temporaries (never `_0` or an argument, so they are neither returned nor
supplied by the caller), never observed (no arithmetic, comparison, cast,
branch, or borrow), and every `PointerWithExposedProvenance` operand is one of
them (no forged integers). Vacuous for bodies without provenance casts. -/
def provCastFlowOk (body : MirAst.CapturedMir) : Bool :=
  !hasProvCast body ||
  (let E := exposedIntLocals body
   E.all (fun e => decide (body.argCount < e)) &&
   body.basicBlocks.all (fun bb =>
     bb.statements.all (provCastStmtFlowOk body E) &&
     (termLocals bb.terminator).all (fun j => !E.contains j)))

/-- Thin raw pointer type standing in for exposed-address locals in
`provCastAliasView`. -/
def provCastAliasTy : MirAst.Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

/-- A provenance cast seen by the alias analysis as the tag-preserving pointer
copy it is in Anneal (`_e = copy _p`, `_q = copy _e`). -/
def provCastAliasStmt (s : MirAst.Statement) : MirAst.Statement :=
  match s.kind with
  | .assign dst (.cast .pointerExposeProvenance op _) => { s with kind := .assign dst (.use op) }
  | .assign dst (.cast .pointerWithExposedProvenance op _) => { s with kind := .assign dst (.use op) }
  | _ => s

/-- The body as `ptrAliasingOk` must see it: exposed-address locals become
pointer locals and provenance casts become pointer copies, so a reconstructed
pointer shares the borrow tag (and `PtrLocalState`) of the exposed one, exactly
as Anneal's `recoverExposedPtrValue?` recovers the exposed tag from its
canonical address (`AnnealExposeRoundTripOk`). The identity on bodies without
provenance casts. -/
def provCastAliasView (body : MirAst.CapturedMir) : MirAst.CapturedMir :=
  if hasProvCast body then
    let E := exposedIntLocals body
    { body with
      localDecls := body.localDecls.zipIdx.map (fun (d, i) =>
        if E.contains i then { d with ty := provCastAliasTy } else d)
      basicBlocks := body.basicBlocks.map (fun bb =>
        { bb with statements := bb.statements.map provCastAliasStmt }) }
  else body

/-- Decidable fragment extended with `CastKind::PointerExposeProvenance` and
`CastKind::PointerWithExposedProvenance` statements lowered via
`translateFnWithIntrinsics`, under the provenance-cast data-flow discipline
`provCastFlowOk` and the borrow discipline `ptrAliasingOk` of
`provCastAliasView` (which `inFragment` imposes through `ptrAliasingOk`). -/
def inFragmentWithIntrinsics (body : MirAst.CapturedMir) : Bool :=
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
    bb.statements.all (statementOkWithIntrinsics body.localDecls · body.layouts) &&
    terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  provCastFlowOk body && ptrDeclLayoutsOk body && ptrAliasingOk (provCastAliasView body) &&
  (translateFnWithIntrinsics body).isSome

theorem ptrDeclLayoutsOk_of_inFragmentWithIntrinsics {body : MirAst.CapturedMir}
    (h : inFragmentWithIntrinsics body = true) :
    ptrDeclLayoutsOk body = true := by
  simp only [inFragmentWithIntrinsics, Bool.and_eq_true] at h
  exact h.1.1.2

/-- Number of `.intrinsic` entries in a `StmtTranslation` list. -/
def countIntrinsics : List StmtTranslation → Nat
  | [] => 0
  | .stmt _ :: rest => countIntrinsics rest
  | .intrinsic _ _ _ :: rest => 1 + countIntrinsics rest

theorem translateStmtOrIntrinsic_assume (decls : List MirAst.LocalDecl)
    (op : MirAst.Operand) (span : String) (layouts : Layout.LayoutTable) :
    translateStmtOrIntrinsic decls ⟨.intrinsic (.assume op), span⟩ layouts =
      (do
        let operand ← translateOperand decls op
        pure (.intrinsic .Assume unitPlace [operand])) :=
  rfl

theorem translateStmtOrIntrinsic_expose (decls : List MirAst.LocalDecl)
    (dst : MirAst.Place) (op : MirAst.Operand) (ty : MirAst.Ty) (span : String)
    (layouts : Layout.LayoutTable) :
    translateStmtOrIntrinsic decls ⟨.assign dst (.cast .pointerExposeProvenance op ty), span⟩ layouts =
      (do
        let destination ← translatePlace decls dst
        let operand ← translateOperand decls op
        pure (.intrinsic .PointerExposeProvenance destination [operand])) :=
  rfl

theorem translateStmtOrIntrinsic_withExposed (decls : List MirAst.LocalDecl)
    (dst : MirAst.Place) (op : MirAst.Operand) (ty : MirAst.Ty) (span : String)
    (layouts : Layout.LayoutTable) :
    translateStmtOrIntrinsic decls ⟨.assign dst (.cast .pointerWithExposedProvenance op ty), span⟩ layouts =
      (do
        let destination ← translatePlace decls dst
        let operand ← translateOperand decls op
        pure (.intrinsic .PointerWithExposedProvenance destination [operand])) :=
  rfl

theorem translateStmtOrIntrinsic_of_not_provCast (decls : List MirAst.LocalDecl)
    (s : MirAst.Statement) (layouts : Layout.LayoutTable)
    (hnp : isProvCastStmt s = false) (hna : isAssume s = false) :
    translateStmtOrIntrinsic decls s layouts = (translateStatement decls s layouts).map .stmt := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck <;> first | rfl | simp [isProvCastStmt] at hnp
    | _ => rfl
  | intrinsic intr =>
    cases intr with
    | assume _ => simp [isAssume] at hna
    | _ => rfl
  | _ => rfl

theorem translateStmtOrIntrinsic_of_translateStatement (decls : List MirAst.LocalDecl)
    (s : MirAst.Statement) (layouts : Layout.LayoutTable) (st' : Gen.Statement)
    (h : translateStatement decls s layouts = some st') :
    translateStmtOrIntrinsic decls s layouts = some (.stmt st') := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck with
      | pointerExposeProvenance =>
        simp [translateStatement, translateRvalue, copyRv] at h
      | pointerWithExposedProvenance =>
        simp [translateStatement, translateRvalue, copyRv] at h
      | _ => simp [translateStmtOrIntrinsic, h]
    | _ => simp [translateStmtOrIntrinsic, h]
  | intrinsic intr =>
    cases intr with
    | assume _ => simp [translateStatement] at h
    | _ => simp [translateStmtOrIntrinsic, h]
  | _ => simp [translateStmtOrIntrinsic, h]

theorem provCastStmtOk_some (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable) (h : provCastStmtOk decls s layouts = true) :
    ∃ op dst args, translateStmtOrIntrinsic decls s layouts = some (.intrinsic op dst args) := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    rcases dst with ⟨i, projs⟩
    cases projs with
    | cons _ _ => simp [provCastStmtOk] at h
    | nil =>
      simp only [provCastStmtOk] at h
      cases hd : decls[i]? with
      | none => simp [hd] at h
      | some d =>
        simp only [hd] at h
        cases hit : intTypeOf d.ty with
        | some it =>
          simp only [hit] at h
          cases rv with
          | cast ck op targetTy =>
            cases ck with
            | pointerExposeProvenance =>
              cases op with
              | copy pl =>
                rcases pl with ⟨p, pprojs⟩
                cases pprojs with
                | nil =>
                  exact ⟨.PointerExposeProvenance, .Local (localName i), [.Load (.Local (localName p))], rfl⟩
                | cons _ _ => simp [copyRv, copyOp, exposeCastOk] at h
              | move pl =>
                rcases pl with ⟨p, pprojs⟩
                cases pprojs with
                | nil =>
                  exact ⟨.PointerExposeProvenance, .Local (localName i), [.Load (.Local (localName p))], rfl⟩
                | cons _ _ => simp [copyRv, copyOp, exposeCastOk] at h
              | constant _ => simp [copyRv, copyOp, exposeCastOk] at h
            | _ => simp [copyRv, exposeCastOk] at h
          | _ => simp [copyRv, exposeCastOk] at h
        | none =>
          simp only [hit] at h
          cases hpt : ptrPointeeOf d.ty with
          | none => simp [hpt] at h
          | some pr =>
            obtain ⟨mutbl, pointeeIt⟩ := pr
            simp only [hpt] at h
            cases rv with
            | cast ck op targetTy =>
              cases ck with
              | pointerWithExposedProvenance =>
                simp only [copyRv, withExposedCastOk, Bool.and_eq_true] at h
                obtain ⟨_, hop⟩ := h
                have hsome : (translateOperand decls op).isSome = true := by
                  cases op with
                  | copy p =>
                    simp only [copyOp, operandOk, Bool.and_eq_true] at hop
                    exact hop.2
                  | move p =>
                    simp only [copyOp, operandOk, Bool.and_eq_true] at hop
                    simpa [translateOperand] using hop.2
                  | constant c =>
                    simp only [copyOp, operandOk, Bool.and_eq_true] at hop
                    exact hop.2
                obtain ⟨ve, hve⟩ := Option.isSome_iff_exists.mp hsome
                refine ⟨.PointerWithExposedProvenance, .Local (localName i), [ve], ?_⟩
                simp [translateStmtOrIntrinsic, translatePlace, hve]
              | _ => simp [copyRv, withExposedCastOk] at h
            | _ => simp [copyRv, withExposedCastOk] at h
  | _ => simp [provCastStmtOk] at h

theorem splitBlockAtIntrinsics_no_intrinsics (curName : Gen.BbName)
    (accStmts : List Gen.Statement) (finalTerm : Gen.Terminator) (kind : Gen.BbKind)
    (nextFresh : Nat) (stmts : List Gen.Statement) :
    splitBlockAtIntrinsics curName accStmts finalTerm kind nextFresh (stmts.map .stmt) =
      ([(curName, ⟨accStmts ++ stmts, finalTerm, kind⟩)], nextFresh) := by
  induction stmts generalizing accStmts with
  | nil => simp [splitBlockAtIntrinsics]
  | cons st rest ih =>
    simp only [List.map_cons, splitBlockAtIntrinsics, ih, List.append_assoc, List.singleton_append]

theorem splitBlockAtIntrinsics_fresh_eq (curName : Gen.BbName)
    (accStmts : List Gen.Statement) (finalTerm : Gen.Terminator) (kind : Gen.BbKind)
    (nextFresh : Nat) (trs : List StmtTranslation) :
    (splitBlockAtIntrinsics curName accStmts finalTerm kind nextFresh trs).2 =
      nextFresh + countIntrinsics trs := by
  induction trs generalizing curName accStmts nextFresh with
  | nil => simp [splitBlockAtIntrinsics, countIntrinsics]
  | cons tr rest ih =>
    cases tr with
    | stmt st =>
      simp only [splitBlockAtIntrinsics, countIntrinsics]
      exact ih curName (accStmts ++ [st]) nextFresh
    | intrinsic op dst args =>
      simp only [splitBlockAtIntrinsics, countIntrinsics]
      rw [ih (bbName nextFresh) [] (nextFresh + 1)]
      omega

theorem splitBlockAtIntrinsics_length (curName : Gen.BbName)
    (accStmts : List Gen.Statement) (finalTerm : Gen.Terminator) (kind : Gen.BbKind)
    (nextFresh : Nat) (trs : List StmtTranslation) :
    (splitBlockAtIntrinsics curName accStmts finalTerm kind nextFresh trs).1.length =
      1 + countIntrinsics trs := by
  induction trs generalizing curName accStmts nextFresh with
  | nil => simp [splitBlockAtIntrinsics, countIntrinsics]
  | cons tr rest ih =>
    cases tr with
    | stmt st =>
      simp only [splitBlockAtIntrinsics, countIntrinsics]
      exact ih curName (accStmts ++ [st]) nextFresh
    | intrinsic op dst args =>
      simp only [splitBlockAtIntrinsics, countIntrinsics, List.length_cons]
      rw [ih (bbName nextFresh) [] (nextFresh + 1)]
      omega

theorem splitBlockAtIntrinsics_single_intrinsic (curName : Gen.BbName)
    (accStmts pre post : List Gen.Statement) (op : Gen.IntrinsicOp) (dst : Gen.PlaceExpr)
    (args : List Gen.ValueExpr) (finalTerm : Gen.Terminator) (kind : Gen.BbKind)
    (nextFresh : Nat) :
    splitBlockAtIntrinsics curName accStmts finalTerm kind nextFresh
        (pre.map .stmt ++ [.intrinsic op dst args] ++ post.map .stmt) =
      ([(curName, ⟨accStmts ++ pre, .Intrinsic op args dst (some (bbName nextFresh)), kind⟩),
        (bbName nextFresh, ⟨post, finalTerm, kind⟩)], nextFresh + 1) := by
  induction pre generalizing accStmts with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.singleton_append, splitBlockAtIntrinsics,
      List.append_nil, splitBlockAtIntrinsics_no_intrinsics]
  | cons st rest ih =>
    simp only [List.map_cons, List.cons_append, splitBlockAtIntrinsics]
    rw [ih (accStmts ++ [st])]
    simp [List.append_assoc]

theorem mapM_translateStmtOrIntrinsic_of_translateStatements (decls : List MirAst.LocalDecl)
    (layouts : Layout.LayoutTable) :
    ∀ (ss : List MirAst.Statement) (stmts : List Gen.Statement),
      ss.mapM (translateStatement decls · layouts) = some stmts →
      ss.mapM (translateStmtOrIntrinsic decls · layouts) = some (stmts.map .stmt)
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | s :: ss, _, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hs : translateStatement decls s layouts with
    | none => simp [hs] at h
    | some st' =>
      simp only [hs, Option.bind_some] at h
      cases hss : ss.mapM (translateStatement decls · layouts) with
      | none => simp [hss] at h
      | some rest' =>
        simp only [hss, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have h1 := translateStmtOrIntrinsic_of_translateStatement decls s layouts st' hs
        have h2 := mapM_translateStmtOrIntrinsic_of_translateStatements decls layouts ss rest' hss
        simp [List.mapM_cons, h1, h2]

theorem translateBlocksWithIntrinsics_of_translateBlocks (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) :
    ∀ (i nextFresh : Nat) (bbs : List MirAst.BasicBlockData)
      (blks : List (Gen.BbName × Gen.BasicBlock)),
      (∀ bb ∈ bbs, bb.isCleanup = false) →
      translateBlocks layouts decls i bbs = some blks →
      translateBlocksWithIntrinsics layouts decls i nextFresh bbs = some (blks, nextFresh)
  | _, nextFresh, [], _, _, h => by
    simp only [translateBlocks, Option.some.injEq] at h
    subst h
    rfl
  | i, nextFresh, bb :: bbs, _, hclean, h => by
    simp only [translateBlocks, translateBlock, Option.bind_eq_bind] at h
    have hbb_clean : bb.isCleanup = false := hclean bb (List.mem_cons_self ..)
    cases hss : bb.statements.mapM (translateStatement decls · layouts) with
    | none => simp [hss] at h
    | some stmts =>
      simp only [hss, Option.bind_some] at h
      cases hterm : translateTerminator layouts decls bb.terminator with
      | none => simp [hterm] at h
      | some term =>
        simp only [hterm, Option.bind_some, Option.pure_def] at h
        cases hrest : translateBlocks layouts decls (i + 1) bbs with
        | none => simp [hrest] at h
        | some restBlks =>
          simp only [hrest, Option.bind_some, Option.some.injEq] at h
          subst h
          have hm := mapM_translateStmtOrIntrinsic_of_translateStatements decls layouts
            bb.statements stmts hss
          have ih := translateBlocksWithIntrinsics_of_translateBlocks layouts decls
            (i + 1) nextFresh bbs restBlks
            (fun b hb => hclean b (List.mem_cons_of_mem bb hb)) hrest
          simp [translateBlocksWithIntrinsics, hm, hterm, hbb_clean,
            splitBlockAtIntrinsics_no_intrinsics, ih]

/-- Every non-cleanup function that `translateFn` translates (with no
block-splitting intrinsics) is translated identically by `translateFnWithIntrinsics`. -/
theorem translateFnWithIntrinsics_of_translateFn {body : MirAst.CapturedMir} {f : Gen.Function}
    (hclean : ∀ bb ∈ body.basicBlocks, bb.isCleanup = false)
    (h : translateFn body = some f) :
    translateFnWithIntrinsics body = some f := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hloc : translateLocals body.layouts 0 body.localDecls with
  | none => simp [hloc] at h
  | some locals =>
    simp only [hloc, Option.bind_some] at h
    cases hblks : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
    | none => simp [hblks] at h
    | some blocks =>
      simp only [hblks, Option.bind_some] at h
      cases hconv : translateCallConv body.fnAbi.conv with
      | none => simp [hconv] at h
      | some conv =>
        simp only [hconv, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have hbi := translateBlocksWithIntrinsics_of_translateBlocks body.layouts body.localDecls
          0 body.basicBlocks.length body.basicBlocks blocks hclean hblks
        simp [translateFnWithIntrinsics, hconv, hloc, hbi]

/-- `translateStatement` rejects provenance casts. -/
theorem translateStatement_not_provCast {decls : List MirAst.LocalDecl} {s : MirAst.Statement}
    {layouts : Layout.LayoutTable} {st : Gen.Statement}
    (h : translateStatement decls s layouts = some st) : isProvCastStmt s = false := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck with
      | pointerExposeProvenance => simp [translateStatement, translateRvalue, copyRv] at h
      | pointerWithExposedProvenance => simp [translateStatement, translateRvalue, copyRv] at h
      | _ => simp [isProvCastStmt]
    | _ => simp [isProvCastStmt]
  | _ => simp [isProvCastStmt]

theorem mapM_translateStatement_not_provCast {decls : List MirAst.LocalDecl}
    {layouts : Layout.LayoutTable} :
    ∀ (ss : List MirAst.Statement) (stmts : List Gen.Statement),
      ss.mapM (translateStatement decls · layouts) = some stmts →
      ∀ s ∈ ss, isProvCastStmt s = false
  | [], _, _, s, hs => by cases hs
  | s0 :: ss, _, h, s, hs => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h0 : translateStatement decls s0 layouts with
    | none => simp [h0] at h
    | some st0 =>
      simp only [h0, Option.bind_some] at h
      cases hss : ss.mapM (translateStatement decls · layouts) with
      | none => simp [hss] at h
      | some rest =>
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact translateStatement_not_provCast h0
        · exact mapM_translateStatement_not_provCast ss rest hss s hs'

theorem translateBlocks_not_provCast {layouts : Layout.LayoutTable}
    {decls : List MirAst.LocalDecl} :
    ∀ (i : Nat) (bbs : List MirAst.BasicBlockData) (blks : List (Gen.BbName × Gen.BasicBlock)),
      translateBlocks layouts decls i bbs = some blks →
      ∀ bb ∈ bbs, ∀ s ∈ bb.statements, isProvCastStmt s = false
  | _, [], _, _, bb, hbb => by cases hbb
  | i, bb0 :: bbs, _, h, bb, hbb => by
    simp only [translateBlocks, translateBlock, Option.bind_eq_bind] at h
    cases hss : bb0.statements.mapM (translateStatement decls · layouts) with
    | none => simp [hss] at h
    | some stmts =>
      simp only [hss, Option.bind_some] at h
      cases hterm : translateTerminator layouts decls bb0.terminator with
      | none => simp [hterm] at h
      | some term =>
        simp only [hterm, Option.bind_some, Option.pure_def] at h
        cases hrest : translateBlocks layouts decls (i + 1) bbs with
        | none => simp [hrest] at h
        | some restBlks =>
          rcases List.mem_cons.mp hbb with rfl | hbb'
          · exact mapM_translateStatement_not_provCast _ stmts hss
          · exact translateBlocks_not_provCast (i + 1) bbs restBlks hrest bb hbb'

/-- Every body that `translateFn` translates is free of provenance casts. -/
theorem translateFn_not_hasProvCast {body : MirAst.CapturedMir} {f : Gen.Function}
    (h : translateFn body = some f) : hasProvCast body = false := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hloc : translateLocals body.layouts 0 body.localDecls with
  | none => simp [hloc] at h
  | some locals =>
    simp only [hloc, Option.bind_some] at h
    cases hblks : translateBlocks body.layouts body.localDecls 0 body.basicBlocks with
    | none => simp [hblks] at h
    | some blocks =>
      have hno := translateBlocks_not_provCast 0 body.basicBlocks blocks hblks
      unfold hasProvCast
      rw [List.any_eq_false]
      intro bb hbb hany
      rw [List.any_eq_true] at hany
      obtain ⟨s, hs, hp⟩ := hany
      rw [hno bb hbb s hs] at hp
      cases hp

/-- `inFragment` bodies contain no provenance cast. In particular every lemma
whose hypotheses include `inFragment body = true` (such as
`StateRelNProv.exposed_target_localPtr`) is about bodies that never expose a
provenance. -/
theorem inFragment_not_hasProvCast {body : MirAst.CapturedMir} (h : inFragment body = true) :
    hasProvCast body = false := by
  simp only [inFragment, Bool.and_eq_true] at h
  obtain ⟨_, h14⟩ := h
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h14
  exact translateFn_not_hasProvCast hf

theorem provCastFlowOk_of_not_hasProvCast {body : MirAst.CapturedMir}
    (h : hasProvCast body = false) : provCastFlowOk body = true := by
  simp [provCastFlowOk, h]

theorem provCastAliasView_of_not_hasProvCast {body : MirAst.CapturedMir}
    (h : hasProvCast body = false) : provCastAliasView body = body := by
  simp [provCastAliasView, h]

/-- Number of `PointerExposeProvenance` statements across all blocks of `body`. -/
def countExposeStmts (body : MirAst.CapturedMir) : Nat :=
  (exposedIntLocals body).length

/-- Whether every control-flow edge in `body` goes strictly forward
(`blk < t`), ruling out CFG cycles/loops. In a cyclic CFG, even a single
syntactic `PointerExposeProvenance` statement (`countExposeStmts body = 1`)
inside a loop body can execute across multiple iterations on fresh reborrows
`&mut _x` and accumulate multiple distinct `TreeBorrowsProvenance` tags
`(AllocId, path)` on the same allocation in `MachTB`. -/
def isAcyclicCfg (body : MirAst.CapturedMir) : Bool :=
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb => (termTargets bb.terminator).all (fun t => decide (blk < t))
    | none => true

/-- Sufficient syntactic condition guaranteeing at most one dynamic
`PointerExposeProvenance` execution in `body`: at most one syntactic
`PointerExposeProvenance` statement (`countExposeStmts body ≤ 1`) and an
acyclic CFG (`isAcyclicCfg body`), so executions in `TreeBorrowsMemory` cannot
accumulate two distinct exposed `TreeBorrowsProvenance` tags `(AllocId, path)`
on the same allocation (neither via multiple statements as in
`exposeTwoRefMutAngelicUnsupported` nor via a loop around a single statement). -/
def singleExposeSiteOk (body : MirAst.CapturedMir) : Bool :=
  !hasProvCast body || (decide (countExposeStmts body ≤ 1) && isAcyclicCfg body)

theorem singleExposeSiteOk_of_not_hasProvCast {body : MirAst.CapturedMir}
    (h : hasProvCast body = false) : singleExposeSiteOk body = true := by
  simp [singleExposeSiteOk, h]

theorem singleExposeSiteOk_imp_acyclic {body : MirAst.CapturedMir}
    (hs : singleExposeSiteOk body = true) (hp : hasProvCast body = true) :
    countExposeStmts body ≤ 1 ∧ isAcyclicCfg body = true := by
  simp [singleExposeSiteOk, hp] at hs
  exact hs

/-- `inFragment` embeds into `inFragmentWithIntrinsics`. -/
theorem inFragment_implies_inFragmentWithIntrinsics {body : MirAst.CapturedMir}
    (h : inFragment body = true) :
    inFragmentWithIntrinsics body = true := by
  have hnp := inFragment_not_hasProvCast h
  simp only [inFragment, inFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h14
  have hclean : ∀ bb ∈ body.basicBlocks, bb.isCleanup = false := by
    intro bb hbb
    simpa using (h9 bb hbb).1.1
  have hdlo : ptrDeclLayoutsOk body = true := by
    simp only [ptrAliasingOk, Bool.and_eq_true] at h13
    exact h13.1.1.1.1
  have hfi := translateFnWithIntrinsics_of_translateFn hclean hf
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, ?_⟩, h10⟩, h11⟩, h12⟩,
    provCastFlowOk_of_not_hasProvCast hnp⟩, hdlo⟩,
    by rw [provCastAliasView_of_not_hasProvCast hnp]; exact h13⟩, by simp [hfi]⟩
  intro bb hbb
  obtain ⟨⟨hc, hst⟩, htm⟩ := h9 bb hbb
  exact ⟨⟨hc, fun s hs => by simp [statementOkWithIntrinsics, progStatementOk_of_statementOk (hst s hs)]⟩, htm⟩
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
  | .intrinsic (.assume op) => dropMovedFrom ti [op]
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
def callArgOk (layouts : Layout.LayoutTable) (decls : List MirAst.LocalDecl)
    (paramDecl : MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  let shapeOk :=
    match op with
    | .move ⟨_, []⟩ => true
    | .move _ => false
    | _ => true
  shapeOk &&
  if isBoolTy paramDecl.ty then operandOkB layouts decls (copyOp op)
  else if isOrderingTy paramDecl.ty then operandOkO decls (copyOp op)
  else
    match intBoolTupleOf paramDecl.ty with
    | some it => operandOkTuple decls it (copyOp op)
    | none =>
      match intTypeOf paramDecl.ty with
      | some it => operandOk layouts decls it (copyOp op)
      | none => false

/-- Check every call argument against the callee's parameter declarations
`_1 .. _argCount`. -/
def callArgsOk (layouts : Layout.LayoutTable) (decls : List MirAst.LocalDecl) :
    List MirAst.LocalDecl → List MirAst.Operand → Bool
  | [], [] => true
  | pd :: pds, op :: ops => callArgOk layouts decls pd op && callArgsOk layouts decls pds ops
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

/-- The callee of a direct fragment call `func` to `defPath` in `callees`,
provided the call is monomorphic: the function item carries no generic
arguments (`MirSemantics.extractCalleeTypeArgs func = []`) and the callee body
declares no generic type parameters (`typeParamCount = 0`).

Anneal resolves a call through `MirSemantics.lookupCallee`, which instantiates
a polymorphic callee body with the call's type arguments
(`CapturedMir.instantiate`, Option 1B polymorphism) and does not find a
type-parametric callee for an argument-free call at all (falling back to an
external call). MiniRust and `minimize` only ever see fully monomorphized
function instances, so every polymorphic call fails closed (`none`) and stays
outside the fragment; on monomorphic calls `lookupCallee` coincides with
`findCallee?` (`lookupCallee_of_monoCallee?`). -/
def monoCallee? (callees : List MirAst.CapturedMir) (func : MirAst.Operand)
    (defPath : String) : Option MirAst.CapturedMir :=
  match MirSemantics.extractCalleeTypeArgs func with
  | [] =>
    match MirSemantics.findCallee? callees defPath with
    | some callee => if callee.typeParamCount = 0 then some callee else none
    | none => none
  | _ :: _ => none

theorem monoCallee?_eq_some_iff {callees : List MirAst.CapturedMir} {func : MirAst.Operand}
    {defPath : String} {callee : MirAst.CapturedMir} :
    monoCallee? callees func defPath = some callee ↔
      MirSemantics.findCallee? callees defPath = some callee ∧
      callee.typeParamCount = 0 ∧ MirSemantics.extractCalleeTypeArgs func = [] := by
  unfold monoCallee?
  cases htys : MirSemantics.extractCalleeTypeArgs func with
  | cons _ _ => simp
  | nil =>
    cases hfc : MirSemantics.findCallee? callees defPath with
    | none => simp
    | some c =>
      by_cases hz : c.typeParamCount = 0
      · simp only [hz, ↓reduceIte]
        constructor
        · intro h; exact ⟨h, by cases h; exact hz, trivial⟩
        · intro h; exact h.1
      · simp only [hz, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨h, h2, _⟩
        cases h
        exact hz h2

/-- Polymorphic direct calls (`RigidTy.fnDef dp tys` with `tys ≠ []`) fail closed. -/
theorem monoCallee?_eq_none_of_typeArgs {callees : List MirAst.CapturedMir}
    {func : MirAst.Operand} {defPath : String} {t : MirAst.RigidTy} {ts : List MirAst.RigidTy}
    (h : MirSemantics.extractCalleeTypeArgs func = t :: ts) :
    monoCallee? callees func defPath = none := by
  simp [monoCallee?, h]

/-- Calls to a type-parametric callee body (`typeParamCount ≠ 0`) fail closed. -/
theorem monoCallee?_eq_none_of_typeParamCount {callees : List MirAst.CapturedMir}
    {func : MirAst.Operand} {defPath : String} {callee : MirAst.CapturedMir}
    (hfc : MirSemantics.findCallee? callees defPath = some callee)
    (hz : callee.typeParamCount ≠ 0) :
    monoCallee? callees func defPath = none := by
  unfold monoCallee?
  cases MirSemantics.extractCalleeTypeArgs func <;> simp [hfc, hz]

/-- On a monomorphic call, Anneal's `lookupCallee` (with any trait-implementation
table and caller layouts) resolves exactly the body that `monoCallee?` returns. -/
theorem lookupCallee_of_monoCallee? {callees : List MirAst.CapturedMir}
    {func : MirAst.Operand} {defPath : String} {callee : MirAst.CapturedMir}
    (h : monoCallee? callees func defPath = some callee)
    (callerLayouts : Layout.LayoutTable) (traitImpls : List MirAst.TraitImplEntry) :
    MirSemantics.lookupCallee callees callerLayouts defPath
        (MirSemantics.extractCalleeTypeArgs func) traitImpls = some callee := by
  obtain ⟨hfc, hz, htys⟩ := monoCallee?_eq_some_iff.mp h
  rw [htys]
  simp [MirSemantics.lookupCallee, MirSemantics.resolveCalleeBodyAndArgs?, hfc, hz]

/-- Whether a `TerminatorKind.call` at the end of block `blk` in `body` is in
the multi-function fragment relative to `callees`. -/
def callTerminatorOk (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir)
    (blk : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind, body.basicBlocks[blk]? with
  | .call func argOps destination (some targetBb) unwind, some bb =>
    match extractFnDefPath func with
    | none => false
    | some defPath =>
      match translateIntrinsicOrNone body.localDecls defPath argOps destination (some targetBb) with
      | some _ => false
      | none =>
        match monoCallee? callees func defPath with
      | none => false
      | some callee =>
        match callee.localDecls with
        | [] => false
        | retDecl :: restDecls =>
          let lv := mustLiveBefore body blk bb.statements.length
          let ti := tupleInitBefore body blk bb.statements.length
          decide (targetBb < body.basicBlocks.length) &&
          callUnwindOk unwind &&
          (translateCallConv callee.fnAbi.conv).isSome &&
          decide (argOps.length = callee.argCount) &&
          decide (callee.argCount ≤ restDecls.length) &&
          callArgsOk body.layouts body.localDecls (restDecls.take callee.argCount) argOps &&
          callDestOk body.localDecls lv ti retDecl destination &&
          argOps.all (fun op => opRead op != some destination.local_)
  | _, _ => false

/-- Block terminator check in a multi-function program: either a single-body
fragment terminator (`terminatorOk`) or a fragment direct call
(`callTerminatorOk`). -/
def terminatorInProgOk (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir)
    (blk : Nat) (t : MirAst.Terminator) : Bool :=
  terminatorOk body.layouts body.localDecls body.basicBlocks.length t ||
  callTerminatorOk callees body blk t

/-- Per-function fragment check within a multi-function program
`(fnMap, callees)`. Statements satisfy `progStatementOk` (admitting
`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` alongside
`statementOk`), and `translateFnInProg` splits each MIR basic block at every
`Assume` statement (`SegChain`, `SegPc`) exactly like `minimize`. -/
def bodyInProgFragment (fnMap : FnMap)
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
      bb.statements.all (progStatementOk body.localDecls · body.layouts) &&
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

/-! ### Unified multi-function program translation and fragment check with intrinsics (MR-4.3 Pass B3) -/

/-- Convert `StmtTranslation` (`translateStmtOrIntrinsic`) to `StatementResult`
(`splitStmts`). -/
def StmtTranslation.toStatementResult : StmtTranslation → StatementResult
  | .stmt s => .statement s
  | .intrinsic op dst args => .intrinsic op dst args

/-- Statement translation for multi-function programs with intrinsics
(`Assume`, `PointerExposeProvenance`, `PointerWithExposedProvenance`). -/
def translateStmtResultWithIntrinsics (decls : List MirAst.LocalDecl) (s : MirAst.Statement)
    (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Option StatementResult :=
  (translateStmtOrIntrinsic decls s layouts).map StmtTranslation.toStatementResult

theorem translateStmtResultWithIntrinsics_eq_of_not_provCast (decls : List MirAst.LocalDecl)
    (s : MirAst.Statement) (layouts : Layout.LayoutTable)
    (hnp : isProvCastStmt s = false) :
    translateStmtResultWithIntrinsics decls s layouts =
      translateStmtResult decls s layouts := by
  by_cases ha : isAssume s = true
  · obtain ⟨kind, span⟩ := s
    cases kind with
    | intrinsic intr =>
      cases intr with
      | assume op =>
        simp only [translateStmtResultWithIntrinsics, translateStmtResult, translateStmtOrIntrinsic]
        cases translateOperand decls op <;> rfl
      | _ => simp [isAssume] at ha
    | _ => simp [isAssume] at ha
  · have hna : isAssume s = false := Bool.eq_false_iff.mpr ha
    have htr := translateStmtOrIntrinsic_of_not_provCast decls s layouts hnp hna
    obtain ⟨kind, span⟩ := s
    cases kind with
    | intrinsic intr =>
      cases intr with
      | assume _ => simp [isAssume] at hna
      | _ =>
        simp only [translateStmtResultWithIntrinsics, translateStmtResult, htr, Option.map_map]
        rfl
    | _ =>
      simp only [translateStmtResultWithIntrinsics, translateStmtResult, htr, Option.map_map]
      rfl

theorem translateStmtResult_not_provCast {decls : List MirAst.LocalDecl}
    {s : MirAst.Statement} {layouts : Layout.LayoutTable} {res : StatementResult}
    (h : translateStmtResult decls s layouts = some res) :
    isProvCastStmt s = false := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    simp only [translateStmtResult, Option.map_eq_some_iff] at h
    obtain ⟨st, hst, _⟩ := h
    exact translateStatement_not_provCast hst
  | _ => simp [isProvCastStmt]

/-- Multi-function basic-block translation extended with block-splitting
lowering of `Assume`, `PointerExposeProvenance`, and
`PointerWithExposedProvenance` alongside `Call` terminators. -/
def translateBlocksInProgWithIntrinsics (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) :
    Nat → Nat → List MirAst.BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock))
  | _, _, [] => some ([], [])
  | i, nextCleanup, bb :: bbs => do
    let results ← bb.statements.mapM (translateStmtResultWithIntrinsics decls · layouts)
    let sp := splitStmts (bbName i) [] nextCleanup results
    let (term, nextCleanup', extra1) ←
      translateTerminatorInProg fnMap layouts decls sp.2.2.2 bb.terminator
    let (rest, extraRest) ←
      translateBlocksInProgWithIntrinsics fnMap layouts decls (i + 1) nextCleanup' bbs
    pure (sp.2.2.1 ++ [(sp.1, ⟨sp.2.1, term, .Regular⟩)] ++ rest, extra1 ++ extraRest)

/-- `FnCtxt::translate` for a function in a multi-function program with
`Assume`, `PointerExposeProvenance`, and `PointerWithExposedProvenance`
intrinsics (`translateBlocksInProgWithIntrinsics`). -/
def translateFnInProgWithIntrinsics (fnMap : FnMap)
    (body : MirAst.CapturedMir) : Option Gen.Function := do
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, extra) ←
    translateBlocksInProgWithIntrinsics fnMap body.layouts body.localDecls 0 (n + 1) body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
    blocks := ⟨blocks ++ [(bbName n, initBlock body)] ++ extra⟩
    start := bbName n
    implicit_writes := true
  }

/-- Translate `(entry :: callees)` in index order using
`translateFnInProgWithIntrinsics`. -/
def translateProgFnsWithIntrinsics (fnMap : FnMap) :
    Nat → List MirAst.CapturedMir → Option (List (Gen.FnName × Gen.Function))
  | _, [] => some []
  | idx, b :: bs => do
    let f ← translateFnInProgWithIntrinsics fnMap b
    let rest ← translateProgFnsWithIntrinsics fnMap (idx + 1) bs
    pure ((fnName idx, f) :: rest)

/-- Multi-function program translation (`entry :: callees` + `mkStartFn 0`)
supporting `Call` terminators together with block-splitting `Assume`,
`PointerExposeProvenance`, and `PointerWithExposedProvenance` statements. -/
def translateProgWithIntrinsics (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Option Gen.Program := do
  let fnMap := fnNameMap entry callees
  let fns ← translateProgFnsWithIntrinsics fnMap 0 (entry :: callees)
  let startFn := fnName (1 + callees.length)
  pure {
    functions := ⟨fns ++ [(startFn, mkStartFn 0)]⟩
    start := startFn
    globals := ⟨[]⟩
    vtables := ⟨[]⟩
    traits := ⟨[]⟩
  }

theorem mapM_translateStmtResultWithIntrinsics_eq_of_no_provCast
    (decls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable) :
    ∀ (ss : List MirAst.Statement),
      (∀ s ∈ ss, isProvCastStmt s = false) →
      ss.mapM (translateStmtResultWithIntrinsics decls · layouts) =
        ss.mapM (translateStmtResult decls · layouts)
  | [], _ => rfl
  | s :: ss, hnp => by
    have hs := translateStmtResultWithIntrinsics_eq_of_not_provCast decls s layouts
      (hnp s (List.mem_cons_self ..))
    have hss := mapM_translateStmtResultWithIntrinsics_eq_of_no_provCast decls layouts ss
      (fun s' hs' => hnp s' (List.mem_cons_of_mem s hs'))
    simp [List.mapM_cons, hs, hss]

theorem translateBlocksInProgWithIntrinsics_eq_of_no_provCast
    (fnMap : FnMap) (layouts : Layout.LayoutTable) (decls : List MirAst.LocalDecl) :
    ∀ (i nextCleanup : Nat) (bbs : List MirAst.BasicBlockData),
      (∀ bb ∈ bbs, ∀ s ∈ bb.statements, isProvCastStmt s = false) →
      translateBlocksInProgWithIntrinsics fnMap layouts decls i nextCleanup bbs =
        translateBlocksInProg fnMap layouts decls i nextCleanup bbs
  | _, _, [], _ => rfl
  | i, nextCleanup, bb :: bbs, hnp => by
    have hbb := mapM_translateStmtResultWithIntrinsics_eq_of_no_provCast decls layouts
      bb.statements (hnp bb (List.mem_cons_self ..))
    simp only [translateBlocksInProgWithIntrinsics, translateBlocksInProg, hbb]
    cases bb.statements.mapM (translateStmtResult decls · layouts) with
    | none => rfl
    | some results =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases translateTerminatorInProg fnMap layouts decls
          (splitStmts (bbName i) [] nextCleanup results).2.2.2 bb.terminator with
      | none => rfl
      | some tre =>
        obtain ⟨term, nextCleanup', extra1⟩ := tre
        have hrest := translateBlocksInProgWithIntrinsics_eq_of_no_provCast
          fnMap layouts decls (i + 1) nextCleanup' bbs
          (fun bb' hbb' => hnp bb' (List.mem_cons_of_mem bb hbb'))
        simp [hrest]

theorem translateFnInProgWithIntrinsics_eq_of_no_provCast
    (fnMap : FnMap) (body : MirAst.CapturedMir)
    (hnp : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements, isProvCastStmt s = false) :
    translateFnInProgWithIntrinsics fnMap body = translateFnInProg fnMap body := by
  simp only [translateFnInProgWithIntrinsics, translateFnInProg,
    translateBlocksInProgWithIntrinsics_eq_of_no_provCast fnMap body.layouts
      body.localDecls 0 (body.basicBlocks.length + 1) body.basicBlocks hnp]

/-- Whether a call argument `op` is well-typed in a multi-function program with
pointer/reference parameters (`ptrPointeeOf paramDecl.ty`). -/
def callArgOkWithIntrinsics (layouts : Layout.LayoutTable) (decls : List MirAst.LocalDecl)
    (paramDecl : MirAst.LocalDecl) (op : MirAst.Operand) : Bool :=
  callArgOk layouts decls paramDecl op ||
  match op with
  | .copy ⟨p, []⟩ | .move ⟨p, []⟩ =>
    decide (p < decls.length) &&
    match decls[p]?, ptrPointeeOf paramDecl.ty with
    | some dp, some (mutbl, pointeeIt) =>
      if isRefTy paramDecl.ty then
        decide (refPointeeOf dp.ty = some (mutbl, pointeeIt))
      else
        decide (rawPtrPointeeOf dp.ty = some (mutbl, pointeeIt))
    | _, _ => false
  | _ => false

def callArgsOkWithIntrinsics (layouts : Layout.LayoutTable) (decls : List MirAst.LocalDecl) :
    List MirAst.LocalDecl → List MirAst.Operand → Bool
  | [], [] => true
  | pd :: pds, op :: ops =>
    callArgOkWithIntrinsics layouts decls pd op && callArgsOkWithIntrinsics layouts decls pds ops
  | _, _ => false

theorem callArgsOkWithIntrinsics_of_callArgsOk {layouts : Layout.LayoutTable}
    {decls : List MirAst.LocalDecl} :
    ∀ (pds : List MirAst.LocalDecl) (ops : List MirAst.Operand),
      callArgsOk layouts decls pds ops = true →
      callArgsOkWithIntrinsics layouts decls pds ops = true
  | [], [], _ => rfl
  | pd :: pds, op :: ops, h => by
    simp only [callArgsOk, Bool.and_eq_true] at h
    simp [callArgsOkWithIntrinsics, callArgOkWithIntrinsics, h.1,
      callArgsOkWithIntrinsics_of_callArgsOk pds ops h.2]

/-- Whether two MIR types translate to the same MiniRust type in the
pointer/reference-extended multi-function fragment. -/
def sameFragmentTyWithIntrinsics (t1 t2 : MirAst.Ty) : Bool :=
  sameFragmentTy t1 t2 ||
  (match ptrPointeeOf t1, ptrPointeeOf t2 with
   | some (m1, it1), some (m2, it2) =>
     decide (m1 = m2) && decide (it1 = it2) && decide (isRefTy t1 = isRefTy t2)
   | _, _ => false)

def callDestOkWithIntrinsics (decls : List MirAst.LocalDecl) (lv ti : List Nat)
    (calleeRetDecl : MirAst.LocalDecl) (destination : MirAst.Place) : Bool :=
  callDestOk decls lv ti calleeRetDecl destination ||
  match destination with
  | ⟨dst, []⟩ =>
    decide (dst < decls.length) && lv.contains dst &&
    match decls[dst]? with
    | some d => sameFragmentTyWithIntrinsics d.ty calleeRetDecl.ty
    | none => false
  | _ => false

def callTerminatorOkWithIntrinsics (callees : List MirAst.CapturedMir)
    (body : MirAst.CapturedMir) (blk : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind, body.basicBlocks[blk]? with
  | .call func argOps destination (some targetBb) unwind, some bb =>
    match extractFnDefPath func with
    | none => false
    | some defPath =>
      match translateIntrinsicOrNone body.localDecls defPath argOps destination (some targetBb) with
      | some _ => false
      | none =>
        match monoCallee? callees func defPath with
        | none => false
        | some callee =>
          match callee.localDecls with
          | [] => false
          | retDecl :: restDecls =>
            let lv := mustLiveBefore body blk bb.statements.length
            let ti := tupleInitBefore body blk bb.statements.length
            decide (targetBb < body.basicBlocks.length) &&
            callUnwindOk unwind &&
            (translateCallConv callee.fnAbi.conv).isSome &&
            decide (argOps.length = callee.argCount) &&
            decide (callee.argCount ≤ restDecls.length) &&
            callArgsOkWithIntrinsics body.layouts body.localDecls
              (restDecls.take callee.argCount) argOps &&
            callDestOkWithIntrinsics body.localDecls lv ti retDecl destination &&
            argOps.all (fun op => opRead op != some destination.local_)
  | _, _ => false

def terminatorInProgOkWithIntrinsics (callees : List MirAst.CapturedMir)
    (body : MirAst.CapturedMir) (blk : Nat) (t : MirAst.Terminator) : Bool :=
  terminatorOk body.layouts body.localDecls body.basicBlocks.length t ||
  callTerminatorOkWithIntrinsics callees body blk t

theorem callTerminatorOkWithIntrinsics_of_callTerminatorOk
    {callees : List MirAst.CapturedMir} {body : MirAst.CapturedMir}
    {blk : Nat} {t : MirAst.Terminator}
    (h : callTerminatorOk callees body blk t = true) :
    callTerminatorOkWithIntrinsics callees body blk t = true := by
  unfold callTerminatorOk at h
  unfold callTerminatorOkWithIntrinsics
  split at h
  · next func argOps destination targetBb unwind bb hkind hbb =>
    cases hex : extractFnDefPath func with
    | none => simp [hex] at h
    | some defPath =>
      simp only [hex] at h ⊢
      cases hint : translateIntrinsicOrNone body.localDecls defPath argOps destination (some targetBb) with
      | some _ => simp [hint] at h
      | none =>
        simp only [hint] at h ⊢
        cases hcal : monoCallee? callees func defPath with
        | none => simp [hcal] at h
        | some callee =>
          simp only [hcal] at h ⊢
          cases hdecls : callee.localDecls with
          | nil => simp [hdecls] at h
          | cons retDecl restDecls =>
            simp only [hdecls, Bool.and_eq_true] at h ⊢
            rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
            refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩,
              callArgsOkWithIntrinsics_of_callArgsOk _ _ h6⟩, ?_⟩, h8⟩
            simp [callDestOkWithIntrinsics, h7]
  · simp at h

theorem terminatorInProgOkWithIntrinsics_of_terminatorInProgOk
    {callees : List MirAst.CapturedMir} {body : MirAst.CapturedMir}
    {blk : Nat} {t : MirAst.Terminator}
    (h : terminatorInProgOk callees body blk t = true) :
    terminatorInProgOkWithIntrinsics callees body blk t = true := by
  simp only [terminatorInProgOk, Bool.or_eq_true] at h
  rcases h with h1 | h2
  · simp [terminatorInProgOkWithIntrinsics, h1]
  · simp [terminatorInProgOkWithIntrinsics,
      callTerminatorOkWithIntrinsics_of_callTerminatorOk h2]

/-- Whether `t` is a non-diverging `Call` terminator (`target = some _`). -/
def isNonDivergingCall (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .call _ _ _ (some _) _ => true
  | _ => false

/-- Pointer/borrow local state transfer across a block terminator `t` in a
multi-function program. In Anneal's `MirSemantics`, all frames share a single
global `s.memory.borrows` table keyed by un-namespaced `BorrowEntry.targetLocal : Nat`,
so any root assignment `_k = rv` inside a callee runs
`invalidateConflictingBorrows mem₁.borrows k .none` across active caller borrows
whose `targetLocal` happens to equal `k`. Consequently, across a returning `Call`
terminator, every caller pointer/reference local transitions to `.disabled`
(forcing fresh borrows after `Return`), while terminators without a returning
`Call` preserve `env` identically. -/
def ptrTermStep (decls : List MirAst.LocalDecl) (env : List PtrLocalState)
    (t : MirAst.Terminator) : List PtrLocalState :=
  let n := decls.length
  match t.kind with
  | .call _ _ ⟨dst, []⟩ (some _) _ =>
    (List.range n).map fun q =>
      if q == dst && isDeclPtrLocal decls dst then .disabled
      else
        match env.getD q .disabled with
        | .empty => .empty
        | .live _ _ _ | .disabled => .disabled
  | .call _ _ _ (some _) _ =>
    (List.range n).map fun q =>
      match env.getD q .disabled with
      | .empty => .empty
      | .live _ _ _ | .disabled => .disabled
  | _ => env

/-- One forward dataflow pass for `ptrAliasingProgOk`, composing `ptrStmtStep`
across block statements with `ptrTermStep` across block terminators. -/
def stepPtrAliasProgEntries (decls : List MirAst.LocalDecl)
    (bbs : List MirAst.BasicBlockData)
    (entries : List (List PtrLocalState)) : List (List PtrLocalState) :=
  let n := decls.length
  (List.range bbs.length).map fun dst =>
    (List.range bbs.length).foldl (fun acc src =>
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let inEnv := entries.getD src (initPtrEnv n)
          let midEnv := bb.statements.foldl (ptrStmtStep decls) inEnv
          let outEnv := ptrTermStep decls midEnv bb.terminator
          joinPtrEnv n acc outEnv
        else acc
      | none => acc) (entries.getD dst (initPtrEnv n))

/-- Iterate `stepPtrAliasProgEntries` up to `fuel` passes. -/
def iterPtrAliasProgEntries :
    Nat → List MirAst.LocalDecl → List MirAst.BasicBlockData →
      List (List PtrLocalState) → List (List PtrLocalState)
  | 0, _, _, entries => entries
  | k + 1, decls, bbs, entries =>
    let entries' := stepPtrAliasProgEntries decls bbs entries
    if entries' == entries then entries
    else iterPtrAliasProgEntries k decls bbs entries'

/-- Abstract `PtrLocalState` environment at entry to block `blk` in a
multi-function body (`ptrAliasingProgOk`). -/
def ptrProgEnvAtEntry (body : MirAst.CapturedMir) (blk : Nat) : List PtrLocalState :=
  let n := body.localDecls.length
  let b := body.basicBlocks.length
  let fuel := b * n * (n + 4) + 1
  let init := initPtrEntries b n
  (iterPtrAliasProgEntries fuel body.localDecls body.basicBlocks init).getD blk (initPtrEnv n)

/-- Multi-function pointer/borrow aliasing discipline extending `ptrAliasingOk`
with `ptrTermStep` across returning `Call` terminators. Coincides identically
with `ptrAliasingOk` when `body` contains no returning `Call` terminators
(`ptrAliasingProgOk_eq_of_no_calls`), and holds automatically on scalar-only
`progInFragment` bodies (`ptrAliasingProgOk_of_scalar`). -/
def ptrAliasingProgOk (body : MirAst.CapturedMir) : Bool :=
  let addrLocals := bodyAddrTakenLocals body
  let n := body.localDecls.length
  ptrDeclLayoutsOk body &&
  addrLocals.all (fun k => decide (1 ≤ k ∧ k ≤ body.argCount)) &&
  body.basicBlocks.all (fun bb =>
    bb.statements.all (stmtPreservesAddrTaken addrLocals) &&
    termPreservesAddrTaken addrLocals bb.terminator) &&
  subsumesPtrEnv n (initPtrEnv n) (ptrProgEnvAtEntry body 0) &&
  (List.range body.basicBlocks.length).all fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      let inEnv := ptrProgEnvAtEntry body blk
      let midEnv := bb.statements.foldl (ptrStmtStep body.localDecls) inEnv
      let exitEnv := ptrTermStep body.localDecls midEnv bb.terminator
      blockPtrAliasOk body.localDecls inEnv bb.statements &&
      (termTargets bb.terminator).all (fun t =>
        subsumesPtrEnv n exitEnv (ptrProgEnvAtEntry body t))
    | none => true

theorem ptrTermStep_eq_of_not_call (decls : List MirAst.LocalDecl)
    (env : List PtrLocalState) (t : MirAst.Terminator)
    (h : isNonDivergingCall t = false) :
    ptrTermStep decls env t = env := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | call fn args dst tgt unw =>
    cases tgt with
    | none => cases dst with | mk d projs => cases projs <;> rfl
    | some _ => simp [isNonDivergingCall] at h
  | _ => rfl

private theorem foldl_congr_prog {α β : Type} (f g : α → β → α) (init : α) (l : List β)
    (h : ∀ a, ∀ b ∈ l, f a b = g a b) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, h init x (List.mem_cons_self ..)]
    exact ih _ (fun a b hb => h a b (List.mem_cons_of_mem x hb))

private theorem list_all_congr_prog {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem stepPtrAliasProgEntries_eq_of_no_calls (decls : List MirAst.LocalDecl)
    (bbs : List MirAst.BasicBlockData) (entries : List (List PtrLocalState))
    (hno : ∀ bb ∈ bbs, isNonDivergingCall bb.terminator = false) :
    stepPtrAliasProgEntries decls bbs entries = stepPtrAliasEntries decls bbs entries := by
  dsimp only [stepPtrAliasProgEntries, stepPtrAliasEntries]
  apply List.map_congr_left
  intro dst _
  apply foldl_congr_prog
  intro acc src _
  cases hbb : bbs[src]? with
  | none => rfl
  | some bb =>
    have hmem : bb ∈ bbs := List.mem_of_getElem? hbb
    simp [ptrTermStep_eq_of_not_call decls _ bb.terminator (hno bb hmem)]

theorem iterPtrAliasProgEntries_eq_of_no_calls :
    ∀ (fuel : Nat) (decls : List MirAst.LocalDecl) (bbs : List MirAst.BasicBlockData)
      (entries : List (List PtrLocalState)),
      (∀ bb ∈ bbs, isNonDivergingCall bb.terminator = false) →
      iterPtrAliasProgEntries fuel decls bbs entries = iterPtrAliasEntries fuel decls bbs entries
  | 0, _, _, _, _ => rfl
  | k + 1, decls, bbs, entries, hno => by
    simp only [iterPtrAliasProgEntries, iterPtrAliasEntries,
      stepPtrAliasProgEntries_eq_of_no_calls decls bbs entries hno]
    split
    · rfl
    · exact iterPtrAliasProgEntries_eq_of_no_calls k decls bbs _ hno

theorem ptrProgEnvAtEntry_eq_of_no_calls (body : MirAst.CapturedMir) (blk : Nat)
    (hno : ∀ bb ∈ body.basicBlocks, isNonDivergingCall bb.terminator = false) :
    ptrProgEnvAtEntry body blk = ptrEnvAtEntry body blk := by
  simp only [ptrProgEnvAtEntry, ptrEnvAtEntry,
    iterPtrAliasProgEntries_eq_of_no_calls _ body.localDecls body.basicBlocks _ hno]

theorem ptrAliasingProgOk_eq_of_no_calls (body : MirAst.CapturedMir)
    (hno : ∀ bb ∈ body.basicBlocks, isNonDivergingCall bb.terminator = false) :
    ptrAliasingProgOk body = ptrAliasingOk body := by
  dsimp only [ptrAliasingProgOk, ptrAliasingOk]
  rw [ptrProgEnvAtEntry_eq_of_no_calls body 0 hno]
  congr 1
  apply list_all_congr_prog
  intro blk _
  cases hbb : body.basicBlocks[blk]? with
  | none => rfl
  | some bb =>
    have hmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
    dsimp only
    rw [ptrProgEnvAtEntry_eq_of_no_calls body blk hno,
      ptrTermStep_eq_of_not_call body.localDecls _ bb.terminator (hno bb hmem)]
    congr 1
    apply list_all_congr_prog
    intro t _
    rw [ptrProgEnvAtEntry_eq_of_no_calls body t hno]

private theorem isPtrTy_false_of_scalarTypeOf {ty : MirAst.Ty}
    (h : (scalarTypeOf ty).isSome = true) : isPtrTy ty = false := by
  obtain ⟨kind, lidx⟩ := ty
  cases kind <;> simp [isPtrTy, ptrPointeeOf] at *
  all_goals simp [scalarTypeOf, isBoolTy, isOrderingTy, intBoolTupleOf, intTypeOf, intTyBytes] at h

private theorem isDeclPtrLocal_false_of_scalar {decls : List MirAst.LocalDecl}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) (i : Nat) :
    isDeclPtrLocal decls i = false := by
  unfold isDeclPtrLocal
  cases hd : decls[i]? with
  | none => rfl
  | some d => exact isPtrTy_false_of_scalarTypeOf (hsc d (List.mem_of_getElem? hd))

private theorem initPtrEnv_getD_lt_prog {n q : Nat} (hq : q < n) :
    (initPtrEnv n).getD q .disabled = .empty := by
  unfold initPtrEnv
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
  rfl

private theorem map_getD_initPtrEnv_prog (n : Nat) :
    (List.range n).map (fun q => (initPtrEnv n).getD q .disabled) = initPtrEnv n := by
  unfold initPtrEnv
  apply List.map_congr_left
  intro q hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hq)]
  rfl

private theorem initPtrEnv_getD_cases (n x : Nat) :
    (initPtrEnv n).getD x .disabled = .empty ∨ (initPtrEnv n).getD x .disabled = .disabled := by
  unfold initPtrEnv
  by_cases h : x < n
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    rfl

private theorem foreignReadKeeps_initPtrEnv (n r q : Nat) :
    foreignReadKeeps (initPtrEnv n) r q = true := by
  unfold foreignReadKeeps
  rcases initPtrEnv_getD_cases n r with hr | hr <;>
    rcases initPtrEnv_getD_cases n q with hq | hq <;> rw [hr, hq] <;> simp

private theorem stepForeignRead_initPtrEnv (decls : List MirAst.LocalDecl) (n r : Nat) :
    stepForeignRead decls n (initPtrEnv n) r = initPtrEnv n := by
  unfold stepForeignRead
  simp only [foreignReadKeeps_initPtrEnv, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  exact map_getD_initPtrEnv_prog n

private theorem statementOk_not_deref_assign_of_scalar {decls : List MirAst.LocalDecl}
    {w : Nat} {rv : MirAst.Rvalue} {span : String} {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true)
    (hok : statementOk decls ⟨.assign ⟨w, [.deref]⟩ rv, span⟩ layouts = true) : False := by
  simp only [statementOk, Bool.and_eq_true] at hok
  cases hd : decls[w]? with
  | none => simp [hd] at hok
  | some d =>
    have hfalse := isPtrTy_false_of_scalarTypeOf (hsc d (List.mem_of_getElem? hd))
    simp only [isPtrTy] at hfalse
    cases hpt : ptrPointeeOf d.ty with
    | none => simp [hd, hpt] at hok
    | some pr => simp [hpt] at hfalse

private theorem progStatementOk_ptrStmtStep_initPtrEnv {decls : List MirAst.LocalDecl}
    {s : MirAst.Statement} {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true)
    (hok : progStatementOk decls s layouts = true) :
    ptrStmtStep decls (initPtrEnv decls.length) s = initPtrEnv decls.length := by
  obtain ⟨kind, span⟩ := s
  have hnoPtr := isDeclPtrLocal_false_of_scalar hsc
  cases kind with
  | assign place rv =>
    rcases place with ⟨i, projs⟩
    cases projs with
    | nil =>
      simp only [ptrStmtStep, hnoPtr i, Bool.false_eq_true, ↓reduceIte]
      cases ptrDerefReadSrc rv with
      | some r => exact stepForeignRead_initPtrEnv decls _ r
      | none => exact map_getD_initPtrEnv_prog _
    | cons p rest =>
      cases p with
      | deref =>
        cases rest with
        | nil =>
          simp only [progStatementOk] at hok
          exact False.elim (statementOk_not_deref_assign_of_scalar hsc hok)
        | cons _ _ => exact map_getD_initPtrEnv_prog _
      | _ => exact map_getD_initPtrEnv_prog _
  | storageLive i | storageDead i =>
    simp only [ptrStmtStep, hnoPtr i, Bool.false_eq_true, ↓reduceIte]
    exact map_getD_initPtrEnv_prog _
  | deinit place =>
    rcases place with ⟨i, projs⟩
    cases projs <;>
      (simp only [ptrStmtStep, hnoPtr i, Bool.false_eq_true, ↓reduceIte];
       exact map_getD_initPtrEnv_prog _)
  | _ => exact map_getD_initPtrEnv_prog _

private theorem foldl_ptrStmtStep_initPtrEnv {decls : List MirAst.LocalDecl}
    {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    ∀ (ss : List MirAst.Statement),
      (∀ s ∈ ss, progStatementOk decls s layouts = true) →
      ss.foldl (ptrStmtStep decls) (initPtrEnv decls.length) = initPtrEnv decls.length
  | [], _ => rfl
  | s :: ss, hok => by
    simp only [List.foldl_cons,
      progStatementOk_ptrStmtStep_initPtrEnv hsc (hok s (List.mem_cons_self ..))]
    exact foldl_ptrStmtStep_initPtrEnv hsc ss (fun s' hs' => hok s' (List.mem_cons_of_mem s hs'))

private theorem ptrTermStep_initPtrEnv_of_scalar {decls : List MirAst.LocalDecl}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) (t : MirAst.Terminator) :
    ptrTermStep decls (initPtrEnv decls.length) t = initPtrEnv decls.length := by
  have hnoPtr := isDeclPtrLocal_false_of_scalar hsc
  obtain ⟨kind, span⟩ := t
  cases kind with
  | call fn args dst tgt unw =>
    cases tgt with
    | none => cases dst with | mk d projs => cases projs <;> rfl
    | some targetBb =>
      rcases dst with ⟨d, projs⟩
      cases projs with
      | nil =>
        dsimp only [ptrTermStep]
        apply List.map_congr_left
        intro q hq
        rw [hnoPtr d, Bool.and_false, initPtrEnv_getD_lt_prog (List.mem_range.mp hq)]
        rfl
      | cons _ _ =>
        dsimp only [ptrTermStep]
        apply List.map_congr_left
        intro q hq
        rw [initPtrEnv_getD_lt_prog (List.mem_range.mp hq)]
  | _ => rfl

private theorem joinPtrEnv_initPtrEnv_self (n : Nat) :
    joinPtrEnv n (initPtrEnv n) (initPtrEnv n) = initPtrEnv n := by
  unfold joinPtrEnv
  apply List.map_congr_left
  intro q hq
  rw [initPtrEnv_getD_lt_prog (List.mem_range.mp hq)]
  rfl

private theorem initPtrEntries_getD_prog {b n k : Nat} :
    (initPtrEntries b n).getD k (initPtrEnv n) = initPtrEnv n := by
  unfold initPtrEntries
  by_cases hk : k < b
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    rfl
  · have hge : ((List.range b).map (fun _ => initPtrEnv n)).length ≤ k := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl

private theorem stepPtrAliasProgEntries_init_of_scalar {decls : List MirAst.LocalDecl}
    {bbs : List MirAst.BasicBlockData} {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ bbs, ∀ s ∈ bb.statements, progStatementOk decls s layouts = true) :
    stepPtrAliasProgEntries decls bbs (initPtrEntries bbs.length decls.length) =
      initPtrEntries bbs.length decls.length := by
  dsimp only [stepPtrAliasProgEntries]
  unfold initPtrEntries
  apply List.map_congr_left
  intro dst _
  have hinit : ((List.range bbs.length).map (fun _ => initPtrEnv decls.length)).getD dst
      (initPtrEnv decls.length) = initPtrEnv decls.length := initPtrEntries_getD_prog
  rw [hinit]
  have hfold : ∀ (l : List Nat),
      l.foldl (fun acc src =>
        match bbs[src]? with
        | some bb =>
          if (termTargets bb.terminator).contains dst then
            let inEnv := (initPtrEntries bbs.length decls.length).getD src (initPtrEnv decls.length)
            let midEnv := bb.statements.foldl (ptrStmtStep decls) inEnv
            let outEnv := ptrTermStep decls midEnv bb.terminator
            joinPtrEnv decls.length acc outEnv
          else acc
        | none => acc) (initPtrEnv decls.length) = initPtrEnv decls.length := by
    intro l
    induction l with
    | nil => rfl
    | cons src rest ih =>
      simp only [List.foldl_cons]
      have hstep :
          (match bbs[src]? with
          | some bb =>
            if (termTargets bb.terminator).contains dst then
              let inEnv := (initPtrEntries bbs.length decls.length).getD src (initPtrEnv decls.length)
              let midEnv := bb.statements.foldl (ptrStmtStep decls) inEnv
              let outEnv := ptrTermStep decls midEnv bb.terminator
              joinPtrEnv decls.length (initPtrEnv decls.length) outEnv
            else initPtrEnv decls.length
          | none => initPtrEnv decls.length) = initPtrEnv decls.length := by
        cases hbb : bbs[src]? with
        | none => rfl
        | some bb =>
          dsimp only
          split
          · rw [initPtrEntries_getD_prog,
              foldl_ptrStmtStep_initPtrEnv hsc bb.statements (hbbs bb (List.mem_of_getElem? hbb)),
              ptrTermStep_initPtrEnv_of_scalar hsc bb.terminator,
              joinPtrEnv_initPtrEnv_self]
          · rfl
      rw [hstep]
      exact ih
  exact hfold (List.range bbs.length)

private theorem ptrProgEnvAtEntry_of_scalar {body : MirAst.CapturedMir} (blk : Nat)
    (hsc : ∀ d ∈ body.localDecls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true) :
    ptrProgEnvAtEntry body blk = initPtrEnv body.localDecls.length := by
  dsimp only [ptrProgEnvAtEntry]
  have hfix := stepPtrAliasProgEntries_init_of_scalar hsc hbbs
  have hiter : ∀ fuel,
      iterPtrAliasProgEntries fuel body.localDecls body.basicBlocks
        (initPtrEntries body.basicBlocks.length body.localDecls.length) =
      initPtrEntries body.basicBlocks.length body.localDecls.length
    | 0 => rfl
    | k + 1 => by simp [iterPtrAliasProgEntries, hfix]
  rw [hiter]
  exact initPtrEntries_getD_prog

private theorem rvalueOk_not_borrow {layouts : Layout.LayoutTable}
    {decls : List MirAst.LocalDecl} (it : Gen.IntType) {rv : MirAst.Rvalue}
    (h : directBorrowOf rv ≠ none) : rvalueOk layouts decls it rv = false ∧
      rvalueOk layouts decls it (copyRv rv) = false := by
  cases rv <;> simp [directBorrowOf, copyRv, rvalueOk] at h ⊢

private theorem tupleRvalueOk_not_borrow {layouts : Layout.LayoutTable}
    {decls : List MirAst.LocalDecl} {dstTy : MirAst.Ty} {fields : List (Nat × TupleSpec)}
    {size align : Nat} {rv : MirAst.Rvalue}
    (h : directBorrowOf rv ≠ none) :
    tupleRvalueOk layouts decls dstTy fields size align rv = false := by
  cases rv <;> simp [directBorrowOf, tupleRvalueOk] at h ⊢

private theorem progStatementOk_not_directBorrow_of_scalar {decls : List MirAst.LocalDecl}
    {s : MirAst.Statement} {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true)
    (hok : progStatementOk decls s layouts = true) :
    (match s.kind with
     | .assign _ rv => (directBorrowOf rv).map (·.2.local_)
     | _ => none) = none := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    dsimp only
    cases hdb : directBorrowOf rv with
    | none => rfl
    | some mp =>
      exfalso
      have hne : directBorrowOf rv ≠ none := by simp [hdb]
      simp only [progStatementOk] at hok
      rcases dst with ⟨i, projs⟩
      cases projs with
      | nil =>
        simp only [statementOk] at hok
        cases hd : decls[i]? with
        | none => simp [hd] at hok
        | some d =>
          have hsc_d := hsc d (List.mem_of_getElem? hd)
          simp only [hd] at hok
          by_cases hb : isBoolTy d.ty
          · cases rv <;> simp [directBorrowOf] at hdb <;> simp [hb, copyRv, rvalueOkB] at hok
          · by_cases ho : isOrderingTy d.ty
            · cases rv <;> simp [directBorrowOf] at hdb <;> simp [hb, ho, copyRv, rvalueOkO] at hok
            · simp only [hb, ho, Bool.false_eq_true, ↓reduceIte] at hok
              cases h1 : intBoolTupleOf d.ty with
              | some it =>
                cases rv <;> simp [directBorrowOf] at hdb <;> simp [h1, copyRv, rvalueOkTuple] at hok
              | none =>
                simp only [h1] at hok
                cases h2 : intTypeOf d.ty with
                | some it =>
                  cases rv <;> simp [directBorrowOf] at hdb <;>
                    simp [h2, copyRv, rvalueOk, ptrDerefReadOk] at hok
                | none => simp [scalarTypeOf, hb, ho, h1, h2] at hsc_d
      | cons pr rest =>
        cases pr with
        | deref =>
          cases rest with
          | nil => exact statementOk_not_deref_assign_of_scalar hsc hok
          | cons _ _ => simp [statementOk] at hok
        | field idx fTy =>
          simp only [statementOk, Bool.and_eq_true] at hok
          obtain ⟨_, hbr⟩ := hok
          cases hpi : placeIntType layouts decls ⟨i, .field idx fTy :: rest⟩ with
          | some it => simp [hpi, (rvalueOk_not_borrow it hne).1] at hbr
          | none =>
            simp only [hpi] at hbr
            cases htp : tuplePlaceSpec layouts decls ⟨i, .field idx fTy :: rest⟩ with
            | none => simp [htp] at hbr
            | some fsa =>
              rcases fsa with ⟨fields, size, align⟩
              cases hpm : placeMirTy decls ⟨i, .field idx fTy :: rest⟩ with
              | none => simp [htp, hpm] at hbr
              | some dstTy => simp [htp, hpm, tupleRvalueOk_not_borrow hne] at hbr
        | index idxLoc =>
          cases rest with
          | nil =>
            simp only [statementOk] at hok
            cases ha : (decls[i]?.bind fun x => arrayTypeOf x.ty) with
            | none => simp [Option.bind_eq_bind, ha] at hok
            | some ec => simp [Option.bind_eq_bind, ha, (rvalueOk_not_borrow ec.1 hne).1] at hok
          | cons _ _ => simp [statementOk] at hok
        | constantIndex o ml fe =>
          cases rest with
          | nil =>
            simp only [statementOk] at hok
            cases ha : (decls[i]?.bind fun x => arrayTypeOf x.ty) with
            | none => simp [Option.bind_eq_bind, ha] at hok
            | some ec => simp [Option.bind_eq_bind, ha, (rvalueOk_not_borrow ec.1 hne).1] at hok
          | cons _ _ => simp [statementOk] at hok
        | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
          cases rest with
          | nil =>
            simp only [statementOk] at hok
            cases ha : (decls[i]?.bind fun x => arrayTypeOf x.ty) with
            | none => simp [Option.bind_eq_bind, ha] at hok
            | some ec => simp [Option.bind_eq_bind, ha, projOk] at hok
          | cons _ _ => simp [statementOk] at hok
  | _ => rfl

private theorem bodyAddrTakenLocals_eq_nil_of_scalar {body : MirAst.CapturedMir}
    (hsc : ∀ d ∈ body.localDecls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true) :
    bodyAddrTakenLocals body = [] := by
  unfold bodyAddrTakenLocals
  rw [List.flatMap_eq_nil_iff]
  intro bb hbb
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  exact progStatementOk_not_directBorrow_of_scalar hsc (hbbs bb hbb s hs)

private theorem progStatementOk_ptrStmtOk_initPtrEnv {decls : List MirAst.LocalDecl}
    {s : MirAst.Statement} {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true)
    (hok : progStatementOk decls s layouts = true) :
    ptrStmtOk (initPtrEnv decls.length) s = true := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    rcases dst with ⟨i, projs⟩
    cases projs with
    | nil =>
      dsimp only [ptrStmtOk]
      cases hpr : ptrDerefReadSrc rv with
      | some p =>
        have hlt : p < decls.length := by
          have hderef : ∃ rest, copyRv rv = .use (.copy ⟨p, .deref :: rest⟩) := by
            unfold ptrDerefReadSrc at hpr
            cases hcr : copyRv rv with
            | use op =>
              cases op with
              | copy pl =>
                rcases pl with ⟨p', prs⟩
                cases prs with
                | nil => simp [hcr] at hpr
                | cons pr0 rest =>
                  cases pr0 <;> simp [hcr] at hpr
                  subst hpr; exact ⟨rest, rfl⟩
              | _ => simp [hcr] at hpr
            | _ => simp [hcr] at hpr
          obtain ⟨rest, hcr⟩ := hderef
          simp only [progStatementOk, statementOk] at hok
          cases hd : decls[i]? with
          | none => simp [hd] at hok
          | some d =>
            have hsc_d := hsc d (List.mem_of_getElem? hd)
            simp only [hd, hcr] at hok
            by_cases hb : isBoolTy d.ty
            · simp [hb, rvalueOkB, operandOkB] at hok
            · by_cases ho : isOrderingTy d.ty
              · simp [hb, ho, rvalueOkO, operandOkO] at hok
              · simp only [hb, ho, Bool.false_eq_true, ↓reduceIte] at hok
                cases h1 : intBoolTupleOf d.ty with
                | some it => simp [h1, rvalueOkTuple, operandOkTuple] at hok
                | none =>
                  simp only [h1] at hok
                  cases h2 : intTypeOf d.ty with
                  | some it =>
                    simp only [h2, Bool.or_eq_true] at hok
                    rcases hok with hr | hp
                    · cases rest with
                      | cons _ _ => simp [rvalueOk, operandOk, placeOk] at hr
                      | nil =>
                        simp only [rvalueOk, operandOk, placeOk, Bool.and_eq_true,
                          decide_eq_true_eq] at hr
                        exact hr.1.1
                    · cases rest with
                      | cons _ _ => simp [ptrDerefReadOk] at hp
                      | nil =>
                        simp only [ptrDerefReadOk, Bool.and_eq_true, decide_eq_true_eq] at hp
                        exact hp.1
                  | none => simp [scalarTypeOf, hb, ho, h1, h2] at hsc_d
        dsimp only
        rw [initPtrEnv_getD_lt_prog hlt]
        rfl
      | none =>
        cases hrb : reborrowParentOf rv with
        | none =>
          cases hof : ptrOffsetSrcOf rv with
          | none => rfl
          | some p =>
            exfalso
            have hcr : ∃ r, copyRv rv = .binaryOp .offset (.copy ⟨p, []⟩) r := by
              unfold ptrOffsetSrcOf at hof
              split at hof
              · next p' r heq => simp at hof; subst hof; exact ⟨r, heq⟩
              · cases hof
            obtain ⟨r, hcr⟩ := hcr
            simp only [progStatementOk, statementOk] at hok
            cases hd : decls[i]? with
            | none => simp [hd] at hok
            | some d =>
              have hsc_d := hsc d (List.mem_of_getElem? hd)
              simp only [hd, hcr] at hok
              by_cases hb : isBoolTy d.ty
              · simp [hb, rvalueOkB, translateRelOp, translateBoolBitOp] at hok
              · by_cases ho : isOrderingTy d.ty
                · simp [hb, ho, rvalueOkO] at hok
                · simp only [hb, ho, Bool.false_eq_true, ↓reduceIte] at hok
                  cases h1 : intBoolTupleOf d.ty with
                  | some it => simp [h1, rvalueOkTuple, translateCheckedBinOp] at hok
                  | none =>
                    simp only [h1] at hok
                    cases h2 : intTypeOf d.ty with
                    | some it => simp [h2, rvalueOk, translateBinOp, ptrDerefReadOk] at hok
                    | none => simp [scalarTypeOf, hb, ho, h1, h2] at hsc_d
        | some p =>
          exfalso
          simp only [progStatementOk, statementOk] at hok
          cases hd : decls[i]? with
          | none => simp [hd] at hok
          | some d =>
            have hsc_d := hsc d (List.mem_of_getElem? hd)
            simp only [hd] at hok
            by_cases hb : isBoolTy d.ty
            · cases rv <;> simp [reborrowParentOf] at hrb <;> simp [hb, copyRv, rvalueOkB] at hok
            · by_cases ho : isOrderingTy d.ty
              · cases rv <;> simp [reborrowParentOf] at hrb <;> simp [hb, ho, copyRv, rvalueOkO] at hok
              · simp only [hb, ho, Bool.false_eq_true, ↓reduceIte] at hok
                cases h1 : intBoolTupleOf d.ty with
                | some it =>
                  cases rv <;> simp [reborrowParentOf] at hrb <;> simp [h1, copyRv, rvalueOkTuple] at hok
                | none =>
                  simp only [h1] at hok
                  cases h2 : intTypeOf d.ty with
                  | some it =>
                    cases rv <;> simp [reborrowParentOf] at hrb <;>
                      simp [h2, copyRv, rvalueOk, ptrDerefReadOk] at hok
                  | none => simp [scalarTypeOf, hb, ho, h1, h2] at hsc_d
    | cons pr rest =>
      cases pr with
      | deref =>
        cases rest with
        | nil =>
          simp only [progStatementOk] at hok
          exact False.elim (statementOk_not_deref_assign_of_scalar hsc hok)
        | cons _ _ => rfl
      | _ => rfl
  | retag rk pl =>
    rcases pl with ⟨p, projs⟩
    cases projs with
    | cons _ _ => rfl
    | nil =>
      simp only [progStatementOk, statementOk, isDeclPtrLocal_false_of_scalar hsc p,
        Bool.and_false] at hok
      cases hok
  | _ => rfl

private theorem blockPtrAliasOk_initPtrEnv_of_scalar {decls : List MirAst.LocalDecl}
    {layouts : Layout.LayoutTable}
    (hsc : ∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) :
    ∀ (ss : List MirAst.Statement),
      (∀ s ∈ ss, progStatementOk decls s layouts = true) →
      blockPtrAliasOk decls (initPtrEnv decls.length) ss = true
  | [], _ => rfl
  | s :: ss, hok => by
    have hs := hok s (List.mem_cons_self ..)
    simp only [blockPtrAliasOk, progStatementOk_ptrStmtOk_initPtrEnv hsc hs,
      progStatementOk_ptrStmtStep_initPtrEnv hsc hs, Bool.true_and]
    exact blockPtrAliasOk_initPtrEnv_of_scalar hsc ss (fun s' hs' => hok s' (List.mem_cons_of_mem s hs'))

private theorem stmtPreservesAddrTaken_nil (s : MirAst.Statement) :
    stmtPreservesAddrTaken [] s = true := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    simp only [stmtPreservesAddrTaken, List.contains_nil, Bool.not_false, Bool.true_and]
    rw [List.all_eq_true]
    intro op _
    cases opMoved op <;> rfl
  | intrinsic intr =>
    cases intr with
    | assume op =>
      simp only [stmtPreservesAddrTaken, List.all_cons, List.all_nil, Bool.and_true]
      cases opMoved op <;> rfl
    | _ => rfl
  | deinit _ | storageLive _ | storageDead _ => simp [stmtPreservesAddrTaken]
  | _ => rfl

private theorem termPreservesAddrTaken_nil (t : MirAst.Terminator) :
    termPreservesAddrTaken [] t = true := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr _ =>
    dsimp only [termPreservesAddrTaken]
    cases opMoved discr <;> rfl
  | call _ argOps dst _ _ =>
    simp only [termPreservesAddrTaken, List.contains_nil, Bool.not_false, Bool.true_and]
    rw [List.all_eq_true]
    intro op _
    cases opMoved op <;> rfl
  | _ => rfl

private theorem bodyDirectBorrowPlaces_eq_nil_of_scalar {body : MirAst.CapturedMir}
    (hsc : ∀ d ∈ body.localDecls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true) :
    bodyDirectBorrowPlaces body = [] := by
  unfold bodyDirectBorrowPlaces
  rw [List.flatMap_eq_nil_iff]
  intro bb hbb
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  have h0 := progStatementOk_not_directBorrow_of_scalar hsc (hbbs bb hbb s hs)
  cases sk : s.kind with
  | assign _ rv =>
    rw [sk] at h0
    dsimp only at h0 ⊢
    cases hdb : directBorrowOf rv with
    | none => rfl
    | some _ => simp [hdb] at h0
  | _ => rfl

private theorem ptrDeclLayoutsOk_of_scalar {body : MirAst.CapturedMir}
    (hsc : ∀ d ∈ body.localDecls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true) :
    ptrDeclLayoutsOk body = true := by
  unfold ptrDeclLayoutsOk
  rw [bodyDirectBorrowPlaces_eq_nil_of_scalar hsc hbbs]
  simp only [List.all_nil, Bool.and_true, List.all_eq_true]
  intro p _
  cases hd : body.localDecls[p]? with
  | none => rfl
  | some dp =>
    have hf := isPtrTy_false_of_scalarTypeOf (hsc dp (List.mem_of_getElem? hd))
    simp only [isPtrTy] at hf
    cases hpt : ptrPointeeOf dp.ty with
    | none => dsimp only; rw [hpt]
    | some _ => simp [hpt] at hf

theorem ptrAliasingProgOk_of_scalar (body : MirAst.CapturedMir)
    (hsc : ∀ d ∈ body.localDecls, (scalarTypeOf d.ty).isSome = true)
    (hbbs : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true) :
    ptrAliasingProgOk body = true := by
  dsimp only [ptrAliasingProgOk]
  rw [ptrDeclLayoutsOk_of_scalar hsc hbbs]
  rw [bodyAddrTakenLocals_eq_nil_of_scalar hsc hbbs]
  rw [ptrProgEnvAtEntry_of_scalar 0 hsc hbbs]
  have hsub_self : subsumesPtrEnv body.localDecls.length
      (initPtrEnv body.localDecls.length) (initPtrEnv body.localDecls.length) = true := by
    simp only [subsumesPtrEnv, List.all_eq_true, List.mem_range]
    intro q hq
    rw [initPtrEnv_getD_lt_prog hq]
    rfl
  have hpres : (body.basicBlocks.all fun bb =>
      bb.statements.all (stmtPreservesAddrTaken []) &&
      termPreservesAddrTaken [] bb.terminator) = true := by
    rw [List.all_eq_true]
    intro bb _
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.mpr (fun s _ => stmtPreservesAddrTaken_nil s),
      termPreservesAddrTaken_nil bb.terminator⟩
  rw [List.all_nil, hpres, hsub_self]
  simp only [Bool.true_and, List.all_eq_true]
  intro blk _
  cases hbb : body.basicBlocks[blk]? with
  | none => rfl
  | some bb =>
    have hmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
    dsimp only
    rw [ptrProgEnvAtEntry_of_scalar blk hsc hbbs,
      foldl_ptrStmtStep_initPtrEnv hsc bb.statements (hbbs bb hmem),
      ptrTermStep_initPtrEnv_of_scalar hsc bb.terminator,
      blockPtrAliasOk_initPtrEnv_of_scalar hsc bb.statements (hbbs bb hmem),
      Bool.true_and, List.all_eq_true]
    intro t _
    rw [ptrProgEnvAtEntry_of_scalar t hsc hbbs]
    exact hsub_self

theorem translateProgFnsWithIntrinsics_eq_of_no_provCast (fnMap : FnMap) :
    ∀ (idx : Nat) (bs : List MirAst.CapturedMir),
      (∀ b ∈ bs, ∀ bb ∈ b.basicBlocks, ∀ s ∈ bb.statements, isProvCastStmt s = false) →
      translateProgFnsWithIntrinsics fnMap idx bs = translateProgFns fnMap idx bs
  | _, [], _ => rfl
  | idx, b :: bs, hnp => by
    have hb := translateFnInProgWithIntrinsics_eq_of_no_provCast fnMap b
      (hnp b (List.mem_cons_self ..))
    have hbs := translateProgFnsWithIntrinsics_eq_of_no_provCast fnMap (idx + 1) bs
      (fun b' hb' => hnp b' (List.mem_cons_of_mem b hb'))
    simp [translateProgFnsWithIntrinsics, translateProgFns, hb, hbs]

theorem translateProgWithIntrinsics_eq_of_no_provCast
    (entry : MirAst.CapturedMir) (callees : List MirAst.CapturedMir)
    (hnp : ∀ b ∈ entry :: callees, ∀ bb ∈ b.basicBlocks, ∀ s ∈ bb.statements,
      isProvCastStmt s = false) :
    translateProgWithIntrinsics entry callees = translateProg entry callees := by
  simp only [translateProgWithIntrinsics, translateProg,
    translateProgFnsWithIntrinsics_eq_of_no_provCast _ 0 (entry :: callees) hnp]

private theorem mapM_translateStmtResult_not_provCast {decls : List MirAst.LocalDecl}
    {layouts : Layout.LayoutTable} :
    ∀ (ss : List MirAst.Statement) (res : List StatementResult),
      ss.mapM (translateStmtResult decls · layouts) = some res →
      ∀ s ∈ ss, isProvCastStmt s = false
  | [], _, _, s, hs => by cases hs
  | s0 :: ss, _, h, s, hs => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h0 : translateStmtResult decls s0 layouts with
    | none => simp [h0] at h
    | some r0 =>
      simp only [h0, Option.bind_some] at h
      cases hss : ss.mapM (translateStmtResult decls · layouts) with
      | none => simp [hss] at h
      | some rs =>
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact translateStmtResult_not_provCast h0
        · exact mapM_translateStmtResult_not_provCast ss rs hss s hs'

private theorem translateBlocksInProg_not_provCast {fnMap : FnMap}
    {layouts : Layout.LayoutTable} {decls : List MirAst.LocalDecl} :
    ∀ (i nextCleanup : Nat) (bbs : List MirAst.BasicBlockData)
      (out : List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock)),
      translateBlocksInProg fnMap layouts decls i nextCleanup bbs = some out →
      ∀ bb ∈ bbs, ∀ s ∈ bb.statements, isProvCastStmt s = false
  | _, _, [], _, _, bb, hbb => by cases hbb
  | i, nextCleanup, bb0 :: bbs, _, h, bb, hbb => by
    simp only [translateBlocksInProg, Option.bind_eq_bind] at h
    cases hss : bb0.statements.mapM (translateStmtResult decls · layouts) with
    | none => simp [hss] at h
    | some results =>
      simp only [hss, Option.bind_some] at h
      cases hterm : translateTerminatorInProg fnMap layouts decls
          (splitStmts (bbName i) [] nextCleanup results).2.2.2 bb0.terminator with
      | none => simp [hterm] at h
      | some tre =>
        rcases tre with ⟨term, nextCleanup', extra1⟩
        simp only [hterm, Option.bind_some] at h
        cases hrest : translateBlocksInProg fnMap layouts decls (i + 1) nextCleanup' bbs with
        | none => simp [hrest] at h
        | some restOut =>
          rcases List.mem_cons.mp hbb with rfl | hbb'
          · exact mapM_translateStmtResult_not_provCast _ results hss
          · exact translateBlocksInProg_not_provCast (i + 1) nextCleanup' bbs restOut hrest bb hbb'

theorem translateFnInProg_not_provCast {fnMap : FnMap} {body : MirAst.CapturedMir}
    {f : Gen.Function} (h : translateFnInProg fnMap body = some f) :
    (∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements, isProvCastStmt s = false) ∧
      hasProvCast body = false := by
  simp only [translateFnInProg, Option.bind_eq_bind] at h
  cases hconv : translateCallConv body.fnAbi.conv with
  | none => simp [hconv] at h
  | some conv =>
    simp only [hconv, Option.bind_some] at h
    cases hloc : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hloc] at h
    | some locals =>
      simp only [hloc, Option.bind_some] at h
      cases hblks : translateBlocksInProg fnMap body.layouts body.localDecls
          0 (body.basicBlocks.length + 1) body.basicBlocks with
      | none => simp [hblks] at h
      | some out =>
        have hno := translateBlocksInProg_not_provCast 0 (body.basicBlocks.length + 1)
          body.basicBlocks out hblks
        refine ⟨hno, ?_⟩
        unfold hasProvCast
        rw [List.any_eq_false]
        intro bb hbb hany
        rw [List.any_eq_true] at hany
        obtain ⟨s, hs, hp⟩ := hany
        rw [hno bb hbb s hs] at hp
        cases hp

theorem terminatorOk_not_call {layouts : Layout.LayoutTable}
    {decls : List MirAst.LocalDecl} {nblocks : Nat} {t : MirAst.Terminator}
    (h : terminatorOk layouts decls nblocks t = true) :
    isNonDivergingCall t = false ∧
    (∀ fn args dst tgt unw, t.kind ≠ .call fn args dst tgt unw) := by
  obtain ⟨kind, span⟩ := t
  cases kind <;> simp [terminatorOk, isNonDivergingCall] at h ⊢

theorem callCalleesOf_eq_nil_of_terminatorOk {body : MirAst.CapturedMir}
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
    callCalleesOf body = [] := by
  unfold callCalleesOf
  rw [List.filterMap_eq_nil_iff]
  intro bb hbb
  have hnc := (terminatorOk_not_call (hterm bb hbb)).2
  cases hk : bb.terminator.kind with
  | call fn args dst tgt unw => exact False.elim (hnc fn args dst tgt unw hk)
  | _ => rfl

private theorem mapM_translateStmtResultWithIntrinsics_isSome_of_orIntrinsic
    {decls : List MirAst.LocalDecl} {layouts : Layout.LayoutTable} :
    ∀ (ss : List MirAst.Statement) (trs : List StmtTranslation),
      ss.mapM (translateStmtOrIntrinsic decls · layouts) = some trs →
      ss.mapM (translateStmtResultWithIntrinsics decls · layouts) =
        some (trs.map StmtTranslation.toStatementResult)
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | s :: ss, _, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hs : translateStmtOrIntrinsic decls s layouts with
    | none => simp [hs] at h
    | some tr0 =>
      simp only [hs, Option.bind_some] at h
      cases hss : ss.mapM (translateStmtOrIntrinsic decls · layouts) with
      | none => simp [hss] at h
      | some rest =>
        simp only [hss, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have ih := mapM_translateStmtResultWithIntrinsics_isSome_of_orIntrinsic ss rest hss
        simp only [List.mapM_cons, Option.bind_eq_bind, ih, Option.bind_some]
        simp [translateStmtResultWithIntrinsics, hs]

private theorem translateBlocksInProgWithIntrinsics_isSome_of_blocksWithIntrinsics
    (fnMap : FnMap) {layouts : Layout.LayoutTable} {decls : List MirAst.LocalDecl}
    {nblocks : Nat} :
    ∀ (i nf nc : Nat) (bbs : List MirAst.BasicBlockData)
      (out : List (Gen.BbName × Gen.BasicBlock) × Nat),
      (∀ bb ∈ bbs, terminatorOk layouts decls nblocks bb.terminator = true) →
      translateBlocksWithIntrinsics layouts decls i nf bbs = some out →
      (translateBlocksInProgWithIntrinsics fnMap layouts decls i nc bbs).isSome = true
  | _, _, _, [], _, _, _ => rfl
  | i, nf, nc, bb :: bbs, _, hterm, h => by
    simp only [translateBlocksWithIntrinsics, Option.bind_eq_bind] at h
    cases hss : bb.statements.mapM (translateStmtOrIntrinsic decls · layouts) with
    | none => simp [hss] at h
    | some trs =>
      simp only [hss, Option.bind_some] at h
      cases htm : translateTerminator layouts decls bb.terminator with
      | none => simp [htm] at h
      | some term =>
        simp only [htm, Option.bind_some] at h
        cases hrest : translateBlocksWithIntrinsics layouts decls (i + 1)
            (splitBlockAtIntrinsics (bbName i) [] term
              (if bb.isCleanup then Gen.BbKind.Cleanup else .Regular) nf trs).2 bbs with
        | none => simp [hrest] at h
        | some restOut =>
          have hss' := mapM_translateStmtResultWithIntrinsics_isSome_of_orIntrinsic
            bb.statements trs hss
          have hnc := (terminatorOk_not_call (hterm bb (List.mem_cons_self ..))).2
          have htmInProg : translateTerminatorInProg fnMap layouts decls
              (splitStmts (bbName i) [] nc (trs.map StmtTranslation.toStatementResult)).2.2.2
              bb.terminator =
              (some (term,
                (splitStmts (bbName i) [] nc (trs.map StmtTranslation.toStatementResult)).2.2.2,
                [])) := by
            rcases hbt : bb.terminator with ⟨tk, tspan⟩
            rw [hbt] at hnc htm
            cases tk with
            | call fn args dst tgt unw => exact False.elim (hnc fn args dst tgt unw rfl)
            | _ => simp [translateTerminatorInProg, htm]
          have ih := translateBlocksInProgWithIntrinsics_isSome_of_blocksWithIntrinsics fnMap
            (i + 1) _ (splitStmts (bbName i) [] nc (trs.map StmtTranslation.toStatementResult)).2.2.2
            bbs restOut
            (fun b hb => hterm b (List.mem_cons_of_mem bb hb)) hrest
          obtain ⟨restRes, hrestRes⟩ := Option.isSome_iff_exists.mp ih
          rcases restRes with ⟨restBlks, extraRest⟩
          simp [translateBlocksInProgWithIntrinsics, hss', htmInProg, hrestRes]

theorem translateFnInProgWithIntrinsics_isSome_of_translateFnWithIntrinsics
    (fnMap : FnMap) {body : MirAst.CapturedMir} {f : Gen.Function}
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true)
    (h : translateFnWithIntrinsics body = some f) :
    (translateFnInProgWithIntrinsics fnMap body).isSome = true := by
  simp only [translateFnWithIntrinsics, Option.bind_eq_bind] at h
  cases hconv : translateCallConv body.fnAbi.conv with
  | none => simp [hconv] at h
  | some conv =>
    simp only [hconv, Option.bind_some] at h
    cases hloc : translateLocals body.layouts 0 body.localDecls with
    | none => simp [hloc] at h
    | some locals =>
      simp only [hloc, Option.bind_some] at h
      cases hblks : translateBlocksWithIntrinsics body.layouts body.localDecls 0
          body.basicBlocks.length body.basicBlocks with
      | none => simp [hblks] at h
      | some out =>
        have his := translateBlocksInProgWithIntrinsics_isSome_of_blocksWithIntrinsics
          fnMap 0 body.basicBlocks.length (body.basicBlocks.length + 1)
          body.basicBlocks out hterm hblks
        obtain ⟨⟨blks, extra⟩, hbe⟩ := Option.isSome_iff_exists.mp his
        simp [translateFnInProgWithIntrinsics, hconv, hloc, hbe]

/-- Per-function sound correspondence fragment within a multi-function program
with intra-frame pointers, references, reborrows, `Transmute`, `Assume`,
`PointerExposeProvenance`, and `PointerWithExposedProvenance` intrinsics, plus
scalar-interface `Call` terminators (`terminatorInProgOk`):
* return local `_0` is scalar (`scalarTypeOf`) and parameters `_1 .. _argCount`
  are non-pointer (`!isPtrTy`), preventing Anneal's un-namespaced
  `BorrowEntry.targetLocal : Nat` from resolving against a callee's own local
  slots across frames;
* temporaries are scalar or pointer/reference (`scalarTypeOf` or `isPtrTy`);
* provenance casts satisfy `provCastFlowOk body`;
* intra-frame and cross-call borrows satisfy
  `ptrAliasingProgOk (provCastAliasView body)` (disabling caller borrows across
  returning `Call`s because any callee root assignment `_k = rv` runs
  `invalidateConflictingBorrows` on the shared `s.memory.borrows` table). -/
def bodyInProgFragmentWithIntrinsics (fnMap : FnMap)
    (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  (body.localDecls[0]? >>= (scalarTypeOf ·.ty)).isSome &&
  body.localDecls.all (localDeclOk body.layouts) &&
  ((body.localDecls.drop 1).take body.argCount).all (fun d => !isPtrTy d.ty) &&
  (body.localDecls.drop (body.argCount + 1)).all
    (fun d => (scalarTypeOf d.ty).isSome || isPtrTy d.ty) &&
  decide (body.basicBlocks ≠ []) &&
  (List.range body.basicBlocks.length).all (fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      !bb.isCleanup &&
      bb.statements.all (statementOkWithIntrinsics body.localDecls · body.layouts) &&
      terminatorInProgOk callees body blk bb.terminator
    | none => true) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  livenessOk body && tupleInitOk body &&
  provCastFlowOk body && ptrDeclLayoutsOk body && ptrAliasingProgOk (provCastAliasView body) &&
  (translateFnInProgWithIntrinsics fnMap body).isSome

/-- Decidable sound multi-function correspondence fragment unifying
`progInFragment` (multi-function `Call` + `Assume`) and
`inFragmentWithIntrinsics` (intra-frame pointers, references, reborrows,
`Transmute`, `Assume`, `PointerExposeProvenance`, and
`PointerWithExposedProvenance`). -/
def progInFragmentWithIntrinsics (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Bool :=
  let fnMap := fnNameMap entry callees
  ((entry :: callees).map (·.defPath)).Nodup &&
  (entry :: callees).all (bodyInProgFragmentWithIntrinsics fnMap callees) &&
  (match maxStackLocals entry callees with
   | some bound => decide (bound < 2 ^ 31)
   | none => false) &&
  (translateProgWithIntrinsics entry callees).isSome

theorem bodyInProgFragment_implies_withIntrinsics {fnMap : FnMap}
    {callees : List MirAst.CapturedMir} {body : MirAst.CapturedMir}
    (h : bodyInProgFragment fnMap callees body = true) :
    bodyInProgFragmentWithIntrinsics fnMap callees body = true := by
  simp only [bodyInProgFragment, bodyInProgFragmentWithIntrinsics,
    Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hsc⟩, h5⟩, hbbs⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, htr⟩ := h
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp htr
  obtain ⟨hnp_stmt, hnp⟩ := translateFnInProg_not_provCast hf
  have hlen_pos : 0 < body.localDecls.length := by
    simp only [decide_eq_true_eq] at h2; omega
  have hd0 : (body.localDecls[0]? >>= (scalarTypeOf ·.ty)).isSome = true := by
    have hd0_eq : body.localDecls[0]? = some body.localDecls[0] := List.getElem?_eq_getElem hlen_pos
    simp only [hd0_eq, Option.bind_eq_bind, Option.bind_some]
    exact hsc body.localDecls[0] (List.mem_of_getElem? hd0_eq)
  have hdeclOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true := by
    intro d hd
    simp [localDeclOk, hsc d hd]
  have hargs : ∀ d ∈ (body.localDecls.drop 1).take body.argCount, (!isPtrTy d.ty) = true := by
    intro d hd
    have hmem : d ∈ body.localDecls := List.mem_of_mem_drop (List.mem_of_mem_take hd)
    simp [isPtrTy_false_of_scalarTypeOf (hsc d hmem)]
  have htemps : ∀ d ∈ body.localDecls.drop (body.argCount + 1),
      ((scalarTypeOf d.ty).isSome || isPtrTy d.ty) = true := by
    intro d hd
    simp [hsc d (List.mem_of_mem_drop hd)]
  have hbbs_stmt : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      progStatementOk body.localDecls s body.layouts = true := by
    intro bb hbb s hs
    obtain ⟨blk, hblk, rfl⟩ := List.getElem_of_mem hbb
    have hb := hbbs blk (List.mem_range.mpr hblk)
    simp only [List.getElem?_eq_getElem hblk, Bool.and_eq_true, List.all_eq_true] at hb
    exact hb.1.2 s hs
  have hbbs' : ∀ blk ∈ List.range body.basicBlocks.length,
      (match body.basicBlocks[blk]? with
       | some bb =>
         !bb.isCleanup &&
         bb.statements.all (statementOkWithIntrinsics body.localDecls · body.layouts) &&
         terminatorInProgOk callees body blk bb.terminator
       | none => true) = true := by
    intro blk hblk
    have hb := hbbs blk hblk
    cases hget : body.basicBlocks[blk]? with
    | none => rfl
    | some bb =>
      simp only [hget, Bool.and_eq_true, List.all_eq_true] at hb ⊢
      exact ⟨⟨hb.1.1, fun s hs => by simp [statementOkWithIntrinsics, hb.1.2 s hs]⟩, hb.2⟩
  have htr' : (translateFnInProgWithIntrinsics fnMap body).isSome = true := by
    rw [translateFnInProgWithIntrinsics_eq_of_no_provCast fnMap body hnp_stmt, hf]
    rfl
  have hptr_sc := ptrAliasingProgOk_of_scalar body hsc hbbs_stmt
  have hdlo : ptrDeclLayoutsOk body = true := by
    simp only [ptrAliasingProgOk, Bool.and_eq_true] at hptr_sc
    exact hptr_sc.1.1.1.1
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hd0⟩, hdeclOk⟩, hargs⟩, htemps⟩, h5⟩, hbbs'⟩,
    h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, provCastFlowOk_of_not_hasProvCast hnp⟩, hdlo⟩, ?_⟩, htr'⟩
  rw [provCastAliasView_of_not_hasProvCast hnp]
  exact hptr_sc

theorem translateProgWithIntrinsics_eq_of_progInFragment
    {entry : MirAst.CapturedMir} {callees : List MirAst.CapturedMir}
    (h : progInFragment entry callees = true) :
    translateProgWithIntrinsics entry callees = translateProg entry callees := by
  simp only [progInFragment, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := h
  apply translateProgWithIntrinsics_eq_of_no_provCast
  intro b hb
  have hbf := hall b hb
  simp only [bodyInProgFragment, Bool.and_eq_true] at hbf
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hbf.2
  exact (translateFnInProg_not_provCast hf).1

theorem progInFragment_implies_progInFragmentWithIntrinsics
    {entry : MirAst.CapturedMir} {callees : List MirAst.CapturedMir}
    (h : progInFragment entry callees = true) :
    progInFragmentWithIntrinsics entry callees = true := by
  have htr_eq := translateProgWithIntrinsics_eq_of_progInFragment h
  simp only [progInFragment, progInFragmentWithIntrinsics,
    Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hnodup, hall⟩, hstack⟩, htr⟩ := h
  exact ⟨⟨⟨hnodup, fun b hb => bodyInProgFragment_implies_withIntrinsics (hall b hb)⟩,
    hstack⟩, by rwa [htr_eq]⟩

/-- Multi-function Tree Borrows single-expose-site discipline: every function
body in `entry :: callees` satisfies `singleExposeSiteOk`, ensuring no single
live stack frame executes `PointerExposeProvenance` more than once on the same
local allocation (e.g. before and after a scalar `Call` in the same caller
frame, after `ptrTermStep` forces a fresh borrow), while allowing both caller
and callee frames to each execute `PointerExposeProvenance` on their own
frame-local allocations (since a callee's stack allocation is deallocated on
`Return`). -/
def progSingleExposeSiteOk (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Bool :=
  (entry :: callees).all singleExposeSiteOk

theorem progSingleExposeSiteOk_nil (body : MirAst.CapturedMir) :
    progSingleExposeSiteOk body [] = singleExposeSiteOk body := by
  simp [progSingleExposeSiteOk]

theorem progInFragment_implies_progSingleExposeSiteOk
    {entry : MirAst.CapturedMir} {callees : List MirAst.CapturedMir}
    (h : progInFragment entry callees = true) :
    progSingleExposeSiteOk entry callees = true := by
  simp only [progInFragment, progSingleExposeSiteOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := h
  intro b hb
  have hbf := hall b hb
  simp only [bodyInProgFragment, Bool.and_eq_true] at hbf
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hbf.2
  exact singleExposeSiteOk_of_not_hasProvCast (translateFnInProg_not_provCast hf).2

theorem inFragment_implies_progSingleExposeSiteOk {body : MirAst.CapturedMir}
    (h : inFragment body = true) :
    progSingleExposeSiteOk body [] = true := by
  rw [progSingleExposeSiteOk_nil]
  exact singleExposeSiteOk_of_not_hasProvCast (inFragment_not_hasProvCast h)

/-- Per-statement syntactic well-formedness for cross-frame pointer/reference
translation (`progCrossFrameTranslatable`): admits `statementOkWithIntrinsics`
plus `Retag([fn entry], _i)` strictly on reference parameter locals (`isRefTy`,
`1 ≤ i ≤ argCount`). Raw pointer parameters (`*const T` / `*mut T`) are excluded
because Anneal's `.retag .fnEntry` attaches a strong borrow protector to any
`.ptr` slot (`Statements.lean`), whereas MiniRust's `Validate` on `PtrType::Raw`
is a no-op. -/
def progStmtOkWithIntrinsics (argCount : Nat) (decls : List MirAst.LocalDecl)
    (s : MirAst.Statement) (layouts : Layout.LayoutTable := ⟨64, true, []⟩) : Bool :=
  statementOkWithIntrinsics decls s layouts ||
  match s.kind with
  | .retag .fnEntry ⟨i, []⟩ =>
    decide (1 ≤ i ∧ i ≤ argCount) && decide (i < decls.length) &&
    match decls[i]? with
    | some d => isRefTy d.ty
    | none => false
  | _ => false

/-- Syntactic per-body translatability check for multi-function programs that
also pass pointer or reference arguments/returns across `Call` boundaries
(`callTerminatorOkWithIntrinsics`, `progStmtOkWithIntrinsics`). Such cross-frame
pointer/reference programs translate cleanly to MiniRust (`Mach` and `MachTB`)
via `translateProgWithIntrinsics`, but lie outside the sound Anneal–MiniRust
correspondence fragment `progInFragmentWithIntrinsics` because Anneal's
`BorrowEntry.targetLocal : Nat` is un-namespaced across frames. -/
def bodyCrossFrameTranslatable (fnMap : FnMap)
    (callees : List MirAst.CapturedMir) (body : MirAst.CapturedMir) : Bool :=
  let addrLocals := bodyAddrTakenLocals body
  body.isRuntimePostCleanup &&
  decide (body.argCount + 1 ≤ body.localDecls.length) &&
  decide (body.localDecls.length < 2 ^ 31) &&
  body.localDecls.all (localDeclOk body.layouts) &&
  decide (body.basicBlocks ≠ []) &&
  (List.range body.basicBlocks.length).all (fun blk =>
    match body.basicBlocks[blk]? with
    | some bb =>
      !bb.isCleanup &&
      bb.statements.all (progStmtOkWithIntrinsics body.argCount body.localDecls · body.layouts) &&
      bb.statements.all (stmtPreservesAddrTaken addrLocals) &&
      termPreservesAddrTaken addrLocals bb.terminator &&
      terminatorInProgOkWithIntrinsics callees body blk bb.terminator
    | none => true) &&
  addrLocals.all (fun k => decide (1 ≤ k ∧ k ≤ body.argCount)) &&
  storageDeadOk body && movesOk body && mentionsOk body &&
  livenessOk body && tupleInitOk body &&
  (translateFnInProgWithIntrinsics fnMap body).isSome

/-- Decidable syntactic translatability check for multi-function programs
including cross-frame pointer/reference arguments, `Retag(FnEntry)` on reference
parameters, `Assume`, and provenance-cast intrinsics. Strictly contains
`progInFragmentWithIntrinsics`
(`progInFragmentWithIntrinsics_implies_progCrossFrameTranslatable`). -/
def progCrossFrameTranslatable (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Bool :=
  let fnMap := fnNameMap entry callees
  ((entry :: callees).map (·.defPath)).Nodup &&
  (entry :: callees).all (bodyCrossFrameTranslatable fnMap callees) &&
  (match maxStackLocals entry callees with
   | some bound => decide (bound < 2 ^ 31)
   | none => false) &&
  (translateProgWithIntrinsics entry callees).isSome

private theorem directBorrowOf_provCastAliasStmt (s : MirAst.Statement) :
    (match (provCastAliasStmt s).kind with
     | .assign _ rv => Option.map (fun x : MirAst.Mutability × MirAst.Place => x.snd.local_) (directBorrowOf rv)
     | _ => none) =
    (match s.kind with
     | .assign _ rv => Option.map (fun x : MirAst.Mutability × MirAst.Place => x.snd.local_) (directBorrowOf rv)
     | _ => none) := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck <;> rfl
    | _ => rfl
  | _ => rfl

private theorem bodyAddrTakenLocals_provCastAliasView (body : MirAst.CapturedMir) :
    bodyAddrTakenLocals (provCastAliasView body) = bodyAddrTakenLocals body := by
  unfold provCastAliasView
  split
  · unfold bodyAddrTakenLocals
    simp only [List.flatMap_map, List.filterMap_map, Function.comp_def]
    congr 1; funext a; congr 1; funext x
    exact directBorrowOf_provCastAliasStmt x
  · rfl

private theorem stmtPreservesAddrTaken_provCastAliasStmt (addrLocals : List Nat)
    (s : MirAst.Statement) :
    stmtPreservesAddrTaken addrLocals (provCastAliasStmt s) =
      stmtPreservesAddrTaken addrLocals s := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck <;> rfl
    | _ => rfl
  | _ => rfl

theorem bodyInProgFragmentWithIntrinsics_implies_crossFrameTranslatable
    {fnMap : FnMap} {callees : List MirAst.CapturedMir} {body : MirAst.CapturedMir}
    (h : bodyInProgFragmentWithIntrinsics fnMap callees body = true) :
    bodyCrossFrameTranslatable fnMap callees body = true := by
  simp only [bodyInProgFragmentWithIntrinsics, bodyCrossFrameTranslatable,
    Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, h5⟩, _⟩, _⟩, h8⟩, hbbs⟩,
    h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, _⟩, _⟩, hptr⟩, htr⟩ := h
  simp only [ptrAliasingProgOk, bodyAddrTakenLocals_provCastAliasView, Bool.and_eq_true,
    List.all_eq_true] at hptr
  obtain ⟨⟨⟨⟨_, hat_arg⟩, hpres⟩, _⟩, _⟩ := hptr
  have hat_arg' : ∀ k ∈ bodyAddrTakenLocals body, decide (1 ≤ k ∧ k ≤ body.argCount) = true := by
    intro k hk
    have hk' := hat_arg k hk
    unfold provCastAliasView at hk'
    split at hk' <;> exact hk'
  have hpres_body : ∀ bb ∈ body.basicBlocks,
      (∀ s ∈ bb.statements, stmtPreservesAddrTaken (bodyAddrTakenLocals body) s = true) ∧
      termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator = true := by
    intro bb hbb
    unfold provCastAliasView at hpres
    split at hpres
    · have hp := hpres { bb with statements := bb.statements.map provCastAliasStmt }
        (List.mem_map_of_mem hbb)
      refine ⟨fun s hs => ?_, hp.2⟩
      rw [← stmtPreservesAddrTaken_provCastAliasStmt]
      exact hp.1 _ (List.mem_map_of_mem hs)
    · exact hpres bb hbb
  have hbbs' : ∀ blk ∈ List.range body.basicBlocks.length,
      (match body.basicBlocks[blk]? with
       | some bb =>
         !bb.isCleanup &&
         bb.statements.all (progStmtOkWithIntrinsics body.argCount body.localDecls · body.layouts) &&
         bb.statements.all (stmtPreservesAddrTaken (bodyAddrTakenLocals body)) &&
         termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator &&
         terminatorInProgOkWithIntrinsics callees body blk bb.terminator
       | none => true) = true := by
    intro blk hblk
    have hb := hbbs blk hblk
    cases hget : body.basicBlocks[blk]? with
    | none => rfl
    | some bb =>
      obtain ⟨hsp, htp⟩ := hpres_body bb (List.mem_of_getElem? hget)
      simp only [hget, Bool.and_eq_true, List.all_eq_true] at hb ⊢
      exact ⟨⟨⟨⟨hb.1.1, fun s hs => by simp [progStmtOkWithIntrinsics, hb.1.2 s hs]⟩,
        hsp⟩, htp⟩, terminatorInProgOkWithIntrinsics_of_terminatorInProgOk hb.2⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h8⟩, hbbs'⟩, hat_arg'⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, htr⟩

theorem progInFragmentWithIntrinsics_implies_progCrossFrameTranslatable
    {entry : MirAst.CapturedMir} {callees : List MirAst.CapturedMir}
    (h : progInFragmentWithIntrinsics entry callees = true) :
    progCrossFrameTranslatable entry callees = true := by
  simp only [progInFragmentWithIntrinsics, progCrossFrameTranslatable,
    Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hnodup, hall⟩, hstack⟩, htr⟩ := h
  exact ⟨⟨⟨hnodup, fun b hb => bodyInProgFragmentWithIntrinsics_implies_crossFrameTranslatable (hall b hb)⟩,
    hstack⟩, htr⟩



/-- `Function::check_next_block` (`spec/lang/well-formed.md`):
> "fn check_next_block(self, expected_block_kind: BbKind, next_block_name: BbName) -> Result<()> {
>      let Some(next_block) = self.blocks.get(next_block_name) else {
>          throw_ill_formed!(\"Terminator: next block does not exist\");
>      };
>      ensure_wf(
>          next_block.kind == expected_block_kind,
>          \"Terminator: next block has the wrong block kind\",
>      )?;
>      ret(())
>  }" -/
def checkNextBlock (f : Gen.Function) (expectedKind : Gen.BbKind) (nextBb : Gen.BbName) : Bool :=
  match Interp.mapGet f.blocks nextBb with
  | some bb => bb.kind == expectedKind
  | none => false

/-- `Function::check_unwind_block` (`spec/lang/well-formed.md`):
> "fn check_unwind_block(self, current_block_kind: BbKind, unwind_block_name: BbName) -> Result<()> {
>      let expected_block_kinds = match current_block_kind {
>          BbKind::Regular => list![BbKind::Cleanup, BbKind::Catch],
>          BbKind::Cleanup | BbKind::Terminate => list![BbKind::Terminate],
>          BbKind::Catch => throw_ill_formed!(\"Terminator: unwinding is not allowed in a catch block\"),
>      };
>      let Some(unwind_block) = self.blocks.get(unwind_block_name) else {
>          throw_ill_formed!(\"Terminator: unwind block does not exist\");
>      };
>      ensure_wf(
>          expected_block_kinds.any(|kind| kind == unwind_block.kind),
>          \"Terminator: unwind block has the wrong block kind\",
>      )?;
>      ret(())
>  }" -/
def checkUnwindBlock (f : Gen.Function) (curKind : Gen.BbKind) (unwindBb : Gen.BbName) : Bool :=
  match curKind, Interp.mapGet f.blocks unwindBb with
  | .Regular, some bb => bb.kind == .Cleanup || bb.kind == .Catch
  | .Cleanup, some bb | .Terminate, some bb => bb.kind == .Terminate
  | _, _ => false

/-- Local-scoping clauses of `Statement::check_wf` (`spec/lang/well-formed.md`):
`StorageLive` and `StorageDead` reference declared locals in `f.locals`, and
`StorageDead` never targets `f.ret` or an argument in `f.args`. -/
def stmtCfgWf (f : Gen.Function) : Gen.Statement → Bool
  | .StorageLive l => (Interp.mapGet f.locals l).isSome
  | .StorageDead l =>
    (Interp.mapGet f.locals l).isSome && l != f.ret && !f.args.contains l
  | _ => true

/-- Block-kind and CFG-target clauses of `Terminator::check_wf` across all nine
`Terminator` variants (`spec/lang/well-formed.md`):
> "Return => {
>      ensure_wf(block_kind == BbKind::Regular, \"Terminator::Return has to be called in a regular block\")?;
>  }
>  ..
>  StopUnwind(next_block) => {
>      ensure_wf(block_kind == BbKind::Catch, \"Terminator::StopUnwind has to be called in a catch block\")?;
>      func.check_next_block(BbKind::Regular, next_block)?;
>  }
>  ResumeUnwind => {
>      ensure_wf(block_kind == BbKind::Cleanup, \"Terminator::ResumeUnwind: has to be called in cleanup block\")?;
>  }" -/
def termCfgWf (f : Gen.Function) (blockKind : Gen.BbKind) : Gen.Terminator → Bool
  | .Goto next => checkNextBlock f blockKind next
  | .Switch _ cases fallback =>
    cases.entries.all (fun p => checkNextBlock f blockKind p.2) &&
    checkNextBlock f blockKind fallback
  | .Unreachable => true
  | .Intrinsic (.AtomicFetchAndOp op) _ _ next =>
    (op == .Add || op == .Sub) &&
    match next with
    | some nb => checkNextBlock f blockKind nb
    | none => true
  | .Intrinsic _ _ _ next =>
    match next with
    | some nb => checkNextBlock f blockKind nb
    | none => true
  | .Call _ _ _ _ next unwind =>
    (match next with | some nb => checkNextBlock f blockKind nb | none => true) &&
    (match unwind with | some ub => checkUnwindBlock f blockKind ub | none => true)
  | .Return => blockKind == .Regular
  | .StartUnwind _ unwind => blockKind == .Regular && checkUnwindBlock f blockKind unwind
  | .StopUnwind next => blockKind == .Catch && checkNextBlock f .Regular next
  | .ResumeUnwind => blockKind == .Cleanup

/-- Function local-map and CFG well-formedness check matching `Function::check_wf`
(`spec/lang/well-formed.md`): distinct `locals` and `blocks` keys, declared and
pairwise distinct `ret :: args`, a `Regular` `start` block in `f.blocks`, and
`stmtCfgWf` + `termCfgWf` on every basic block. -/
def funcCfgWf (f : Gen.Function) : Bool :=
  decide (f.locals.entries.map Prod.fst).Nodup &&
  decide (f.blocks.entries.map Prod.fst).Nodup &&
  (Interp.mapGet f.locals f.ret).isSome &&
  f.args.all (fun a => (Interp.mapGet f.locals a).isSome) &&
  decide (f.ret :: f.args).Nodup &&
  checkNextBlock f .Regular f.start &&
  f.blocks.entries.all fun ⟨_, bb⟩ =>
    bb.statements.all (stmtCfgWf f) &&
    termCfgWf f bb.kind bb.terminator

/-- Program function-table, CFG, and `start`-wrapper well-formedness check
matching `Program::check_wf` (`spec/lang/well-formed.md`):
> "// Check all the functions.
>  for function in self.functions.values() {
>      function.check_wf::<T>(self)?;
>  }
>
>  // Ensure the start function exists, has the right ABI, takes no arguments, and returns a 1-ZST.
>  let Some(start) = self.functions.get(self.start) else {
>      throw_ill_formed!(\"Program: start function does not exist\");
>  };
>  ensure_wf(start.calling_convention == CallingConvention::C, \"Program: start function has invalid calling convention\")?;
>  let ret_layout = start.locals[start.ret].layout::<T>();
>  ensure_wf(
>      ret_layout == LayoutStrategy::Sized(Size::ZERO, Align::ONE),
>      \"Program: start function return local has invalid layout\"
>  )?;
>  ensure_wf(start.args.is_empty(), \"Program: start function has arguments\")?;" -/
def progWf (p : Gen.Program) : Bool :=
  decide (p.functions.entries.map Prod.fst).Nodup &&
  p.functions.entries.all (fun ⟨_, f⟩ => funcCfgWf f) &&
  match Interp.mapGet p.functions p.start with
  | some start =>
    start.calling_convention == .C &&
    start.args.isEmpty &&
    match Interp.mapGet start.locals start.ret with
    | some retTy =>
      match Interp.Type.layout retTy with
      | .ok (.Sized sz align) => sz == ⟨0⟩ && align == ⟨1⟩
      | _ => false
    | none => false
  | none => false

end MiniRustSpec.Correspondence
