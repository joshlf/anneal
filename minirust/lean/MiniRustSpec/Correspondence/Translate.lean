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

* the body is `Runtime(PostCleanup)` MIR and declares only the return place and
  the arguments (`localDecls.length = argCount + 1`); the return place `_0` has
  scalar integer type, and each local has either scalar integer type,
  homogeneous 1D integer array type `[T; N]` whose total byte size
  `N * size_of::<T>()` fits in signed 64-bit `isize` (`< 2^63`), or well-formed
  tuple / single-variant struct type (`RigidTy.tuple` or `RigidTy.adt`) with
  explicit layout offsets and padding (`FieldsShape.arbitrary`, `VariantsShape.single 0`);
* scalar places are an unprojected integer local `_j`, a single-element
  array indexing projection `_j[proj]` (`ProjectionElem.index _k` or
  `ProjectionElem.constantIndex offset minLen fromEnd` satisfying `projOk`), or
  a (possibly nested) field projection chain `_j.f1...fk` (`ProjectionElem.field`),
  and scalar operands are `copy p` of a scalar place `p` or an integer constant;
* statements are:
  - scalar assignments `dst = rv` to a scalar place `dst` (`_i`, `_i[proj]`, or
    `_i.f1...fk`), where `rv` is `Use(a)`, `UnaryOp(uop, a)` (`uop ∈ {Neg, Not}`),
    `BinaryOp(op, a, b)` (`op` among the 15 integer `BinOp` variants, with `b`
    of `dst`'s integer type `it` or of any integer type `rhsIt` for the shift
    operators `Shl, Shr, ShlUnchecked, ShrUnchecked`),
    `Cast(IntToInt, a, targetTy)`, or `Len(_j)` of an array local `_j` (into a
    `usize` destination);
  - array assignments `_i = rv` to an unprojected array local `_i : [T; N]`,
    where `rv` is `Use(copy _j)` of an array local of the same type,
    `Aggregate(Array(T), [op_0, .., op_{N-1}])`, or `Repeat(op, N)` with `N > 0`
    (or `N = 0` when `op` is a constant);
  - tuple and single-variant struct assignments `dst = rv` to a tuple/struct
    place `dst` (`_i` or nested tuple/struct field `_i.f1...fk`), where `rv` is
    `Use(copy p)` of a tuple/struct place of matching layout or
    `Aggregate(Tuple | Adt(_, 0, None), [op_0, .., op_{M-1}])`;
  - `PlaceMention(_i)` of an unprojected local `_i`;
* terminators are `Goto`, `SwitchInt` on any scalar integer operand (`copy p`
  or constant), `Unreachable`, or `Return`, and every jump target is a block of
  the body;
* no block is a cleanup block.

`Operand::Move`, `Repeat(copy p, 0)`, and projected `PlaceMention(_j[proj])`
are excluded on purpose because `minimize` and Anneal's MIR semantics genuinely
differ on them (`minimize` translates `Move` as `Load`, drops the operand of
`list![op; 0]`, and evaluates projections in `PlaceMention`); `minirust/README.md`
lists these and the other gaps.
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
is a tuple (`RigidTy.tuple`) or single-variant struct (`RigidTy.adt`). -/
def tupleTypeOf (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (t : MirAst.Ty) :
    Option (List (Nat × TupleSpec) × Nat × Nat) :=
  match t.kind with
  | .tuple _ | .adt _ _ =>
    match specOfRigidTy layouts t.kind t.layoutIdx with
    | some (.tuple fields size align) => some (fields, size, align)
    | _ => none
  | _ => none

/-- `minimize`'s type translation for scalar integers, tuples, single-variant
structs, and homogeneous arrays (`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Int(t) => {
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
  match intTypeOf t with
  | some it => some (.Int it)
  | none =>
    match arrayTypeOf t with
    | some (elemIt, count) => some (.Array (.Int elemIt) (Int.ofNat count))
    | none =>
      match tupleTypeOf layouts t with
      | some (fields, size, align) =>
        some ((TupleSpec.tuple fields size align).toMiniRustTy)
      | none => none

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- Left-to-right fold translating a chain of `ProjectionElem.field` projections
into nested `PlaceExpr.Field` expressions (`tooling/minimize/src/rvalue.rs`):
> "smir::ProjectionElem::Field(f, _ty) => {
>      let indirected = GcCow::new(expr);
>      PlaceExpr::Field { root: indirected, field: (*f).into() }
>  }" -/
def translateFieldPlace (root : Gen.PlaceExpr) :
    List MirAst.ProjectionElem → Option Gen.PlaceExpr
  | [] => some root
  | .field idx _ :: rest => translateFieldPlace (.Field root (Int.ofNat idx)) rest
  | _ => none

/-- `minimize`'s place translation for locals, field projections, and array
indexing (`tooling/minimize/src/rvalue.rs`):
> "let expr = PlaceExpr::Local(self.local_name_map[&place.local.into()]);
>  ..
>  smir::ProjectionElem::Field(f, _ty) => {
>      let indirected = GcCow::new(expr);
>      PlaceExpr::Field { root: indirected, field: (*f).into() }
>  }
>  ..
>  smir::ProjectionElem::Index(loc) => {
>      let i = PlaceExpr::Local(self.local_name_map[&(*loc).into()]);
>      let i = GcCow::new(i);
>      let i = ValueExpr::Load { source: i };
>      let i = GcCow::new(i);
>      let root = GcCow::new(expr);
>      PlaceExpr::Index { root, index: i }
>  }
>  ..
>  smir::ProjectionElem::ConstantIndex { .. }
>  | smir::ProjectionElem::Subslice { .. }
>  | smir::ProjectionElem::OpaqueCast(_) => {
>      rs::span_bug!(span, \"Place Projection not supported: {:?}\", proj);
>  }"
Upstream `minimize` rejects `ProjectionElem::ConstantIndex`, so its lowering
here is an extension rather than a transcription: for
`ConstantIndex { offset, min_length, from_end }` on a fixed-size array
`[T; count]`, the index that MIR defines for the projection (`count - offset`
when `from_end` is true, or `offset` when `from_end` is false) becomes a
`usize` constant index expression of `PlaceExpr::Index`. -/
def translatePlace (decls : List MirAst.LocalDecl) : MirAst.Place → Option Gen.PlaceExpr
  | ⟨i, []⟩ => some (.Local (localName i))
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

/-- Scalar integer type of a place (`_j`, `_j[idx]` / `_j[constIdx]`, or
`_j.f1...fk`). -/
def placeIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Place → Option Gen.IntType
  | ⟨j, []⟩ => decls[j]? >>= fun d => intTypeOf d.ty
  | ⟨j, [.index _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | ⟨j, [.constantIndex _ _ _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | ⟨j, .field idx fieldTy :: rest⟩ => do
    let d ← decls[j]?
    let (fields, size, align) ← tupleTypeOf layouts d.ty
    let (_, leafSpec) ←
      resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest)
    match leafSpec with
    | .scalar it => some it
    | .tuple _ _ _ => none
  | _ => none

/-- Type of a fragment scalar operand: `copy p` has `p`'s resolved scalar type;
a constant carries its type. -/
def operandIntType (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy p => placeIntType layouts decls p
  | .constant c => intTypeOf c.ty
  | _ => none

/-- `minimize`'s operand translation (`tooling/minimize/src/rvalue.rs`):
> "smir::Operand::Constant(c) => self.translate_const_smir(&c.const_, span),
>  smir::Operand::Copy(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },"
for places in the fragment (`PlaceExpr::Local`, `PlaceExpr::Field`, and
`PlaceExpr::Index`) and integer scalar constants
(`Constant::Int(int_from_bits(..))` at the constant's type). -/
def translateOperand (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.ValueExpr
  | .copy p => (translatePlace decls p).map .Load
  | .constant c =>
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

/-- `minimize`'s rvalue translation for `Use`, `UnaryOp(Neg | Not)` on
integers, `BinaryOp`, `Aggregate(Tuple | Adt | Array)`, `Len`, `Repeat`, and
`Cast(CastKind::IntToInt)` on integers (`tooling/minimize/src/rvalue.rs`):
> "match rv {
>      smir::Rvalue::Use(operand) => self.translate_operand_smir(operand, span),
>      smir::Rvalue::BinaryOp(bin_op, l, r) => {
>          ..
>          let l = self.translate_operand_smir(l, span);
>          let r = self.translate_operand_smir(r, span);
>          ..
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
>              ..
>          }
>      }
>      ..
>      smir::Rvalue::Aggregate(agg, operands) => {
>          ..
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
>                      ..
>                  };
>                  ValueExpr::UnOp {
>                      operator: UnOp::Cast(CastOp::IntToInt(int_ty)),
>                      operand: GcCow::new(operand),
>                  }
>              }"
where `build::neg(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::Neg), operand: x }`
and `build::bit_not(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::BitNot), operand: x }`. -/
def translateRvalue (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty := none) :
    MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand decls op
  | .unaryOp uop op => do
    let iuop ← translateUnOp uop
    pure (.UnOp (.Int iuop) (← translateOperand decls op))
  | .binaryOp op l r => do
    let iop ← translateBinOp op
    pure (.BinOp (.Int iop) (← translateOperand decls l) (← translateOperand decls r))
  | .cast .intToInt op castTy => do
    let intTy ← intTypeOf castTy
    let operand ← translateOperand decls op
    pure (.UnOp (.Cast (.IntToInt intTy)) operand)
  | .aggregate (.array elemTy) ops => do
    let elemIt ← intTypeOf elemTy
    let exprs ← ops.mapM (translateOperand decls)
    pure (.Tuple exprs (.Array (.Int elemIt) (Int.ofNat ops.length)))
  | .aggregate .tuple ops => do
    let dstTy ← targetTy
    let (fields, size, align) ← tupleTypeOf layouts dstTy
    let exprs ← ops.mapM (translateOperand decls)
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
  | _ => none

/-- `minimize`'s statement translation for assignments and `PlaceMention`
(`tooling/minimize/src/bb.rs`):
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
outside the fragment, and `PlaceMention` is restricted to unprojected locals
`⟨i, []⟩` because Anneal's `.placeMention` checks only `place.local_` and
ignores `place.projection`. -/
def translateStatement (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (s : MirAst.Statement) :
    Option Gen.Statement :=
  match s.kind with
  | .assign dst rv => do
    let destination ← translatePlace decls dst
    let source ← translateRvalue layouts decls (placeMirTy decls dst) rv
    pure (.Assign destination source)
  | .placeMention ⟨i, []⟩ => some (.PlaceMention (.Local (localName i)))
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

/-- `minimize`'s terminator translation (`tooling/minimize/src/bb.rs`):
> "rs::TerminatorKind::Return => Terminator::Return,
>  rs::TerminatorKind::Goto { target } => Terminator::Goto(self.bb_name_map[&target]),
>  ..
>  rs::TerminatorKind::SwitchInt { discr, targets } => {
>      ..
>      let cases = targets .. .collect();
>      let fallback_block = targets.otherwise();
>      let fallback = self.bb_name_map[&fallback_block];
>      Terminator::Switch { value, cases, fallback }
>  }
>  rs::TerminatorKind::Unreachable => Terminator::Unreachable,"
restricted to integer-typed `switchInt` discriminants (for `bool`, `minimize`
inserts a transmute to `u8`, which is outside this fragment). -/
def translateTerminator (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (t : MirAst.Terminator) :
    Option Gen.Terminator :=
  match t.kind with
  | .goto target => some (.Goto (bbName target))
  | .switchInt discr targets => do
    let v ← translateOperand decls discr
    let it ← operandIntType layouts decls discr
    pure (.Switch v (switchCases it targets.branches) (bbName targets.otherwise))
  | .unreachable => some .Unreachable
  | .return_ => some .Return
  | _ => none

/-- `minimize`'s basic-block translation; fragment blocks are not cleanup blocks,
so their kind is `BbKind::Regular`. -/
def translateBlock (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (bb : MirAst.BasicBlockData) :
    Option Gen.BasicBlock := do
  let stmts ← bb.statements.mapM (translateStatement layouts decls)
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
  let locals ← translateLocals body.layouts 0 body.localDecls
  let blocks ← translateBlocks body.layouts body.localDecls 0 body.basicBlocks
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

/-- A scalar place of integer type `it`: an unprojected scalar local `_j`,
a (possibly nested) field projection `_j.f1...fk`, or an indexed element
`_j[proj]` of a homogeneous array local. -/
def placeOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Place → Bool
  | ⟨j, []⟩ =>
    decide (j < decls.length) && decide ((decls[j]? >>= (intTypeOf ·.ty)) = some it)
  | ⟨j, .field idx fieldTy :: rest⟩ =>
    decide (j < decls.length) &&
    match decls[j]? >>= (tupleTypeOf layouts ·.ty) with
    | some (fields, size, align) =>
      match resolveFieldPath layouts (.tuple fields size align) (.field idx fieldTy :: rest) with
      | some (_, .scalar leafIt) => decide (leafIt = it)
      | _ => false
    | none => false
  | ⟨j, [proj]⟩ =>
    decide (j < decls.length) &&
    match decls[j]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) => decide (elemIt = it) && projOk decls count proj
    | none => false
  | _ => false

/-- A scalar integer operand of type `it`. -/
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
    | none => false
  | .len ⟨j, []⟩ =>
    decide (it = usizeIt) &&
    decide (j < decls.length) &&
    (decls[j]? >>= (arrayTypeOf ·.ty)).isSome
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

/-- Fragment statements, type-checked against the destination's type. -/
def statementOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      match intTypeOf d.ty with
      | some it => rvalueOk layouts decls it rv
      | none =>
        match arrayTypeOf d.ty with
        | some (elemIt, count) => arrayRvalueOk layouts decls elemIt count rv
        | none =>
          match tupleTypeOf layouts d.ty with
          | some (fields, size, align) =>
            tupleRvalueOk layouts decls d.ty fields size align rv
          | none => false
  | .assign ⟨i, .field idx fieldTy :: rest⟩ rv =>
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
  | .assign ⟨i, [proj]⟩ rv =>
    match decls[i]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) =>
      projOk decls count proj && rvalueOk layouts decls elemIt rv
    | none => false
  | .placeMention ⟨i, []⟩ => decide (i < decls.length)
  | _ => false

/-- Fragment terminators; jump targets must be blocks of the body and
`switchInt` values must be distinct in-range bit patterns of the
discriminant's type. -/
def terminatorOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩)
    (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match operandIntType layouts decls discr with
    | some it =>
      operandOk layouts decls it discr &&
      targets.branches.all (fun p => decide (p.1 < 2 ^ (8 * it.size.bytes)) && decide (p.2 < nblocks)) &&
      (targets.branches.map Prod.fst).Nodup &&
      decide (targets.otherwise < nblocks)
    | none => false
  | .unreachable => true
  | .return_ => true
  | _ => false

/-- Well-formedness of a local declaration in the fragment: a scalar integer,
a homogeneous 1D integer array whose byte size fits in signed 64-bit `isize`
(`< 2 ^ 63`), or a well-formed tuple / single-variant struct. -/
def localDeclOk (layouts : Layout.LayoutTable := ⟨64, true, []⟩) (d : MirAst.LocalDecl) : Bool :=
  (intTypeOf d.ty).isSome ||
  match arrayTypeOf d.ty with
  | some (elemIt, count) => decide (count * elemIt.size.bytes < 2 ^ 63)
  | none =>
    match tupleTypeOf layouts d.ty with
    | some (fields, size, align) => (TupleSpec.tuple fields size align).wf
    | none => false

/-- The decidable fragment on which the correspondence theorem is stated. -/
def inFragment (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.localDecls.length = body.argCount + 1) &&
  (body.localDecls[0]? >>= (intTypeOf ·.ty)).isSome &&
  body.localDecls.all (localDeclOk body.layouts) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.layouts body.localDecls) &&
    terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator) &&
  (translateFn body).isSome

end MiniRustSpec.Correspondence
