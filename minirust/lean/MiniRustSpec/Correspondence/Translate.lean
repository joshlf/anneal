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
  scalar integer type, and each local has either scalar integer type or
  homogeneous 1D integer array type `[T; N]` whose total byte size
  `N * size_of::<T>()` fits in signed 64-bit `isize` (`< 2^63`);
* scalar places are either an unprojected integer local `_j` or a single-element
  array indexing projection `_j[proj]` (`ProjectionElem.index _k` or
  `ProjectionElem.constantIndex offset minLen fromEnd` satisfying `projOk`),
  and scalar operands are `copy p` of a scalar place `p` or an integer constant;
* statements are:
  - scalar assignments `dst = rv` to a scalar place `dst` (`_i` or `_i[proj]`),
    where `rv` is `Use(a)`, `UnaryOp(uop, a)` (`uop ∈ {Neg, Not}`),
    `BinaryOp(op, a, b)` (`op` among the 15 integer `BinOp` variants, with `b`
    of `dst`'s integer type `it` or of any integer type `rhsIt` for the shift
    operators `Shl, Shr, ShlUnchecked, ShrUnchecked`),
    `Cast(IntToInt, a, targetTy)`, or `Len(_j)` of an array local `_j` (into a
    `usize` destination);
  - array assignments `_i = rv` to an unprojected array local `_i : [T; N]`,
    where `rv` is `Use(copy _j)` of an array local of the same type,
    `Aggregate(Array(T), [op_0, .., op_{N-1}])`, or `Repeat(op, N)` with `N > 0`
    (or `N = 0` when `op` is a constant);
  - `PlaceMention(_i)` of an unprojected scalar or array local `_i`;
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

/-- `minimize`'s type translation for scalar integers and homogeneous arrays
(`tooling/minimize/src/ty.rs`):
> "rs::TyKind::Int(t) => {
>      let sz = rs::abi::Integer::from_int_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Signed })
>  }
>  rs::TyKind::Uint(t) => {
>      let sz = rs::abi::Integer::from_uint_ty(&self.tcx, *t).size();
>      Type::Int(IntType { size: translate_size(sz), signed: Signedness::Unsigned })
>  }
>  ..
>  rs::TyKind::Array(ty, c) => {
>      let count = Int::from(c.try_to_target_usize(self.tcx).unwrap());
>      let elem = GcCow::new(self.translate_ty(*ty, span));
>      Type::Array { elem, count }
>  }" -/
def translateTy (t : MirAst.Ty) : Option Gen.Type :=
  match intTypeOf t with
  | some it => some (.Int it)
  | none =>
    match arrayTypeOf t with
    | some (elemIt, count) => some (.Array (.Int elemIt) (Int.ofNat count))
    | none => none

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- `minimize`'s place translation for locals and array indexing
(`tooling/minimize/src/rvalue.rs`):
> "let expr = PlaceExpr::Local(self.local_name_map[&place.local.into()]);
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
  | _ => none

/-- Scalar integer type of a place (`_j` or `_j[idx]` / `_j[constIdx]`). -/
def placeIntType (decls : List MirAst.LocalDecl) : MirAst.Place → Option Gen.IntType
  | ⟨j, []⟩ => decls[j]? >>= fun d => intTypeOf d.ty
  | ⟨j, [.index _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | ⟨j, [.constantIndex _ _ _]⟩ => decls[j]? >>= fun d => (arrayTypeOf d.ty).map Prod.fst
  | _ => none

/-- Type of a fragment scalar operand: `copy p` has `p`'s resolved scalar type;
a constant carries its type. -/
def operandIntType (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy p => placeIntType decls p
  | .constant c => intTypeOf c.ty
  | _ => none

/-- `minimize`'s operand translation (`tooling/minimize/src/rvalue.rs`):
> "smir::Operand::Constant(c) => self.translate_const_smir(&c.const_, span),
>  smir::Operand::Copy(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },"
for places in the fragment (`PlaceExpr::Local` and `PlaceExpr::Index`) and
integer scalar constants (`Constant::Int(int_from_bits(..))` at the constant's
type). -/
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
integers, `BinaryOp`, `Aggregate(Array)`, `Len`, `Repeat`, and
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
def translateRvalue (decls : List MirAst.LocalDecl) : MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand decls op
  | .unaryOp uop op => do
    let iuop ← translateUnOp uop
    pure (.UnOp (.Int iuop) (← translateOperand decls op))
  | .binaryOp op l r => do
    let iop ← translateBinOp op
    pure (.BinOp (.Int iop) (← translateOperand decls l) (← translateOperand decls r))
  | .cast .intToInt op targetTy => do
    let intTy ← intTypeOf targetTy
    let operand ← translateOperand decls op
    pure (.UnOp (.Cast (.IntToInt intTy)) operand)
  | .aggregate (.array elemTy) ops => do
    let elemIt ← intTypeOf elemTy
    let exprs ← ops.mapM (translateOperand decls)
    pure (.Tuple exprs (.Array (.Int elemIt) (Int.ofNat ops.length)))
  | .repeat op count => do
    let elemIt ← operandIntType decls op
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
def translateStatement (decls : List MirAst.LocalDecl) (s : MirAst.Statement) :
    Option Gen.Statement :=
  match s.kind with
  | .assign dst rv => do
    let destination ← translatePlace decls dst
    let source ← translateRvalue decls rv
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
def translateTerminator (decls : List MirAst.LocalDecl) (t : MirAst.Terminator) :
    Option Gen.Terminator :=
  match t.kind with
  | .goto target => some (.Goto (bbName target))
  | .switchInt discr targets => do
    let v ← translateOperand decls discr
    let it ← operandIntType decls discr
    pure (.Switch v (switchCases it targets.branches) (bbName targets.otherwise))
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
    let ty ← translateTy d.ty
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

/-- A scalar place of integer type `it`: either an unprojected scalar local `_j`
or an indexed element `_j[proj]` of a homogeneous array local. -/
def placeOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Place → Bool
  | ⟨j, []⟩ =>
    decide (j < decls.length) && decide ((decls[j]? >>= (intTypeOf ·.ty)) = some it)
  | ⟨j, [proj]⟩ =>
    decide (j < decls.length) &&
    match decls[j]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) => decide (elemIt = it) && projOk decls count proj
    | none => false
  | _ => false

/-- A scalar integer operand of type `it`. -/
def operandOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy p => placeOk decls it p && (translateOperand decls op).isSome
  | .constant _ =>
    decide (operandIntType decls op = some it) && (translateOperand decls op).isSome
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
    | none => false
  | .len ⟨j, []⟩ =>
    decide (it = usizeIt) &&
    decide (j < decls.length) &&
    (decls[j]? >>= (arrayTypeOf ·.ty)).isSome
  | _ => false

/-- Fragment rvalues producing a homogeneous array `[elemIt; count]`. -/
def arrayRvalueOk (decls : List MirAst.LocalDecl) (elemIt : Gen.IntType) (count : Nat) :
    MirAst.Rvalue → Bool
  | .use (.copy ⟨j, []⟩) =>
    decide (j < decls.length) &&
    decide ((decls[j]? >>= (arrayTypeOf ·.ty)) = some (elemIt, count))
  | .aggregate (.array elemTy) ops =>
    decide (intTypeOf elemTy = some elemIt) &&
    decide (ops.length = count) &&
    ops.all (operandOk decls elemIt)
  | .repeat op n =>
    decide (n = count) &&
    (decide (0 < count) || match op with | .constant _ => true | _ => false) &&
    operandOk decls elemIt op
  | _ => false

/-- Fragment statements, type-checked against the destination's type. -/
def statementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? with
    | none => false
    | some d =>
      match intTypeOf d.ty with
      | some it => rvalueOk decls it rv
      | none =>
        match arrayTypeOf d.ty with
        | some (elemIt, count) => arrayRvalueOk decls elemIt count rv
        | none => false
  | .assign ⟨i, [proj]⟩ rv =>
    match decls[i]? >>= (arrayTypeOf ·.ty) with
    | some (elemIt, count) =>
      projOk decls count proj && rvalueOk decls elemIt rv
    | none => false
  | .placeMention ⟨i, []⟩ => decide (i < decls.length)
  | _ => false

/-- Fragment terminators; jump targets must be blocks of the body and
`switchInt` values must be distinct in-range bit patterns of the
discriminant's type. -/
def terminatorOk (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match operandIntType decls discr with
    | some it =>
      operandOk decls it discr &&
      targets.branches.all (fun p => decide (p.1 < 2 ^ (8 * it.size.bytes)) && decide (p.2 < nblocks)) &&
      (targets.branches.map Prod.fst).Nodup &&
      decide (targets.otherwise < nblocks)
    | none => false
  | .unreachable => true
  | .return_ => true
  | _ => false

/-- Well-formedness of a local declaration in the fragment: either a scalar
integer or a homogeneous 1D integer array whose byte size fits in signed 64-bit
`isize` (`< 2 ^ 63`). -/
def localDeclOk (d : MirAst.LocalDecl) : Bool :=
  (intTypeOf d.ty).isSome ||
  match arrayTypeOf d.ty with
  | some (elemIt, count) => decide (count * elemIt.size.bytes < 2 ^ 63)
  | none => false

/-- The decidable fragment on which the correspondence theorem is stated. -/
def inFragment (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.localDecls.length = body.argCount + 1) &&
  (body.localDecls[0]? >>= (intTypeOf ·.ty)).isSome &&
  body.localDecls.all localDeclOk &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.localDecls) &&
    terminatorOk body.localDecls body.basicBlocks.length bb.terminator) &&
  (translateFn body).isSome

end MiniRustSpec.Correspondence
