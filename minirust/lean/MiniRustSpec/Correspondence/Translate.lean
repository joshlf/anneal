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
  (`localDecls.length = argCount + 1`), all of integer type;
* statements are `_i = Use(copy _j)`, `_i = Use(const c)`,
  `_i = UnaryOp(Neg, a)`, `_i = BinaryOp(op, a, b)` with `op ∈ {Add, Sub, Mul}`,
  where every operand is `copy _j` (no projections) or an integer constant, all
  of the destination's type, or `PlaceMention(_i)`;
* terminators are `Goto`, `SwitchInt` on an integer `copy _j`, `Unreachable`, or
  `Return`, and every jump target is a block of the body;
* no block is a cleanup block.

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

/-- `minimize`'s `int_from_bits(bits, int_ty)`: interpret a `u128` bit pattern as
the mathematical integer it encodes at type `int_ty` (two's complement for
signed types). -/
def intFromBits (bits : Nat) (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => bits
  | .Signed =>
    if bits < 2 ^ (8 * it.size.bytes - 1) then bits else (bits : Int) - 2 ^ (8 * it.size.bytes)

/-- Type of a fragment operand: `copy _j` has `_j`'s declared type; a constant
carries its type. -/
def operandIntType (decls : List MirAst.LocalDecl) : MirAst.Operand → Option Gen.IntType
  | .copy ⟨j, []⟩ => decls[j]? >>= fun d => intTypeOf d.ty
  | .constant c => intTypeOf c.ty
  | _ => none

/-- `minimize`'s operand translation (`tooling/minimize/src/rvalue.rs`):
> "smir::Operand::Constant(c) => self.translate_const_smir(&c.const_, span),
>  smir::Operand::Copy(place) =>
>      ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },"
restricted to projection-free places (`PlaceExpr::Local`) and integer scalar
constants (`Constant::Int(int_from_bits(..))` at the constant's type). -/
def translateOperand : MirAst.Operand → Option Gen.ValueExpr
  | .copy ⟨j, []⟩ => some (.Load (.Local (localName j)))
  | .constant c =>
    match c.val, intTypeOf c.ty with
    | .scalar (.int ⟨bits, sz⟩), some it =>
      if sz = it.size.bytes ∧ bits < 2 ^ (8 * sz) then
        some (.Constant (.Int (intFromBits bits it)) (.Int it))
      else none
    | _, _ => none
  | _ => none

/-- `minimize`'s binary-operator translation for integer operands:
> "(Add, Type::Int(_)) => build::add(l, r),
>  (Sub, Type::Int(_)) => build::sub(l, r),
>  (Mul, Type::Int(_)) => build::mul(l, r),"
where `build::add(l, r)` is `ValueExpr::BinOp { operator: BinOp::Int(IntBinOp::Add), .. }`. -/
def translateBinOp : MirAst.BinOp → Option Gen.IntBinOp
  | .add => some .Add
  | .sub => some .Sub
  | .mul => some .Mul
  | _ => none

/-- `minimize`'s rvalue translation for `Use`, `UnaryOp(Neg)`, and `BinaryOp`
(`tooling/minimize/src/rvalue.rs`):
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
>              (Neg, Type::Int(_)) => build::neg(operand),"
where `build::neg(x)` is `ValueExpr::UnOp { operator: UnOp::Int(IntUnOp::Neg), operand: x }`. -/
def translateRvalue : MirAst.Rvalue → Option Gen.ValueExpr
  | .use op => translateOperand op
  | .unaryOp .neg op => do
    pure (.UnOp (.Int .Neg) (← translateOperand op))
  | .binaryOp op l r => do
    let iop ← translateBinOp op
    pure (.BinOp (.Int iop) (← translateOperand l) (← translateOperand r))
  | _ => none

/-- `minimize`'s statement translation for assignments and `PlaceMention` on a
projection-free place (`tooling/minimize/src/bb.rs`):
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
def translateStatement (s : MirAst.Statement) : Option Gen.Statement :=
  match s.kind with
  | .assign ⟨i, []⟩ rv => (translateRvalue rv).map (fun src => .Assign (.Local (localName i)) src)
  | .placeMention ⟨i, []⟩ => some (.PlaceMention (.Local (localName i)))
  | _ => none

/-- `minimize`'s switch cases for a discriminant of type `it`:
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
    let v ← translateOperand discr
    let it ← operandIntType decls discr
    pure (.Switch v (switchCases it targets.branches) (bbName targets.otherwise))
  | .unreachable => some .Unreachable
  | .return_ => some .Return
  | _ => none

/-- `minimize`'s basic-block translation; fragment blocks are not cleanup blocks,
so their kind is `BbKind::Regular`. -/
def translateBlock (decls : List MirAst.LocalDecl) (bb : MirAst.BasicBlockData) :
    Option Gen.BasicBlock := do
  let stmts ← bb.statements.mapM translateStatement
  let term ← translateTerminator decls bb.terminator
  pure ⟨stmts, term, .Regular⟩

/-- `minimize`'s local-type map, one entry per MIR local in index order:
> "for (id, local_name) in &self.local_name_map {
>      let local_decl = &self.body.local_decls[*id];
>      let span = local_decl.source_info.span;
>      let ty = self.cx.translate_ty(local_decl.ty, span);
>      self.locals.insert(*local_name, ty);
>  }" -/
def translateLocals : Nat → List MirAst.LocalDecl → Option (List (Gen.LocalName × Gen.Type))
  | _, [] => some []
  | i, d :: ds => do
    let it ← intTypeOf d.ty
    let rest ← translateLocals (i + 1) ds
    pure ((localName i, .Int it) :: rest)

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

/-- A projection-free integer operand of type `it`. -/
def operandOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) (op : MirAst.Operand) : Bool :=
  match op with
  | .copy ⟨j, []⟩ => decide (j < decls.length) && decide (operandIntType decls op = some it)
  | .constant _ =>
    decide (operandIntType decls op = some it) && (translateOperand op).isSome
  | _ => false

/-- Fragment rvalues of integer type `it`. -/
def rvalueOk (decls : List MirAst.LocalDecl) (it : Gen.IntType) : MirAst.Rvalue → Bool
  | .use op => operandOk decls it op
  | .unaryOp .neg op => operandOk decls it op
  | .binaryOp op a b => (translateBinOp op).isSome && operandOk decls it a && operandOk decls it b
  | _ => false

/-- Fragment statements, type-checked against the destination's type. -/
def statementOk (decls : List MirAst.LocalDecl) (s : MirAst.Statement) : Bool :=
  match s.kind with
  | .assign ⟨i, []⟩ rv =>
    match decls[i]? >>= fun d => intTypeOf d.ty with
    | none => false
    | some it => rvalueOk decls it rv
  | .placeMention ⟨i, []⟩ => decide (i < decls.length)
  | _ => false

/-- Fragment terminators; jump targets must be blocks of the body and
`switchInt` values must be distinct in-range bit patterns of the
discriminant's type. -/
def terminatorOk (decls : List MirAst.LocalDecl) (nblocks : Nat) (t : MirAst.Terminator) : Bool :=
  match t.kind with
  | .goto target => decide (target < nblocks)
  | .switchInt discr targets =>
    match discr, operandIntType decls discr with
    | .copy ⟨j, []⟩, some it =>
      decide (j < decls.length) &&
      targets.branches.all (fun p => decide (p.1 < 2 ^ (8 * it.size.bytes)) && decide (p.2 < nblocks)) &&
      (targets.branches.map Prod.fst).Nodup &&
      decide (targets.otherwise < nblocks)
    | _, _ => false
  | .unreachable => true
  | .return_ => true
  | _ => false

/-- The decidable fragment on which the correspondence theorem is stated. -/
def inFragment (body : MirAst.CapturedMir) : Bool :=
  body.isRuntimePostCleanup &&
  decide (body.localDecls.length = body.argCount + 1) &&
  body.localDecls.all (fun d => (intTypeOf d.ty).isSome) &&
  decide (body.basicBlocks ≠ []) &&
  body.basicBlocks.all (fun bb =>
    !bb.isCleanup &&
    bb.statements.all (statementOk body.localDecls) &&
    terminatorOk body.localDecls body.basicBlocks.length bb.terminator) &&
  (translateFn body).isSome

end MiniRustSpec.Correspondence
