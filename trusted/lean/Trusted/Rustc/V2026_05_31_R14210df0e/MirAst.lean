-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst

namespace Trusted.Rustc.V2026_05_31_R14210df0e.MirAst

/-!
# Versioned Rustc MIR Abstract Syntax (`Trusted.Rustc.V2026_05_31_R14210df0e.MirAst`)

Captured post-cleanup runtime MIR syntax (`Runtime(PostCleanup)`) for
`rust-lang/rust` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`commit-date: 2026-05-31`; distributed in `nightly-2026-06-01`).

For the modeled MIR fragment, the post-cleanup runtime MIR syntax at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is identical to `Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst` (`7189d39d9ce936881b8132c6addeaf3e295cd455`,
`commit-date: 2026-10-22`; upstream `TerminatorKind::Goto` gained
non-operational `loop_hint_attrs` in `7189d39d9ce936881b8132c6addeaf3e295cd455`,
which `TerminatorKind.goto` omits across all dialects); every syntax category
and constructor is therefore re-exported as a kernel-reducible `abbrev`.
-/

/-- Function definition identifier (`rustc_hir::def_id::DefId` index). -/
abbrev DefId := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.DefId

/-- Local variable slot index (`rustc_middle::mir::Local`). -/
abbrev LocalId := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.LocalId

/-- Basic-block index (`rustc_middle::mir::BasicBlock`). -/
abbrev BasicBlockId := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BasicBlockId

/-- Aggregate field index (`rustc_abi::FieldIdx`). -/
abbrev FieldIdx := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.FieldIdx

/-- Memory allocation identifier (`rustc_middle::mir::interpret::AllocId`). -/
abbrev AllocId := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AllocId

/-- Integer and pointer-sized scalar widths. -/
abbrev IntWidth := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth
abbrev IntWidth.i8 := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i8
abbrev IntWidth.i16 := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i16
abbrev IntWidth.i32 := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i32
abbrev IntWidth.i64 := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i64
abbrev IntWidth.i128 := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i128
abbrev IntWidth.isize := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.isize

/-- Reference and raw-pointer mutability. -/
abbrev Mutability := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Mutability
abbrev Mutability.shared := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Mutability.shared
abbrev Mutability.mut := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Mutability.mut

/-- In-memory tag representation of a fieldless Rust enum. -/
abbrev EnumTagRepr := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.EnumTagRepr
abbrev EnumTagRepr.zeroSized := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.EnumTagRepr.zeroSized
abbrev EnumTagRepr.scalar := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.EnumTagRepr.scalar

/-- Structural descriptor for a fieldless Rust enum. -/
abbrev EnumTy := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.EnumTy
abbrev EnumTy.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.EnumTy.mk

/-- Structural MIR type descriptors carried by value. -/
abbrev MirTy := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy
abbrev MirTy.bool := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.bool
abbrev MirTy.int := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.int
abbrev MirTy.unit := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.unit
abbrev MirTy.never := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.never
abbrev MirTy.enum := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.enum
abbrev MirTy.tuple := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.tuple
abbrev MirTy.ref := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.ref
abbrev MirTy.rawPtr := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.rawPtr
abbrev MirTy.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.unsupported

/-- MIR binary operators (`rustc_middle::mir::BinOp`). -/
abbrev BinOp := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp
abbrev BinOp.add := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.add
abbrev BinOp.addUnchecked := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.addUnchecked
abbrev BinOp.addWithOverflow := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.addWithOverflow
abbrev BinOp.sub := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.sub
abbrev BinOp.subUnchecked := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.subUnchecked
abbrev BinOp.subWithOverflow := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.subWithOverflow
abbrev BinOp.mul := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.mul
abbrev BinOp.mulUnchecked := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.mulUnchecked
abbrev BinOp.mulWithOverflow := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.mulWithOverflow
abbrev BinOp.div := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.div
abbrev BinOp.rem := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.rem
abbrev BinOp.bitXor := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.bitXor
abbrev BinOp.bitAnd := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.bitAnd
abbrev BinOp.bitOr := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.bitOr
abbrev BinOp.shl := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.shl
abbrev BinOp.shlUnchecked := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.shlUnchecked
abbrev BinOp.shr := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.shr
abbrev BinOp.shrUnchecked := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.shrUnchecked
abbrev BinOp.eq := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.eq
abbrev BinOp.lt := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.lt
abbrev BinOp.le := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.le
abbrev BinOp.ne := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.ne
abbrev BinOp.ge := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.ge
abbrev BinOp.gt := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.gt
abbrev BinOp.offset := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.offset

/-- MIR unary operators (`rustc_middle::mir::UnOp`). -/
abbrev UnOp := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnOp
abbrev UnOp.not := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnOp.not
abbrev UnOp.neg := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnOp.neg
abbrev UnOp.ptrMetadata := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnOp.ptrMetadata

/-- Place projection elements (`*p`, `p.f`, or unmodeled projection). -/
abbrev ProjectionElem := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ProjectionElem
abbrev ProjectionElem.deref := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ProjectionElem.deref
abbrev ProjectionElem.field := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ProjectionElem.field
abbrev ProjectionElem.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ProjectionElem.unsupported

/-- A MIR place (`rustc_middle::mir::Place`). -/
abbrev Place := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Place
abbrev Place.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Place.mk

/-- Constant literal payload inside `ConstOperand`. -/
abbrev ConstLit := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ConstLit
abbrev ConstLit.scalar := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ConstLit.scalar
abbrev ConstLit.zeroSized := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ConstLit.zeroSized

/-- Typed constant operand carrying `ty : MirTy` and `lit : ConstLit`. -/
abbrev ConstOperand := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ConstOperand
abbrev ConstOperand.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.ConstOperand.mk

/-- A MIR operand (`copy place`, `move place`, or `const c`). -/
abbrev Operand := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Operand
abbrev Operand.copy := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Operand.copy
abbrev Operand.move := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Operand.move
abbrev Operand.constant := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Operand.constant

/-- A MIR right-hand-side expression (`rustc_middle::mir::Rvalue`). -/
abbrev Rvalue := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue
abbrev Rvalue.use := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.use
abbrev Rvalue.binaryOp := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.binaryOp
abbrev Rvalue.unaryOp := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.unaryOp
abbrev Rvalue.discriminant := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.discriminant
abbrev Rvalue.ref := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.ref
abbrev Rvalue.addressOf := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.addressOf
abbrev Rvalue.aggregateTuple := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.aggregateTuple
abbrev Rvalue.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Rvalue.unsupported

/-- A MIR statement inside a basic block (`rustc_middle::mir::StatementKind`). -/
abbrev StatementKind := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind
abbrev StatementKind.assign := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.assign
abbrev StatementKind.storageLive := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.storageLive
abbrev StatementKind.storageDead := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.storageDead
abbrev StatementKind.nop := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.nop
abbrev StatementKind.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.unsupported

/-- Branch table for `TerminatorKind.switchInt`. -/
abbrev SwitchTargets := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.SwitchTargets
abbrev SwitchTargets.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.SwitchTargets.mk

/-- Unwind continuation action on panicking terminators. -/
abbrev UnwindAction := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnwindAction
abbrev UnwindAction.continue_ := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnwindAction.continue_
abbrev UnwindAction.unreachable := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnwindAction.unreachable
abbrev UnwindAction.terminate := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnwindAction.terminate
abbrev UnwindAction.cleanup := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.UnwindAction.cleanup

/-- Built-in MIR `Assert` condition kind (`rustc_middle::mir::AssertKind`). -/
abbrev AssertKind := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind
abbrev AssertKind.overflow := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.overflow
abbrev AssertKind.overflowNeg := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.overflowNeg
abbrev AssertKind.divByZero := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.divByZero
abbrev AssertKind.remByZero := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.remByZero
abbrev AssertKind.boundsCheck := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.boundsCheck
abbrev AssertKind.misalignedPtrDeref := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.misalignedPtrDeref
abbrev AssertKind.nullPtrDeref := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.nullPtrDeref
abbrev AssertKind.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.AssertKind.unsupported

/-- A MIR basic-block terminator (`rustc_middle::mir::TerminatorKind`). -/
abbrev TerminatorKind := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind
abbrev TerminatorKind.goto := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.goto
abbrev TerminatorKind.switchInt := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.switchInt
abbrev TerminatorKind.return_ := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.return_
abbrev TerminatorKind.unreachable := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.unreachable
abbrev TerminatorKind.unwindResume := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.unwindResume
abbrev TerminatorKind.assert := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.assert
abbrev TerminatorKind.call := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.call
abbrev TerminatorKind.unsupported := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.unsupported

/-- A MIR basic block (`rustc_middle::mir::BasicBlockData`). -/
abbrev BasicBlock := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BasicBlock
abbrev BasicBlock.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BasicBlock.mk

/-- A MIR function body (`rustc_middle::mir::Body`). -/
abbrev Body := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Body
abbrev Body.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Body.mk

/-- Capture scope of a `Program` (`.unit` or `.crate`). -/
abbrev VerificationScope := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.VerificationScope
abbrev VerificationScope.unit := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.VerificationScope.unit
abbrev VerificationScope.crate := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.VerificationScope.crate

/-- A complete MIR program unit. -/
abbrev Program := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Program
abbrev Program.mk := Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.Program.mk

end Trusted.Rustc.V2026_05_31_R14210df0e.MirAst
