/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.IntrinsicLM4_2
import LeanMiriSpec.Correspondence.NumericLM4_2
import LeanMiriSpec.Correspondence.SaturatingLM4_2

/-!
# Intrinsic Call Infrastructure for `LM-4.2`

Generic one-step correspondence lemmas for translated `TerminatorKind.call`s of
`AnnealIntrinsic`s between Anneal's `stepMirFn` and `lean-miri`'s
`Miri.Interpreter.Step.step` (under `annealStepHooks`), from
`StateRelLM3_1`-related states:

* operand evaluation before the immediate read (`annealEvalOperand_scalar_lm3_1`),
  writing a scalar result and returning to the call's target
  (`StateRelLM3_1.write_scalar_return`);
* one-step simulation of one- and two-argument intrinsic calls, parameterized by
  the intrinsic's own evaluation on both sides
  (`step_intrinsic_call_one_simulation`, `step_intrinsic_call_two_simulation`);
* the vendored dispatcher's handling of `rotate_left` / `rotate_right`
  (`intrinsics_eval_rotateLeft`, `intrinsics_eval_rotateRight`) and the
  resulting `lean-miri` step on intrinsics it leaves to their MIR fallback body
  (`step_intrinsic_call_two_unhandled`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- Classify a `DefPath` as one of the seven one-operand integer bit-manipulation
intrinsics, or `.none`. -/
def integerBitIntrinsicOfPath? (defPath : DefPath) : Option IntegerBitIntrinsic :=
  match stringEq defPath "core::intrinsics::ctpop" with
  | true => .some .ctpop
  | false =>
  match stringEq defPath "core::intrinsics::ctlz" with
  | true => .some .ctlz
  | false =>
  match stringEq defPath "core::intrinsics::ctlz_nonzero" with
  | true => .some .ctlzNonzero
  | false =>
  match stringEq defPath "core::intrinsics::cttz" with
  | true => .some .cttz
  | false =>
  match stringEq defPath "core::intrinsics::cttz_nonzero" with
  | true => .some .cttzNonzero
  | false =>
  match stringEq defPath "core::intrinsics::bswap" with
  | true => .some .bswap
  | false =>
  match stringEq defPath "core::intrinsics::bitreverse" with
  | true => .some .bitreverse
  | false => .none

/-- Byte width of an operand whose declared type is a primitive integer type
(`u8`..`u128`, `usize`, `i8`..`i128`, `isize`), and `.none` for every other
operand type. -/
def integerOperandBytes?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Nat :=
  match operandTy localDecls layouts op with
  | .some ty => intCastTargetBytes ty.kind
  | .none => .none

/-- Byte size of the pointee `T` of an operand of type `*const T`, `*mut T`, `&T`,
or `&mut T`, resolved directly from `pointeeTy.kind` via `rigidTyKindByteSize`. -/
def operandPointeeBytes?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Nat :=
  match operandTy localDecls layouts op with
  | .some ptrTy =>
    match pointeeTyOf ptrTy with
    | .some pointeeTy => rigidTyKindByteSize pointeeTy.kind
    | .none => .none
  | .none => .none

/-- Step to block `targetBb` (statement `0`) with `locals` and `mem`, the
continuation of a returning intrinsic call. -/
def intrinsicReturnTo
    (s : MachineState)
    (targetBb : BasicBlockIdx)
    (locals : List LocalSlot)
    (mem : Memory) :
    MirStepNode :=
  MirStepNode.step {
    frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals }
    memory := mem
  }

/-- Write the return value `retVal` of an intrinsic call to `destination` and step
to `targetBb`; writing to a dead or otherwise invalid destination is undefined
behavior, matching `writeIntrinsicReturn`. -/
def intrinsicWriteReturn
    (s : MachineState)
    (locals : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (retVal : Value) :
    MirStepNode :=
  match writePlaceValue locals s.memory.borrows destination retVal with
  | .ok updatedLocals => intrinsicReturnTo s targetBb updatedLocals s.memory
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/-- Largest byte count of a Rust value or memory access on a 64-bit target,
`isize::MAX = 2^63 - 1`. -/
@[reducible]
def isizeMaxBytes : Nat := 9223372036854775807

/-- Fill `byteCount` little-endian bytes with the byte `byte`:
`∑_{i < byteCount} byte * 256^i`. -/
def repeatByteBits (byte : Nat) : Nat → Nat
  | .zero => 0
  | .succ k => Nat.add byte (Nat.mul 256 (repeatByteBits byte k))

/-- Evaluate `core::intrinsics::write_bytes::<T>(dst, val, count)` on the
evaluated arguments `dstVal`, `val`, and `count` (pre-Stage-1 inline model). -/
def evalWriteBytesCall
    (s : MachineState)
    (dstOp : Operand)
    (dstVal : Value)
    (val count : ScalarInt)
    (locals' : List LocalSlot)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    MirStepNode :=
  let dstPtr? : Option (Option ProvenancePtr) :=
    match dstVal with
    | .ptr dstPtr _ => .some (.some dstPtr)
    | .scalar addr =>
      match Nat.beq addr.sizeBytes 8 with
      | true => .some .none
      | false => .none
    | _ => .none
  match dstPtr?, operandPointeeBytes? localDecls layouts dstOp with
  | .some maybePtr, .some elemBytes =>
    let total := Nat.mul count.bits elemBytes
    match Nat.ble total isizeMaxBytes with
    | false => MirStepNode.fail .ub
    | true =>
      match Nat.beq total 0 with
      | true => intrinsicReturnTo s targetBb locals' s.memory
      | false =>
        match maybePtr with
        | .none => MirStepNode.fail .ub
        | .some dstPtr =>
          match lookupBorrow s.memory.borrows dstPtr.tag with
          | .none => MirStepNode.fail .ub
          | .some entry =>
            match entry.perm with
            | .frozen => MirStepNode.fail .ub
            | .disabled => MirStepNode.fail .ub
            | _ =>
              match get? locals' entry.targetLocal, get? localDecls entry.targetLocal with
              | .none, _ => MirStepNode.fail .ub
              | .some .dead, _ => MirStepNode.fail .ub
              | _, .none => MirStepNode.fail .ub
              | .some slot, .some decl =>
                match entry.targetProjection with
                | _ :: _ => MirStepNode.unsupported
                | .nil =>
                  match intCastTargetBytes decl.ty.kind with
                  | .none => MirStepNode.unsupported
                  | .some targetBytes =>
                    match Nat.ble (Nat.add dstPtr.offsetBytes total) targetBytes with
                    | false => MirStepNode.fail .ub
                    | true =>
                      let off := dstPtr.offsetBytes
                      let fill := repeatByteBits (Nat.mod val.bits 256) total
                      let newSlot? : Option LocalSlot :=
                        match slot with
                        | .dead => .none
                        | .uninit =>
                          match Bool.and (Nat.beq off 0) (Nat.beq total targetBytes) with
                          | true => .some (.init (.scalar ⟨fill, targetBytes⟩))
                          | false => .some .uninit
                        | .init (.scalar sc) =>
                          let lowMod := scalarModulus off
                          let highMod := scalarModulus (Nat.add off total)
                          let old := wrapScalarBits sc.bits (scalarModulus targetBytes)
                          .some (.init (.scalar ⟨
                            Nat.add (Nat.mod old lowMod)
                              (Nat.add (Nat.mul fill lowMod)
                                (Nat.mul (Nat.div old highMod) highMod)),
                            targetBytes⟩))
                        | .init _ => .none
                      match newSlot? with
                      | .none => MirStepNode.fail .ub
                      | .some newSlot =>
                        match set? locals' entry.targetLocal newSlot with
                        | .none => MirStepNode.fail .ub
                        | .some locals'' =>
                          intrinsicReturnTo s targetBb locals''
                            { s.memory with
                              borrows :=
                                invalidateConflictingBorrows
                                  s.memory.borrows
                                  entry.targetLocal
                                  (.some dstPtr.tag) }
  | _, _ => MirStepNode.unsupported

/-- Evaluate `core::intrinsics::arith_offset::<T>(ptr, count)` (and wrapping_offset
aliases): offset `ptr` by `count * size_of::<T>()` bytes with two's-complement
wrapping modulo `2^64`. -/
def evalArithOffsetCall
    (s : MachineState)
    (ptrOp : Operand)
    (ptrVal count : Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    MirStepNode :=
  match operandPointeeBytes? localDecls layouts ptrOp, count with
  | .some elemBytes, .scalar countSc =>
    match Nat.beq countSc.sizeBytes 8 with
    | false => MirStepNode.unsupported
    | true =>
      let delta := Nat.mul countSc.bits elemBytes
      let addrModulus := scalarModulus 8
      match ptrVal with
      | .ptr p sz =>
        intrinsicWriteReturn s locals' destination targetBb
          (.ptr { p with offsetBytes := Nat.mod (Nat.add p.offsetBytes delta) addrModulus } sz)
      | .scalar addr =>
        match Nat.beq addr.sizeBytes 8 with
        | false => MirStepNode.unsupported
        | true =>
          intrinsicWriteReturn s locals' destination targetBb
            (.scalar ⟨Nat.mod (Nat.add addr.bits delta) addrModulus, 8⟩)
      | _ => MirStepNode.fail .ub
  | _, _ => MirStepNode.unsupported

/-- Evaluate a call to one of the `LM-4.2` inline intrinsics other than `exact_div`
on the evaluated arguments `argVals` (with `locals'` after evaluating them), or
return `.none` when `defPath` names none of them. -/
def evalInlineIntrinsicCall?
    (s : MachineState)
    (defPath : DefPath)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Option MirStepNode :=
  match integerBitIntrinsicOfPath? defPath with
  | .some op =>
    .some
      (match argOps, argVals with
      | xOp :: .nil, .scalar x :: .nil =>
        match integerOperandBytes? localDecls layouts xOp with
        | .some n =>
          match Nat.beq x.sizeBytes n with
          | true =>
            match evalIntegerBitIntrinsic op x with
            | .some r => intrinsicWriteReturn s locals' destination targetBb (.scalar r)
            | .none => MirStepNode.fail .ub
          | false => MirStepNode.unsupported
        | .none => MirStepNode.unsupported
      | _, _ => MirStepNode.unsupported)
  | .none =>
  let rotateOrSaturating? : Option (Bool × Bool) :=
    match stringEq defPath "core::intrinsics::rotate_left" with
    | true => .some (true, true)
    | false =>
    match stringEq defPath "core::intrinsics::rotate_right" with
    | true => .some (true, false)
    | false =>
    match stringEq defPath "core::intrinsics::saturating_add" with
    | true => .some (false, true)
    | false =>
    match stringEq defPath "core::intrinsics::saturating_sub" with
    | true => .some (false, false)
    | false => .none
  match rotateOrSaturating? with
  | .some (isRotate, flag) =>
    .some
      (match argOps, argVals with
      | lhsOp :: _ :: .nil, .scalar a :: .scalar b :: .nil =>
        match integerOperandBytes? localDecls layouts lhsOp with
        | .some n =>
          match Nat.beq a.sizeBytes n with
          | false => MirStepNode.unsupported
          | true =>
            match isRotate with
            | true =>
              match Nat.beq b.sizeBytes 4 with
              | true => intrinsicWriteReturn s locals' destination targetBb (.scalar (evalRotate flag a b))
              | false => MirStepNode.unsupported
            | false =>
              match
                evalSaturatingArith flag a b locals' s.memory
                  (operandIsSigned localDecls lhsOp layouts)
              with
              | .ok retVal localsAfter _ =>
                intrinsicWriteReturn s localsAfter destination targetBb retVal
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
        | .none => MirStepNode.unsupported
      | _, _ => MirStepNode.unsupported)
  | .none =>
  match stringEq defPath "core::intrinsics::write_bytes" with
  | true =>
    .some
      (match argOps, argVals with
      | dstOp :: _ :: _ :: .nil, dstVal :: .scalar val :: .scalar count :: .nil =>
        evalWriteBytesCall s dstOp dstVal val count locals' targetBb localDecls layouts
      | _, _ => MirStepNode.unsupported)
  | false =>
  let isOffsetPath : Bool :=
    Bool.or
      (Bool.or
        (stringEq defPath "core::intrinsics::arith_offset")
        (stringEq defPath "core::intrinsics::wrapping_offset"))
      (Bool.or
        (stringEq defPath "std::intrinsics::arith_offset")
        (stringEq defPath "std::intrinsics::wrapping_offset"))
  match isOffsetPath with
  | true =>
    .some
      (match argOps, argVals with
      | ptrOp :: _ :: .nil, ptrVal :: count :: .nil =>
        evalArithOffsetCall s ptrOp ptrVal count locals' destination targetBb localDecls layouts
      | _, _ => MirStepNode.unsupported)
  | false => .none

/-- `LM-4.2` inline-intrinsic terminator evaluator (extending `evalTerminator`
with `evalInlineIntrinsicCall?` for `rotate_left`, `rotate_right`, `write_bytes`,
and `wrapping_offset` / `std::intrinsics::*` aliases when unlinked). -/
def evalTerminatorLM4_2
    (s : MachineState)
    (term : Terminator)
    (currentBody : Option CapturedMir := .none) :
    MirStepNode :=
  let bodyLayouts : LayoutTable :=
    match currentBody with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  let bodyLocalDecls : List LocalDecl :=
    match currentBody with
    | .some b => b.localDecls
    | .none => .nil
  match term.kind with
  | .call func argOps destination (.some targetBb) unwind =>
    match extractCalleeDefPath? func with
    | .none => evalTerminator s term currentBody
    | .some defPath =>
      match
        evalOperands
          s.frame.locals
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match findCallee? s.memory.callees defPath with
        | .some _ => evalTerminator s term currentBody
        | .none =>
          match stringEq defPath "core::intrinsics::exact_div" with
          | true => evalTerminator s term currentBody
          | false =>
            match
              evalInlineIntrinsicCall? s defPath argOps argVals locals' destination targetBb
                bodyLocalDecls bodyLayouts
            with
            | .some node => node
            | .none =>
              MirStepNode.extCall
                { defPath := defPath, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
  | _ => evalTerminator s term currentBody

/-- Compute the ABI alignment in bytes of a `RigidTy` when determined directly by
its primitive, pointer, or homogeneous array constructor on a 64-bit target. -/
@[reducible]
def rigidTyKindAlignBytes : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .tuple .nil => .some 1
  | .fnDef _ _ => .some 1
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ _ => .some 8
  | .rawPtr _ _ => .some 8
  | .array elemKind _ => rigidTyKindAlignBytes elemKind
  | _ => .none

/-- Determine the ABI alignment in bytes of `ty` using `rigidTyKindAlignBytes` for
primitives, pointers, and homogeneous arrays, or `LayoutTable.lookup layouts
ty.layoutIdx` for ADTs and layout-indexed aggregates. -/
@[reducible]
def rigidTyAlignBytes (layouts : LayoutTable) (ty : Ty) : Option Nat :=
  match rigidTyKindAlignBytes ty.kind with
  | .some al => .some al
  | .none =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some l => .some l.align.bytes
    | .none => .none

/-- Outcome of `copy_nonoverlapping` size-overflow, alignment, and zero-byte
prechecks prior to live-allocation dereference. -/
inductive CopyPrecheckResult where
  | ub
  | unsupported
  | zero
  | nonZero (totalBytesOpt : Option Nat)

/-- Test whether runtime pointer operand `v` satisfies byte alignment `elemAlign`
(either as a provenance-carrying `ProvenancePtr` at aligned `offsetBytes` or as
an 8-byte provenance-free integer scalar at aligned `bits`). -/
@[reducible]
def ptrValueAligned (elemAlign : Nat) : Value → Bool
  | .ptr p _ =>
    Bool.or (Nat.beq elemAlign 0) (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)
  | .scalar sc =>
    Bool.and
      (Nat.beq sc.sizeBytes 8)
      (Bool.or (Nat.beq elemAlign 0) (Nat.beq (Nat.mod sc.bits elemAlign) 0))
  | _ => false

/-- Check `count * size_of::<T>() <= isize::MAX` (`9223372036854775807`), pointer
alignment of both `srcVal` and `dstVal` to `align_of::<T>()` (including when
`count == 0`), and zero-byte short-circuiting (`count == 0` or `size_of::<T>()
== 0`). -/
@[reducible]
def copyPrecheck
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (src : Operand)
    (srcVal dstVal : Value)
    (countBits : Nat) :
    CopyPrecheckResult :=
  match operandPointeeTy localDecls layouts src with
  | .none => .unsupported
  | .some srcPt =>
    match
      rigidTyKindByteSize srcPt.kind,
      rigidTyKindAlignBytes srcPt.kind
    with
    | .some elemBytes, .some elemAlign =>
      let totalBytes := Nat.mul countBits elemBytes
      match Nat.ble totalBytes 9223372036854775807 with
      | false => .ub
      | true =>
        let alignOk : Bool :=
          Bool.and
            (ptrValueAligned elemAlign srcVal)
            (ptrValueAligned elemAlign dstVal)
        match alignOk with
        | false => .ub
        | true =>
          match Nat.beq countBits 0 with
          | true => .zero
          | false =>
            match Nat.beq totalBytes 0 with
            | true => .zero
            | false => .nonZero (.some totalBytes)
    | _, _ => .unsupported

/-- Check that a borrow access of `totalBytes` starting at `ptr.offsetBytes` targets
a declared local in `localDecls` and, for a root-local borrow whose byte size
`layouts` resolves, fits within that local's byte size. -/
@[reducible]
def copyBorrowInRootBounds
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptr : ProvenancePtr)
    (entry : BorrowEntry)
    (totalBytesOpt : Option Nat) :
    Bool :=
  match totalBytesOpt with
  | .none => true
  | .some totalBytes =>
    match get? localDecls entry.targetLocal with
    | .none => false
    | .some decl =>
      match entry.targetProjection with
      | .nil =>
        match rigidTyByteSize layouts decl.ty with
        | .some localBytes =>
          Nat.ble (Nat.add ptr.offsetBytes totalBytes) localBytes
        | .none => true
      | _ :: _ => true

/-- Look up `ptr.tag` in `borrows` and verify `copyBorrowInRootBounds` for
`totalBytesOpt`. -/
@[reducible]
def lookupCopyBorrowChecked
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (borrows : List BorrowEntry)
    (ptr : ProvenancePtr)
    (totalBytesOpt : Option Nat) :
    Option BorrowEntry :=
  match lookupBorrow borrows ptr.tag with
  | .none => .none
  | .some entry =>
    match copyBorrowInRootBounds localDecls layouts ptr entry totalBytesOpt with
    | true => .some entry
    | false => .none

/-- Extract `totalBytes` little-endian bytes starting at byte offset `srcStart` from
canonicalized `srcBytes`-byte unsigned integer `srcBits`. -/
@[reducible]
def sliceScalarBytes (srcBits srcBytes srcStart totalBytes : Nat) : Nat :=
  Nat.mod
    (Nat.div
      (wrapScalarBits srcBits (scalarModulus srcBytes))
      (scalarModulus srcStart))
    (scalarModulus totalBytes)

/-- Splice `totalBytes`-byte little-endian integer `chunkBits` into `dstBytes`-byte
unsigned integer `dstBits` at byte offset `dstStart`. -/
@[reducible]
def spliceScalarBytes
    (dstBits chunkBits dstStart totalBytes dstBytes : Nat) : Nat :=
  let lowMod := scalarModulus dstStart
  let highMod := scalarModulus (Nat.add dstStart totalBytes)
  let old := wrapScalarBits dstBits (scalarModulus dstBytes)
  Nat.add (Nat.mod old lowMod)
    (Nat.add (Nat.mul chunkBits lowMod)
      (Nat.mul (Nat.div old highMod) highMod))

/-- Look up a root-local `LocalSlot` for `copy_nonoverlapping` in `locals₃`, falling
back to `s.memory.callerLocals` when `targetLocal` names a caller slot. -/
@[reducible]
def lookupCopyRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (targetLocal : Local) :
    Option LocalSlot :=
  match get? locals₃ targetLocal with
  | .some slot => .some slot
  | .none =>
    match get? s.memory.callerLocals targetLocal with
    | .some slot => .some slot
    | .none =>
      get? s.memory.callerLocals (Nat.sub targetLocal (length locals₃))

/-- Write `newSlot` to root local `dstLocal` (in `locals₃` or `callerLocals`),
invalidate conflicting borrows on `dstLocal` relative to `dstPtr.tag`, and
advance the current statement. -/
def writeCopyRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (dstPtr : ProvenancePtr)
    (dstLocal : Local)
    (newSlot : LocalSlot) :
    MirStepNode :=
  match get? locals₃ dstLocal with
  | .some .dead => MirStepNode.fail .ub
  | .some _ =>
    match set? locals₃ dstLocal newSlot with
    | .some locals₄ =>
      let borrows' :=
        invalidateConflictingBorrows
          s.memory.borrows
          dstLocal
          (.some dstPtr.tag)
      MirStepNode.step
        (advanceStmt
          s
          locals₄
          { s.memory with borrows := borrows' })
    | .none => MirStepNode.fail .ub
  | .none =>
    let callerIdx :=
      match get? s.memory.callerLocals dstLocal with
      | .some _ => dstLocal
      | .none => Nat.sub dstLocal (length locals₃)
    match get? s.memory.callerLocals callerIdx with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? s.memory.callerLocals callerIdx newSlot with
      | .some callerLocals' =>
        let borrows' :=
          invalidateConflictingBorrows
            s.memory.borrows
            dstLocal
            (.some dstPtr.tag)
        MirStepNode.step
          (advanceStmt
            s
            locals₃
            { s.memory with
              borrows := borrows'
              callerLocals := callerLocals' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub

/-- Evaluate a positive-byte `copy_nonoverlapping` of `totalBytes` bytes between two
root-local primitive integer locals (`srcBytes`, `dstBytes`) once in-bounds and
permission checks have passed. -/
def evalCopyRootIntScalars
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (srcBytes dstBytes totalBytes : Nat) :
    MirStepNode :=
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  match
    lookupCopyRootSlot s locals₃ srcEntry.targetLocal,
    lookupCopyRootSlot s locals₃ dstEntry.targetLocal
  with
  | .none, _ => MirStepNode.fail .ub
  | .some .dead, _ => MirStepNode.fail .ub
  | _, .none => MirStepNode.fail .ub
  | _, .some .dead => MirStepNode.fail .ub
  | .some .uninit, _ => MirStepNode.fail .ub
  | .some (.init (.scalar srcSc)), .some dstSlot =>
    match Nat.beq srcSc.sizeBytes srcBytes with
    | false => MirStepNode.unsupported
    | true =>
      let overlaps : Bool :=
        Bool.and
          (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
          (Bool.not
            (Bool.or
              (Nat.ble (Nat.add srcStart totalBytes) dstStart)
              (Nat.ble (Nat.add dstStart totalBytes) srcStart)))
      match overlaps with
      | true => MirStepNode.fail .ub
      | false =>
        let chunk := sliceScalarBytes srcSc.bits srcBytes srcStart totalBytes
        match Bool.and (Nat.beq dstStart 0) (Nat.beq totalBytes dstBytes) with
        | true =>
          writeCopyRootSlot
            s
            locals₃
            dstPtr
            dstEntry.targetLocal
            (.init (.scalar { bits := chunk, sizeBytes := dstBytes }))
        | false =>
          match dstSlot with
          | .dead => MirStepNode.fail .ub
          | .uninit =>
            writeCopyRootSlot s locals₃ dstPtr dstEntry.targetLocal .uninit
          | .init (.scalar dstSc) =>
            match Nat.beq dstSc.sizeBytes dstBytes with
            | false => MirStepNode.unsupported
            | true =>
              let spliced :=
                spliceScalarBytes
                  dstSc.bits chunk dstStart totalBytes dstBytes
              writeCopyRootSlot
                s
                locals₃
                dstPtr
                dstEntry.targetLocal
                (.init (.scalar { bits := spliced, sizeBytes := dstBytes }))
          | .init _ => MirStepNode.unsupported
  | .some (.init _), _ => MirStepNode.unsupported

/-- `LM-4.2` byte-range-extended `copy_nonoverlapping` evaluator once `srcVal`,
`dstVal`, and `countBits` have been evaluated into `locals₃`. -/
def evalCopyNonOverlappingWithCountLM4_2
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match copyPrecheck localDecls layouts src srcVal dstVal countBits with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .zero => MirStepNode.step (advanceStmt s locals₃)
  | .nonZero totalBytesOpt =>
    match srcVal, dstVal with
    | .ptr srcPtr _, .ptr dstPtr _ =>
      match
        lookupCopyBorrowChecked
          localDecls layouts s.memory.borrows srcPtr totalBytesOpt,
        lookupCopyBorrowChecked
          localDecls layouts s.memory.borrows dstPtr totalBytesOpt
      with
      | .some srcEntry, .some dstEntry =>
        match srcEntry.perm, dstEntry.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ =>
          let rootIntStep? : Option MirStepNode :=
            match
              totalBytesOpt,
              srcEntry.targetProjection,
              dstEntry.targetProjection
            with
            | .some totalBytes, .nil, .nil =>
              match
                get? localDecls srcEntry.targetLocal,
                get? localDecls dstEntry.targetLocal
              with
              | .some srcDecl, .some dstDecl =>
                match
                  intCastTargetBytes srcDecl.ty.kind,
                  intCastTargetBytes dstDecl.ty.kind
                with
                | .some srcBytes, .some dstBytes =>
                  .some
                    (evalCopyRootIntScalars
                      s
                      locals₃
                      srcPtr
                      dstPtr
                      srcEntry
                      dstEntry
                      srcBytes
                      dstBytes
                      totalBytes)
                | _, _ => .none
              | _, _ => .none
            | _, _, _ => .none
          match rootIntStep? with
          | .some stepNode => stepNode
          | .none =>
            let n := countBits
            let srcStart := srcPtr.offsetBytes
            let dstStart := dstPtr.offsetBytes
            let singleSizeMatches : Bool :=
              match totalBytesOpt with
              | .none => true
              | .some totalBytes =>
                let srcPlace : Place := {
                  local_ := srcEntry.targetLocal
                  projection := srcEntry.targetProjection
                }
                let dstPlace : Place := {
                  local_ := dstEntry.targetLocal
                  projection := dstEntry.targetProjection
                }
                let srcOk : Bool :=
                  match placeTy localDecls layouts srcPlace with
                  | .some st =>
                    match rigidTyByteSize layouts st with
                    | .some sBytes => Nat.beq totalBytes sBytes
                    | .none => true
                  | .none => true
                let dstOk : Bool :=
                  match placeTy localDecls layouts dstPlace with
                  | .some dt =>
                    match rigidTyByteSize layouts dt with
                    | .some dBytes => Nat.beq totalBytes dBytes
                    | .none => true
                  | .none => true
                Bool.and srcOk dstOk
            let isSingleDirect :=
              Bool.and
                (Bool.and
                  (Nat.beq n 1)
                  (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0)))
                singleSizeMatches
            match isSingleDirect with
            | true =>
              evalCopySingleDirect
                s src dst localDecls layouts
                srcPtr dstPtr srcEntry dstEntry locals₃
            | false =>
              evalCopyNonOverlappingWithCount
                s src dst localDecls layouts srcVal dstVal countBits locals₃
      | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub

/-- `LM-4.2` byte-range-extended `copy_nonoverlapping` statement evaluator. -/
def evalCopyNonOverlappingLM4_2
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok srcVal locals₁ =>
    match
      evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok dstVal locals₂ =>
      match
        evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        evalCopyNonOverlappingWithCountLM4_2
          s src dst localDecls layouts srcVal dstVal countSc.bits locals₃
      | .ok _ _ => MirStepNode.fail .ub

/-- `LM-4.2` statement evaluator (using `evalCopyNonOverlappingLM4_2` on
`.intrinsic (.copyNonOverlapping ...)` and delegating all other statements to
Stage-1 `evalStmt`). -/
def evalStmtLM4_2
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlappingLM4_2 s src dst count localDecls layouts
  | _ => evalStmt s stmt localDecls layouts

/-- `LM-4.2` small-step function combining `evalStmtLM4_2` and
`evalTerminatorLM4_2`. -/
def stepMirFnLM4_2 (rootBody : CapturedMir) (s : MachineState) : MirStepNode :=
  let activeBody := s.memory.activeCallee.getD rootBody
  match activeBody.phase with
  | .other _ => MirStepNode.unsupported
  | _ =>
    match get? activeBody.basicBlocks s.frame.blockIdx with
    | .none => MirStepNode.fail .ub
    | .some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | .some stmt => evalStmtLM4_2 s stmt activeBody.localDecls activeBody.layouts
      | .none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminatorLM4_2 s bb.terminator (.some activeBody)
        else
          MirStepNode.fail .ub

theorem stepMirFnLM4_2_eq_of_not_other (body : CapturedMir) (s : MachineState)
    (hcal : s.memory.activeCallee = none)
    (hphase : ∀ p, body.phase ≠ .other p) :
    stepMirFnLM4_2 body s =
      match get? body.basicBlocks s.frame.blockIdx with
      | none => MirStepNode.fail .ub
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => evalStmtLM4_2 s stmt body.localDecls body.layouts
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminatorLM4_2 s bb.terminator (some body)
          else
            MirStepNode.fail .ub := by
  unfold stepMirFnLM4_2
  rw [hcal]
  dsimp only [Option.getD]
  cases hp : body.phase with
  | other p => exact False.elim (hphase p hp)
  | _ => rfl

/-! ## 1. Frame bookkeeping -/

/-- `StateRelLM3_1` survives advancing both machines to the next statement when
neither the locals of either machine nor Anneal's memory change. -/
theorem StateRelLM3_1.advance_same
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    StateRelLM3_1 body (advanceStmt s s.frame.locals)
      { m with stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace hfr.advance hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    exact halloc.local_alloc_sync tf hframes e he
  · intro i j mi mj li lj hne hi hj
    exact hdisj i j mi mj li lj hne hi hj

/-! ## 2. Call infrastructure -/

/-- `StateRelLM3_1` survives moving both machines to the same new location. -/
theorem StateRelLM3_1.relocate
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (b i : Nat) :
    StateRelLM3_1 body { s with frame := { s.frame with blockIdx := b, stmtIdx := i } }
      { m with stack := ⟨#[{ tf with location := .mir ⟨b, i⟩ }]⟩ } allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace
    ⟨hfr.body_eq, rfl, hfr.af_locals_len, hfr.mf_locals_size, hfr.locals_rel⟩
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    exact halloc.local_alloc_sync tf hframes e he
  · intro i j mi mj li lj hne hi hj
    exact hdisj i j mi mj li lj hne hi hj

/-- `annealReturnToBlock (some b)` moves the single frame to statement `0` of
block `b`. -/
theorem annealReturnToBlock_some {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (b : Nat) :
    annealReturnToBlock (some b) m =
      .ok () { m with stack := ⟨#[{ tf with location := .mir ⟨b, 0⟩ }]⟩ } := by
  unfold annealReturnToBlock Miri.Interpreter.ControlFlow.returnToBlock
    Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
  rw [stack_currentFrame?_singleton m.stack tf hframes, hframes]
  rfl

/-- The callee constant of a translated intrinsic call evaluates without
changing a single-frame state. -/
theorem annealEvalOperand_fnItemConst_ok (ld : List LocalDecl) (ly : LayoutTable)
    (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none m =
      .ok ⟨.immediate .uninit, layoutOfEncodedTyId (annealFnItemTyId k argTy) ly⟩ m := by
  rw [annealEvalOperand_fnItemConst]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some, Bool.false_eq_true,
    ↓reduceIte, pure, EStateM.pure]

/-- **Operand evaluation without the immediate read.** `annealEvalOperand` on a
well-typed primitive scalar operand, from `StateRelLM3_1`-related states, as in
`evalOperand_scalar_lm3_1_simulation` but before `annealReadImmediate`: a dead
local fails in both machines, an uninitialized local fails in Anneal and
evaluates to `Immediate.uninit` in `lean-miri` (whose later read fails), and an
initialized local or constant evaluates to related scalars. Only the layout
cache of the frame changes. -/
theorem annealEvalOperand_scalar_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty) :
    (∃ m' msg,
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok ⟨.immediate .uninit, translateTy ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ sc msc tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hsame : { m with stack := ⟨#[tf]⟩ } = m := stepState_with_same_singleton m tf hframes
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a :
        evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand
      dsimp only
      rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    right; right
    refine ⟨sc, msc, tf, heval_a, ?_, by rw [hsame]; exact hstate,
      .scalar sc msc hrel hlaysz hbool hchar, fun _ => rfl⟩
    rw [hsame]; exact heval_m
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hcache := hloc.cachedLayout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    have hvals : ∀ k : Nat,
        ((cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)).locals[k]?).map
          Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value := by
      intro k
      simp only [cacheFrameLocalLayout]
      by_cases hki : idx = k
      · subst hki
        rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
        rfl
      · rw [Array.getElem?_set_ne _ hki]
    cases hloc with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso
      rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
      | dead _ _ =>
        left
        refine ⟨{ m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt_mf
            (translateTy decl.ty body.layouts)]⟩ }, "read of dead local", ?_, ?_⟩
        · simp [evalOperand, hslot]
        · rw [htr]
          exact annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache
      | immediate _ imm _ _ hval =>
        have hstate' := hstate.cache_layout hframes hdecl hlt_mf
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · right; left
          refine ⟨_, ?_, ?_, hstate', hvals⟩
          · simp [evalOperand, hslot]
          · rw [htr]
            exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz_sc, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar hprim
          right; right
          refine ⟨sc, msc, _, ?_, ?_, hstate', .scalar sc msc hrel hsz_sc hbool hchar, hvals⟩
          · simp [evalOperand, readProjectedValue, hslot]
          · rw [htr]
            exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache

/-- Immediacy of a frame local depends only on the local values. -/
theorem IsImmediateFrameLocal.of_values_eq
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hvals : ∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
      (tf.locals[k]?).map Miri.Interpreter.LocalState.value)
    {j : Nat} (h : IsImmediateFrameLocal tf j) : IsImmediateFrameLocal tf' j := by
  intro mls hmls mp hmp
  have hv := hvals j
  rw [hmls] at hv
  cases hj : tf.locals[j]? with
  | none => rw [hj] at hv; cases hv
  | some mls₀ =>
    rw [hj] at hv
    injection hv with hv'
    exact h mls₀ hj mp (hv'.symm.trans hmp)

/-- **Write an intrinsic's scalar result and return to the call's target.**
From `StateRelLM3_1`-related states, writing the related scalars `r` / `mr` to
an immediate primitive-scalar destination local and moving to statement `0` of
`targetBb` either fails in both machines (dead destination) or succeeds in both
with `StateRelLM3_1`-related results. -/
theorem StateRelLM3_1.write_scalar_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hprim : IsPrimScalarTy dstDecl.ty)
    (himm : IsImmediateFrameLocal tf dstIdx)
    {r : MirAst.ScalarInt} {mr : Miri.Memory.ScalarInt}
    (hrelI : ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)))
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    (∃ msg m', writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) = .ub ∧
        (do
          annealWriteImmediate (.scalar (.fromScalarInt mr)) ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .error (.undefinedBehavior msg) m') ∨
    (∃ locals' tf',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) = .ok locals' ∧
        (do
          annealWriteImmediate (.scalar (.fromScalarInt mr)) ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .ok true { m with stack := ⟨#[tf']⟩ } ∧
        tf'.location = .mir ⟨targetBb, 0⟩ ∧
        StateRelLM3_1 body
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }
          { m with stack := ⟨#[tf']⟩ } allocMap) := by
  obtain ⟨tf₀, hframes₀, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have himm' := himm mls hmls
  have hget : tf.getLocal dstIdx = .ok mls := frame_getLocal_of_getElem? tf dstIdx mls hmls
  cases hloc with
  | rawPtr _ _ _ _ _ _ hty_raw _ =>
    exfalso
    rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
    | dead lay _ =>
      left
      refine ⟨"write to dead local", m, ?_, ?_⟩
      · simp [writePlaceValue, hslot]
      · rw [EStateM.bind_eq_error (annealWriteImmediate_dead hframes hget)]
    | immediate _ oldImm lay hlay hval =>
      have hne_dead : slot ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> nofun
      have hnot_dst := StateRelLM3_1.immediate_not_in_allocMap hstate hframes hslot hne_dead himm
      have hwrite_a : writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar r) =
          .ok (s.frame.locals.set dstIdx (.init (.scalar r))) := by
        have hset : set? s.frame.locals dstIdx (.init (.scalar r)) =
            some (s.frame.locals.set dstIdx (.init (.scalar r))) := set?_eq_some_set hlt_af _
        unfold writePlaceValue
        dsimp only
        rw [hslot, hset]
        cases slot with
        | dead => exact absurd rfl hne_dead
        | uninit => rfl
        | init _ => rfl
      let tfw : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { tf with
          locals := tf.locals.set dstIdx
            { tf.locals[dstIdx]'hlt_mf with value := .live (.immediate (.scalar (.fromScalarInt mr))) }
            hlt_mf }
      have hwrite_m := annealWriteImmediate_live (val := .scalar (.fromScalarInt mr))
        (id0 := id0) (dstLay := dstLay) hframes hlt_mf hget
      have hret := annealReturnToBlock_some (m := { m with stack := ⟨#[tfw]⟩ }) (tf := tfw) rfl
        targetBb
      right
      refine ⟨_, { tfw with location := .mir ⟨targetBb, 0⟩ }, hwrite_a, ?_, rfl, ?_⟩
      · rw [EStateM.bind_eq_ok hwrite_m, EStateM.bind_eq_ok hret]
        rfl
      · have hnew : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
            (.init (.scalar r))
            { tf.locals[dstIdx]'hlt_mf with
              value := .live (.immediate (.scalar (.fromScalarInt mr))) } := by
          rw [List.map_id]
          rw [hmls_eq]
          exact .base (.immediate _ _ lay hlay (Or.inr ⟨_, rfl, hrelI⟩))
        have hadv := StateRelLM3_1.advance_write_immediate_perm_map hstate hframes id
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hdecl hnot_dst
          (hlt_d := hlt_mf) (oldImm := oldImm) (by rw [hmls_eq]) hnew
          (mem' := s.memory) hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
        rw [List.map_id] at hadv
        exact hadv.relocate rfl targetBb 0

/-- `translateCalleeOperand` recognizes every `AnnealIntrinsic` by its
canonical `DefPath`. -/
theorem AnnealIntrinsic.ofDefPath?_defPath (k : AnnealIntrinsic) :
    AnnealIntrinsic.ofDefPath? k.defPath = some k := by
  cases k <;> rfl

/-- A well-typed scalar operand translates to a non-`Move` operand. -/
theorem WellTypedScalarOperand.translate_ne_move {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty} (h : WellTypedScalarOperand body tf op ty) :
    ∀ p, translateOperand op ≠ .Move p := by
  intro p hp
  cases h with
  | constScalar c _ _ _ _ _ _ _ _ =>
    simp only [translateOperand, reduceCtorEq] at hp
  | copyLocal idx _ _ _ _ =>
    simp only [translateOperand, reduceCtorEq] at hp

/-- The translation of a call of intrinsic `k` at any recognized `calleePath`
(`AnnealIntrinsic.ofDefPath? calleePath = some k`) with generic argument `argKind`,
a root-local destination, and a target. -/
theorem translateTerminator_intrinsic_call_ofDefPath?
    {term : Terminator} {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {calleePath : DefPath} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef calleePath [argKind])
    (hpath : AnnealIntrinsic.ofDefPath? calleePath = some k) :
    translateTerminator term =
      { sourceInfo := defaultSourceInfo
        kind := .Call
          (.Constant (annealFnItemConst k (encodeTyId { kind := argKind, layoutIdx := 0 })))
          (args.map fun a =>
            ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
          ⟨dstIdx, #[]⟩ (some targetBb) (translateUnwindAction unwind) .Normal
          defaultSpanRef } := by
  unfold translateTerminator
  rw [hterm]
  simp only [translateTerminatorKind, translateCalleeOperand, hc, hpath]
  rfl

/-- The translation of a call of intrinsic `k` with generic argument `argKind`,
a root-local destination, and a target. -/
theorem translateTerminator_intrinsic_call
    {term : Terminator} {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind]) :
    translateTerminator term =
      { sourceInfo := defaultSourceInfo
        kind := .Call
          (.Constant (annealFnItemConst k (encodeTyId { kind := argKind, layoutIdx := 0 })))
          (args.map fun a =>
            ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
          ⟨dstIdx, #[]⟩ (some targetBb) (translateUnwindAction unwind) .Normal
          defaultSpanRef } :=
  translateTerminator_intrinsic_call_ofDefPath? hterm hc (AnnealIntrinsic.ofDefPath?_defPath k)

/-- The location check of `Call.evalCallTerminator` and
`ControlFlow.evalTerminator` passes when the call moves to another location. -/
theorem frameLocation_beq_false {b i b' : Nat} (h : b' ≠ b ∨ i ≠ 0) :
    (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩ == .mir ⟨b, i⟩) = false := by
  cases hb : (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩ == .mir ⟨b, i⟩) with
  | false => rfl
  | true =>
    have heq := beq_iff_eq.mp hb
    injection heq with heq'
    injection heq' with h₁ h₂
    rcases h with h | h
    · exact absurd h₁ h
    · exact absurd h₂.symm h

/-- The location check of `ControlFlow.evalTerminator` passes when the call
moves to another location. -/
theorem option_frameLocation_beq_false {b i b' : Nat} (h : b' ≠ b ∨ i ≠ 0) :
    (some (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩) ==
      some (Miri.Interpreter.FrameLocation.mir ⟨b, i⟩)) = false := by
  cases hb : (some (Miri.Interpreter.FrameLocation.mir ⟨b', 0⟩) ==
      some (Miri.Interpreter.FrameLocation.mir ⟨b, i⟩)) with
  | false => rfl
  | true =>
    have heq := beq_iff_eq.mp hb
    injection heq with heq'
    injection heq' with heq''
    injection heq'' with h₁ h₂
    rcases h with h | h
    · exact absurd h₁ h
    · exact absurd h₂.symm h

/-- **One real step of a translated two-argument intrinsic call.** From
`StateRelLM3_1`-related states at a `TerminatorKind.call` of `AnnealIntrinsic`
`k` (whose arity is `2`) with well-typed primitive scalar arguments, an
immediate primitive-scalar root-local destination, and a target that moves the
frame, both machines take related steps, provided that:

* `hanneal`: Anneal evaluates the call by evaluating the arguments and then
  `annealCall` on their values;
* `hmiri_uninit₁` / `hmiri_uninit₂`: `Intrinsics.eval` reports undefined
  behavior on an uninitialized first argument, or on an uninitialized second
  argument after an initialized first one;
* `hsim`: on related initialized arguments, `annealCall` and `Intrinsics.eval`
  either both report undefined behavior, or both write related scalar results
  to the destination and return to the target.

Uninitialized and dead arguments and a dead destination are undefined behavior
in both machines. -/
theorem step_intrinsic_call_two_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} (hk : k.arity = 2) {argKind : RigidTy}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ty₁ ty₂ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstPrim : IsPrimScalarTy dstDecl.ty)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (annealCall : List Value → List LocalSlot → MirStepNode)
    (hanneal : evalTerminator s bb.terminator (some body) =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' => annealCall vs locals'
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported)
    (hmiri_uninit₁ : ∀ (v₂ : Miri.Interpreter.OpTy AnnealProv)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState), ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate .uninit, translateTy ty₁ body.layouts⟩, v₂] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hmiri_uninit₂ : ∀ (msc₁ : Miri.Memory.ScalarInt)
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState), ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
          ⟨.immediate .uninit, translateTy ty₂ body.layouts⟩] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hsim : ∀ (sc₁ sc₂ : MirAst.ScalarInt) (msc₁ msc₂ : Miri.Memory.ScalarInt),
      ImmediateRel ty₁ body.layouts (.scalar sc₁) (.scalar (.fromScalarInt msc₁)) →
      ImmediateRel ty₂ body.layouts (.scalar sc₂) (.scalar (.fromScalarInt msc₂)) →
      ∀ (id0 : Miri.Interpreter.LocalsIdentity) (m' : AnnealStepState),
        (annealCall [.scalar sc₁, .scalar sc₂] s.frame.locals = MirStepNode.fail .ub ∧
          ∃ msg, Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            .error (.undefinedBehavior msg) m') ∨
        (∃ r mr,
          ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)) ∧
          annealCall [.scalar sc₁, .scalar sc₂] s.frame.locals =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb (.scalar r) ∧
          Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            (do
              annealWriteImmediate (.scalar (.fromScalarInt mr))
                ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩
              annealReturnToBlock (some targetBb)
              pure true) m')) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [hanneal, miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_two _ _ k _ hk _ _ ((hop₁ tf hframes).translate_ne_move)
      ((hop₂ tf hframes).translate_ne_move)]
  -- Destination place and callee.
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  -- First argument.
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, hstate₂, hvals₂⟩ | ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, hrel₁, hvals₂⟩
  · rw [EStateM.bind_eq_error hm₁]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, _, hm₂⟩ | ⟨tf₃, _, hm₂, _, _⟩ | ⟨sc₂, msc₂, tf₃, _, hm₂, _, _, _⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₁ ⟨.immediate .uninit, translateTy ty₂ body.layouts⟩
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₁
        ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty₂ body.layouts⟩
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, _, _⟩ |
        ⟨sc₂, msc₂, tf₃, ha₂, hm₂, hstate₃, hrel₂, hvals₃⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      obtain ⟨msg, hev⟩ := hmiri_uninit₂ msc₁
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf₃]⟩ }
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hevals : evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok [.scalar sc₁, .scalar sc₂] s.frame.locals := by
        simp only [evalOperands, ha₁, ha₂]
      simp only [hevals]
      rcases hsim sc₁ sc₂ msc₁ msc₂ hrel₁ hrel₂ tf.localsIdentity
          { m with stack := ⟨#[tf₃]⟩ } with
        ⟨ha, msg, hev⟩ | ⟨r, mr, hrelR, ha, hev⟩
      · rw [EStateM.bind_eq_error hev, ha]
        exact .ub _ _
      · have himm₃ : IsImmediateFrameLocal tf₃ dstIdx :=
          IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ dstIdx (hdstImm tf hframes))
        rcases StateRelLM3_1.write_scalar_return hstate₃ rfl hdst hdstPrim himm₃ hrelR
            tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
          ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
        · rw [EStateM.bind_eq_error (hev.trans hwm), ha]
          simp only [intrinsicWriteReturn, hwa]
          exact .ub _ _
        · rw [EStateM.bind_eq_ok (hev.trans hwm), ha]
          simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
            Option.isSome_some]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq (m := { m with stack := ⟨#[tf₄]⟩ })
            (tf := tf₄) rfl)]
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
            (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
          rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
          simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
            stack_currentFrame?_singleton m.stack tf hframes, hframes,
            stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
              Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
            option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
          exact .step _ _ hstate₄
/-- **One real step of a translated one-argument intrinsic call**, as
`step_intrinsic_call_two_simulation`. -/
theorem step_intrinsic_call_one_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {k : AnnealIntrinsic} (hk : k.arity = 1) {argKind : RigidTy}
    {c : ConstOperand} {op₁ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ty₁ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hprim₁ : IsPrimScalarTy ty₁)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstPrim : IsPrimScalarTy dstDecl.ty)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (annealCall : List Value → List LocalSlot → MirStepNode)
    (hanneal : evalTerminator s bb.terminator (some body) =
      match evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals with
      | .ok vs locals' => annealCall vs locals'
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported)
    (hmiri_uninit₁ : ∀ (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState),
      ∃ msg,
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
        #[⟨.immediate .uninit, translateTy ty₁ body.layouts⟩] dest (some targetBb) m' =
        .error (.undefinedBehavior msg) m')
    (hsim : ∀ (sc₁ : MirAst.ScalarInt) (msc₁ : Miri.Memory.ScalarInt),
      ImmediateRel ty₁ body.layouts (.scalar sc₁) (.scalar (.fromScalarInt msc₁)) →
      ∀ (id0 : Miri.Interpreter.LocalsIdentity) (m' : AnnealStepState),
        (annealCall [.scalar sc₁] s.frame.locals = MirStepNode.fail .ub ∧
          ∃ msg, Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            .error (.undefinedBehavior msg) m') ∨
        (∃ r mr,
          ImmediateRel dstDecl.ty body.layouts (.scalar r) (.scalar (.fromScalarInt mr)) ∧
          annealCall [.scalar sc₁] s.frame.locals =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb (.scalar r) ∧
          Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }]
            #[⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty₁ body.layouts⟩]
            ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩ (some targetBb) m' =
            (do
              annealWriteImmediate (.scalar (.fromScalarInt mr))
                ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩
              annealReturnToBlock (some targetBb)
              pure true) m')) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [hanneal, miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_one _ _ k _ hk _ ((hop₁ tf hframes).translate_ne_move)]
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, _, _⟩ |
      ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, hrel₁, hvals₂⟩
  · rw [EStateM.bind_eq_error hm₁]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    obtain ⟨msg, hev⟩ := hmiri_uninit₁
      ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
      { m with stack := ⟨#[tf₂]⟩ }
    rw [EStateM.bind_eq_error hev]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · rw [EStateM.bind_eq_ok hm₁]
    have hevals : evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok [.scalar sc₁] s.frame.locals := by
      simp only [evalOperands, ha₁]
    simp only [hevals]
    rcases hsim sc₁ msc₁ hrel₁ tf.localsIdentity { m with stack := ⟨#[tf₂]⟩ } with
      ⟨ha, msg, hev⟩ | ⟨r, mr, hrelR, ha, hev⟩
    · rw [EStateM.bind_eq_error hev, ha]
      exact .ub _ _
    · have himm₂ : IsImmediateFrameLocal tf₂ dstIdx :=
        IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ dstIdx (hdstImm tf hframes))
      rcases StateRelLM3_1.write_scalar_return hstate₂ rfl hdst hdstPrim himm₂ hrelR
          tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
        ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
      · rw [EStateM.bind_eq_error (hev.trans hwm), ha]
        simp only [intrinsicWriteReturn, hwa]
        exact .ub _ _
      · rw [EStateM.bind_eq_ok (hev.trans hwm), ha]
        simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
          Option.isSome_some]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq (m := { m with stack := ⟨#[tf₄]⟩ })
          (tf := tf₄) rfl)]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
          (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
        rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
        simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, hframes,
          stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
            Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
          option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
        exact .step _ _ hstate₄

private theorem listByteEq_eq_true_iff {xs ys : List UInt8} :
    listByteEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [listByteEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listByteEq]
    | cons y ys =>
      unfold listByteEq
      cases hb : Nat.beq x.toBitVec.toNat y.toBitVec.toNat with
      | false =>
        refine ⟨(fun h => nomatch h), fun h => ?_⟩
        cases h; simp [Nat.beq_refl] at hb
      | true =>
        have hxy : x = y :=
          UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
        subst hxy
        simpa using ih

/-- If `stringEq a a' = true`, `a` and `a'` have identical UTF-8 byte lists, so
`stringEq a b = stringEq a' b` for every `b`. -/
theorem stringEq_congr_left {a a' : String} (h : stringEq a a' = true) (b : String) :
    stringEq a b = stringEq a' b := by
  unfold stringEq at h ⊢
  rw [listByteEq_eq_true_iff.mp h]

/-- Classification of `DefPath`s recognized by `AnnealIntrinsic.ofDefPath?`:
every match satisfies `stringEq p k.defPath = true` or one of the two
`std::intrinsics::*` offset aliases. -/
theorem AnnealIntrinsic.ofDefPath?_cases {p : DefPath} {k : AnnealIntrinsic}
    (h : AnnealIntrinsic.ofDefPath? p = some k) :
    stringEq p k.defPath = true ∨
      (k = .arithOffset ∧ stringEq p "std::intrinsics::arith_offset" = true) ∨
      (k = .wrappingOffset ∧ stringEq p "std::intrinsics::wrapping_offset" = true) := by
  unfold AnnealIntrinsic.ofDefPath? at h
  cases hfind : AnnealIntrinsic.all.find? (fun x => stringEq p x.defPath) with
  | some k' =>
    rw [hfind] at h
    injection h with hk
    subst hk
    exact Or.inl (by simpa using List.find?_some hfind)
  | none =>
    rw [hfind] at h
    by_cases h1 : stringEq p "std::intrinsics::arith_offset" = true
    · simp only [h1, ↓reduceIte] at h
      injection h with hk
      exact Or.inr (Or.inl ⟨hk.symm, h1⟩)
    · have h1f : stringEq p "std::intrinsics::arith_offset" = false :=
        Bool.eq_false_iff.mpr h1
      simp only [h1f, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : stringEq p "std::intrinsics::wrapping_offset" = true
      · simp only [h2, ↓reduceIte] at h
        injection h with hk
        exact Or.inr (Or.inr ⟨hk.symm, h2⟩)
      · have h2f : stringEq p "std::intrinsics::wrapping_offset" = false :=
          Bool.eq_false_iff.mpr h2
        simp only [h2f, Bool.false_eq_true, ↓reduceIte] at h
        cases h

/-- Anneal's `evalTerminatorLM4_2` on a call at any recognized `calleePath` of an
inline `AnnealIntrinsic` other than `exact_div` with no transparent body:
evaluate the arguments, then `evalInlineIntrinsicCall?`. -/
theorem evalTerminator_inline_intrinsic_call_ofDefPath?
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {calleePath : DefPath} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef calleePath [argKind])
    (hcallee : findCallee? s.memory.callees calleePath = none)
    (hpath : AnnealIntrinsic.ofDefPath? calleePath = some k)
    (hk : k ≠ .exactDiv) :
    evalTerminatorLM4_2 s term (some body) =
      match evalOperands s.frame.locals args s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match evalInlineIntrinsicCall? s calleePath args vs locals' ⟨dstIdx, []⟩ targetBb
            body.localDecls body.layouts with
        | some node => node
        | none =>
          MirStepNode.extCall { defPath := calleePath, args := vs, memory := s.memory }
            (resumeExternalCall s locals' ⟨dstIdx, []⟩ targetBb unwind)
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  have hne : stringEq calleePath "core::intrinsics::exact_div" = false := by
    rcases AnnealIntrinsic.ofDefPath?_cases hpath with hdef | ⟨_, hstd⟩ | ⟨_, hstd⟩
    · rw [stringEq_congr_left hdef]
      cases k <;> first | rfl | exact absurd rfl hk
    · rw [stringEq_congr_left hstd]; rfl
    · rw [stringEq_congr_left hstd]; rfl
  unfold evalTerminatorLM4_2
  rw [hterm]
  simp only [extractCalleeDefPath?, hc]
  cases evalOperands s.frame.locals args s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' => simp only [hcallee, hne] <;> rfl
  | ub => rfl
  | unsupported => rfl

/-- Anneal's `evalTerminatorLM4_2` on a call of an inline `AnnealIntrinsic` other
than `exact_div` with no transparent body: evaluate the arguments, then
`evalInlineIntrinsicCall?`. -/
theorem evalTerminator_inline_intrinsic_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {args : List MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction} {k : AnnealIntrinsic} {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) args ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    (hcallee : findCallee? s.memory.callees k.defPath = none)
    (hk : k ≠ .exactDiv) :
    evalTerminatorLM4_2 s term (some body) =
      match evalOperands s.frame.locals args s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match evalInlineIntrinsicCall? s k.defPath args vs locals' ⟨dstIdx, []⟩ targetBb
            body.localDecls body.layouts with
        | some node => node
        | none =>
          MirStepNode.extCall { defPath := k.defPath, args := vs, memory := s.memory }
            (resumeExternalCall s locals' ⟨dstIdx, []⟩ targetBb unwind)
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported :=
  evalTerminator_inline_intrinsic_call_ofDefPath? hterm hc hcallee
    (AnnealIntrinsic.ofDefPath?_defPath k) hk

/-- The `AnnealIntrinsic` of a one-operand integer bit intrinsic. -/
def AnnealIntrinsic.ofBit : IntegerBitIntrinsic → AnnealIntrinsic
  | .ctpop => .ctpop
  | .ctlz => .ctlz
  | .ctlzNonzero => .ctlzNonzero
  | .cttz => .cttz
  | .cttzNonzero => .cttzNonzero
  | .bswap => .bswap
  | .bitreverse => .bitreverse

theorem AnnealIntrinsic.ofBit_arity (op : IntegerBitIntrinsic) :
    (AnnealIntrinsic.ofBit op).arity = 1 := by
  cases op <;> rfl

theorem AnnealIntrinsic.ofBit_numeric (op : IntegerBitIntrinsic) :
    (AnnealIntrinsic.ofBit op).numeric? = some (toMiriIntegerIntrinsic op) := by
  cases op <;> rfl

theorem AnnealIntrinsic.ofBit_ne_exactDiv (op : IntegerBitIntrinsic) :
    AnnealIntrinsic.ofBit op ≠ .exactDiv := by
  cases op <;> nofun

theorem integerBitIntrinsicOfPath?_ofBit (op : IntegerBitIntrinsic) :
    integerBitIntrinsicOfPath? (AnnealIntrinsic.ofBit op).defPath = some op := by
  cases op <;> rfl

/-- The byte width of an integral type, as `intCastTargetBytes` reports it. -/
theorem IsIntegralTy.intCastTargetBytes_eq {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) :
    intCastTargetBytes ty.kind = some (integerKindByteWidth kind) := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]; cases it <;> rfl
  · rw [hk]; cases ut <;> rfl

/-- The signedness of an integral type, as `intrinsicIntSignedness? false` reports it. -/
theorem IsIntegralTy.intrinsicIntSignedness?_eq {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) :
    intrinsicIntSignedness? false ty.kind = some kind.signed := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]; cases it <;> rfl
  · rw [hk]; cases ut <;> rfl

/-- Stage-1 `evalTerminator` on a call of `AnnealIntrinsic.ofBit op` when unlinked:
evaluates the argument and runs the Stage-1 bit intrinsic (`evalCtpop`, `evalCtlz`,
`evalCtlzNonzero`, `evalCttz`, `evalCttzNonzero`, `evalBswap`, `evalBitreverse`). -/
theorem evalTerminator_stage1_bitcount_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {op₁ : MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    (op : IntegerBitIntrinsic) {argKind : RigidTy}
    (hterm : term.kind = .call (.constant c) [op₁] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef (AnnealIntrinsic.ofBit op).defPath [argKind])
    (hcallee : lookupCallee s.memory.callees body.layouts (AnnealIntrinsic.ofBit op).defPath
      [argKind] s.memory.traitImpls = none) :
    evalTerminator s term (some body) =
      match evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match vs with
        | .scalar sc :: .nil =>
          writeIntrinsicScalarResult s locals' ⟨dstIdx, []⟩ targetBb
            (match op with
            | .ctpop => evalCtpop sc
            | .ctlz => evalCtlz sc
            | .ctlzNonzero => evalCtlzNonzero sc
            | .cttz => evalCttz sc
            | .cttzNonzero => evalCttzNonzero sc
            | .bswap => evalBswap sc
            | .bitreverse => evalBitreverse sc)
        | _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalTerminator
  rw [hterm]
  simp only [resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hc]
  cases evalOperands s.frame.locals [op₁] s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' =>
    simp only [hcallee]
    cases op <;> rfl
  | ub => rfl
  | unsupported => rfl

/-- Stage-1 `evalTerminator` on a call of `saturating_add` (`isAdd = true`) or
`saturating_sub` (`isAdd = false`) at integral type `ty` when unlinked. -/
theorem evalTerminator_stage1_saturating_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {k : AnnealIntrinsic} {isAdd : Bool}
    (hsat : (k = .saturatingAdd ∧ isAdd = true) ∨ (k = .saturatingSub ∧ isAdd = false))
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hterm : term.kind = .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [ty.kind])
    (hcallee : lookupCallee s.memory.callees body.layouts k.defPath [ty.kind]
      s.memory.traitImpls = none) :
    evalTerminator s term (some body) =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match vs with
        | .scalar lhs :: .scalar rhs :: .nil =>
          writeIntrinsicScalarResult s locals' ⟨dstIdx, []⟩ targetBb
            (if isAdd then evalSaturatingAdd lhs rhs kind.signed
             else evalSaturatingSub lhs rhs kind.signed)
        | _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalTerminator
  rw [hterm]
  simp only [resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hc]
  cases evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' =>
    simp only [hcallee]
    rcases hsat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · dsimp only [isDirectExactDivTarget, AnnealIntrinsic.defPath, stringEq, listByteEq,
        evalDirectRustIntrinsic?, classifyRustIntrinsic?, evalNonSelectIntrinsicCall,
        resolveIntrinsicIsSigned]
      rw [hint.intrinsicIntSignedness?_eq]
      rfl
  | ub => rfl
  | unsupported => rfl

/-- Stage-1 `evalTerminator` on a call of `exact_div` at integral type `ty` when unlinked. -/
theorem evalTerminator_stage1_exactDiv_call
    {s : MachineState} {body : CapturedMir} {term : Terminator}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local}
    {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {ty : Ty} {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (hterm : term.kind = .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef AnnealIntrinsic.exactDiv.defPath [ty.kind])
    (hcallee : lookupCallee s.memory.callees body.layouts AnnealIntrinsic.exactDiv.defPath
      [ty.kind] s.memory.traitImpls = none) :
    evalTerminator s term (some body) =
      match evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
      | .ok vs locals' =>
        match vs with
        | .scalar lhs :: .scalar rhs :: .nil =>
          match evalExactDiv lhs rhs kind.signed with
          | .some retScalar =>
            intrinsicWriteReturn s locals' ⟨dstIdx, []⟩ targetBb (.scalar retScalar)
          | .none => MirStepNode.fail .ub
        | _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalTerminator
  rw [hterm]
  simp only [resolveCallTarget, extractCalleeDefPath?, extractCalleeTypeArgs, hc]
  cases evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals with
  | ok vs locals' =>
    simp only [hcallee]
    dsimp only [isDirectExactDivTarget, AnnealIntrinsic.defPath, stringEq, listByteEq,
      resolveIntrinsicIsSigned]
    rw [hint.intrinsicIntSignedness?_eq]
    rfl
  | ub => rfl
  | unsupported => rfl

/-! ## 3. `rotate_left` / `rotate_right`

`lean-miri`'s pinned dispatcher `Intrinsics.eval` has no arm for
`rotate_left` / `rotate_right`: the names are neither atomic, SIMD, numeric, nor
float intrinsics, and `annealIntrinsicHooks` provides no `mathHooks`, so
`Intrinsics.eval` returns `false` without changing the state. The call then
needs the intrinsic's MIR fallback body, which `annealCallHooks.findMirOrEvalFn`
rejects with `StepError.unsupported`.
-/

/-- `"rotate_left"` names no portable float intrinsic. -/
theorem rotateLeft_not_float :
    ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32), ("f64", .binary64),
      ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_left".endsWith suffix then
          some (("rotate_left".dropEnd suffix.length).toString, format)
        else none) = none := by
  have h16 : "rotate_left".endsWith "f16" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h32 : "rotate_left".endsWith "f32" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h64 : "rotate_left".endsWith "f64" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h128 : "rotate_left".endsWith "f128" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  simp only [List.findSome?, h16, h32, h64, h128, Bool.false_eq_true, ↓reduceIte]

/-- `Intrinsics.floatIntrinsic` does not handle `"rotate_left"`. -/
theorem floatIntrinsic_rotateLeft
    {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V)
    (choice : C) (args : Array (Miri.Interpreter.OpTy P)) (dest : V) :
    Miri.Interpreter.Intrinsics.floatIntrinsic h choice "rotate_left" args dest = pure false := by
  unfold Miri.Interpreter.Intrinsics.floatIntrinsic
  split
  · next base format hfl =>
    exfalso
    have h' := rotateLeft_not_float
    rw [show ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32),
      ("f64", .binary64), ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_left".endsWith suffix then
          some (("rotate_left".dropEnd suffix.length).toString, format)
        else none) = some (base, format) from hfl] at h'
    cases h'
  · rfl

/-- `"rotate_right"` names no portable float intrinsic. -/
theorem rotateRight_not_float :
    ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32), ("f64", .binary64),
      ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_right".endsWith suffix then
          some (("rotate_right".dropEnd suffix.length).toString, format)
        else none) = none := by
  have h16 : "rotate_right".endsWith "f16" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h32 : "rotate_right".endsWith "f32" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h64 : "rotate_right".endsWith "f64" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  have h128 : "rotate_right".endsWith "f128" = false := by
    rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]; simp; decide
  simp only [List.findSome?, h16, h32, h64, h128, Bool.false_eq_true, ↓reduceIte]

/-- `Intrinsics.floatIntrinsic` does not handle `"rotate_right"`. -/
theorem floatIntrinsic_rotateRight
    {P S C V : Type} [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.IntrinsicHooks P S C V)
    (choice : C) (args : Array (Miri.Interpreter.OpTy P)) (dest : V) :
    Miri.Interpreter.Intrinsics.floatIntrinsic h choice "rotate_right" args dest = pure false := by
  unfold Miri.Interpreter.Intrinsics.floatIntrinsic
  split
  · next base format hfl =>
    exfalso
    have h' := rotateRight_not_float
    rw [show ([("f16", Miri.Interpreter.FloatFormat.binary16), ("f32", .binary32),
      ("f64", .binary64), ("f128", .binary128)] : List (String × Miri.Interpreter.FloatFormat)).findSome?
      (fun (suffix, format) =>
        if "rotate_right".endsWith suffix then
          some (("rotate_right".dropEnd suffix.length).toString, format)
        else none) = some (base, format) from hfl] at h'
    cases h'
  · rfl

/-- `Intrinsics.eval` leaves `rotate_left` to its MIR fallback body. -/
theorem intrinsics_eval_rotateLeft (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateLeft.name types args dest target = pure false := by
  have h : Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateLeft.name types args dest target =
      (do
        if !(← Miri.Interpreter.Intrinsics.floatIntrinsic (annealIntrinsicHooks ld ly) ()
            "rotate_left" args dest) then
          return false
        annealReturnToBlock target
        return true) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [h, floatIntrinsic_rotateLeft]
  rfl

/-- `Intrinsics.eval` leaves `rotate_right` to its MIR fallback body. -/
theorem intrinsics_eval_rotateRight (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateRight.name types args dest target = pure false := by
  have h : Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.rotateRight.name types args dest target =
      (do
        if !(← Miri.Interpreter.Intrinsics.floatIntrinsic (annealIntrinsicHooks ld ly) ()
            "rotate_right" args dest) then
          return false
        annealReturnToBlock target
        return true) := by
    unfold Miri.Interpreter.Intrinsics.eval
    simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [h, floatIntrinsic_rotateRight]
  rfl

/-- **`lean-miri` on a two-argument intrinsic that `Intrinsics.eval` leaves
unhandled.** From `StateRelLM3_1`-related states at a translated call of `k`
whose `Intrinsics.eval` returns `false` without changing the state, the real
`lean-miri` step reports undefined behavior for a dead argument (as Anneal's
argument evaluation does) and otherwise fails closed with
`StepError.unsupported` (the MIR fallback body is outside the fragment). It
never takes a successful step. -/
theorem step_intrinsic_call_two_unhandled
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {k : AnnealIntrinsic} (hk : k.arity = 2) {argKind : RigidTy}
    {c : ConstOperand} {op₁ op₂ : MirAst.Operand} {dstIdx : Local} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [op₁, op₂] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef k.defPath [argKind])
    {ty₁ ty₂ : Ty}
    (hop₁ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₁ ty₁)
    (hop₂ : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂)
    {dstDecl : LocalDecl} (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hunhandled : ∀ (args : Array (Miri.Interpreter.OpTy AnnealProv))
      (dest : Miri.Interpreter.RuntimePlace AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks body.localDecls body.layouts) ()
        k.name #[encodeTyId { kind := argKind, layoutIdx := 0 }] args dest (some targetBb) m' =
        .ok false m') :
    (∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported msg))) ∨
    (∃ m' msg, Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) ∧
      evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call hterm hc]
  simp only [List.map_cons, List.map_nil]
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_two _ _ k _ hk _ _ ((hop₁ tf hframes).translate_ne_move)
      ((hop₂ tf hframes).translate_ne_move)]
  obtain ⟨dslot, dmls, hlt_af, hlt_mf, hdslot, hdmls, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := argKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  have hfinish : ∀ (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (m₃ : AnnealStepState),
      ∃ msg, (do
        let handled ← Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) () k.name
          #[encodeTyId { kind := argKind, layoutIdx := 0 }] #[v₁, v₂]
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          (some targetBb)
        if handled then pure ()
        else (annealUnsupportedLeaf
          "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
        if (some targetBb).isSome then
          if (← (annealPlaceHooks body.localDecls body.layouts).frameIndex) == 0 then
            if (← (annealPlaceHooks body.localDecls body.layouts).getFrame).location ==
                tf.location then
              throw (Miri.Interpreter.StepError.invalidProgram
                "evaluating this call made no progress")) m₃ =
        .error (.unsupported msg) m₃ := by
    intro v₁ v₂ m₃
    rw [EStateM.bind_eq_ok (hunhandled _ _ m₃)]
    exact ⟨_, rfl⟩
  rcases annealEvalOperand_scalar_lm3_1 hstate₁ rfl ((hop₁ tf hframes).mono_immediate himm₁)
      hprim₁ with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, hstate₂, hvals₂⟩ |
      ⟨sc₁, msc₁, tf₂, ha₁, hm₁, hstate₂, _, hvals₂⟩
  · right
    refine ⟨m₂, msg, ?_, by simp only [evalOperands, ha₁]⟩
    rw [EStateM.bind_eq_error hm₁]
    rfl
  all_goals
    rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hop₂ tf hframes).mono_immediate himm₂)
        hprim₂ with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, _, hm₂, _, _⟩ | ⟨sc₂, msc₂, tf₃, _, hm₂, _, _, _⟩
    · right
      refine ⟨m₃, msg, ?_, by simp only [evalOperands, ha₁, ha₂]⟩
      rw [EStateM.bind_eq_error hm₂]
      rfl
    all_goals
      rw [EStateM.bind_eq_ok hm₂]
      left
      obtain ⟨msg, hfin⟩ := hfinish _ _ { m with stack := ⟨#[tf₃]⟩ }
      refine ⟨{ m with stack := ⟨#[tf₃]⟩ }, msg, ?_⟩
      rw [hfin]
      rfl

/-- Anneal's evaluation of two well-typed primitive scalar arguments from
`StateRelLM3_1`-related states: undefined behavior, or two scalars related to
`lean-miri` immediates of their types (and unchanged locals). -/
theorem evalOperands_two_scalar_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op₁ op₂ : MirAst.Operand} {ty₁ ty₂ : Ty}
    (hop₁ : WellTypedScalarOperand body tf op₁ ty₁) (hop₂ : WellTypedScalarOperand body tf op₂ ty₂)
    (hprim₁ : IsPrimScalarTy ty₁) (hprim₂ : IsPrimScalarTy ty₂) :
    evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∨
    ∃ a b ma mb, evalOperands s.frame.locals [op₁, op₂] s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok [.scalar a, .scalar b] s.frame.locals ∧
      ImmediateRel ty₁ body.layouts (.scalar a) (.scalar (.fromScalarInt ma)) ∧
      ImmediateRel ty₂ body.layouts (.scalar b) (.scalar (.fromScalarInt mb)) := by
  rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop₁ hprim₁ with
    ⟨_, _, ha₁, _⟩ | ⟨_, ha₁, _⟩ | ⟨a, ma, _, ha₁, _, _, hrel₁, _⟩
  · left; simp only [evalOperands, ha₁]
  · left; simp only [evalOperands, ha₁]
  · rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop₂ hprim₂ with
      ⟨_, _, ha₂, _⟩ | ⟨_, ha₂, _⟩ | ⟨b, mb, _, ha₂, _, _, hrel₂, _⟩
    · left; simp only [evalOperands, ha₁, ha₂]
    · left; simp only [evalOperands, ha₁, ha₂]
    · right
      exact ⟨a, b, ma, mb, by simp only [evalOperands, ha₁, ha₂], hrel₁, hrel₂⟩

/-- The size of an Anneal scalar related to an immediate of an integral type is
that type's byte width. -/
theorem ImmediateRel.integral_sizeBytes {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind) {layouts : LayoutTable} {a : MirAst.ScalarInt}
    {ma : Miri.Memory.ScalarInt}
    (h : ImmediateRel ty layouts (.scalar a) (.scalar (.fromScalarInt ma))) :
    a.sizeBytes = integerKindByteWidth kind := by
  cases h with
  | scalar _ _ hrel hsz _ _ =>
    have hvalid : ValidScalarBytes (integerKindByteWidth kind) := by
      unfold ValidScalarBytes; cases kind <;> simp [integerKindByteWidth]
    exact translateSizeBytes_inj hrel.validBytes hvalid (hsz.symm.trans (hint.size_eq layouts))

end LeanMiriSpec.Correspondence
