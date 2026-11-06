/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.IntrinsicFallback
import Trusted.VerificationResult

/-!
# Boundary witnesses and external-handler correspondence for intrinsics

`IntrinsicFallback` covers intrinsic calls whose fallback bodies are passed in
`callees`. This module records, by kernel computation and symbolic proof, what
happens to the intrinsic-related MIR constructs outside `progInFragment` (note
that `StatementKind::Intrinsic(Assume)` *is* now inside `progInFragment`; see
`Witness.lean`):

1. `Rvalue::NullaryOp(UbChecks)`: Anneal fails closed (`unsupported`), while
   `minimize` produces a `bool` constant fixed by the compilation session.
2. `StatementKind::Intrinsic(CopyNonOverlapping)`: Anneal executes it, while
   `minimize` aborts translation. With `count = 0` Anneal never checks that
   `src` and `dst` are pointers, and a two-element `u32` copy between two
   4-byte locals returns normally with no UB (`bdCopy2_noUB`).
3. `BinOp::Offset`: Anneal adds the raw count to `offsetBytes`, without
   scaling, a bounds check, or a sign interpretation; `minimize` scales by the
   pointee size and emits an in-bounds byte offset. `arith_offset` remains an
   external call in Anneal.
4. Calls to `core::intrinsics::*` without a body in `callees` become external
   `MirCallReq` requests carrying only `defPath`, `args`, and `memory`. When
   interpreted via `mirHandledTree` (`Trusted.VerificationResult`), an
   `ExternalCallHandler` can return values or raise UB (`ITree.fail .ub` in
   `MirClosedEffect`):
   * `cold_path` (`coldPathHandler`) corresponds to `minimize`'s no-op `Goto`.
   * `ctpop` (`ctpopHandler`) corresponds uniformly across all signed and
     unsigned `IntType`s because `evalCountOnes (intFromBits bits it) it`
     depends only on the low `8 * it.size.bytes` bits (`evalCountOnes_intFromBits`,
     `evalCountOnes_signedness_indep`).
   * `exact_div::<T>` erases `Signedness` in `MirCallReq` (`bdExactDiv_same_request`),
     so a single untyped handler cannot simultaneously match `exact_div::<i32>`
     and `exact_div::<u32>`, whereas the monomorphized handler
     `exactDivHandler it` matches MiniRust's `IntBinOp::DivExact` on both valid
     quotients and all three UB conditions (`/ 0`, signed `MIN / -1`, and
     `left % right != 0`).
   * Diverging `abort` calls hit `MirStepNode.unsupported` before `MirCallE`.
5. `core::hint::unreachable_unchecked()`: Anneal raises UB, like MiniRust's
   `Terminator::Unreachable`; the fragment rejects the call form but covers
   MIR's own `TerminatorKind::Unreachable`.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
open Trusted.VerificationResult (MirClosedEffect ExternalCallHandler
  handleMirExternalCalls mirHandledTree mirStatefulTree
  initMachineStateWithMemory)
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence.Witness

/-! ## Shared building blocks -/

def bdDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
def bdUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def bdIsizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }
def bdUnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def bdNeverTy : Ty := { kind := .never, layoutIdx := 0 }
def bdRawConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
def bdRawMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
def bdRefU32Ty : Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }

def bdConstUsize (n : Nat) : Operand := .constant { ty := bdUsizeTy, val := .scalar (.int ⟨n, 8⟩) }

/-- An `isize` constant with two's-complement bit pattern `bits`. -/
def bdConstIsize (bits : Nat) : Operand :=
  .constant { ty := bdIsizeTy, val := .scalar (.int ⟨bits, 8⟩) }

/-- A `Runtime(PostCleanup)` body; none of these bodies is translated, so the
ABI (whose layouts nothing reads) is a placeholder. -/
def bdBody (dp : String) (argCount : Nat) (decls : List LocalDecl)
    (bbs : List BasicBlockData) : CapturedMir where
  defPath := dp
  phase := .runtimePostCleanup
  role := .subject
  argCount := argCount
  localDecls := decls
  basicBlocks := bbs
  fnAbi := fbAbi [] u32Layout
  layouts := emptyLayoutTable
  allocations := []

/-- MIR of a body whose parameters `_1 .. _argCount` are passed by copy to
`calleeDp::<tys>`, with the result in `_0`:
```text
bb0: _0 = calleeDp::<tys>(copy _1, .., copy _argCount) -> [return: bb1, unwind unreachable]
bb1: return
```
With `target = none` the call is diverging (no return edge), as MIR writes a
call to a function returning `!`. -/
def bdCallBody (dp calleeDp : String) (tys : List RigidTy) (argCount : Nat)
    (decls : List LocalDecl) (target : Option Nat) : CapturedMir :=
  bdBody dp argCount decls [
    { statements := [],
      terminator := mkTerm (.call (fbFnOp calleeDp tys)
        ((List.range argCount).map fun i => .copy (local_ (i + 1))) (local_ 0) target .unreachable),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]

/-- The request of an external call node (`MirStepNode.extCall`), if any. -/
def bdCallReq? : MirStepNode → Option MirCallReq
  | .vis (.inr (.inr (.call req))) _ => some req
  | _ => none

/-! ## 1. `Rvalue::NullaryOp(UbChecks)` -/

/-- MIR of `fn ub_checks() -> bool`, which reads the `ub_checks` flag:
```text
bb0: _0 = UbChecks(); return
```
Anneal: `evalRvalue` (`Places.lean:1951`) has no arm for `Rvalue.nullaryOp`,
so its final catch-all arm (`Places.lean:2267`) returns `.unsupported`, and
the assignment arm of `evalStmt` (`Statements.lean:909`, `1020`) turns that
into `MirStepNode.unsupported`, a fault that no UB-free tree may reach.

`minimize`: `translate_rvalue_smir` (`rvalue.rs:8-371`) has no arm for a
nullary operation. In the stable MIR it consumes, the runtime-check flags are
the operand `Operand::RuntimeChecks`, which `translate_operand_smir`
(`rvalue.rs:384-393`) lowers to `build::const_bool(sess.ub_checks())`: a `bool`
constant fixed by the compilation session. Anneal's MIR (`Rvalue.nullaryOp`,
from `Rvalue::NullaryOp(RuntimeChecks, Ty)`) and `minimize`'s stable MIR thus
represent the flag differently. -/
def bdUbChecksBody : CapturedMir :=
  bdBody "boundary::ub_checks" 0 [boolDecl] [
    { statements := [mkStmt (.assign (local_ 0) (.nullaryOp .ubChecks boolTy))],
      terminator := mkTerm .return_, isCleanup := false }]

/-- Every nullary operation is unsupported in Anneal, in every state. -/
theorem bdNullaryOp_unsupported (locals : List LocalSlot) (op : NullOp) (ty : Ty) (mem : Memory)
    (decls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.nullaryOp op ty) mem decls layouts = .unsupported := rfl

theorem bdUbChecks_step :
    stepMirFn bdUbChecksBody (initMachineState bdUbChecksBody []) = MirStepNode.unsupported :=
  rfl

/-- Anneal cannot certify any execution of `bdUbChecksBody`. -/
theorem bdUbChecks_not_noUB : ¬ MirNoUBTree (mirCallTree bdUbChecksBody []) := by
  obtain ⟨tr, u, hr, hf⟩ :=
    faultsA_sound bdUbChecksBody 1 (initMachineState bdUbChecksBody []) rfl
  exact fun hsafe => hsafe tr u hr hf

theorem bdNullaryOp_translateRvalue (decls : List LocalDecl) (op : NullOp) (ty : Ty) :
    translateRvalue decls (.nullaryOp op ty) = none := rfl

theorem bdUbChecks_rejected :
    statementOk [boolDecl] (mkStmt (.assign (local_ 0) (.nullaryOp .ubChecks boolTy))) = false ∧
      inFragment bdUbChecksBody = false :=
  ⟨rfl, by decide⟩

/-! ## 2. `StatementKind::Intrinsic(CopyNonOverlapping)` -/

/-- MIR of a body that copies `n` `u32` elements from its parameter `_1` into
its return place `_0` through raw pointers:
```text
bb0: _0 = const 0_u32;
     StorageLive(_2); _2 = &raw const _1;
     StorageLive(_3); _3 = &raw mut _0;
     copy_nonoverlapping(src = copy _2, dst = copy _3, count = const n_usize);
     StorageDead(_3); StorageDead(_2); return
```
Anneal: the `.intrinsic (.copyNonOverlapping ..)` arm of `evalStmt`
(`Statements.lean:870-871`) calls `evalCopyNonOverlapping`
(`Statements.lean:697-749`), which evaluates the three operands and then
`evalCopyNonOverlappingWithCount` (`Statements.lean:357`). Its first test
(`Statements.lean:366-367`) steps to the next statement when the count is `0`,
without examining the values of `src` and `dst`.

`minimize`: the `StatementKind::Intrinsic` arm of statement translation
(`bb.rs:118-133`) lowers `Assume` to `IntrinsicOp::Assume` but stops with
`span_bug!` on `CopyNonOverlapping` (`bb.rs:130-131`), so `minimize` produces
no MiniRust program for this body. -/
def bdCopyBody (n : Nat) : CapturedMir :=
  bdBody "boundary::copy_nonoverlapping" 1
    [u32Decl, u32Decl, bdDecl bdRawConstU32Ty, bdDecl bdRawMutU32Ty] [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (constU32 0))),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (local_ 0))),
        mkStmt (.intrinsic (.copyNonOverlapping (.copy (local_ 2)) (.copy (local_ 3))
          (bdConstUsize n))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]

/-- `count = 0`: nothing is copied, and the function returns `0`. -/
theorem bdCopy0_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdCopyBody 0) [.scalar ⟨7, 4⟩]) []
      (.normal (.scalar ⟨0, 4⟩, mem)) :=
  ⟨_, runA_sound (bdCopyBody 0) 30 _ _ _ rfl⟩

/-- `count = 1`: the argument `7` is copied into `_0` and returned. -/
theorem bdCopy1_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdCopyBody 1) [.scalar ⟨7, 4⟩]) []
      (.normal (.scalar ⟨7, 4⟩, mem)) :=
  ⟨_, runA_sound (bdCopyBody 1) 30 _ _ _ rfl⟩

/-- `count = 2`: the copy covers `2 * size_of::<u32>() = 8` bytes, but `_1`
and `_0` are 4-byte locals, and the `copy_nonoverlapping` safety contract
requires `src` to be valid for reads and `dst` for writes of all 8 bytes.
Anneal nevertheless returns `7`, the same result as for `count = 1`. -/
theorem bdCopy2_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdCopyBody 2) [.scalar ⟨7, 4⟩]) []
      (.normal (.scalar ⟨7, 4⟩, mem)) :=
  ⟨_, runA_sound (bdCopyBody 2) 30 _ _ _ rfl⟩

/-- Anneal certifies the `count = 2` run free of UB. -/
theorem bdCopy2_noUB : MirNoUBTree (mirCallTree (bdCopyBody 2) [.scalar ⟨7, 4⟩]) :=
  runA_noUB (bdCopyBody 2) 30 _ _ _ rfl

/-- A `copy_nonoverlapping` with `count = 0` and two non-pointer operands. -/
def bdCopyZeroScalars : MirAst.Statement :=
  mkStmt (.intrinsic (.copyNonOverlapping (constU32 0) (constU32 0) (bdConstUsize 0)))

/-- With `count = 0`, Anneal steps past the statement in every state, even
though neither `src` nor `dst` is a pointer. -/
theorem bdCopyZeroScalars_step (s : MachineState) (decls : List LocalDecl)
    (layouts : LayoutTable) :
    evalStmt s bdCopyZeroScalars decls layouts = MirStepNode.step (advanceStmt s s.frame.locals) :=
  rfl

theorem bdCopy_translateStatement (decls : List LocalDecl) (src dst count : Operand) :
    translateStatement decls (mkStmt (.intrinsic (.copyNonOverlapping src dst count))) = none ∧
      statementOk decls (mkStmt (.intrinsic (.copyNonOverlapping src dst count))) = false :=
  ⟨rfl, rfl⟩

/-- The fragment also has no type for the raw-pointer locals. -/
theorem bdCopy_rejected :
    scalarTypeOf bdRawConstU32Ty = none ∧ inFragment (bdCopyBody 1) = false :=
  ⟨rfl, by decide⟩

/-! ## 3. `BinOp::Offset` and `arith_offset` -/

/-- MIR of a body that offsets a pointer to its parameter `_1 : u32` by `k`
elements (`k` an `isize` bit pattern) and returns it:
```text
bb0: _0 = &raw const _1; _0 = Offset(copy _0, const k_isize); return
```
Anneal: the `.binaryOp` arm of `evalRvalue` (`Places.lean:2160-2184`) handles
a pointer left operand and a scalar right operand only for `.offset`
(`Places.lean:2171-2178`), returning the pointer with
`offsetBytes := ptrVal.offsetBytes + offsetSc.bits`: the count is neither
multiplied by the pointee size nor read as signed, and no bounds check
applies. (`ProvenancePtr.offsetBytes` is documented as a byte offset, while
`evalCopyNonOverlappingWithCount` uses it as an element index into array
values.)

`minimize`: the `(Offset, Type::Ptr(_))` arm of `translate_rvalue_smir`
(`rvalue.rs:22-35`) multiplies the count by the pointee's size
(`build::mul_unchecked`) and emits `build::ptr_offset(.., InBounds::Yes)`, an
in-bounds offset in bytes; for `u32` and `k = 1` that is 4 bytes, and for
`k = -1` it is `-4` bytes from the start of `_1`. -/
def bdOffsetBody (k : Nat) : CapturedMir :=
  bdBody "boundary::offset" 1 [bdDecl bdRawConstU32Ty, u32Decl] [
    { statements := [
        mkStmt (.assign (local_ 0) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 0) (.binaryOp .offset (.copy (local_ 0)) (bdConstIsize k)))],
      terminator := mkTerm .return_, isCleanup := false }]

/-- `k = 1`: the raw pointer `_0` (borrow tag `1`) ends at `offsetBytes = 1`,
not `4 = size_of::<u32>()`. -/
theorem bdOffset1_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdOffsetBody 1) [.scalar ⟨7, 4⟩]) []
      (.normal (.ptr ⟨1, 1⟩ 8, mem)) :=
  ⟨_, runA_sound (bdOffsetBody 1) 30 _ _ _ rfl⟩

/-- `k = -1` (bits `2^64 - 1`): the pointer ends at
`offsetBytes = 2^64 - 1`, with no wraparound and no UB, although the offset
moves before the start of `_1`. -/
theorem bdOffsetNeg1_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdOffsetBody 18446744073709551615) [.scalar ⟨7, 4⟩]) []
      (.normal (.ptr ⟨1, 18446744073709551615⟩ 8, mem)) :=
  ⟨_, runA_sound (bdOffsetBody 18446744073709551615) 30 _ _ _ rfl⟩

theorem bdOffsetNeg1_noUB :
    MirNoUBTree (mirCallTree (bdOffsetBody 18446744073709551615) [.scalar ⟨7, 4⟩]) :=
  runA_noUB (bdOffsetBody 18446744073709551615) 30 _ _ _ rfl

theorem bdOffset_rejected :
    translateBinOp .offset = none ∧
      translateRvalue [bdDecl bdRawConstU32Ty, u32Decl]
        (.binaryOp .offset (.copy (local_ 0)) (bdConstIsize 1)) = none ∧
      inFragment (bdOffsetBody 1) = false :=
  ⟨rfl, rfl, by decide⟩

/-- MIR of `fn arith_offset_caller(p: *const u32, k: isize) -> *const u32`,
which calls `core::intrinsics::arith_offset::<u32>(p, k)`. `arith_offset`
reaches MIR as a `Call` terminator (which is why `minimize` handles it in
`translate_rs_intrinsic`), so Anneal treats it like the calls of the next
section: as an external call request (`Terminators.lean:338-341`). `minimize`
lowers it (`bb.rs:502-523`) to an assignment of
`build::ptr_offset(p, k * size_of::<u32>(), InBounds::No)`, a byte offset
without the in-bounds requirement, followed by a `Goto`. -/
def bdArithOffsetCaller : CapturedMir :=
  bdCallBody "boundary::arith_offset_caller" "core::intrinsics::arith_offset" [.uint .u32] 2
    [bdDecl bdRawConstU32Ty, bdDecl bdRawConstU32Ty, bdDecl bdIsizeTy] (some 1)

def bdArithOffsetArgs : List Value := [.ptr ⟨1, 0⟩ 8, .scalar ⟨1, 8⟩]

theorem bdArithOffset_extCall :
    ∃ k, stepMirFn bdArithOffsetCaller (initMachineState bdArithOffsetCaller bdArithOffsetArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::arith_offset", args := bdArithOffsetArgs,
          memory := (initMachineState bdArithOffsetCaller bdArithOffsetArgs).memory } k :=
  ⟨_, rfl⟩

/-! ## 4. Intrinsic calls without a body in `callees` -/

/-- An external request records a `DefPath`, the untyped argument `Value`s, and
the `Memory` (`State.lean:314-320`); in particular it erases generic type
arguments `T` and integer `Signedness` (`ScalarInt` carries only `bits` and
`sizeBytes`). While `MirCallAns` (`State.lean:335-341`) has constructors
`returned`, `panicked`, and `aborted`, Anneal interprets `MirCallE` via an
`ExternalCallHandler : MirCallReq → ITree MirClosedEffect MirCallAns`
(`Trusted/VerificationResult.lean:225-240`), which *can* directly raise UB via
`ITree.fail .ub` in `MirClosedEffect`. -/
theorem bdMirCallReq_fields (r : MirCallReq) :
    r = { defPath := r.defPath, args := r.args, memory := r.memory } := rfl

/-- `fn write_bytes_caller(dst: *mut u32, val: u8, count: usize)`, calling
`core::intrinsics::write_bytes::<u32>`. When a call resolves to an intrinsic
instance, `minimize` hands it to `translate_rs_intrinsic` (`bb.rs:750-753`),
which has no arm for `write_bytes`; its catch-all arm stops with `span_bug!`
(`bb.rs:615`). -/
def bdWriteBytesCaller : CapturedMir :=
  bdCallBody "boundary::write_bytes_caller" "core::intrinsics::write_bytes" [.uint .u32] 3
    [bdDecl bdUnitTy, bdDecl bdRawMutU32Ty, u8Decl, bdDecl bdUsizeTy] (some 1)

def bdWriteBytesArgs : List Value := [.ptr ⟨1, 0⟩ 8, .scalar ⟨171, 1⟩, .scalar ⟨1, 8⟩]

/-- `fn raw_eq_caller(a: &u32, b: &u32) -> bool`, calling
`core::intrinsics::raw_eq::<u32>`. `minimize` lowers it to
`Terminator::Intrinsic { intrinsic: IntrinsicOp::RawEq, .. }`
(`bb.rs:489-501`). -/
def bdRawEqCaller : CapturedMir :=
  bdCallBody "boundary::raw_eq_caller" "core::intrinsics::raw_eq" [.uint .u32] 2
    [boolDecl, bdDecl bdRefU32Ty, bdDecl bdRefU32Ty] (some 1)

def bdRawEqArgs : List Value := [.ptr ⟨1, 0⟩ 8, .ptr ⟨2, 0⟩ 8]

/-- `fn cold_path_caller()`, calling `core::intrinsics::cold_path`. `minimize`
lowers it to a `Goto` to the call's target, a no-op (`bb.rs:595-599`). -/
def bdColdPathCaller : CapturedMir :=
  bdCallBody "boundary::cold_path_caller" "core::intrinsics::cold_path" [] 0 [bdDecl bdUnitTy]
    (some 1)

/-- `fn ctpop_caller(x: u32) -> u32`, calling `core::intrinsics::ctpop::<u32>`.
`minimize` lowers it to an assignment of `build::count_ones(x)` and a `Goto`
(`bb.rs:551-560`). -/
def bdCtpopCaller : CapturedMir :=
  bdCallBody "boundary::ctpop_caller" "core::intrinsics::ctpop" [.uint .u32] 1
    [u32Decl, u32Decl] (some 1)

def bdCtpopArgs : List Value := [.scalar ⟨240, 4⟩]

/-- `fn exact_div_caller(x: i32, y: i32) -> i32`, calling
`core::intrinsics::exact_div::<i32>`. `minimize` lowers `exact_div` to an
assignment of `build::div_exact(x, y)` and a `Goto` (`bb.rs:561-572`), so
MiniRust evaluates `IntBinOp::DivExact` at the operands' integer type. -/
def bdExactDivI32Caller : CapturedMir :=
  bdCallBody "boundary::exact_div_i32_caller" "core::intrinsics::exact_div" [.int .i32] 2
    [i32Decl, i32Decl, i32Decl] (some 1)

/-- The same caller at `u32`, calling `core::intrinsics::exact_div::<u32>`. -/
def bdExactDivU32Caller : CapturedMir :=
  bdCallBody "boundary::exact_div_u32_caller" "core::intrinsics::exact_div" [.uint .u32] 2
    [u32Decl, u32Decl, u32Decl] (some 1)

/-- The bit patterns of `(-6i32, 3i32)`, which are also those of
`(4294967290u32, 3u32)`. -/
def bdExactDivArgs : List Value := [.scalar ⟨4294967290, 4⟩, .scalar ⟨3, 4⟩]

/-- `fn abort_caller() -> !`, calling `core::intrinsics::abort`. Because
`abort` returns `!`, the MIR call has no return target. `minimize` lowers it
to `build::abort()` (`bb.rs:611-614`). -/
def bdAbortCaller : CapturedMir :=
  bdCallBody "boundary::abort_caller" "core::intrinsics::abort" [] 0 [bdDecl bdNeverTy] none

/-- Anneal: a call with a return target whose `DefPath` has no body in
`Memory.callees` evaluates its arguments and emits an external call node
(`Terminators.lean:298-341`, the node at `339-341`), and the same holds for
each of the following callers. -/
theorem bdWriteBytes_extCall :
    ∃ k, stepMirFn bdWriteBytesCaller (initMachineState bdWriteBytesCaller bdWriteBytesArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::write_bytes", args := bdWriteBytesArgs,
          memory := (initMachineState bdWriteBytesCaller bdWriteBytesArgs).memory } k :=
  ⟨_, rfl⟩

theorem bdRawEq_extCall :
    ∃ k, stepMirFn bdRawEqCaller (initMachineState bdRawEqCaller bdRawEqArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::raw_eq", args := bdRawEqArgs,
          memory := (initMachineState bdRawEqCaller bdRawEqArgs).memory } k :=
  ⟨_, rfl⟩

theorem bdColdPath_extCall :
    ∃ k, stepMirFn bdColdPathCaller (initMachineState bdColdPathCaller []) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::cold_path", args := [],
          memory := (initMachineState bdColdPathCaller []).memory } k :=
  ⟨_, rfl⟩

theorem bdCtpop_extCall :
    ∃ k, stepMirFn bdCtpopCaller (initMachineState bdCtpopCaller bdCtpopArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::ctpop", args := bdCtpopArgs,
          memory := (initMachineState bdCtpopCaller bdCtpopArgs).memory } k :=
  ⟨_, rfl⟩

theorem bdExactDivI32_extCall :
    ∃ k, stepMirFn bdExactDivI32Caller (initMachineState bdExactDivI32Caller bdExactDivArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::exact_div", args := bdExactDivArgs,
          memory := (initMachineState bdExactDivI32Caller bdExactDivArgs).memory } k :=
  ⟨_, rfl⟩

/-- Anneal: a call without a return target is UB only for
`core::hint::unreachable_unchecked`; every other diverging call, including
`abort`, is `unsupported` (`Terminators.lean:350-353`), not an external
call. -/
theorem bdAbort_unsupported :
    stepMirFn bdAbortCaller (initMachineState bdAbortCaller []) = MirStepNode.unsupported := rfl

/-- The two `exact_div` callers declare parameters of different types. -/
theorem bdExactDiv_param_types :
    (bdExactDivI32Caller.localDecls[1]?).bind (fun d => intTypeOf d.ty) = some ⟨.Signed, ⟨4⟩⟩ ∧
      (bdExactDivU32Caller.localDecls[1]?).bind (fun d => intTypeOf d.ty) =
        some ⟨.Unsigned, ⟨4⟩⟩ :=
  ⟨rfl, rfl⟩

/-- Nevertheless, on the same argument bits, Anneal's two external requests
are identical: the request cannot tell `exact_div::<i32>` from
`exact_div::<u32>`. -/
theorem bdExactDiv_same_request :
    bdCallReq?
        (stepMirFn bdExactDivI32Caller (initMachineState bdExactDivI32Caller bdExactDivArgs)) =
      bdCallReq?
        (stepMirFn bdExactDivU32Caller (initMachineState bdExactDivU32Caller bdExactDivArgs)) :=
  rfl

/-- The bits `4294967290` decode to `-6` at `i32` and to `4294967290` at
`u32` (`intFromBits`, `minimize`'s `int_from_bits`). -/
theorem bdExactDiv_decode :
    intFromBits 4294967290 i32 = -6 ∧ intFromBits 4294967290 u32 = 4294967290 :=
  ⟨rfl, rfl⟩

/-- MiniRust's `IntBinOp::DivExact`, which `minimize` emits for `exact_div`,
returns `-2` at `i32`. -/
theorem bdExactDiv_minirust_i32 :
    evalBinOp (.Int .DivExact) (.Int (-6), .Int i32) (.Int 3, .Int i32) =
      .ok (.Int (-2), .Int i32) := rfl

/-- At `u32` the division has remainder `1`, and MiniRust raises UB. -/
theorem bdExactDiv_minirust_u32 :
    evalBinOp (.Int .DivExact) (.Int 4294967290, .Int u32) (.Int 3, .Int u32) =
      .error (.ub "non-zero remainder in exact division") := rfl

/-- The callers of this section, together with `bdArithOffsetCaller`. -/
def bdExtCallers : List CapturedMir :=
  [bdArithOffsetCaller, bdWriteBytesCaller, bdRawEqCaller, bdColdPathCaller, bdCtpopCaller,
    bdExactDivI32Caller, bdExactDivU32Caller, bdAbortCaller]

/-- None of these callers is in the multi-function fragment with an empty
`callees`, and none translates: `lookupFnTarget` finds no `FnName` for the
intrinsic's `DefPath` (or, for the pointer and unit locals, `scalarTypeOf`
finds no MiniRust type). -/
theorem bdExtCallers_rejected :
    bdExtCallers.all (fun b => !progInFragment b [] && (translateProg b []).isNone) = true := by
  decide

/-! ### 4b. `ExternalCallHandler` correspondence for `cold_path`, `ctpop`, and `exact_div` -/

/-- Population count of the low `n` bits of `u : Nat`. -/
def popcountBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, u => u % 2 + popcountBits n (u / 2)

private theorem intBitRec_and_zero (fuel : Nat) (a : Int) :
    intBitRec (fun _ => 0) (fun b => b) (fun x y => if x = 1 ∧ y = 1 then 1 else 0) fuel a 0 = 0 := by
  induction fuel generalizing a with
  | zero =>
    simp [intBitRec]
  | succ n ih =>
    simp only [intBitRec]
    split
    · rfl
    · split
      · rfl
      · have h0 : (0 : Int) / 2 = 0 := rfl
        have hm : (0 : Int) % 2 = 0 := rfl
        rw [h0, hm, ih]
        omega

/-- Two's-complement `a & 1` on `libspecr::Int` equals Euclidean residue `a % 2`
for every integer `a` (positive, zero, or negative). -/
private theorem bdIntBitAnd_one (a : Int) : intBitAnd a 1 = a % 2 := by
  unfold intBitAnd
  by_cases ha0 : a = 0
  · subst ha0; rfl
  · by_cases ha1 : a = -1
    · subst ha1; rfl
    · have hpos : 0 < intBitMeasure a := by
        unfold intBitMeasure
        split <;> omega
      obtain ⟨n, hn⟩ : ∃ n, intBitMeasure a = n + 1 := ⟨intBitMeasure a - 1, by omega⟩
      rw [hn]
      simp only [intBitRec, ha0, ha1, ↓reduceIte]
      have hdiv : (1 : Int) / 2 = 0 := rfl
      have hmod1 : (1 : Int) % 2 = 1 := rfl
      rw [hdiv, hmod1, intBitRec_and_zero]
      have hmod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hmod2 with h0 | h1
      · simp [h0]
      · simp [h1]

/-- `countOnesLoop` extracts the population count of `u` across `n` bit
positions regardless of any high-order multiple `k * 2^n` above bit `n` (such as
two's-complement sign extension `k = -1`). -/
theorem countOnesLoop_mod (n u : Nat) (ones k : Int) :
    countOnesLoop n ones ((u : Int) + k * (2 : Int) ^ n) = ones + (popcountBits n u : Int) := by
  induction n generalizing u ones with
  | zero =>
    simp [countOnesLoop, popcountBits]
  | succ n ih =>
    simp only [countOnesLoop, popcountBits, bdIntBitAnd_one]
    have hsplit : (u : Int) + k * (2 : Int) ^ (n + 1) =
        ((u % 2 : Nat) : Int) + 2 * (((u / 2 : Nat) : Int) + k * (2 : Int) ^ n) := by
      have hp : k * (2 : Int) ^ (n + 1) = 2 * (k * (2 : Int) ^ n) := by
        rw [Int.pow_succ, ← Int.mul_assoc, Int.mul_comm _ 2]
      rw [hp]
      omega
    have hmod : (((u % 2 : Nat) : Int) + 2 * (((u / 2 : Nat) : Int) + k * (2 : Int) ^ n)) % 2 =
        ((u % 2 : Nat) : Int) := by omega
    have hdiv : (((u % 2 : Nat) : Int) + 2 * (((u / 2 : Nat) : Int) + k * (2 : Int) ^ n)) / 2 =
        ((u / 2 : Nat) : Int) + k * (2 : Int) ^ n := by omega
    rw [hsplit, hmod, hdiv, ih (u / 2) (ones + ((u % 2 : Nat) : Int))]
    omega

/-- Symbolic equivalence of MiniRust's `evalCountOnes` (`spec/lang/step/operators.md`)
with `popcountBits` across **all** signed and unsigned `IntType` widths. -/
theorem evalCountOnes_intFromBits (it : Gen.IntType) (bits : Nat) :
    evalCountOnes (intFromBits bits it) it = (popcountBits (8 * it.size.bytes) bits : Int) := by
  cases it with
  | mk s sz =>
    cases s with
    | Unsigned =>
      have hi : intFromBits bits ⟨.Unsigned, sz⟩ = (bits : Int) + 0 * (2 : Int) ^ (8 * sz.bytes) := by
        simp [intFromBits]
      rw [hi]
      unfold evalCountOnes Interp.Size.bits
      simpa using countOnesLoop_mod (8 * sz.bytes) bits 0 0
    | Signed =>
      by_cases hlt : bits < 2 ^ (8 * sz.bytes - 1)
      · have hi : intFromBits bits ⟨.Signed, sz⟩ = (bits : Int) + 0 * (2 : Int) ^ (8 * sz.bytes) := by
          simp [intFromBits, hlt]
        rw [hi]
        unfold evalCountOnes Interp.Size.bits
        simpa using countOnesLoop_mod (8 * sz.bytes) bits 0 0
      · have hi : intFromBits bits ⟨.Signed, sz⟩ = (bits : Int) + (-1) * (2 : Int) ^ (8 * sz.bytes) := by
          simp [intFromBits, hlt]
          omega
        rw [hi]
        unfold evalCountOnes Interp.Size.bits
        simpa using countOnesLoop_mod (8 * sz.bytes) bits 0 (-1)

/-- `evalCountOnes` on `intFromBits bits ⟨signed, sz⟩` is completely invariant
under `Signedness`, explaining why an untyped `MirCallReq` handler can implement
`core::intrinsics::ctpop::<T>` uniformly from `ScalarInt.bits` and `sizeBytes`. -/
theorem evalCountOnes_signedness_indep (sz : LibSpecr.Size) (bits : Nat) :
    evalCountOnes (intFromBits bits ⟨.Signed, sz⟩) ⟨.Signed, sz⟩ =
      evalCountOnes (intFromBits bits ⟨.Unsigned, sz⟩) ⟨.Unsigned, sz⟩ := by
  rw [evalCountOnes_intFromBits, evalCountOnes_intFromBits]

private theorem mirHandledTree_extCall_ret {body : CapturedMir} {args : List Value}
    {mem mem' : Memory} {h : ExternalCallHandler} {req : MirCallReq}
    {kStep : MirCallAns → MirExecState} {retVal : Value} {s1 : MachineState}
    {out : MirOutcome}
    (hstep0 : stepMirFn body (initMachineStateWithMemory body args mem) = .extCall req kStep)
    (hreq : h req = ITree.ret (.returned retVal mem'))
    (hk : kStep (.returned retVal mem') = .running s1)
    (hstep1 : stepMirFn body s1 = .ret out) :
    ReachesRet (mirHandledTree body args mem h) [] out := by
  let interpF : ITree.InterpCarrier MirEffect MirClosedEffect MirOutcome →
      ITree MirClosedEffect MirOutcome :=
    ITree.cofix (ITree.interpStep (handleMirExternalCalls h))
  have hobs0 : (mirStatefulTree body args mem).observe =
      .vis (.inr (.inr (CallReq.call req : MirCallE.I)))
        (fun ans => ITree.cofix (stepMirState body) (kStep ans)) := by
    rw [mirStatefulTree, mirTree, ITree.observe_cofix]
    simp [stepMirState, hstep0, MirStepNode.extCall, ITreeF.map]
  have hobs1 : (mirHandledTree body args mem h).observe =
      .tau (interpF (.inl (ITree.cofix (stepMirState body) (.running s1)))) := by
    rw [mirHandledTree, ITree.interp, ITree.observe_cofix]
    dsimp only [ITree.interpStep]
    rw [hobs0]
    dsimp only [handleMirExternalCalls]
    erw [hreq, ITree.observe_ret]
    dsimp only
    erw [hk]
    rfl
  have hobsS1 : (ITree.cofix (stepMirState body) (.running s1)).observe =
      .ret out := by
    rw [ITree.observe_cofix]
    simp [stepMirState, hstep1, ITreeF.map]
  have hobs2 : (interpF (.inl (ITree.cofix (stepMirState body) (.running s1)))).observe =
      .ret out := by
    dsimp only [interpF]
    rw [ITree.observe_cofix]
    simp [ITree.interpStep, hobsS1, ITreeF.map]
  exact ⟨_, .tau hobs1 (.refl _), hobs2⟩

private theorem mirHandledTree_extCall_ub {body : CapturedMir} {args : List Value}
    {mem : Memory} {h : ExternalCallHandler} {req : MirCallReq}
    {kStep : MirCallAns → MirExecState} {fk : FailureKind}
    (hstep0 : stepMirFn body (initMachineStateWithMemory body args mem) = .extCall req kStep)
    (hreq : h req = ITree.fail (E := MirClosedEffect) fk) :
    FaultNow (mirHandledTree body args mem h) := by
  have hobs0 : (mirStatefulTree body args mem).observe =
      .vis (.inr (.inr (CallReq.call req : MirCallE.I)))
        (fun ans => ITree.cofix (stepMirState body) (kStep ans)) := by
    rw [mirStatefulTree, mirTree, ITree.observe_cofix]
    simp [stepMirState, hstep0, MirStepNode.extCall, ITreeF.map]
  have hfail : ∃ (kFail : PEmpty → ITree MirClosedEffect MirCallAns),
      (ITree.fail (E := MirClosedEffect) (R := MirCallAns) fk).observe =
      .vis (.inl (FailReq.fail fk : (FailE FailureKind).I)) kFail := by
    dsimp only [ITree.fail, Bind.bind, Monad.toBind, ITree.bind, ITree.triggerSub]
    rw [ITree.observe_cofix]
    dsimp only
    rw [ITree.observe_vis]
    exact ⟨_, rfl⟩
  obtain ⟨kFail, hkFail⟩ := hfail
  have hobsH : ∃ (kOut : PEmpty → ITree MirClosedEffect MirOutcome),
      (mirHandledTree body args mem h).observe =
      .vis (.inl (FailReq.fail fk : (FailE FailureKind).I)) kOut := by
    rw [mirHandledTree, ITree.interp, ITree.observe_cofix]
    dsimp only [ITree.interpStep]
    rw [hobs0]
    dsimp only [handleMirExternalCalls]
    erw [hreq, hkFail]
    exact ⟨_, rfl⟩
  obtain ⟨kOut, hkOut⟩ := hobsH
  exact ⟨mirHandledTree body args mem h, .inl (.fail fk), kOut, .refl _, hkOut, trivial⟩

/-- `ExternalCallHandler` for `core::intrinsics::cold_path`: returns `()` with
unchanged memory, matching `minimize`'s no-op `Terminator::Goto(target)`
(`bb.rs:595-599`). -/
def coldPathHandler : ExternalCallHandler := fun req =>
  if req.defPath == "core::intrinsics::cold_path" && req.args.isEmpty then
    ITree.ret (.returned .unit req.memory)
  else
    ITree.fail FailureKind.unsupported

/-- `ExternalCallHandler` for `core::intrinsics::ctpop::<T>`: computes the `u32`
population count of `sc.bits` across `8 * sc.sizeBytes` bits, matching MiniRust's
`IntUnOp::CountOnes` (`evalCountOnes_intFromBits`) uniformly across all signed
and unsigned integer types. -/
def ctpopHandler : ExternalCallHandler := fun req =>
  if req.defPath == "core::intrinsics::ctpop" then
    match req.args with
    | [.scalar sc] =>
      ITree.ret (.returned (.scalar ⟨popcountBits (8 * sc.sizeBytes) sc.bits, 4⟩) req.memory)
    | _ => ITree.fail FailureKind.ub
  else
    ITree.fail FailureKind.unsupported

/-- Monomorphized `ExternalCallHandler` for `core::intrinsics::exact_div::<T>` at
`it : Gen.IntType`: raises UB (`ITree.fail FailureKind.ub`) on division by zero,
signed `MIN / -1` overflow, or non-zero remainder, and otherwise returns the
exact quotient encoded at `it`, matching MiniRust's `IntBinOp::DivExact`. -/
def exactDivHandler (it : Gen.IntType) : ExternalCallHandler := fun req =>
  if req.defPath == "core::intrinsics::exact_div" then
    match req.args with
    | [.scalar lSc, .scalar rSc] =>
      if lSc.sizeBytes == it.size.bytes && rSc.sizeBytes == it.size.bytes then
        let left := intFromBits lSc.bits it
        let right := intFromBits rSc.bits it
        if right == 0 then
          ITree.fail FailureKind.ub
        else
          let q := Int.tdiv left right
          if !IntType.can_represent it q || Int.tmod left right != 0 then
            ITree.fail FailureKind.ub
          else
            let outBits := (q % (2 : Int) ^ (8 * it.size.bytes)).toNat
            ITree.ret (.returned (.scalar ⟨outBits, it.size.bytes⟩) req.memory)
      else
        ITree.fail FailureKind.unsupported
    | _ => ITree.fail FailureKind.ub
  else
    ITree.fail FailureKind.unsupported

/-- `fn ctpop_i8_caller(x: i8) -> u32`, calling `core::intrinsics::ctpop::<i8>`. -/
def bdCtpopI8Caller : CapturedMir :=
  bdCallBody "boundary::ctpop_i8_caller" "core::intrinsics::ctpop" [.int .i8] 1
    [u32Decl, i8Decl] (some 1)

theorem bdColdPath_handled :
    ReachesRet (mirHandledTree bdColdPathCaller [] emptyMemory coldPathHandler) []
      (.normal (.unit, emptyMemory)) :=
  mirHandledTree_extCall_ret rfl rfl rfl rfl

/-- The single untyped `ctpopHandler` handles both `ctpop::<u32>(240u32) == 4u32`
and signed `ctpop::<i8>(-1i8) == 8u32` (bits `255`), matching MiniRust's
`evalUnOp (.Int .CountOnes)` in both cases. -/
theorem bdCtpop_handled :
    ReachesRet (mirHandledTree bdCtpopCaller [.scalar ⟨240, 4⟩] emptyMemory ctpopHandler) []
        (.normal (.scalar ⟨4, 4⟩, emptyMemory)) ∧
      evalUnOp (.Int .CountOnes) (.Int 240, .Int u32) = .ok (.Int 4, .Int u32) ∧
      ReachesRet (mirHandledTree bdCtpopI8Caller [.scalar ⟨255, 1⟩] emptyMemory ctpopHandler) []
        (.normal (.scalar ⟨8, 4⟩, emptyMemory)) ∧
      evalUnOp (.Int .CountOnes) (.Int (-1), .Int IntType.I8) = .ok (.Int 8, .Int u32) :=
  ⟨mirHandledTree_extCall_ret rfl rfl rfl rfl, rfl,
   mirHandledTree_extCall_ret rfl rfl rfl rfl, rfl⟩

/-- `exactDivHandler` on `bdExactDivI32Caller` and `bdExactDivU32Caller` matches
MiniRust's `IntBinOp::DivExact` across exact division (`-6i32 / 3i32 = -2i32`,
bits `4294967294`) and all three UB conditions: non-zero remainder
(`4294967290u32 / 3u32`), division by zero (`6i32 / 0i32`), and signed overflow
(`i32::MIN / -1i32`). -/
theorem bdExactDiv_handled :
    ReachesRet
        (mirHandledTree bdExactDivI32Caller [.scalar ⟨4294967290, 4⟩, .scalar ⟨3, 4⟩]
          emptyMemory (exactDivHandler i32))
        [] (.normal (.scalar ⟨4294967294, 4⟩, emptyMemory)) ∧
      FaultNow
        (mirHandledTree bdExactDivU32Caller [.scalar ⟨4294967290, 4⟩, .scalar ⟨3, 4⟩]
          emptyMemory (exactDivHandler u32)) ∧
      FaultNow
        (mirHandledTree bdExactDivI32Caller [.scalar ⟨6, 4⟩, .scalar ⟨0, 4⟩]
          emptyMemory (exactDivHandler i32)) ∧
      evalBinOp (.Int .DivExact) (.Int 6, .Int i32) (.Int 0, .Int i32) =
        .error (.ub "division by zero") ∧
      FaultNow
        (mirHandledTree bdExactDivI32Caller [.scalar ⟨2147483648, 4⟩, .scalar ⟨4294967295, 4⟩]
          emptyMemory (exactDivHandler i32)) ∧
      evalBinOp (.Int .DivExact) (.Int (-2147483648), .Int i32) (.Int (-1), .Int i32) =
        .error (.ub "overflow in division") :=
  ⟨mirHandledTree_extCall_ret rfl rfl rfl rfl,
   mirHandledTree_extCall_ub rfl rfl,
   mirHandledTree_extCall_ub rfl rfl,
   rfl,
   mirHandledTree_extCall_ub rfl rfl,
   rfl⟩

/-- Symbolic correspondence between `exactDivHandler it` and MiniRust's
`evalBinOp (.Int .DivExact)` for every integer type `it` and all operand bit
patterns `b1, b2`. -/
theorem exactDivHandler_iff_minirust (it : Gen.IntType)
    (b1 b2 : Nat) (mem : Memory) :
    let req : MirCallReq :=
      { defPath := "core::intrinsics::exact_div"
        args := [.scalar ⟨b1, it.size.bytes⟩, .scalar ⟨b2, it.size.bytes⟩]
        memory := mem }
    let l := intFromBits b1 it
    let r := intFromBits b2 it
    ((∃ msg, evalBinOp (.Int .DivExact) (.Int l, .Int it) (.Int r, .Int it) = .error (.ub msg)) →
      exactDivHandler it req = ITree.fail FailureKind.ub) ∧
    (∀ q, evalBinOp (.Int .DivExact) (.Int l, .Int it) (.Int r, .Int it) = .ok (.Int q, .Int it) →
      exactDivHandler it req =
        ITree.ret (.returned (.scalar ⟨(q % (2 : Int) ^ (8 * it.size.bytes)).toNat, it.size.bytes⟩) mem)) := by
  dsimp only
  simp only [exactDivHandler, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  by_cases hr0 : intFromBits b2 it = 0
  · simp [hr0, evalBinOp, evalIntBinOp, ub]
  · have hr0b : (intFromBits b2 it == 0) = false := beq_false_of_ne hr0
    simp only [hr0b, Bool.false_eq_true, ↓reduceIte]
    by_cases hrep : IntType.can_represent it (Int.tdiv (intFromBits b1 it) (intFromBits b2 it)) = true
    · by_cases hrem : Int.tmod (intFromBits b1 it) (intFromBits b2 it) = 0
      · have hbmod : IntType.bring_in_bounds it (Int.tdiv (intFromBits b1 it) (intFromBits b2 it)) %
            (2 : Int) ^ (8 * it.size.bytes) =
            Int.tdiv (intFromBits b1 it) (intFromBits b2 it) % (2 : Int) ^ (8 * it.size.bytes) := by
          cases it with
          | mk s sz =>
            unfold IntType.bring_in_bounds bringInBounds Interp.Size.bits
            dsimp only
            cases s
            · dsimp only
              exact Int.emod_emod _ _
            · dsimp only
              split
              · exact Int.emod_emod _ _
              · rw [Int.sub_emod_right, Int.emod_emod]
        simp only [evalBinOp, evalIntBinOp, hr0, hrep, hrem, bne_self_eq_false, Bool.not_true,
          Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · rintro ⟨msg, h⟩
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        · intro q hq
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at hq
          rcases hq with rfl
          rw [hbmod]
      · have hremB : (Int.tmod (intFromBits b1 it) (intFromBits b2 it) != 0) = true := by
          simp [hrem]
        simp [evalBinOp, evalIntBinOp, hr0, hrep, hrem, hremB, ub]
    · simp only [Bool.not_eq_true] at hrep
      simp [evalBinOp, evalIntBinOp, hr0, hrep, ub]


/-! ### 4c. Completeness boundary for `write_bytes` and `ub_checks`

* `core::intrinsics::write_bytes`: `stepMirFn` does **not** return
  `MirStepNode.unsupported` directly; because `write_bytes` has a return target
  and no body in `Memory.callees`, `stepMirFn` emits `MirStepNode.extCall`
  (`bdWriteBytes_extCall`). Under any `ExternalCallHandler` that rejects
  unmodeled calls with `ITree.fail FailureKind.unsupported`, `mirHandledTree`
  faults immediately (`bdWriteBytes_unhandled_fault`), while `minimize`'s
  `translate_rs_intrinsic` (`bb.rs:429-694`) has no `sym::write_bytes` arm and
  hits `span_bug!` (`bb.rs:615`).
* `core::intrinsics::ub_checks`: appears in two MIR forms. Inline
  `Rvalue.nullaryOp .ubChecks` steps directly to `MirStepNode.unsupported` in
  Anneal (`bdUbChecks_step`, `bdUbChecks_not_noUB`) and is rejected by
  `translateRvalue` (`bdNullaryOp_translateRvalue`). An unlowered
  `TerminatorKind.call` to `core::intrinsics::ub_checks` instead emits
  `MirStepNode.extCall` (`bdUbChecksCall_extCall`), and `ubChecksHandler flag`
  supplies the session-configured `bool` matching `minimize`'s
  `build::const_bool(self.tcx.sess.ub_checks())` (`bb.rs:607-610`,
  `bdUbChecksCall_handled`).
-/

/-- Without a handler for `core::intrinsics::write_bytes`, interpreting
`bdWriteBytesCaller` under an `unsupported`-defaulting `ExternalCallHandler`
faults immediately (`FaultNow`), and `progInFragment` rejects the caller
(`bdExtCallers_rejected`). -/
theorem bdWriteBytes_unhandled_fault :
    FaultNow
      (mirHandledTree bdWriteBytesCaller bdWriteBytesArgs emptyMemory
        (fun _ => ITree.fail FailureKind.unsupported)) :=
  mirHandledTree_extCall_ub rfl rfl

/-- `fn ub_checks_call_caller() -> bool`, calling `core::intrinsics::ub_checks`
as an unlowered `TerminatorKind.call` (`bb.rs:607-610`). -/
def bdUbChecksCallCaller : CapturedMir :=
  bdCallBody "boundary::ub_checks_call_caller" "core::intrinsics::ub_checks" [] 0
    [boolDecl] (some 1)

theorem bdUbChecksCall_extCall :
    ∃ k, stepMirFn bdUbChecksCallCaller (initMachineState bdUbChecksCallCaller []) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::ub_checks", args := [],
          memory := (initMachineState bdUbChecksCallCaller []).memory } k :=
  ⟨_, rfl⟩

/-- Session-parameterized `ExternalCallHandler` for unlowered calls to
`core::intrinsics::ub_checks`: returns `flag` as a 1-byte scalar (`0` or `1`)
with unchanged memory, matching `minimize`'s
`build::const_bool(self.tcx.sess.ub_checks())` (`bb.rs:607-610`). -/
def ubChecksHandler (flag : Bool) : ExternalCallHandler := fun req =>
  if req.defPath == "core::intrinsics::ub_checks" && req.args.isEmpty then
    ITree.ret (.returned (.scalar ⟨if flag then 1 else 0, 1⟩) req.memory)
  else
    ITree.fail FailureKind.unsupported

theorem bdUbChecksCall_handled (flag : Bool) (m : Mach) :
    ReachesRet (mirHandledTree bdUbChecksCallCaller [] emptyMemory (ubChecksHandler flag)) []
        (.normal (.scalar ⟨if flag then 1 else 0, 1⟩, emptyMemory)) ∧
      Interp.evalValue m (.Constant (.Bool flag) .Bool) = .ok ((.Bool flag, .Bool), m) := by
  cases flag <;> exact ⟨mirHandledTree_extCall_ret rfl rfl rfl rfl, rfl⟩

/-! ## 5. `core::hint::unreachable_unchecked()` -/

/-- MIR of `fn unreachable_caller() -> !`, which calls
`core::hint::unreachable_unchecked()` (a diverging call with no return
target).

Anneal: the diverging-call arm of `evalTerminator`
(`Terminators.lean:350-353`) maps exactly this `DefPath` to
`MirStepNode.fail .ub`.

`minimize`: `unreachable_unchecked` is not an intrinsic, so `translate_call`
(`bb.rs:696-887`) translates it as an ordinary `Terminator::Call` of that
function's own translated body (`bb.rs:877-884`) with `next_block: None`.
MiniRust raises UB when execution reaches a `Terminator::Unreachable`, which
`minimize` produces for MIR's `TerminatorKind::Unreachable` (`bb.rs:196`). -/
def bdUnreachCaller : CapturedMir :=
  bdCallBody "boundary::unreachable_caller" "core::hint::unreachable_unchecked" [] 0
    [bdDecl bdNeverTy] none

theorem bdUnreach_anneal_ub :
    stepMirFn bdUnreachCaller (initMachineState bdUnreachCaller []) = MirStepNode.fail .ub := rfl

theorem bdUnreach_anneal_fault :
    ∃ tr u, Reaches (mirCallTree bdUnreachCaller []) tr u ∧ FaultNow u :=
  faultsA_sound bdUnreachCaller 1 _ rfl

/-- MiniRust's `Terminator::Unreachable` raises UB in every machine
(`Interp.evalTerminator`). -/
theorem bd_minirust_unreachable_ub (m : Mach) :
    Interp.evalTerminator m .Unreachable = .error (.ub "reached unreachable code") := rfl

theorem bdUnreach_rejected :
    progInFragment bdUnreachCaller [] = false ∧ translateProg bdUnreachCaller [] = none :=
  ⟨by decide, rfl⟩

/-- The fragment does cover MIR's own `TerminatorKind::Unreachable`, which
translates to MiniRust's `Terminator::Unreachable`. -/
theorem bdUnreachableTerminator_covered :
    terminatorOk [] 1 (mkTerm .unreachable) = true ∧
      translateTerminator [] (mkTerm .unreachable) = some .Unreachable :=
  ⟨rfl, rfl⟩

end MiniRustSpec.Correspondence
