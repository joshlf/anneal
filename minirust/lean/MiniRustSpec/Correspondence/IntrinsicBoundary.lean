/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.IntrinsicFallback

/-!
# Boundary witnesses for intrinsics outside the correspondence

`IntrinsicFallback` covers intrinsic calls whose fallback bodies are passed in
`callees`. This module records, by kernel computation, what happens to the
intrinsic-related MIR constructs that the fragment does *not* cover. For each
one it compares Anneal's frozen semantics
(`trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/*.lean`, cited by file
and line) with MiniRust's `minimize` translator (`tooling/minimize/src/` in
the MiniRust sources vendored under
`minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/`, paraphrased and
cited by file and line), proves Anneal's behavior on a concrete state, and
proves that the translation or fragment check rejects the construct, so no
correspondence theorem applies to it:

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
   call requests that carry only `defPath`, `args`, and `memory`, so
   `exact_div::<i32>` and `exact_div::<u32>` on the same bits issue identical
   requests although MiniRust's `DivExact` returns `-2` for one and raises UB
   for the other. The diverging `abort` call is `unsupported` instead.
5. `core::hint::unreachable_unchecked()`: Anneal raises UB, like MiniRust's
   `Terminator::Unreachable`; the fragment rejects the call form but covers
   MIR's own `TerminatorKind::Unreachable`.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
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

/-- An external request records exactly a `DefPath`, the argument values, and
the memory (`State.lean:314-320`); in particular it records no generic
arguments and no argument types. The environment answers with a
`MirCallAns` (`State.lean:335-341`), whose constructors are `returned`,
`panicked`, and `aborted`; none of them reports UB inside the callee. -/
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
