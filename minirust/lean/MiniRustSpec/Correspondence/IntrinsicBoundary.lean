/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.IntrinsicFallback
import MiniRustSpec.Correspondence.DeinitBridge
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
3. `BinOp::Offset`: Anneal scales the signed count by `size_of::<T>()` and
   enforces in-bounds byte arithmetic (`bdOffset1_anneal_ret`,
   `bdOffsetNeg1_anneal_ub`, `bdOffsetNeg1_not_noUB`), matching `minimize`'s
   `ptr_offset(.., InBounds::Yes)`, while `arith_offset` evaluates inline with
   wrapping byte arithmetic (`bdArithOffset_anneal_ret`).
4. Calls to `core::intrinsics::*` without a body in `callees`:
   * Compiler intrinsics modeled in `evalDirectRustIntrinsic?` (`arith_offset`,
     `ctpop`, `exact_div`, `ub_checks`) evaluate inline in `stepMirFn`, using
     the callee `FnDef`'s generic `typeArgs` (`bdCtpop_inline`,
     `bdExactDiv_inline`, `bdUbChecksCall_anneal_ret`), and diverging
     `core::intrinsics::abort` steps to `MirStepNode.retOutcome .abort`
     (`bdAbort_anneal_abort`).
   * Unmodeled intrinsics (`write_bytes`, `raw_eq`, `cold_path`) emit external
     `MirCallReq` requests carrying `defPath`, `typeArgs`, `args`, and `memory`
     (`bdMirCallReq_fields`). When interpreted via `mirHandledTree`
     (`Trusted.VerificationResult`), `coldPathHandler` corresponds to
     `minimize`'s no-op `Goto` (`bdColdPath_handled`), `ctpopHandler` matches
     `evalCountOnes` uniformly across signedness (`evalCountOnes_intFromBits`,
     `evalCountOnes_signedness_indep`), and `exactDivHandler it` matches
     MiniRust's `IntBinOp::DivExact` (`exactDivHandler_iff_minirust`).
5. `core::hint::unreachable_unchecked()`: Anneal raises UB, like MiniRust's
   `Terminator::Unreachable`; the fragment rejects the call form but covers
   MIR's own `TerminatorKind::Unreachable`.

This module also imports `Correspondence.DeinitBridge` (projected `Deinit`:
`crates/anneal-mir`'s `PartialShell` model, formalized in
`Anneal.Mir.AdtAndControl` next to its sub-place `CopyNonOverlapping` model
`evalCopyNonOverlappingSubplace`, against MiniRust's byte-slice `Uninit`
store), so that `lake build MiniRustSpec` builds it together with
`Anneal.Mir.AdtAndControl` (guarding both against drift of the Trusted
semantics they refine) and `MiniRustSpec.Audit` audits it together with the
`Anneal.Mir.AdtAndControl` theorems that its `subplace_audit_closure` mentions.

Sections 7, 8, and 9 relate Episode 2's lowered `Anneal.Mir.AdtAndControl.LIntrinsicOp` evaluator
to MiniRust: Section 7 gives the symbolic `ctpop` bridge, exhaustive bit-manipulation and saturating
correspondences against the `IntrinsicFallback` specifications, and the `V2026_06_01` adapter
classification; Section 8 (`[adv ep2-B3]`) proves MiniRust integer arithmetic total on the
`ok`/UB dichotomy (upgrading the `DeinitBridge` unchecked, shift, and `exact_div` bridges to
two-sided success parity), links the bits of `three_way_compare` / `ub_checks` to MiniRust's
decoding of them, relates `abort`, `unreachable_unchecked`, and `ctlz_nonzero` / `cttz_nonzero` to
MiniRust's `IntrinsicOp::Abort`, `Terminator::Unreachable`, and `IntrinsicOp::Assume` for all
inputs, and records negative controls and `i8` signedness-independence checks; Section 9
(`[adv ep2-A3]`) closes the remaining symbolic bridges across **all** integer widths (`bswap` ↔
MiniRust `Endianness.decode .BigEndian` + involution, `bitreverse` / `cttz` / `ctlz` bit-list
characterizations + `CountOnes` conservation, full value-level two-sided `some v ↔ .ok` &
`none ↔ .ub` parity, `saturating` `valOf` clamping, `three_way_compare::<char>`, `size_of_val` /
`align_of_val` ↔ `Type.layout` & `LayoutStrategy.compute_size_and_align`, symbolic `panicUnwind`,
and multi-byte / `char` / slice-layout negative controls). Section 10 (`[adv ep2-B4]`) pins the
remaining boundary: MiniRust's executable spec rejects every unwinding terminator (`StartUnwind`,
`StopUnwind`, `ResumeUnwind`) as `unsupported`, so `panicUnwind` corresponds to `Trusted` only.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Effect
open Trusted.ITree
open Trusted.VerificationResult (MirClosedEffect ExternalCallHandler
  handleMirExternalCalls mirHandledTree mirHandledTreeWithCallees
  mirStatefulTree mirStatefulTreeWithCallees
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

theorem bdNullaryOp_translateRvalue (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : NullOp) (ty : Ty) :
    translateRvalue layouts decls targetTy (.nullaryOp op ty) = none := rfl

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
Both Anneal (`evalBinOpOffset` in `Places.lean`) and `minimize`
(`translate_rvalue_smir` in `rvalue.rs:22-35`) scale the signed count `k` by
`size_of::<u32>() = 4` and require the resulting byte offset to remain in bounds
of `_1` (`0..=4`): `k = 1` produces the one-past-the-end byte offset `4`, while
`k = -1` (`2^64 - 1`) faults with UB. -/
def bdOffsetBody (k : Nat) : CapturedMir :=
  bdBody "boundary::offset" 1 [bdDecl bdRawConstU32Ty, u32Decl] [
    { statements := [
        mkStmt (.assign (local_ 0) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 0) (.binaryOp .offset (.copy (local_ 0)) (bdConstIsize k)))],
      terminator := mkTerm .return_, isCleanup := false }]

/-- `k = 1`: the raw pointer `_0` (borrow tag `1`) ends at the stride-scaled
one-past-the-end byte offset `offsetBytes = 4 = size_of::<u32>()`. -/
theorem bdOffset1_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdOffsetBody 1) [.scalar ⟨7, 4⟩]) []
      (.normal (.ptr ⟨1, 4⟩ 8, mem)) :=
  ⟨_, runA_sound (bdOffsetBody 1) 30 _ _ _ rfl⟩

/-- `k = -1` (bits `2^64 - 1`): moving `-4` bytes before the start of `_1`
faults with UB in Anneal, matching MiniRust's `InBounds::Yes` `ptr_offset`. -/
theorem bdOffsetNeg1_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree (bdOffsetBody 18446744073709551615) [.scalar ⟨7, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound (bdOffsetBody 18446744073709551615) 30 _ rfl

theorem bdOffsetNeg1_not_noUB :
    ¬ MirNoUBTree (mirCallTree (bdOffsetBody 18446744073709551615) [.scalar ⟨7, 4⟩]) := by
  obtain ⟨tr, u, hr, hf⟩ := bdOffsetNeg1_anneal_ub
  exact fun hsafe => hsafe tr u hr hf

/-- `BinOp::Offset` is not an integer `BinOp` (`translateBinOp`).
`translateRvalue` lowers it as `minimize` does (`ptrOffsetExpr`, which scales
the count by the pointee size), and `inFragment` conservatively restricts
`BinOp::Offset` to zero constant offsets (`zeroOffsetConstOk`), rejecting
`bdOffsetBody 1`. -/
theorem bdOffset_rejected :
    translateBinOp .offset = none ∧
      (translateRvalue ⟨64, true, []⟩ [bdDecl bdRawConstU32Ty, u32Decl] none
        (.binaryOp .offset (.copy (local_ 0)) (bdConstIsize 1))).isSome = true ∧
      inFragment (bdOffsetBody 1) = false :=
  ⟨rfl, rfl, by decide⟩

/-- MIR of `fn arith_offset_caller(p: *const u32, k: isize) -> *const u32`,
which calls `core::intrinsics::arith_offset::<u32>(p, k)`. Anneal's
`evalDirectRustIntrinsic?` (`evalArithOffset` in `Terminators.lean`) evaluates
it inline with wrapping `usize` byte arithmetic (`offsetBytes = 4`), matching
`minimize`'s `build::ptr_offset(p, k * size_of::<u32>(), InBounds::No)`
(`bb.rs:502-523`). -/
def bdArithOffsetCaller : CapturedMir :=
  bdCallBody "boundary::arith_offset_caller" "core::intrinsics::arith_offset" [.uint .u32] 2
    [bdDecl bdRawConstU32Ty, bdDecl bdRawConstU32Ty, bdDecl bdIsizeTy] (some 1)

def bdArithOffsetArgs : List Value := [.ptr ⟨1, 0⟩ 8, .scalar ⟨1, 8⟩]

theorem bdArithOffset_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdArithOffsetCaller bdArithOffsetArgs) []
      (.normal (.ptr ⟨1, 4⟩ 8, mem)) :=
  ⟨_, runA_sound bdArithOffsetCaller 10 _ _ _ rfl⟩

/-! ## 4. Intrinsic calls without a body in `callees` -/

/-- An external request records `defPath`, generic `typeArgs`, the argument
`Value`s, and `memory` (`State.lean:458-466`). While `MirCallAns` has
constructors `returned`, `panicked`, and `aborted`, Anneal interprets `MirCallE`
via an `ExternalCallHandler : MirCallReq → ITree MirClosedEffect MirCallAns`
(`Trusted/VerificationResult.lean`), which can also raise UB via
`ITree.fail .ub` in `MirClosedEffect`. -/
theorem bdMirCallReq_fields (r : MirCallReq) :
    r = { defPath := r.defPath, typeArgs := r.typeArgs, args := r.args, memory := r.memory } := rfl

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

/-- Anneal: unmodeled intrinsics with a return target and no body in
`Memory.callees` (`write_bytes`, `raw_eq`, `cold_path`) emit `MirStepNode.extCall`
with `typeArgs` preserved, whereas `ctpop` and `exact_div` evaluate inline via
`evalDirectRustIntrinsic?` and `abort` returns `MirOutcome.abort`. -/
theorem bdWriteBytes_extCall :
    ∃ k, stepMirFn bdWriteBytesCaller (initMachineState bdWriteBytesCaller bdWriteBytesArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::write_bytes", typeArgs := [.uint .u32],
          args := bdWriteBytesArgs,
          memory := (initMachineState bdWriteBytesCaller bdWriteBytesArgs).memory } k :=
  ⟨_, rfl⟩

theorem bdRawEq_extCall :
    ∃ k, stepMirFn bdRawEqCaller (initMachineState bdRawEqCaller bdRawEqArgs) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::raw_eq", typeArgs := [.uint .u32],
          args := bdRawEqArgs,
          memory := (initMachineState bdRawEqCaller bdRawEqArgs).memory } k :=
  ⟨_, rfl⟩

theorem bdColdPath_extCall :
    ∃ k, stepMirFn bdColdPathCaller (initMachineState bdColdPathCaller []) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::cold_path", typeArgs := [], args := [],
          memory := (initMachineState bdColdPathCaller []).memory } k :=
  ⟨_, rfl⟩

theorem bdCtpop_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdCtpopCaller bdCtpopArgs) []
      (.normal (.scalar ⟨4, 4⟩, mem)) :=
  ⟨_, runA_sound bdCtpopCaller 10 _ _ _ rfl⟩

theorem bdExactDivI32_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdExactDivI32Caller bdExactDivArgs) []
      (.normal (.scalar ⟨4294967294, 4⟩, mem)) :=
  ⟨_, runA_sound bdExactDivI32Caller 10 _ _ _ rfl⟩

/-- Anneal: `core::intrinsics::abort` is recognized in `isAbortingPanicDefPath`
and terminates with `MirStepNode.retOutcome .abort`, matching MiniRust's
`Terminator::Abort`. -/
theorem bdAbort_anneal_abort :
    stepMirFn bdAbortCaller (initMachineState bdAbortCaller []) =
      MirStepNode.retOutcome .abort := rfl

/-- The two `exact_div` callers declare parameters of different types. -/
theorem bdExactDiv_param_types :
    (bdExactDivI32Caller.localDecls[1]?).bind (fun d => intTypeOf d.ty) = some ⟨.Signed, ⟨4⟩⟩ ∧
      (bdExactDivU32Caller.localDecls[1]?).bind (fun d => intTypeOf d.ty) =
        some ⟨.Unsigned, ⟨4⟩⟩ :=
  ⟨rfl, rfl⟩

/-- On the same argument bits `(-6i32, 3i32)` vs. `(4294967290u32, 3u32)`,
Anneal's inline `evalDirectExactDiv` inspects the callee `FnDef` `typeArgs`
(`[.int .i32]` vs. `[.uint .u32]`): `exact_div::<i32>` steps normally while
`exact_div::<u32>` immediately faults with `.ub` on non-zero remainder. -/
theorem bdExactDiv_typeArgs_distinct :
    stepMirFn bdExactDivU32Caller (initMachineState bdExactDivU32Caller bdExactDivArgs) =
      MirStepNode.fail .ub :=
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
  [bdArithOffsetCaller, bdWriteBytesCaller]

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
    rw [mirHandledTree, mirHandledTreeWithCallees, ITree.interp, ITree.observe_cofix]
    dsimp only [ITree.interpStep]
    erw [hobs0]
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
    rw [mirHandledTree, mirHandledTreeWithCallees, ITree.interp, ITree.observe_cofix]
    dsimp only [ITree.interpStep]
    erw [hobs0]
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

/-- Anneal's inline `evalCtpop` and `ctpopHandler` both produce `ctpop::<u32>(240u32) == 4u32`
and signed `ctpop::<i8>(-1i8) == 8u32` (bits `255`), matching MiniRust's
`evalUnOp (.Int .CountOnes)` in both cases. -/
theorem bdCtpop_inline :
    (∃ mem, ReachesRet (mirCallTree bdCtpopCaller [.scalar ⟨240, 4⟩]) []
      (.normal (.scalar ⟨4, 4⟩, mem))) ∧
      evalUnOp (.Int .CountOnes) (.Int 240, .Int u32) = .ok (.Int 4, .Int u32) ∧
      (∃ mem, ReachesRet (mirCallTree bdCtpopI8Caller [.scalar ⟨255, 1⟩]) []
        (.normal (.scalar ⟨8, 4⟩, mem))) ∧
      evalUnOp (.Int .CountOnes) (.Int (-1), .Int IntType.I8) = .ok (.Int 8, .Int u32) :=
  ⟨⟨_, runA_sound bdCtpopCaller 10 _ _ _ rfl⟩, rfl,
   ⟨_, runA_sound bdCtpopI8Caller 10 _ _ _ rfl⟩, rfl⟩

/-- Anneal's inline `evalDirectExactDiv` on `bdExactDivI32Caller` and
`bdExactDivU32Caller` matches MiniRust's `IntBinOp::DivExact` across exact
division (`-6i32 / 3i32 = -2i32`, bits `4294967294`) and all three UB
conditions: non-zero remainder (`4294967290u32 / 3u32`), division by zero
(`6i32 / 0i32`), and signed overflow (`i32::MIN / -1i32`). -/
theorem bdExactDiv_inline :
    (∃ mem, ReachesRet
        (mirCallTree bdExactDivI32Caller [.scalar ⟨4294967290, 4⟩, .scalar ⟨3, 4⟩])
        [] (.normal (.scalar ⟨4294967294, 4⟩, mem))) ∧
      (∃ tr u,
        Reaches (mirCallTree bdExactDivU32Caller [.scalar ⟨4294967290, 4⟩, .scalar ⟨3, 4⟩]) tr u ∧
        FaultNow u) ∧
      (∃ tr u,
        Reaches (mirCallTree bdExactDivI32Caller [.scalar ⟨6, 4⟩, .scalar ⟨0, 4⟩]) tr u ∧
        FaultNow u) ∧
      evalBinOp (.Int .DivExact) (.Int 6, .Int i32) (.Int 0, .Int i32) =
        .error (.ub "division by zero") ∧
      (∃ tr u,
        Reaches (mirCallTree bdExactDivI32Caller [.scalar ⟨2147483648, 4⟩, .scalar ⟨4294967295, 4⟩]) tr u ∧
        FaultNow u) ∧
      evalBinOp (.Int .DivExact) (.Int (-2147483648), .Int i32) (.Int (-1), .Int i32) =
        .error (.ub "overflow in division") :=
  ⟨⟨_, runA_sound bdExactDivI32Caller 10 _ _ _ rfl⟩,
   faultsA_sound bdExactDivU32Caller 10 _ rfl,
   faultsA_sound bdExactDivI32Caller 10 _ rfl,
   rfl,
   faultsA_sound bdExactDivI32Caller 10 _ rfl,
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

/-- Direct calls to `core::intrinsics::ub_checks` evaluate inline in
`evalDirectRustIntrinsic?` to `true` (`1 : u8`), enabling `core` runtime UB
assertions in Anneal. -/
theorem bdUbChecksCall_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdUbChecksCallCaller []) []
      (.normal (.scalar ⟨1, 1⟩, mem)) :=
  ⟨_, runA_sound bdUbChecksCallCaller 10 _ _ _ rfl⟩

/-- Session-parameterized `ExternalCallHandler` for external calls to
`core::intrinsics::ub_checks`: returns `flag` as a 1-byte scalar (`0` or `1`)
with unchanged memory, matching `minimize`'s
`build::const_bool(self.tcx.sess.ub_checks())` (`bb.rs:607-610`). -/
def ubChecksHandler (flag : Bool) : ExternalCallHandler := fun req =>
  if req.defPath == "core::intrinsics::ub_checks" && req.args.isEmpty then
    ITree.ret (.returned (.scalar ⟨if flag then 1 else 0, 1⟩) req.memory)
  else
    ITree.fail FailureKind.unsupported

theorem bdUbChecksCall_handled (flag : Bool) (m : Mach) :
    ubChecksHandler flag { defPath := "core::intrinsics::ub_checks", args := [], memory := emptyMemory } =
        ITree.ret (.returned (.scalar ⟨if flag then 1 else 0, 1⟩) emptyMemory) ∧
      Interp.evalValue m (.Constant (.Bool flag) .Bool) = .ok ((.Bool flag, .Bool), m) := by
  cases flag <;> exact ⟨rfl, rfl⟩

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
    terminatorOk ⟨64, true, []⟩ [] 1 (mkTerm .unreachable) = true ∧
      translateTerminator ⟨64, true, []⟩ [] (mkTerm .unreachable) = some .Unreachable :=
  ⟨rfl, rfl⟩

/-! ## 6. Polymorphic types and `monoCallee?` fail-closed rejection -/

/-- Unmonomorphized `RigidTy.param` / `RigidTy.alias` types fail closed in
`translateTy`, and `monoCallee?` / `progInFragment` reject both callers passing
non-empty generic `tys` (`RigidTy.param`, `RigidTy.alias`, or concrete type
arguments) to a monomorphic callee (`typeParamCount = 0`) and callees with
`typeParamCount ≠ 0`. -/
theorem bdPolymorphicCallee_rejected :
    translateTy ⟨64, true, []⟩ { kind := .param 0 "T", layoutIdx := 0 } = none ∧
      translateTy ⟨64, true, []⟩ { kind := .alias "T::Item" [], layoutIdx := 0 } = none ∧
      monoCallee? [fbBlackBoxCallee] (fbFnOp "core::intrinsics::black_box" [.uint .u32])
        "core::intrinsics::black_box" = none ∧
      monoCallee? [{ fbBlackBoxCallee with typeParamCount := 1 }]
        (fbFnOp "core::intrinsics::black_box" []) "core::intrinsics::black_box" = none ∧
      progInFragment
        (fbCaller "boundary::poly_caller" "core::intrinsics::black_box" [.param 0 "T"]
          [u32Decl, u32Decl] (fbAbi [u32Layout] u32Layout))
        [fbBlackBoxCallee] = false ∧
      progInFragment fbBlackBoxCaller [{ fbBlackBoxCallee with typeParamCount := 1 }] = false :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- Runtime fail-closed execution for polymorphic callee mismatches in Anneal's
`stepMirFn`:
1. Even when `Memory.callees` links `fbBlackBoxCallee` (`typeParamCount = 0`),
   a caller passing unmonomorphized `tys = [.param 0 "T"]` (`bdPolyBlackBoxCaller`)
   is **not** dispatched to `fbBlackBoxCallee` (`lookupCallee = none`); `stepMirFn`
   emits `MirStepNode.extCall` carrying `typeArgs := [.param 0 "T"]` instead of
   silently pushing a frame with erased type arguments.
2. Calling `core::intrinsics::exact_div` with unmonomorphized `RigidTy.param` or
   `RigidTy.alias` `typeArgs` fails closed immediately with
   `MirStepNode.unsupported` (`resolveIntrinsicIsSigned = none`). -/
def bdPolyBlackBoxCaller : CapturedMir :=
  fbCaller "boundary::poly_caller" "core::intrinsics::black_box" [.param 0 "T"]
    [u32Decl, u32Decl] (fbAbi [u32Layout] u32Layout)

def bdExactDivParamCaller : CapturedMir :=
  bdCallBody "boundary::exact_div_param" "core::intrinsics::exact_div" [.param 0 "T"] 2
    [u32Decl, u32Decl, u32Decl] (some 1)

def bdExactDivAliasCaller : CapturedMir :=
  bdCallBody "boundary::exact_div_alias" "core::intrinsics::exact_div" [.alias "T::Item" []] 2
    [u32Decl, u32Decl, u32Decl] (some 1)

theorem bdPolymorphicCall_anneal_failClosed :
    (∃ k, stepMirFn bdPolyBlackBoxCaller
        (initMachineStateWithCallees bdPolyBlackBoxCaller [.scalar ⟨7, 4⟩] [fbBlackBoxCallee]) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::black_box", typeArgs := [.param 0 "T"],
          args := [.scalar ⟨7, 4⟩],
          memory := (initMachineStateWithCallees bdPolyBlackBoxCaller
            [.scalar ⟨7, 4⟩] [fbBlackBoxCallee]).memory } k) ∧
    stepMirFn bdExactDivParamCaller
        (initMachineState bdExactDivParamCaller bdExactDivArgs) = MirStepNode.unsupported ∧
    stepMirFn bdExactDivAliasCaller
        (initMachineState bdExactDivAliasCaller bdExactDivArgs) = MirStepNode.unsupported :=
  ⟨⟨_, rfl⟩, rfl, rfl⟩

/-- End-to-end fail-closed rejection of MIR bodies containing unmonomorphized
`RigidTy.param` or `RigidTy.alias` locals/casts across `inFragment`,
`translateFn`, and Anneal's `stepMirFn` (`MirStepNode.unsupported`). -/
def bdUnmonoCastBody (rk : RigidTy) : CapturedMir :=
  { defPath := "boundary::unmono_cast"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls := [
      { mutability := .mut, ty := { kind := rk, layoutIdx := 0 }, debugName := none },
      u32Decl]
    basicBlocks := [
      { statements := [
          mkStmt (.assign (local_ 0)
            (.cast .intToInt (.copy (local_ 1)) { kind := rk, layoutIdx := 0 }))]
        terminator := mkTerm .return_
        isCleanup := false }]
    fnAbi := fbAbi [u32Layout] u32Layout
    layouts := emptyLayoutTable
    allocations := [] }

theorem bdUnmonoParamAliasBody_failClosed :
    inFragment (bdUnmonoCastBody (.param 0 "T")) = false ∧
      translateFn (bdUnmonoCastBody (.param 0 "T")) = none ∧
      stepMirFn (bdUnmonoCastBody (.param 0 "T"))
        (initMachineState (bdUnmonoCastBody (.param 0 "T")) [.scalar ⟨7, 4⟩]) =
        MirStepNode.unsupported ∧
      inFragment (bdUnmonoCastBody (.alias "T::Item" [])) = false ∧
      translateFn (bdUnmonoCastBody (.alias "T::Item" [])) = none ∧
      stepMirFn (bdUnmonoCastBody (.alias "T::Item" []))
        (initMachineState (bdUnmonoCastBody (.alias "T::Item" [])) [.scalar ⟨7, 4⟩]) =
        MirStepNode.unsupported :=
  ⟨by decide, rfl, rfl, by decide, rfl, rfl⟩

/-! ## 7. Lowered `LIntrinsicOp` / `LCallTarget` boundary correspondence (`DeinitBridge`) -/

/-- `MirSemantics.ctpopLoop` coincides identically with `popcountBits`. -/
theorem ctpopLoop_eq_popcountBits : ∀ (n u : Nat), ctpopLoop n u = popcountBits n u
  | 0, _ => rfl
  | n + 1, u => by simp [ctpopLoop, popcountBits, Nat.add_eq, ctpopLoop_eq_popcountBits n (u / 2)]

/-- **Symbolic correspondence for `LIntrinsicOp.ctpop` against MiniRust's `IntUnOp::CountOnes`
(`evalLIntrinsic_ctpop_eq_minirust`)**: across every signed and unsigned `IntType` width
(`GoodSize it.size.bytes`) and every valid bit pattern `bits < 2 ^ (8 * it.size.bytes)`,
`evalLIntrinsicValue .ctpop` produces the 4-byte `u32` population count matching MiniRust's
`evalUnOp (.Int .CountOnes)`. -/
theorem evalLIntrinsic_ctpop_eq_minirust
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (bits : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (tys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    evalUnOp (.Int .CountOnes) (.Int (intFromBits bits it), .Int it) =
        .ok (.Int (evalCountOnes (intFromBits bits it) it), .Int ⟨.Unsigned, ⟨4⟩⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctpop tys decls layouts argOps
          [.scalar ⟨bits, it.size.bytes⟩] flag =
        some (.scalar ⟨(evalCountOnes (intFromBits bits it) it).toNat, 4⟩) := by
  refine ⟨evalUnOp_countOnes (intFromBits bits it) it hgood, ?_⟩
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hWrap : wrapScalarBits bits (scalarModulus it.size.bytes) = bits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hbits]
  rw [evalCountOnes_intFromBits, Int.toNat_natCast]
  simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCtpop, hbeq, hWrap,
    Nat.mul_eq, Nat.mul_comm it.size.bytes 8, ctpopLoop_eq_popcountBits]

/-- Boolean check that `ov` is `some (.scalar ⟨bits, sz⟩)`, used for fast kernel reduction over
exhaustive `u8`/`i8` domains and `u32` boundary samples. -/
def optScalarIs (ov : Option Value) (bits sz : Nat) : Bool :=
  match ov with
  | some (.scalar sc) => Nat.beq sc.bits bits && Nat.beq sc.sizeBytes sz
  | _ => false

theorem optScalarIs_iff (ov : Option Value) (bits sz : Nat) :
    optScalarIs ov bits sz = true ↔ ov = some (.scalar ⟨bits, sz⟩) := by
  cases ov with
  | none => simp [optScalarIs]
  | some v =>
    cases v with
    | scalar sc =>
      rcases sc with ⟨b, s⟩
      simp [optScalarIs, nat_beq_eq_decide]
    | _ => simp [optScalarIs]

/-- **Exhaustive bit-manipulation & saturating correspondence between `LIntrinsicOp` and
`IntrinsicFallback`'s MiniRust-verified specifications (`evalLIntrinsic_bitops_fallback_correspondence`)**:
- `ctlz`, `cttz`, and `bitreverse` agree with `fbCtlzSpec`, `fbCttzSpec`, and `fbBitrevSpec` for
  all `a < 256` (which `fbCtlz_minirust_all`, `fbCttz_minirust_all`, and `fbBitrev_minirust_all`
  connect end-to-end to MiniRust machine execution);
- `ctlzNonzero` and `cttzNonzero` fault (`none`) at `0` and agree with `fbCtlzSpec` / `fbCttzSpec`
  for all `1 ≤ a < 256`;
- `bswap` agrees with `fbBswapSpec` across all `fbU32Samples` (`fbBswap_minirust_samples`);
- `saturatingAdd` (`u8`) and `saturatingSub` (`i8`) agree with `fbSatAddSpec` and `fbSatSubSpec`
  across the full 256-input `b = 128` rows (`fbSatAdd_minirust_row`, `fbSatSub_minirust_row`). -/
theorem evalLIntrinsic_bitops_fallback_correspondence :
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbCtlzSpec a, 4⟩)) ∧
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlzNonzero [.uint .u8] [] emptyLayoutTable []
      [.scalar ⟨0, 1⟩] true = none ∧
    (∀ i < 255,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlzNonzero [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨i + 1, 1⟩] true = some (.scalar ⟨fbCtlzSpec (i + 1), 4⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbCttzSpec a, 4⟩)) ∧
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttzNonzero [.uint .u8] [] emptyLayoutTable []
      [.scalar ⟨0, 1⟩] true = none ∧
    (∀ i < 255,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttzNonzero [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨i + 1, 1⟩] true = some (.scalar ⟨fbCttzSpec (i + 1), 4⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbBitrevSpec a, 1⟩)) ∧
    (∀ a ∈ fbU32Samples,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bswap [.uint .u32] [] emptyLayoutTable []
        [.scalar ⟨a, 4⟩] true = some (.scalar ⟨fbBswapSpec a, 4⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .saturatingAdd [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩] true = some (.scalar ⟨fbSatAddSpec a 128, 1⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .saturatingSub [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩, .scalar ⟨128, 1⟩] true = some (.scalar ⟨fbSatSubSpec a 128, 1⟩)) := by
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .ctlz [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbCtlzSpec x) 4)
        (by decide +kernel) a ha)
  · intro i hi
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .ctlzNonzero [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x + 1, 1⟩] true) (fbCtlzSpec (x + 1)) 4)
        (by decide +kernel) i hi)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .cttz [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbCttzSpec x) 4)
        (by decide +kernel) a ha)
  · intro i hi
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .cttzNonzero [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x + 1, 1⟩] true) (fbCttzSpec (x + 1)) 4)
        (by decide +kernel) i hi)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .bitreverse [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbBitrevSpec x) 1)
        (by decide +kernel) a ha)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_mem_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .bswap [.uint .u32] [] emptyLayoutTable [] [.scalar ⟨x, 4⟩] true) (fbBswapSpec x) 4)
        (by decide +kernel) a ha)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .saturatingAdd [.uint .u8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩, .scalar ⟨128, 1⟩] true)
        (fbSatAddSpec x 128) 1) (by decide +kernel) a ha)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .saturatingSub [.int .i8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩, .scalar ⟨128, 1⟩] true)
        (fbSatSubSpec x 128) 1) (by decide +kernel) a ha)

/-- **`V2026_06_01` adapter classification on `IntrinsicBoundary` call targets
(`lowerIntrinsicKind_boundary_correspondence`)**: verifies how `lowerIntrinsicKind_V2026_06_01` and
`classifyLinkedCallTarget_V2026_06_01` partition inline intrinsics (`exact_div`, `arith_offset`,
`ctpop`, `ub_checks`, `abort`, `unreachable_unchecked`, sub-place `write_bytes` /
`copy_nonoverlapping`), unmodeled external intrinsics (`cold_path` -> `none` -> `.callee`), and
linked fallback bodies (`hasLinkedBody = true` overrides `.inlineIntrinsic` with `.callee`,
matching `lookupCallee` precedence in `IntrinsicFallback`). -/
theorem lowerIntrinsicKind_boundary_correspondence :
    Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::exact_div" =
        some .exactDiv ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::arith_offset" =
        some .arithOffset ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::ctpop" =
        some .ctpop ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::ub_checks" =
        some .ubChecks ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::abort" =
        some .abort ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::hint::unreachable_unchecked" =
        some .unreachableUnchecked ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::write_bytes" =
        some .writeBytes ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01
          "core::intrinsics::copy_nonoverlapping" =
        some .copyNonOverlapping ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::cold_path" =
        none ∧
      Anneal.Mir.AdtAndControl.classifyLinkedCallTarget_V2026_06_01 true
          "core::intrinsics::ctlz" [] =
        .callee "core::intrinsics::ctlz" [] ∧
      Anneal.Mir.AdtAndControl.classifyLinkedCallTarget_V2026_06_01 false
          "core::intrinsics::ctlz" [.uint .u8] =
        .inlineIntrinsic .ctlz [.uint .u8] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 8. `[adv ep2-B3]` Two-sided success parity, bit-level value links, diverging intrinsics,
`*_nonzero` vs MiniRust `Assume`, and negative controls

The Section 7 / `DeinitBridge` bridges state one-directional implications (`MiniRust ok → Anneal
some` and `MiniRust UB → Anneal none`). Those implications would hold vacuously if MiniRust's
`evalBinOp` could return some third outcome (`specPanic`, `unsupported`, ...) on the operands in
question. Section 8a closes that hole: `evalIntBinOp_ok_or_ub` proves MiniRust integer arithmetic
is total on the `ok`/`UB` dichotomy, which upgrades the unchecked-arithmetic, unchecked-shift, and
`exact_div` bridges to genuine `isSome ↔ ok` equivalences. Section 8b ties the *same bits* Anneal
returns for `three_way_compare` and `ub_checks` to MiniRust's decoding of them (`valOf`),
instead of pairing two independently computed results. Section 8c lifts the diverging
`abort` / `unreachable_unchecked` correspondence from a single witness body to every
`evalLoweredIntrinsicCall` input and connects `abort` to MiniRust's `IntrinsicOp::Abort` and
`ctlz_nonzero` / `cttz_nonzero` to MiniRust's `IntrinsicOp::Assume`. Section 8d records concrete
negative controls that a mis-wired bridge (wrapping vs unchecked vs saturating, signed vs
unsigned, operand width) would fail, and Section 8e checks signedness independence of the
bit-manipulation intrinsics exhaustively on `i8`. -/

section AdvEp2B3

set_option autoImplicit false

/-! ### 8a. UB/ok dichotomy of MiniRust integer arithmetic and two-sided success parity -/

/-- **MiniRust integer arithmetic is total on the `ok`/`UB` dichotomy
(`evalIntBinOp_ok_or_ub`)**: for every `IntBinOp` and all mathematical integer operands,
`evalIntBinOp` either returns `.ok z` or raises `.ub msg` — never `specPanic`, `unsupported`, or
any other `Stop`. -/
theorem evalIntBinOp_ok_or_ub (op : Gen.IntBinOp) (l r : Int) (it : Gen.IntType) :
    (∃ z, evalIntBinOp op l r it = .ok z) ∨
      (∃ msg, evalIntBinOp op l r it = .error (.ub msg)) := by
  cases op <;> simp only [evalIntBinOp]
  all_goals
    first
    | exact .inl ⟨_, rfl⟩
    | (repeat' split) <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩

/-- **`BinOp::Int` on integer operands is total on the `ok`/`UB` dichotomy
(`evalBinOp_int_ok_or_ub`)**: for any right-operand type `rTy` (the heterogeneous shift case),
`evalBinOp (.Int op)` either returns `.ok (.Int res, .Int it)` or raises `.ub msg`. -/
theorem evalBinOp_int_ok_or_ub (op : Gen.IntBinOp) (l r : Int) (it : Gen.IntType)
    (rTy : Gen.Type) :
    (∃ res, evalBinOp (.Int op) (.Int l, .Int it) (.Int r, rTy) = .ok (.Int res, .Int it)) ∨
      (∃ msg, evalBinOp (.Int op) (.Int l, .Int it) (.Int r, rTy) = .error (.ub msg)) := by
  rcases evalIntBinOp_ok_or_ub op l r it with ⟨z, hz⟩ | ⟨msg, hm⟩
  · exact .inl ⟨IntType.bring_in_bounds it z,
      by simp [evalBinOp, hz, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr ⟨msg, by simp [evalBinOp, hm, Bind.bind, Except.bind]⟩

/-- **Two-sided success parity for `uncheckedAdd` / `uncheckedSub` / `uncheckedMul` /
`uncheckedDiv` / `uncheckedRem` (`evalLIntrinsic_unchecked_binop_isSome_iff_minirust_ok`)**:
`evalLIntrinsicValue` succeeds **iff** MiniRust's `evalBinOp (.Int iop)` succeeds, across every
integer `RigidTy` and all valid bit patterns (strengthening
`DeinitBridge.evalLIntrinsic_unchecked_binop_iff_minirust` with `evalBinOp_int_ok_or_ub`). -/
theorem evalLIntrinsic_unchecked_binop_isSome_iff_minirust_ok
    (op : Anneal.Mir.AdtAndControl.LIntrinsicOp) (bop : MirAst.BinOp) (iop : Gen.IntBinOp)
    (hop : DeinitBridge.uncheckedArithLIntrinsicPair op = some (bop, iop))
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag).isSome = true ↔
      ∃ res, evalBinOp (.Int iop) (.Int (intFromBits x it), .Int it)
        (.Int (intFromBits y it), .Int it) = .ok (.Int res, .Int it) := by
  have h := DeinitBridge.evalLIntrinsic_unchecked_binop_iff_minirust op bop iop hop hrk x y hx hy
    restTys decls layouts argOps flag
  dsimp only at h
  constructor
  · intro hs
    rcases evalBinOp_int_ok_or_ub iop (intFromBits x it) (intFromBits y it) it (.Int it) with
      hok | hub
    · exact hok
    · rw [h.2 hub] at hs; nomatch hs
  · rintro ⟨res, hres⟩
    rw [(h.1 res hres).2]; rfl

/-- **Two-sided success parity for `uncheckedShl` / `uncheckedShr`, including heterogeneous
right-operand widths and negative signed shift counts
(`evalLIntrinsic_unchecked_shift_isSome_iff_minirust_ok`)**: `evalLIntrinsicValue` succeeds
**iff** MiniRust's `evalBinOp (.Int .ShlUnchecked / .ShrUnchecked)` succeeds. -/
theorem evalLIntrinsic_unchecked_shift_isSome_iff_minirust_ok
    (isShr : Bool)
    {lhsRk rhsRk : RigidTy} {it rhsIt : Gen.IntType}
    (hLhs : intTyBytes lhsRk = some (it.signed, it.size.bytes))
    (hRhs : intTyBytes rhsRk = some (rhsIt.signed, rhsIt.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * rhsIt.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        (if isShr then .uncheckedShr else .uncheckedShl) (lhsRk :: rhsRk :: restTys) decls
        layouts argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, rhsIt.size.bytes⟩] flag).isSome =
        true ↔
      ∃ res, evalBinOp (.Int (if isShr then .ShrUnchecked else .ShlUnchecked))
        (.Int (intFromBits x it), .Int it) (.Int (intFromBits y rhsIt), .Int rhsIt) =
          .ok (.Int res, .Int it) := by
  have h := DeinitBridge.evalLIntrinsic_unchecked_shift_iff_minirust isShr hLhs hRhs x y hx hy
    restTys decls layouts argOps flag
  dsimp only at h
  constructor
  · intro hs
    rcases evalBinOp_int_ok_or_ub (if isShr then .ShrUnchecked else .ShlUnchecked)
      (intFromBits x it) (intFromBits y rhsIt) it (.Int rhsIt) with hok | hub
    · exact hok
    · rw [h.2 hub] at hs; nomatch hs
  · rintro ⟨res, hres⟩
    rw [(h.1 res hres).2]; rfl

/-- **Two-sided success parity for `exactDiv` (`evalLIntrinsic_exactDiv_isSome_iff_minirust_ok`)**:
`evalLIntrinsicValue .exactDiv` succeeds **iff** MiniRust's `evalBinOp (.Int .DivExact)` succeeds,
i.e. Anneal faults on exactly MiniRust's three UB conditions (division by zero, signed
`MIN / -1`, non-zero remainder) and on nothing else. -/
theorem evalLIntrinsic_exactDiv_isSome_iff_minirust_ok
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag).isSome = true ↔
      ∃ q, evalBinOp (.Int .DivExact) (.Int (intFromBits x it), .Int it)
        (.Int (intFromBits y it), .Int it) = .ok (.Int q, .Int it) := by
  have h := DeinitBridge.evalLIntrinsic_exactDiv_iff_minirust hrk x y hx hy
    restTys decls layouts argOps flag
  dsimp only at h
  constructor
  · intro hs
    rcases evalBinOp_int_ok_or_ub .DivExact (intFromBits x it) (intFromBits y it) it (.Int it) with
      hok | hub
    · exact hok
    · rw [h.2 hub] at hs; nomatch hs
  · rintro ⟨q, hq⟩
    rw [(h.1 q hq).2]; rfl

/-! ### 8b. Bit-level value links for `threeWayCompare` and `ubChecks` -/

/-- **`threeWayCompare` returns exactly the `Ordering` tag MiniRust computes
(`evalLIntrinsic_threeWayCompare_ordering_tag`)**: the 1-byte scalar `bits` that
`evalLIntrinsicValue .threeWayCompare` returns is a valid `Ordering` tag, and MiniRust's
`translateCmp` lowering (`BinOp::Rel(Cmp)` followed by `Transmute` to `Ordering`) evaluates to
`valOf orderingTy bits` — MiniRust's decoding of those very bits — across every integer type and
all valid operands. -/
theorem evalLIntrinsic_threeWayCompare_ordering_tag
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    ∃ bits,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare (rk :: restTys) decls layouts
          argOps [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨bits, 1⟩) ∧
      ValidBits orderingTy bits ∧
      (evalBinOp (.Rel .Cmp) (.Int (intFromBits x it), .Int it) (.Int (intFromBits y it), .Int it)
          >>= evalUnOp (.Cast (.Transmute orderingTy))) =
        .ok (valOf orderingTy bits, orderingTy) := by
  have h := DeinitBridge.evalLIntrinsic_threeWayCompare_eq_minirust hrk x y hx hy restTys decls
    layouts argOps flag
  dsimp only at h
  refine ⟨ordBits (cmpOf (.Int it) x y), h.2, validBits_ordBits _, ?_⟩
  rw [h.1]
  exact evalUnOp_transmute_ordering _

/-- **`ubChecks` returns exactly the bits MiniRust decodes as the session's `bool`
(`evalLIntrinsic_ubChecks_bool_encoding`)**: the 1-byte scalar `bits` that
`evalLIntrinsicValue .ubChecks` returns decodes (`valOf .Bool`) to the very `bool` constant that
`minimize` emits for `ub_checks()` and MiniRust evaluates. -/
theorem evalLIntrinsic_ubChecks_bool_encoding
    (flag : Bool) (m : Mach) (tys : List RigidTy) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) :
    ∃ bits,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ubChecks tys decls layouts argOps [] flag =
        some (.scalar ⟨bits, 1⟩) ∧
      Interp.evalValue m (.Constant (.Bool flag) .Bool) = .ok ((valOf .Bool bits, .Bool), m) := by
  cases flag <;> exact ⟨_, rfl, rfl⟩

/-! ### 8c. Diverging intrinsics and `*_nonzero` against MiniRust `Abort`, `Unreachable`, and
`Assume` -/

/-- **Symbolic `abort` correspondence (`evalLIntrinsic_abort_minirust_correspondence`)**: for
every machine, argument list, and return type, MiniRust's `IntrinsicOp::Abort` stops with
`.error .abort`; for every `evalLoweredIntrinsicCall` input, Anneal's lowered `abort` terminates
the program at the current block (`.terminated bb`, bypassing any cleanup edge) exactly when the
terminator's unwind action is admissible (`unwindActionOk`, mirroring Trusted's check), and is
rejected whenever a return `target` is present (`abort` is diverging); and the adapter routes
`core::intrinsics::abort`, which Trusted treats as an aborting panic path, to `.abort`. -/
theorem evalLIntrinsic_abort_minirust_correspondence
    (m : Mach) (arguments : List (Val × Gen.Type)) (retTy : Gen.Type)
    (env : Anneal.Mir.AdtAndControl.CfgEnv) (body : Anneal.Mir.AdtAndControl.LBody)
    (bb : Nat) (inCleanup : Bool) (args : List Operand) (avs : List Value)
    (slots2 : List Anneal.Mir.PlaceAndRvalue.LocalSlotState) (dest : Place) (destTy : Ty)
    (unwind : UnwindAction) (unwinding : Option Nat) (typeArgs : List RigidTy) :
    Interp.evalIntrinsic m .Abort arguments retTy = .error .abort ∧
      Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup args avs slots2 dest
          destTy none unwind unwinding .abort typeArgs =
        (if Anneal.Mir.AdtAndControl.unwindActionOk body inCleanup unwind then
          some (.terminated bb) else none) ∧
      (∀ t, Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup args avs slots2
          dest destTy (some t) unwind unwinding .abort typeArgs = none) ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::abort" =
        some .abort ∧
      isAbortingPanicDefPath "core::intrinsics::abort" = true := by
  refine ⟨rfl, ?_, fun t => ?_, rfl, by decide⟩
  · simp only [Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall]
    cases Anneal.Mir.AdtAndControl.unwindActionOk body inCleanup unwind <;> rfl
  · simp only [Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall]
    cases Anneal.Mir.AdtAndControl.unwindActionOk body inCleanup unwind <;> rfl

/-- **Symbolic `unreachable_unchecked` correspondence
(`evalLIntrinsic_unreachable_minirust_correspondence`)**: MiniRust's `Terminator::Unreachable`
raises UB on every machine, and Anneal's lowered `unreachableUnchecked` is rejected (`none`) for
every `evalLoweredIntrinsicCall` input (any target, unwind action, operands, and destination);
both `core::hint::unreachable_unchecked` and `core::intrinsics::unreachable` lower to it and are
Trusted unreachable call targets. -/
theorem evalLIntrinsic_unreachable_minirust_correspondence
    (m : Mach) (env : Anneal.Mir.AdtAndControl.CfgEnv) (body : Anneal.Mir.AdtAndControl.LBody)
    (bb : Nat) (inCleanup : Bool) (args : List Operand) (avs : List Value)
    (slots2 : List Anneal.Mir.PlaceAndRvalue.LocalSlotState) (dest : Place) (destTy : Ty)
    (target : Option Nat) (unwind : UnwindAction) (unwinding : Option Nat)
    (typeArgs : List RigidTy) :
    Interp.evalTerminator m .Unreachable = .error (.ub "reached unreachable code") ∧
      Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup args avs slots2 dest
          destTy target unwind unwinding .unreachableUnchecked typeArgs = none ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::hint::unreachable_unchecked" =
        some .unreachableUnchecked ∧
      Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::intrinsics::unreachable" =
        some .unreachableUnchecked ∧
      isUnreachableCallTarget "core::hint::unreachable_unchecked" = true ∧
      isUnreachableCallTarget "core::intrinsics::unreachable" = true :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- **`ctlz_nonzero` / `cttz_nonzero` against MiniRust's `IntrinsicOp::Assume`
(`evalLIntrinsic_nonzero_minirust_assume`)**: across every integer width (`GoodSize`) and valid
bit pattern, Anneal's `ctlzNonzero` / `cttzNonzero` fault exactly at `0` and otherwise coincide
with `ctlz` / `cttz`, while MiniRust's `Assume(x != 0)` (the precondition the `*_nonzero`
intrinsics impose) raises UB exactly at `0` and otherwise returns `()`. -/
theorem evalLIntrinsic_nonzero_minirust_assume
    (it : Gen.IntType) (hgood : GoodSize it.size.bytes)
    (bits : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (tys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) (m : Mach) :
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlzNonzero tys decls layouts argOps
        [.scalar ⟨bits, it.size.bytes⟩] flag =
      (if bits = 0 then none else
        Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz tys decls layouts argOps
          [.scalar ⟨bits, it.size.bytes⟩] flag) ∧
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttzNonzero tys decls layouts argOps
        [.scalar ⟨bits, it.size.bytes⟩] flag =
      (if bits = 0 then none else
        Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz tys decls layouts argOps
          [.scalar ⟨bits, it.size.bytes⟩] flag) ∧
    Interp.evalIntrinsic m .Assume [(.Bool (!decide (bits = 0)), .Bool)]
        (.Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none) =
      (if bits = 0 then .error (.ub "`Assume` intrinsic called on condition that is violated")
        else .ok (unitValue, m)) := by
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hWrap : wrapScalarBits bits (scalarModulus it.size.bytes) = bits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hbits]
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : bits = 0
    · subst h0
      simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCtlzNonzero, hbeq, hWrap]
    · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCtlzNonzero, evalCtlz, hbeq, hWrap,
        h0, nat_beq_eq_decide]
  · by_cases h0 : bits = 0
    · subst h0
      simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCttzNonzero, hbeq, hWrap]
    · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCttzNonzero, evalCttz, hbeq, hWrap,
        h0, nat_beq_eq_decide]
  · by_cases h0 : bits = 0
    · subst h0; rfl
    · simp [h0, Interp.evalIntrinsic]

/-! ### 8d. Negative controls -/

/-- **Negative controls for the lowered-intrinsic ↔ MiniRust bridges
(`minirust_intrinsic_negative_controls`)**: concrete operand pairs on which the candidate
semantics *disagree*, each checked on both sides, so that a bridge wired to the wrong operation,
signedness, or width would fail to compile:
1. `u8` `255 + 1`: wrapping (`IntBinOp::Add`) gives `0`, saturating gives `255`, while
2. `unchecked_add` is UB in MiniRust and faults in Anneal;
3. signed `i8` `127 + 1` overflows (UB / fault) although
4. unsigned `u8` `127 + 1 = 128` does not;
5. `exact_div(i8::MIN, -1)` is UB ("overflow in division") / faults, although
6. the same mathematical operands in `i32` give `128`;
7. `unchecked_shr(-128i8, 7) = -1` (arithmetic shift, bits `0xFF`), while
8. `unchecked_shr(128u8, 7) = 1` (logical shift) on the same bit pattern `0x80`;
9. `three_way_compare(-128i8, 1)` is `Less` (tag bits `255`), while
10. `three_way_compare(128u8, 1)` is `Greater` (tag bits `1`) on the same bit patterns. -/
theorem minirust_intrinsic_negative_controls :
    (evalBinOp (.Int .Add) (.Int 255, .Int u8) (.Int 1, .Int u8) = .ok (.Int 0, .Int u8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .wrappingAdd [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨0, 1⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .saturatingAdd [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨255, 1⟩)) ∧
    (evalBinOp (.Int .AddUnchecked) (.Int 255, .Int u8) (.Int 1, .Int u8) =
        .error (.ub "overflow in unchecked add") ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .uncheckedAdd [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨255, 1⟩, .scalar ⟨1, 1⟩] true = none) ∧
    (evalBinOp (.Int .AddUnchecked) (.Int 127, .Int i8) (.Int 1, .Int i8) =
        .error (.ub "overflow in unchecked add") ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .uncheckedAdd [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨127, 1⟩, .scalar ⟨1, 1⟩] true = none) ∧
    (evalBinOp (.Int .AddUnchecked) (.Int 127, .Int u8) (.Int 1, .Int u8) =
        .ok (.Int 128, .Int u8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .uncheckedAdd [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨127, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨128, 1⟩)) ∧
    (evalBinOp (.Int .DivExact) (.Int (-128), .Int i8) (.Int (-1), .Int i8) =
        .error (.ub "overflow in division") ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨0x80, 1⟩, .scalar ⟨0xFF, 1⟩] true = none) ∧
    (evalBinOp (.Int .DivExact) (.Int (-128), .Int i32) (.Int (-1), .Int i32) =
        .ok (.Int 128, .Int i32) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv [.int .i32] [] emptyLayoutTable []
        [.scalar ⟨0xFFFFFF80, 4⟩, .scalar ⟨0xFFFFFFFF, 4⟩] true = some (.scalar ⟨0x80, 4⟩)) ∧
    (evalBinOp (.Int .ShrUnchecked) (.Int (-128), .Int i8) (.Int 7, .Int u32) =
        .ok (.Int (-1), .Int i8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .uncheckedShr [.int .i8, .uint .u32] []
        emptyLayoutTable [] [.scalar ⟨0x80, 1⟩, .scalar ⟨7, 4⟩] true = some (.scalar ⟨0xFF, 1⟩)) ∧
    (evalBinOp (.Int .ShrUnchecked) (.Int 128, .Int u8) (.Int 7, .Int u32) =
        .ok (.Int 1, .Int u8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .uncheckedShr [.uint .u8, .uint .u32] []
        emptyLayoutTable [] [.scalar ⟨0x80, 1⟩, .scalar ⟨7, 4⟩] true = some (.scalar ⟨0x01, 1⟩)) ∧
    (evalBinOp (.Rel .Cmp) (.Int (-128), .Int i8) (.Int 1, .Int i8) = .ok (.Int (-1), .Int i8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨0x80, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨255, 1⟩)) ∧
    (evalBinOp (.Rel .Cmp) (.Int 128, .Int u8) (.Int 1, .Int u8) = .ok (.Int 1, .Int i8) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨0x80, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨1, 1⟩)) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ### 8e. Signedness independence of the bit-manipulation intrinsics on `i8` -/

/-- **Signedness independence of `ctlz`, `cttz`, and `bitreverse`
(`evalLIntrinsic_bitops_i8_signedness_independent`)**: on the signed `i8` type, exhaustively over
all 256 bit patterns, `evalLIntrinsicValue` returns the same MiniRust-verified fallback
specifications (`fbCtlzSpec`, `fbCttzSpec`, `fbBitrevSpec`) that
`evalLIntrinsic_bitops_fallback_correspondence` establishes for `u8`: these intrinsics act on the
raw bit pattern, never on the decoded signed value. -/
theorem evalLIntrinsic_bitops_i8_signedness_independent :
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbCtlzSpec a, 4⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbCttzSpec a, 4⟩)) ∧
    (∀ a < 256,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨a, 1⟩] true = some (.scalar ⟨fbBitrevSpec a, 1⟩)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .ctlz [.int .i8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbCtlzSpec x) 4)
        (by decide +kernel) a ha)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .cttz [.int .i8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbCttzSpec x) 4)
        (by decide +kernel) a ha)
  · intro a ha
    exact (optScalarIs_iff _ _ _).mp
      (fb_forall_lt_of_all (p := fun x => optScalarIs (Anneal.Mir.AdtAndControl.evalLIntrinsicValue
        .bitreverse [.int .i8] [] emptyLayoutTable [] [.scalar ⟨x, 1⟩] true) (fbBitrevSpec x) 1)
        (by decide +kernel) a ha)

end AdvEp2B3

/-! ## 9. `[adv ep2-A3]` Symbolic all-width bit-manipulation & endianness bridges, value-level
two-sided parity, `saturating` `valOf` clamping, `three_way_compare::<char>`, `size_of_val` /
`align_of_val` ↔ MiniRust `Type.layout` & `LayoutStrategy.compute_size_and_align`, symbolic
`panicUnwind`, and extended negative controls -/

section AdvEp2A3

set_option autoImplicit false

/-! ### 9a. Symbolic all-width `bswap`, `bitreverse`, `cttz`, `ctlz`, & MiniRust `CountOnes`
conservation (`B3` Open Item #1) -/

/-- `Interp.leValue` distributes across byte-list concatenation with radix `256`. -/
theorem leValue_append : ∀ (xs ys : List UInt8),
    Interp.leValue (xs ++ ys) = Interp.leValue xs + 256 ^ xs.length * Interp.leValue ys
  | [], ys => by simp [Interp.leValue]
  | b :: xs, ys => by
    simp only [List.cons_append, Interp.leValue, List.length_cons, leValue_append xs ys,
      Nat.pow_succ, Nat.left_distrib]
    rw [show (256 ^ xs.length * 256) * Interp.leValue ys =
      256 * (256 ^ xs.length * Interp.leValue ys) by
        rw [Nat.mul_comm _ 256, Nat.mul_assoc]]
    exact (Nat.add_assoc _ _ _).symm

/-- `Interp.leValue xs` is strictly bounded by `256 ^ xs.length`. -/
theorem leValue_lt : ∀ (xs : List UInt8), Interp.leValue xs < 256 ^ xs.length
  | [] => by simp [Interp.leValue]
  | b :: xs => by
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have ih := leValue_lt xs
    simp only [Interp.leValue, List.length_cons, Nat.pow_succ]
    generalize 256 ^ xs.length = P at ih ⊢
    omega

private theorem uint8_ofNat_mod_256 (u : Nat) : (UInt8.ofNat (u % 256)).toNat = u % 256 := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.mod_lt u (by decide))

/-- `Interp.leBytes (Interp.leValue xs) xs.length = xs` for every byte list `xs`. -/
theorem leBytes_leValue : ∀ (xs : List UInt8), Interp.leBytes (Interp.leValue xs) xs.length = xs
  | [] => rfl
  | b :: xs => by
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hMod : (b.toNat + 256 * Interp.leValue xs) % 256 = b.toNat := by omega
    have hDiv : (b.toNat + 256 * Interp.leValue xs) / 256 = Interp.leValue xs := by omega
    have hbEq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
    simp only [List.length_cons, Interp.leBytes, Interp.leValue, hMod, hDiv, hbEq,
      leBytes_leValue xs]

/-- `bswapLoop n u acc` equals `256 ^ n * acc + Interp.leValue ((Interp.leBytes u n).reverse)`. -/
theorem bswapLoop_eq_leValue_reverse : ∀ (n u acc : Nat),
    bswapLoop n u acc = 256 ^ n * acc + Interp.leValue ((Interp.leBytes u n).reverse)
  | 0, u, acc => by simp [bswapLoop, Interp.leBytes, Interp.leValue]
  | n + 1, u, acc => by
    have hStep : bswapLoop (n + 1) u acc = bswapLoop n (u / 256) (acc * 256 + u % 256) := rfl
    have hBytes : Interp.leBytes u (n + 1) =
        UInt8.ofNat (u % 256) :: Interp.leBytes (u / 256) n := rfl
    rw [hStep, hBytes, bswapLoop_eq_leValue_reverse n]
    simp only [List.reverse_cons, leValue_append, List.length_reverse, leBytes_length,
      Interp.leValue, uint8_ofNat_mod_256, Nat.pow_succ, Nat.mul_zero, Nat.add_zero]
    rw [Nat.left_distrib, show (256 ^ n * 256) * acc = 256 ^ n * (acc * 256) by
      rw [Nat.mul_assoc, Nat.mul_comm 256 acc]]
    omega

private theorem two_pow_eight_mul_eq_256_pow : ∀ (n : Nat), 2 ^ (8 * n) = 256 ^ n
  | 0 => rfl
  | n + 1 => by
    have h8 : 8 * (n + 1) = 8 * n + 8 := by omega
    rw [h8, Nat.pow_add, two_pow_eight_mul_eq_256_pow n, Nat.pow_succ]
    rfl

/-- **Symbolic all-width `bswap` ↔ MiniRust `Endianness.decode` & involution bridge
(`evalLIntrinsic_bswap_minirust_endianness_all_widths`)**: across **every** signed and unsigned
integer `RigidTy` `rk` (`intTyBytes rk = some (it.signed, it.size.bytes)`) and all valid bit
patterns `bits < 2 ^ (8 * it.size.bytes)` (`u8`, `i8`, `u16`, `i16`, `u32`, `i32`, `u64`, `i64`,
`u128`, `i128`, `usize`, `isize`):
1. `evalLIntrinsicValue .bswap` produces `rev := Interp.leValue ((Interp.leBytes bits n).reverse)`,
   which satisfies `ValidBits (.Int it) rev`;
2. MiniRust's `valOf (.Int it) rev` equals `.Int (Interp.Endianness.decode .BigEndian it.signed
   (Interp.leBytes bits n))` — `bswap` converts directly between MiniRust's little-endian and
   big-endian byte representations;
3. `bswap` is an **involution** across all widths: applying `evalLIntrinsicValue .bswap` a second
   time recovers `some (.scalar ⟨bits, n⟩)`. -/
theorem evalLIntrinsic_bswap_minirust_endianness_all_widths
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (bits : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let n := it.size.bytes
    let rev := Interp.leValue ((Interp.leBytes bits n).reverse)
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bswap (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, n⟩] flag = some (.scalar ⟨rev, n⟩) ∧
      ValidBits (.Int it) rev ∧
      valOf (.Int it) rev =
        .Int (Interp.Endianness.decode .BigEndian it.signed (Interp.leBytes bits n)) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bswap (rk :: restTys) decls layouts argOps
        [.scalar ⟨rev, n⟩] flag = some (.scalar ⟨bits, n⟩) := by
  dsimp only
  obtain ⟨hgood, _, _⟩ := DeinitBridge.intTyBytes_intrinsic_props hrk false decls layouts
  generalize hRev : Interp.leValue ((Interp.leBytes bits it.size.bytes).reverse) = rev
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hWrap : wrapScalarBits bits (scalarModulus it.size.bytes) = bits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hbits]
  have hRevLt256 : rev < 256 ^ it.size.bytes := by
    have hL := leValue_lt ((Interp.leBytes bits it.size.bytes).reverse)
    simpa [← hRev, List.length_reverse, leBytes_length] using hL
  have hRevLt : rev < 2 ^ (8 * it.size.bytes) := by
    rwa [two_pow_eight_mul_eq_256_pow]
  have hRevWrap : wrapScalarBits rev (scalarModulus it.size.bytes) = rev := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hRevLt]
  have hBswap1 : bswapLoop it.size.bytes bits 0 = rev := by
    simp [bswapLoop_eq_leValue_reverse, hRev]
  have hBswap2 : bswapLoop it.size.bytes rev 0 = bits := by
    rw [bswapLoop_eq_leValue_reverse, Nat.mul_zero, Nat.zero_add]
    have hLen : ((Interp.leBytes bits it.size.bytes).reverse).length = it.size.bytes := by
      rw [List.length_reverse, leBytes_length]
    have hLB : Interp.leBytes rev it.size.bytes = (Interp.leBytes bits it.size.bytes).reverse := by
      simpa [hRev, hLen] using leBytes_leValue ((Interp.leBytes bits it.size.bytes).reverse)
    have hBits256 : bits < 256 ^ it.size.bytes := by
      rwa [← two_pow_eight_mul_eq_256_pow]
    rw [hLB, List.reverse_reverse, leValue_leBytes, Nat.mod_eq_of_lt hBits256]
  refine ⟨?_, hRevLt, ?_, ?_⟩
  · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalBswap, hbeq, hWrap, hBswap1]
  · simp only [valOf, intFromBits, Interp.Endianness.decode, leBytes_length, hRev]
    cases it.signed with
    | Unsigned => rfl
    | Signed =>
      congr 1
      have hp1 : ((2 ^ (8 * it.size.bytes - 1) : Nat) : Int) =
          (2 : Int) ^ (8 * it.size.bytes - 1) := by push_cast; rfl
      have hp2 : ((2 ^ (8 * it.size.bytes) : Nat) : Int) =
          (2 : Int) ^ (8 * it.size.bytes) := by push_cast; rfl
      rw [← hp1, ← hp2]
      by_cases hlt : rev < 2 ^ (8 * it.size.bytes - 1)
      · have hltI : (rev : Int) < ((2 ^ (8 * it.size.bytes - 1) : Nat) : Int) :=
          Int.ofNat_lt.mpr hlt
        simp only [hlt, hltI, ↓reduceIte]
      · have hltI : ¬((rev : Int) < ((2 ^ (8 * it.size.bytes - 1) : Nat) : Int)) :=
          mt Int.ofNat_lt.mp hlt
        simp only [hlt, hltI, ↓reduceIte]
  · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalBswap, hbeq, hRevWrap, hBswap2]

/-- Little-endian binary bit list of `u` of length `k` (LSB first). -/
def leBits (u : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => decide (u % 2 = 1) :: leBits (u / 2) k

/-- Natural number denoted by an LSB-first bit list `bs`. -/
def leBitValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * leBitValue bs

theorem leBits_length (u : Nat) : ∀ (k : Nat), (leBits u k).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (leBits_length (u / 2) k)

theorem leBitValue_append : ∀ (xs ys : List Bool),
    leBitValue (xs ++ ys) = leBitValue xs + 2 ^ xs.length * leBitValue ys
  | [], ys => by simp [leBitValue]
  | b :: xs, ys => by
    simp only [List.cons_append, leBitValue, List.length_cons, leBitValue_append xs ys,
      Nat.pow_succ, Nat.left_distrib]
    rw [show (2 ^ xs.length * 2) * leBitValue ys = 2 * (2 ^ xs.length * leBitValue ys) by
      rw [Nat.mul_comm _ 2, Nat.mul_assoc]]
    exact (Nat.add_assoc _ _ _).symm

theorem leBitValue_lt : ∀ (xs : List Bool), leBitValue xs < 2 ^ xs.length
  | [] => by simp [leBitValue]
  | b :: xs => by
    have ih := leBitValue_lt xs
    cases b <;> (simp only [leBitValue, ↓reduceIte, Bool.false_eq_true, List.length_cons,
      Nat.pow_succ]; generalize 2 ^ xs.length = P at ih ⊢; omega)

theorem leBitValue_leBits (u k : Nat) : leBitValue (leBits u k) = u % 2 ^ k := by
  induction k generalizing u with
  | zero => simp [leBits, leBitValue, Nat.mod_one]
  | succ k ih =>
    have hBit : (if decide (u % 2 = 1) then 1 else 0) = u % 2 := by
      by_cases h1 : u % 2 = 1
      · simp [h1]
      · have h0 : u % 2 = 0 := by omega
        simp [h0]
    simp only [leBits, leBitValue, hBit, ih]
    rw [show (2 : Nat) ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul]

theorem leBits_leBitValue : ∀ (xs : List Bool), leBits (leBitValue xs) xs.length = xs
  | [] => rfl
  | false :: xs => by
    have hMod : (0 + 2 * leBitValue xs) % 2 = 0 := by omega
    have hDiv : (0 + 2 * leBitValue xs) / 2 = leBitValue xs := by omega
    simp only [List.length_cons, leBits, leBitValue, Bool.false_eq_true, ↓reduceIte, hMod, hDiv,
      show decide (0 = 1) = false from rfl, leBits_leBitValue xs]
  | true :: xs => by
    have hMod : (1 + 2 * leBitValue xs) % 2 = 1 := by omega
    have hDiv : (1 + 2 * leBitValue xs) / 2 = leBitValue xs := by omega
    simp only [List.length_cons, leBits, leBitValue, ↓reduceIte, hMod, hDiv, decide_true,
      leBits_leBitValue xs]

theorem bitreverseLoop_eq_leBitValue_reverse : ∀ (k u acc : Nat),
    bitreverseLoop k u acc = 2 ^ k * acc + leBitValue ((leBits u k).reverse)
  | 0, u, acc => by simp [bitreverseLoop, leBits, leBitValue]
  | k + 1, u, acc => by
    have hStep : bitreverseLoop (k + 1) u acc = bitreverseLoop k (u / 2) (acc * 2 + u % 2) := rfl
    have hBits : leBits u (k + 1) = decide (u % 2 = 1) :: leBits (u / 2) k := rfl
    have hBit : (if decide (u % 2 = 1) then 1 else 0) = u % 2 := by
      by_cases h1 : u % 2 = 1
      · simp [h1]
      · have h0 : u % 2 = 0 := by omega
        simp [h0]
    rw [hStep, hBits, bitreverseLoop_eq_leBitValue_reverse k]
    simp only [List.reverse_cons, leBitValue_append, List.length_reverse, leBits_length,
      leBitValue, hBit, Nat.pow_succ, Nat.mul_zero, Nat.add_zero]
    rw [Nat.left_distrib, show (2 ^ k * 2) * acc = 2 ^ k * (acc * 2) by
      rw [Nat.mul_assoc, Nat.mul_comm 2 acc]]
    omega

theorem cttzLoop_eq_takeWhile_leBits : ∀ (k u : Nat),
    cttzLoop k u = ((leBits u k).takeWhile (!·)).length
  | 0, _ => rfl
  | k + 1, u => by
    have hBits : leBits u (k + 1) = decide (u % 2 = 1) :: leBits (u / 2) k := rfl
    have hModEq : Nat.mod u 2 = u % 2 := rfl
    have hDivEq : Nat.div u 2 = u / 2 := rfl
    unfold cttzLoop
    rw [hBits, hModEq, hDivEq]
    by_cases h0 : u % 2 = 0
    · have hBeq : Nat.beq (u % 2) 0 = true := by rw [nat_beq_eq_decide, decide_eq_true h0]
      have hNot1 : decide (u % 2 = 1) = false := by rw [h0]; rfl
      rw [hBeq, hNot1]
      change 1 + cttzLoop k (u / 2) = ((leBits (u / 2) k).takeWhile (!·)).length + 1
      rw [cttzLoop_eq_takeWhile_leBits k (u / 2)]
      omega
    · have h1 : u % 2 = 1 := by omega
      have hBeq : Nat.beq (u % 2) 0 = false := by rw [nat_beq_eq_decide, decide_eq_false h0]
      have hIs1 : decide (u % 2 = 1) = true := by rw [h1]; rfl
      rw [hBeq, hIs1]
      rfl

theorem popcountBits_eq_countP_leBits : ∀ (k u : Nat),
    popcountBits k u = (leBits u k).countP id
  | 0, _ => rfl
  | k + 1, u => by
    simp only [popcountBits, leBits, List.countP_cons, id_eq, popcountBits_eq_countP_leBits k (u / 2)]
    by_cases h1 : u % 2 = 1
    · simp [h1, Nat.add_comm]
    · have h0 : u % 2 = 0 := by omega
      simp [h0]

/-- **Symbolic all-width `bitreverse`, `cttz`, `ctlz`, & MiniRust `CountOnes` conservation bridge
(`evalLIntrinsic_bitops_symbolic_all_widths`)**: across **every** signed and unsigned integer
`RigidTy` `rk` (`intTyBytes rk = some (it.signed, it.size.bytes)`) and all valid bit patterns
`bits < 2 ^ (8 * it.size.bytes)`:
1. `bitreverse` returns `revBits := leBitValue ((leBits bits (8 * n)).reverse)` (`ValidBits (.Int it)
   revBits`), is an **involution** across all widths, AND **conserves MiniRust's native
   `evalUnOp (.Int .CountOnes)`** (`CountOnes(bitreverse(x)) = CountOnes(x)`);
2. `cttz` returns `((leBits bits (8 * n)).takeWhile (!·)).length` (bounded by `8 * n`, signedness-
   independent across all widths);
3. `ctlz` returns `(((leBits bits (8 * n)).reverse).takeWhile (!·)).length` and equals **`cttz`
   composed with `bitreverse`** across all widths! -/
theorem evalLIntrinsic_bitops_symbolic_all_widths
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (bits : Nat) (hbits : bits < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let n := it.size.bytes
    let w := 8 * n
    let revBits := leBitValue ((leBits bits w).reverse)
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, n⟩] flag = some (.scalar ⟨revBits, n⟩) ∧
      ValidBits (.Int it) revBits ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse (rk :: restTys) decls layouts argOps
        [.scalar ⟨revBits, n⟩] flag = some (.scalar ⟨bits, n⟩) ∧
      evalUnOp (.Int .CountOnes) (.Int (intFromBits revBits it), .Int it) =
        evalUnOp (.Int .CountOnes) (.Int (intFromBits bits it), .Int it) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, n⟩] flag =
        some (.scalar ⟨((leBits bits w).takeWhile (!·)).length, 4⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, n⟩] flag =
        some (.scalar ⟨(((leBits bits w).reverse).takeWhile (!·)).length, 4⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, n⟩] flag =
        Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz (rk :: restTys) decls layouts argOps
          [.scalar ⟨revBits, n⟩] flag := by
  dsimp only
  obtain ⟨hgood, _, _⟩ := DeinitBridge.intTyBytes_intrinsic_props hrk false decls layouts
  generalize hRev : leBitValue ((leBits bits (8 * it.size.bytes)).reverse) = revBits
  have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
  have hbeq : Nat.beq it.size.bytes 0 = false := by
    rw [nat_beq_eq_decide, decide_eq_false hsz]
  have hWrap : wrapScalarBits bits (scalarModulus it.size.bytes) = bits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hbits]
  have hMulComm : it.size.bytes * 8 = 8 * it.size.bytes := Nat.mul_comm _ _
  have hRevLen : ((leBits bits (8 * it.size.bytes)).reverse).length = 8 * it.size.bytes := by
    rw [List.length_reverse, leBits_length]
  have hRevLt : revBits < 2 ^ (8 * it.size.bytes) := by
    have hL := leBitValue_lt ((leBits bits (8 * it.size.bytes)).reverse)
    simpa [hRev, hRevLen] using hL
  have hRevWrap : wrapScalarBits revBits (scalarModulus it.size.bytes) = revBits := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hRevLt]
  have hLBRev : leBits revBits (8 * it.size.bytes) =
      (leBits bits (8 * it.size.bytes)).reverse := by
    simpa [hRev, hRevLen] using leBits_leBitValue ((leBits bits (8 * it.size.bytes)).reverse)
  have hBitrev1 : bitreverseLoop (it.size.bytes * 8) bits 0 = revBits := by
    rw [hMulComm, bitreverseLoop_eq_leBitValue_reverse, Nat.mul_zero, Nat.zero_add, hRev]
  have hBitrev2 : bitreverseLoop (it.size.bytes * 8) revBits 0 = bits := by
    rw [hMulComm, bitreverseLoop_eq_leBitValue_reverse, Nat.mul_zero, Nat.zero_add,
      hLBRev, List.reverse_reverse, leBitValue_leBits, Nat.mod_eq_of_lt hbits]
  have hCtlzEq : ctlzBits (it.size.bytes * 8) bits =
      (((leBits bits (8 * it.size.bytes)).reverse).takeWhile (!·)).length := by
    change cttzLoop (it.size.bytes * 8) (bitreverseLoop (it.size.bytes * 8) bits 0) = _
    rw [hBitrev1, hMulComm, cttzLoop_eq_takeWhile_leBits, hLBRev]
  have hCtlzVal :
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .ctlz (rk :: restTys) decls layouts argOps
        [.scalar ⟨bits, it.size.bytes⟩] flag =
        some (.scalar ⟨(((leBits bits (8 * it.size.bytes)).reverse).takeWhile (!·)).length, 4⟩) := by
    simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCtlz, hbeq, hWrap, hCtlzEq]
  have hCttzRevVal :
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .cttz (rk :: restTys) decls layouts argOps
        [.scalar ⟨revBits, it.size.bytes⟩] flag =
        some (.scalar ⟨((leBits revBits (8 * it.size.bytes)).takeWhile (!·)).length, 4⟩) := by
    simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCttz, hbeq, hRevWrap, hMulComm,
      cttzLoop_eq_takeWhile_leBits]
  refine ⟨?_, hRevLt, ?_, ?_, ?_, hCtlzVal, ?_⟩
  · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalBitreverse, hbeq, hWrap, hBitrev1]
  · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalBitreverse, hbeq, hRevWrap, hBitrev2]
  · rw [evalUnOp_countOnes (intFromBits revBits it) it hgood,
      evalUnOp_countOnes (intFromBits bits it) it hgood,
      evalCountOnes_intFromBits it revBits,
      evalCountOnes_intFromBits it bits]
    congr 3
    rw [popcountBits_eq_countP_leBits (8 * it.size.bytes) revBits,
      popcountBits_eq_countP_leBits (8 * it.size.bytes) bits, hLBRev, List.countP_reverse]
  · simp [Anneal.Mir.AdtAndControl.evalLIntrinsicValue, evalCttz, hbeq, hWrap, hMulComm,
      cttzLoop_eq_takeWhile_leBits]
  · rw [hCtlzVal, hCttzRevVal, hLBRev]

/-! ### 9b. Value-level two-sided parity, `saturating` `valOf` clamping, `three_way_compare::<char>`,
`size_of_val` / `align_of_val` ↔ MiniRust `Type.layout` & `LayoutStrategy.compute_size_and_align`,
symbolic `panicUnwind`, and negative controls -/

/-- **Full value-and-UB two-sided equivalence (`evalLIntrinsic_unchecked_and_exactDiv_value_iff_minirust`)**:
strengthens Section 8a's `.isSome ↔ ∃ res` theorems to exact value-level bi-implications (`= some
(.scalar ⟨outBits, sz⟩) ↔ ...` AND `= none ↔ ∃ msg, ... = .error (.ub msg)`) for both the five
unchecked arithmetic intrinsics (`uncheckedArithLIntrinsicPair`) and `exactDiv`. -/
theorem evalLIntrinsic_unchecked_and_exactDiv_value_iff_minirust
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y outBits : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (∀ op bop iop, DeinitBridge.uncheckedArithLIntrinsicPair op = some (bop, iop) →
      (Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨outBits, it.size.bytes⟩) ↔
        ∃ res, evalBinOp (.Int iop) (.Int (intFromBits x it), .Int it)
            (.Int (intFromBits y it), .Int it) = .ok (.Int res, .Int it) ∧
          outBits = (res % 2 ^ (8 * it.size.bytes)).toNat) ∧
      (Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag = none ↔
        ∃ msg, evalBinOp (.Int iop) (.Int (intFromBits x it), .Int it)
          (.Int (intFromBits y it), .Int it) = .error (.ub msg))) ∧
    ((Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
      some (.scalar ⟨outBits, it.size.bytes⟩) ↔
      ∃ q, evalBinOp (.Int .DivExact) (.Int (intFromBits x it), .Int it)
          (.Int (intFromBits y it), .Int it) = .ok (.Int q, .Int it) ∧
        outBits = (q % 2 ^ (8 * it.size.bytes)).toNat) ∧
     (Anneal.Mir.AdtAndControl.evalLIntrinsicValue .exactDiv (rk :: restTys) decls layouts argOps
        [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag = none ↔
      ∃ msg, evalBinOp (.Int .DivExact) (.Int (intFromBits x it), .Int it)
        (.Int (intFromBits y it), .Int it) = .error (.ub msg))) := by
  refine ⟨fun op bop iop hop => ?_, ?_⟩
  · have h := DeinitBridge.evalLIntrinsic_unchecked_binop_iff_minirust op bop iop hop hrk x y hx hy
      restTys decls layouts argOps flag
    dsimp only at h
    refine ⟨⟨fun hSome => ?_, fun ⟨res, hOk, hOut⟩ => ?_⟩,
            ⟨fun hNone => ?_, fun hub => h.2 hub⟩⟩
    · rcases evalBinOp_int_ok_or_ub iop (intFromBits x it) (intFromBits y it) it (.Int it) with
        ⟨res, hOk⟩ | hub
      · have hEq := (h.1 res hOk).2
        rw [hSome] at hEq
        cases hEq
        exact ⟨res, hOk, rfl⟩
      · rw [h.2 hub] at hSome; nomatch hSome
    · subst hOut; exact (h.1 res hOk).2
    · rcases evalBinOp_int_ok_or_ub iop (intFromBits x it) (intFromBits y it) it (.Int it) with
        ⟨res, hOk⟩ | hub
      · rw [(h.1 res hOk).2] at hNone; nomatch hNone
      · exact hub
  · have h := DeinitBridge.evalLIntrinsic_exactDiv_iff_minirust hrk x y hx hy
      restTys decls layouts argOps flag
    dsimp only at h
    refine ⟨⟨fun hSome => ?_, fun ⟨q, hOk, hOut⟩ => ?_⟩,
            ⟨fun hNone => ?_, fun hub => h.2 hub⟩⟩
    · rcases evalBinOp_int_ok_or_ub .DivExact (intFromBits x it) (intFromBits y it) it (.Int it) with
        ⟨q, hOk⟩ | hub
      · have hEq := (h.1 q hOk).2
        rw [hSome] at hEq
        cases hEq
        exact ⟨q, hOk, rfl⟩
      · rw [h.2 hub] at hSome; nomatch hSome
    · subst hOut; exact (h.1 q hOk).2
    · rcases evalBinOp_int_ok_or_ub .DivExact (intFromBits x it) (intFromBits y it) it (.Int it) with
        ⟨q, hOk⟩ | hub
      · rw [(h.1 q hOk).2] at hNone; nomatch hNone
      · exact hub

/-- Minimum representable mathematical integer of `it : Gen.IntType` (`inBounds` lower bound). -/
def intTypeMinVal (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => 0
  | .Signed => -((2 : Int) ^ (8 * it.size.bytes - 1))

/-- Maximum representable mathematical integer of `it : Gen.IntType` (`inBounds` upper bound). -/
def intTypeMaxVal (it : Gen.IntType) : Int :=
  match it.signed with
  | .Unsigned => (2 : Int) ^ (8 * it.size.bytes) - 1
  | .Signed => (2 : Int) ^ (8 * it.size.bytes - 1) - 1

/-- **Bit-level `valOf` clamping link for `saturatingAdd` / `saturatingSub`
(`evalLIntrinsic_saturating_valOf_minirust`)**: across every integer `RigidTy` `rk` and valid bit
patterns `x, y`, the scalar `bits` returned by `evalLIntrinsicValue` is `ValidBits (.Int it) bits`
and decodes under MiniRust's `valOf (.Int it) bits` to the exact clamped mathematical result
`max (intTypeMinVal it) (min (intTypeMaxVal it) (intCheckedArith cop l r))`. -/
theorem evalLIntrinsic_saturating_valOf_minirust
    (isSub : Bool)
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (x y : Nat) (hx : x < 2 ^ (8 * it.size.bytes)) (hy : y < 2 ^ (8 * it.size.bytes))
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let op : Anneal.Mir.AdtAndControl.LIntrinsicOp :=
      if isSub then .saturatingSub else .saturatingAdd
    let cop : Gen.IntBinOpWithOverflow := if isSub then .Sub else .Add
    let l := intFromBits x it
    let r := intFromBits y it
    let raw := intCheckedArith cop l r
    ∃ bits,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue op (rk :: restTys) decls layouts argOps
          [.scalar ⟨x, it.size.bytes⟩, .scalar ⟨y, it.size.bytes⟩] flag =
        some (.scalar ⟨bits, it.size.bytes⟩) ∧
      ValidBits (.Int it) bits ∧
      valOf (.Int it) bits = .Int (max (intTypeMinVal it) (min (intTypeMaxVal it) raw)) := by
  dsimp only
  obtain ⟨hgood, _, _⟩ := DeinitBridge.intTyBytes_intrinsic_props hrk false decls layouts
  refine ⟨if IntType.can_represent it
      (intCheckedArith (if isSub then .Sub else .Add) (intFromBits x it) (intFromBits y it)) then
      (intCheckedArith (if isSub then .Sub else .Add) (intFromBits x it) (intFromBits y it) %
        2 ^ (8 * it.size.bytes)).toNat
    else match it.signed with
      | .Unsigned => if isSub then 0 else 2 ^ (8 * it.size.bytes) - 1
      | .Signed =>
        if intFromBits x it < 0 then 2 ^ (8 * it.size.bytes - 1)
        else 2 ^ (8 * it.size.bytes - 1) - 1,
    (DeinitBridge.evalLIntrinsic_saturating_eq_minirust isSub hrk x y hx hy
      restTys decls layouts argOps flag).2, ?_, ?_⟩
  · -- `ValidBits (.Int it) clampedBits`
    have hsz : it.size.bytes ≠ 0 := Nat.ne_of_gt hgood.pos
    have hMpos : (0 : Int) < (2 : Int) ^ (8 * it.size.bytes) := two_pow_pos (8 * it.size.bytes)
    have hp : (2 : Int) ^ (8 * it.size.bytes) = ((2 ^ (8 * it.size.bytes) : Nat) : Int) := by
      push_cast; rfl
    have hHalfLt : 2 ^ (8 * it.size.bytes - 1) < 2 ^ (8 * it.size.bytes) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hPowPos : 0 < 2 ^ (8 * it.size.bytes) := Nat.pow_pos (by decide)
    cases hRep : IntType.can_represent it
        (intCheckedArith (if isSub then .Sub else .Add) (intFromBits x it) (intFromBits y it))
    · simp only [ValidBits, Bool.false_eq_true, ↓reduceIte]
      cases it.signed <;> dsimp only <;> (split <;> omega)
    · simp only [ValidBits, ↓reduceIte]
      have hModNonneg : 0 ≤ intCheckedArith (if isSub then .Sub else .Add)
          (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes) :=
        Int.emod_nonneg _ (by omega)
      have hModLt : intCheckedArith (if isSub then .Sub else .Add)
          (intFromBits x it) (intFromBits y it) % (2 : Int) ^ (8 * it.size.bytes) <
          (2 : Int) ^ (8 * it.size.bytes) :=
        Int.emod_lt_of_pos _ hMpos
      rw [hp] at hModNonneg hModLt
      omega
  · -- `valOf (.Int it) clampedBits = .Int (max minVal (min maxVal raw))`
    rcases it with ⟨s, ⟨sz⟩⟩
    dsimp only [valOf, intTypeMinVal, intTypeMaxVal] at hgood hx hy ⊢
    congr 1
    have hBitsPos : 0 < 8 * sz := Nat.mul_pos (by decide) hgood.pos
    have hHalfPos : 0 < 2 ^ (8 * sz - 1) := Nat.pow_pos (by decide)
    have hTwoHalfNat : 2 ^ (8 * sz) = 2 * 2 ^ (8 * sz - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, 8 * sz = m + 1 := ⟨8 * sz - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hp : (2 : Int) ^ (8 * sz) = ((2 ^ (8 * sz) : Nat) : Int) := by push_cast; rfl
    have hpH : (2 : Int) ^ (8 * sz - 1) = ((2 ^ (8 * sz - 1) : Nat) : Int) := by push_cast; rfl
    cases s with
    | Unsigned =>
      dsimp only [intFromBits] at hx hy ⊢
      cases isSub
      · simp only [Bool.false_eq_true, ↓reduceIte, intCheckedArith]
        by_cases hFit : (x : Int) + (y : Int) < (2 : Int) ^ (8 * sz)
        · have hRep : IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ ((x : Int) + (y : Int)) = true := by
            simp only [IntType.can_represent, Interp.inBounds, Interp.Size.bits, Bool.and_eq_true]
            exact ⟨decide_eq_true (by omega), decide_eq_true hFit⟩
          simp only [hRep, ↓reduceIte]
          have hMod : ((x : Int) + (y : Int)) % (2 : Int) ^ (8 * sz) = (x : Int) + (y : Int) :=
            Int.emod_eq_of_lt (by omega) hFit
          rw [hMod]
          rw [hp] at hFit ⊢
          omega
        · have hRep : IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ ((x : Int) + (y : Int)) = false := by
            simp only [IntType.can_represent, Interp.inBounds, Interp.Size.bits,
              Bool.and_eq_false_iff]
            exact Or.inr (decide_eq_false hFit)
          simp only [hRep, Bool.false_eq_true, ↓reduceIte]
          rw [hp] at hFit ⊢
          omega
      · simp only [↓reduceIte, intCheckedArith]
        by_cases hFit : 0 ≤ (x : Int) - (y : Int)
        · have hLt : (x : Int) - (y : Int) < (2 : Int) ^ (8 * sz) := by rw [hp]; omega
          have hRep : IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ ((x : Int) - (y : Int)) = true := by
            simp only [IntType.can_represent, Interp.inBounds, Interp.Size.bits, Bool.and_eq_true]
            exact ⟨decide_eq_true hFit, decide_eq_true hLt⟩
          simp only [hRep, ↓reduceIte]
          have hMod : ((x : Int) - (y : Int)) % (2 : Int) ^ (8 * sz) = (x : Int) - (y : Int) :=
            Int.emod_eq_of_lt hFit hLt
          rw [hMod]
          rw [hp] at hLt ⊢
          omega
        · have hRep : IntType.can_represent ⟨.Unsigned, ⟨sz⟩⟩ ((x : Int) - (y : Int)) = false := by
            simp only [IntType.can_represent, Interp.inBounds, Interp.Size.bits,
              Bool.and_eq_false_iff]
            exact Or.inl (decide_eq_false hFit)
          simp only [hRep, Bool.false_eq_true, ↓reduceIte]
          rw [hp]
          omega
    | Signed =>
      dsimp only
      have hlBounds : -((2 ^ (8 * sz - 1) : Nat) : Int) ≤ intFromBits x ⟨.Signed, ⟨sz⟩⟩ ∧
          intFromBits x ⟨.Signed, ⟨sz⟩⟩ < ((2 ^ (8 * sz - 1) : Nat) : Int) := by
        dsimp only [intFromBits]
        rw [hp]
        split <;> omega
      have hrBounds : -((2 ^ (8 * sz - 1) : Nat) : Int) ≤ intFromBits y ⟨.Signed, ⟨sz⟩⟩ ∧
          intFromBits y ⟨.Signed, ⟨sz⟩⟩ < ((2 ^ (8 * sz - 1) : Nat) : Int) := by
        dsimp only [intFromBits]
        rw [hp]
        split <;> omega
      generalize hl : intFromBits x ⟨.Signed, ⟨sz⟩⟩ = l at hlBounds ⊢
      generalize hr : intFromBits y ⟨.Signed, ⟨sz⟩⟩ = r at hrBounds ⊢
      have hSignMatch :
          (l < 0 → intCheckedArith (if isSub then .Sub else .Add) l r <
            ((2 ^ (8 * sz - 1) : Nat) : Int)) ∧
          (¬(l < 0) → -((2 ^ (8 * sz - 1) : Nat) : Int) ≤
            intCheckedArith (if isSub then .Sub else .Add) l r) := by
        cases isSub
        · simp only [Bool.false_eq_true, ↓reduceIte, intCheckedArith]
          exact ⟨by omega, by omega⟩
        · simp only [↓reduceIte, intCheckedArith]
          exact ⟨by omega, by omega⟩
      generalize hz : intCheckedArith (if isSub then .Sub else .Add) l r = z at hSignMatch ⊢
      have hCanRepIff : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩ z = true ↔
          -((2 ^ (8 * sz - 1) : Nat) : Int) ≤ z ∧ z < ((2 ^ (8 * sz - 1) : Nat) : Int) := by
        change inBounds z .Signed ⟨sz⟩ = true ↔ _
        rw [inBounds_iff z .Signed ⟨sz⟩ hBitsPos]
        dsimp only [windowLo, Interp.Size.bits]
        have hAdd := two_pow_pred_add (8 * sz) hBitsPos
        rw [hp, hpH] at hAdd ⊢
        omega
      cases hRep : IntType.can_represent ⟨.Signed, ⟨sz⟩⟩ z
      · have hNotBounds :
            ¬(-((2 ^ (8 * sz - 1) : Nat) : Int) ≤ z ∧ z < ((2 ^ (8 * sz - 1) : Nat) : Int)) := by
          intro hb
          have hTrue := hCanRepIff.mpr hb
          rw [hRep] at hTrue
          nomatch hTrue
        simp only [Bool.false_eq_true, ↓reduceIte, hpH]
        by_cases hlNeg : l < 0
        · have hzUpper := hSignMatch.1 hlNeg
          have hNotLt : ¬(2 ^ (8 * sz - 1) < 2 ^ (8 * sz - 1)) := Nat.lt_irrefl _
          simp only [hlNeg, ↓reduceIte, intFromBits, hNotLt, hp]
          omega
        · have hzLower := hSignMatch.2 hlNeg
          have hLtSelf : 2 ^ (8 * sz - 1) - 1 < 2 ^ (8 * sz - 1) := by omega
          simp only [hlNeg, ↓reduceIte, intFromBits, hLtSelf]
          omega
      · have hzBounds :
            -((2 ^ (8 * sz - 1) : Nat) : Int) ≤ z ∧ z < ((2 ^ (8 * sz - 1) : Nat) : Int) :=
          hCanRepIff.mp hRep
        simp only [↓reduceIte, hp, hpH]
        have hMaxMin :
            max (-((2 ^ (8 * sz - 1) : Nat) : Int))
              (min (((2 ^ (8 * sz - 1) : Nat) : Int) - 1) z) = z := by omega
        rw [hMaxMin]
        dsimp only [intFromBits]
        rw [hp]
        by_cases hz0 : 0 ≤ z
        · have hMod : z % ((2 ^ (8 * sz) : Nat) : Int) = z :=
            Int.emod_eq_of_lt hz0 (by omega)
          rw [hMod]
          have hToNatLt : z.toNat < 2 ^ (8 * sz - 1) := by omega
          simp only [hToNatLt, ↓reduceIte]
          omega
        · have hzPlusNonneg : 0 ≤ z + 1 * ((2 ^ (8 * sz) : Nat) : Int) := by omega
          have hzPlusLt : z + 1 * ((2 ^ (8 * sz) : Nat) : Int) < ((2 ^ (8 * sz) : Nat) : Int) := by
            omega
          have hMod : z % ((2 ^ (8 * sz) : Nat) : Int) = z + ((2 ^ (8 * sz) : Nat) : Int) := by
            have h1 := Int.emod_eq_of_lt hzPlusNonneg hzPlusLt
            rw [Int.add_mul_emod_self_right] at h1
            simpa using h1
          rw [hMod]
          have hNotLt : ¬((z + ((2 ^ (8 * sz) : Nat) : Int)).toNat < 2 ^ (8 * sz - 1)) := by omega
          simp only [hNotLt, ↓reduceIte]
          omega

/-- **`threeWayCompare` on `RigidTy.char` (`evalLIntrinsic_threeWayCompare_char_minirust`)**:
bridges `LIntrinsicOp.threeWayCompare` on `char` (whose `intTyBytes .char = none` excluded it from
Section 8b!) across all 32-bit scalar values `x, y < 2 ^ 32` to MiniRust's unsigned `u32` scalar
`RelOp::Cmp` + `Transmute orderingTy`. -/
theorem evalLIntrinsic_threeWayCompare_char_minirust
    (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    ∃ bits,
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare (.char :: restTys) decls layouts
          argOps [.scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩] flag =
        some (.scalar ⟨bits, 1⟩) ∧
      ValidBits orderingTy bits ∧
      (evalBinOp (.Rel .Cmp) (.Int (x : Int), .Int u32) (.Int (y : Int), .Int u32)
          >>= evalUnOp (.Cast (.Transmute orderingTy))) =
        .ok (valOf orderingTy bits, orderingTy) := by
  have hU32 := evalLIntrinsic_threeWayCompare_ordering_tag (rk := .uint .u32) (it := u32) rfl
    x y hx hy restTys decls layouts argOps flag
  obtain ⟨bits, hValU32, hVB, hMR⟩ := hU32
  dsimp only [intFromBits, u32] at hValU32 hMR
  have hSame :
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare (.char :: restTys) decls layouts
        argOps [.scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩] flag =
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare (.uint .u32 :: restTys) decls
        layouts argOps [.scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩] flag := rfl
  rw [← hSame] at hValU32
  exact ⟨bits, hValU32, hVB, hMR⟩

/-- **`sizeOfVal` & `alignOfVal` ↔ MiniRust `Type.layout` & `LayoutStrategy.compute_size_and_align`
(`evalLIntrinsic_sizeOfVal_alignOfVal_minirust_layout`)**: across every integer `RigidTy` `rk`
(`intTyBytes rk = some (it.signed, it.size.bytes)`):
1. **Thin pointer to sized `rk` (`&T` / `*const T`)**: MiniRust's `Type.layout (.Int it) >>=
   LayoutStrategy.compute_size_and_align ... none` returns `(it.size, ⟨it.size.bytes⟩)`, and
   Anneal's `evalLIntrinsicValue` returns `some (.scalar ⟨it.size.bytes, 8⟩)` for both `.sizeOfVal`
   and `.alignOfVal`;
2. **Wide pointer to unsized slice `.slice rk` (`&[T]` / `*const [T]`, metadata `len < 2 ^ 64`)**:
   MiniRust's `Type.layout (.Slice (.Int it)) >>= LayoutStrategy.compute_size_and_align ...
   (some (.ElementCount len))` returns `(⟨len * it.size.bytes⟩, ⟨it.size.bytes⟩)`, and Anneal's
   `.sizeOfVal` / `.alignOfVal` return those exact 8-byte `usize` scalars iff `len * it.size.bytes <
   2 ^ 63` (Rust's `isize::MAX` raw slice-size UB bound), faulting with `none` otherwise. -/
theorem evalLIntrinsic_sizeOfVal_alignOfVal_minirust_layout
    {rk : RigidTy} {it : Gen.IntType} (hrk : intTyBytes rk = some (it.signed, it.size.bytes))
    (vtables : Interp.Ptr → Interp Gen.VTable)
    (p : ProvenancePtr) (len : Nat) (hlen : len < 2 ^ 64)
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    let n := it.size.bytes
    ((Interp.Type.layout (.Int it) >>= fun ls =>
        Interp.LayoutStrategy.compute_size_and_align vtables ls none) =
        .ok (it.size, ⟨n⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .sizeOfVal (rk :: restTys) decls layouts argOps
        [.ptr p 8] flag = some (.scalar ⟨n, 8⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .alignOfVal (rk :: restTys) decls layouts argOps
        [.ptr p 8] flag = some (.scalar ⟨n, 8⟩)) ∧
    ((Interp.Type.layout (.Slice (.Int it)) >>= fun ls =>
        Interp.LayoutStrategy.compute_size_and_align vtables ls (some (.ElementCount (len : Int)))) =
        .ok (⟨len * n⟩, ⟨n⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .sizeOfVal (.slice rk :: restTys) decls layouts
        argOps [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] flag =
        (if len * n < 2 ^ 63 then some (.scalar ⟨len * n, 8⟩) else none) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .alignOfVal (.slice rk :: restTys) decls layouts
        argOps [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] flag =
        (if len * n < 2 ^ 63 then some (.scalar ⟨n, 8⟩) else none)) := by
  dsimp only
  have hLenWrap : wrapScalarBits len (scalarModulus 8) = len := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hlen]
  have hProps :
      (Interp.IntType.align it = .ok ⟨it.size.bytes⟩) ∧
      intrinsicRigidTyByteSize decls layouts rk = some it.size.bytes ∧
      intrinsicRigidTyAlign decls layouts rk = some it.size.bytes := by
    rcases it with ⟨s, ⟨sz⟩⟩
    cases rk with
    | uint u => cases u <;> cases hrk <;> exact ⟨rfl, rfl, rfl⟩
    | int i => cases i <;> cases hrk <;> exact ⟨rfl, rfl, rfl⟩
    | _ => simp [intTyBytes] at hrk
  obtain ⟨hMrAlign, hSzRk, hAlRk⟩ := hProps
  have hHalf8 : signedHalfModulus 8 = 2 ^ 63 := by decide
  have hSlice : evalSliceSizeOfVal it.size.bytes ⟨len, 8⟩ =
      if len * it.size.bytes < 2 ^ 63 then some ⟨len * it.size.bytes, 8⟩ else none := by
    unfold evalSliceSizeOfVal
    dsimp only
    change (match Nat.ble (signedHalfModulus 8)
        (it.size.bytes * wrapScalarBits len (scalarModulus 8)) with
      | true => (none : Option ScalarInt)
      | false => some (ScalarInt.mk (it.size.bytes * wrapScalarBits len (scalarModulus 8)) 8)) = _
    rw [hLenWrap, Nat.mul_comm it.size.bytes len, hHalf8, nat_ble_eq_decide]
    by_cases hlt : len * it.size.bytes < 2 ^ 63
    · rw [decide_eq_false (by omega : ¬(2 ^ 63 ≤ len * it.size.bytes))]
      simp only [hlt, ↓reduceIte]
    · rw [decide_eq_true (by omega : 2 ^ 63 ≤ len * it.size.bytes)]
      simp only [hlt, ↓reduceIte]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rcases it with ⟨s, ⟨sz⟩⟩
    dsimp only at hMrAlign ⊢
    simp [Interp.Type.layout, hMrAlign, Interp.LayoutStrategy.compute_size_and_align,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rcases it with ⟨s, ⟨sz⟩⟩
    cases rk with
    | uint u => cases u <;> cases hrk <;> rfl
    | int i => cases i <;> cases hrk <;> rfl
    | _ => simp [intTyBytes] at hrk
  · rcases it with ⟨s, ⟨sz⟩⟩
    cases rk with
    | uint u => cases u <;> cases hrk <;> rfl
    | int i => cases i <;> cases hrk <;> rfl
    | _ => simp [intTyBytes] at hrk
  · rcases it with ⟨s, ⟨sz⟩⟩
    dsimp only at hMrAlign ⊢
    have hNonneg : (0 : Int) ≤ (len : Int) * (sz : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hCast : ((len : Int) * (sz : Int)).toNat = len * sz := by
      have : (len : Int) * (sz : Int) = ((len * sz : Nat) : Int) := by push_cast; rfl
      rw [this, Int.toNat_natCast]
    simp [Interp.Type.layout, hMrAlign, Interp.LayoutStrategy.expect_size,
      Interp.LayoutStrategy.expect_align, Interp.LayoutStrategy.compute_size_and_align,
      Bind.bind, Except.bind, Pure.pure, Except.pure, hNonneg, hCast]
  · change (match intrinsicRigidTyByteSize decls layouts rk with
      | some elemSz => Option.map Value.scalar (evalSliceSizeOfVal elemSz ⟨len, 8⟩)
      | none => none) = _
    rw [hSzRk]
    dsimp only
    rw [hSlice]
    by_cases hlt : len * it.size.bytes < 2 ^ 63 <;> simp [hlt]
  · change (match intrinsicRigidTyByteSize decls layouts rk,
        intrinsicRigidTyAlign decls layouts rk with
      | some elemSz, some alignBytes =>
        match evalSliceSizeOfVal elemSz ⟨len, 8⟩ with
        | some _ => some (Value.scalar ⟨alignBytes, 8⟩)
        | none => none
      | _, _ => none) = _
    rw [hSzRk, hAlRk]
    dsimp only
    rw [hSlice]
    by_cases hlt : len * it.size.bytes < 2 ^ 63 <;> simp [hlt]

/-- **Symbolic `panicUnwind` dispatch & contrast with `abort`
(`evalLIntrinsic_panicUnwind_minirust_correspondence`)**: completes Section 8c's diverging triad
(`abort`, `unreachableUnchecked`, `panicUnwind`) across every `evalLoweredIntrinsicCall` input:
- `panicUnwind` rejects any present return `target = some t` (`none`);
- with `target = none`, `panicUnwind` delegates to `startPanic` (entering cleanup block `c` on
  `unwind = .cleanup c`, whereas Section 8c's `.abort` bypasses `c` and returns `some (.terminated
  bb)`!);
- canonical `V2026_06_01` unwinding panic entry points (`core::panicking::panic`, `panic_fmt`,
  `assert_failed`) lower to `.panicUnwind`.
The statement itself mentions no MiniRust term: MiniRust's executable spec has no unwinding, and
`minirust_unwind_terminators_unsupported` (Section 10) pins that fail-closed boundary, so the
semantic counterpart of `panicUnwind` is `Trusted`'s `startPanic` / `applyUnwindAction` only. -/
theorem evalLIntrinsic_panicUnwind_minirust_correspondence
    (env : Anneal.Mir.AdtAndControl.CfgEnv) (body : Anneal.Mir.AdtAndControl.LBody)
    (bb : Nat) (inCleanup : Bool) (args : List Operand) (avs : List Value)
    (slots2 : List Anneal.Mir.PlaceAndRvalue.LocalSlotState) (dest : Place) (destTy : Ty)
    (unwind : UnwindAction) (unwinding : Option Nat) (typeArgs : List RigidTy) :
    Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup args avs slots2 dest
        destTy none unwind unwinding .panicUnwind typeArgs =
      Anneal.Mir.AdtAndControl.startPanic body bb unwind slots2 unwinding ∧
    (∀ t, Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup args avs slots2
        dest destTy (some t) unwind unwinding .panicUnwind typeArgs = none) ∧
    Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::panicking::panic" =
      some .panicUnwind ∧
    Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::panicking::panic_fmt" =
      some .panicUnwind ∧
    Anneal.Mir.AdtAndControl.lowerIntrinsicKind_V2026_06_01 "core::panicking::assert_failed" =
      some .panicUnwind := by
  refine ⟨rfl, fun _ => ?_, by decide, by decide, by decide⟩
  simp only [Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall]

/-- **Extended negative controls (`minirust_bitops_char_and_layout_negative_controls`)**:
1. Multi-byte `bswap` (`0x1234_u16 -> 0x3412_u16`, matching `Endianness.decode .BigEndian`) vs
   `bitreverse` (`0x1234_u16 -> 0x2C48_u16`) vs `u8` where `bswap` is identity (`0x12_u8 -> 0x12_u8`)
   while `bitreverse` is `0x48_u8`;
2. `three_way_compare::<char>('\u{0080}', '\u{0001}')` produces `Greater` (`1`), whereas `i8` on the
   same low byte `0x80` (`-128`) produces `Less` (`255`);
3. Wide-pointer `size_of_val::<[u32]>` at `len = 2^61 - 1` succeeds (`some (2^63 - 4)`), whereas at
   `len = 2^61` (`4 * 2^61 = 2^63 > isize::MAX`) Anneal faults (`none`) even though MiniRust's
   `LayoutStrategy.compute_size_and_align` computes `Size::from_bytes(2^63)`. -/
theorem minirust_bitops_char_and_layout_negative_controls
    (vtables : Interp.Ptr → Interp Gen.VTable) :
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bswap [.uint .u16] [] emptyLayoutTable []
        [.scalar ⟨0x1234, 2⟩] true = some (.scalar ⟨0x3412, 2⟩) ∧
      Interp.Endianness.decode .BigEndian .Unsigned (Interp.leBytes 0x1234 2) = 0x3412 ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse [.uint .u16] [] emptyLayoutTable []
        [.scalar ⟨0x1234, 2⟩] true = some (.scalar ⟨0x2C48, 2⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bswap [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨0x12, 1⟩] true = some (.scalar ⟨0x12, 1⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .bitreverse [.uint .u8] [] emptyLayoutTable []
        [.scalar ⟨0x12, 1⟩] true = some (.scalar ⟨0x48, 1⟩)) ∧
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare [.char] [] emptyLayoutTable []
        [.scalar ⟨0x80, 4⟩, .scalar ⟨1, 4⟩] true = some (.scalar ⟨1, 1⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .threeWayCompare [.int .i8] [] emptyLayoutTable []
        [.scalar ⟨0x80, 1⟩, .scalar ⟨1, 1⟩] true = some (.scalar ⟨255, 1⟩)) ∧
    (Anneal.Mir.AdtAndControl.evalLIntrinsicValue .sizeOfVal [.slice (.uint .u32)] []
        emptyLayoutTable [] [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2 ^ 61 - 1, 8⟩]] true =
        some (.scalar ⟨2 ^ 63 - 4, 8⟩) ∧
      Anneal.Mir.AdtAndControl.evalLIntrinsicValue .sizeOfVal [.slice (.uint .u32)] []
        emptyLayoutTable [] [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2 ^ 61, 8⟩]] true = none ∧
      (Interp.Type.layout (.Slice (.Int u32)) >>= fun ls =>
        Interp.LayoutStrategy.compute_size_and_align vtables ls
          (some (.ElementCount ((2 ^ 61 : Nat) : Int)))) = .ok (⟨2 ^ 63⟩, ⟨4⟩)) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

end AdvEp2A3

/-! ## 10. `[adv ep2-B4]` MiniRust unwinding boundary -/

section AdvEp2B4

set_option autoImplicit false

/-- **MiniRust's executable spec has no unwinding (`minirust_unwind_terminators_unsupported`)**:
`Interp.evalTerminator` stops with `.unsupported` on every `StartUnwind`, `StopUnwind`, and
`ResumeUnwind` terminator, for every machine, payload, and target block. Anneal's lowered
`panicUnwind` (routed to `startPanic` by `evalLIntrinsic_panicUnwind_minirust_correspondence`)
and its cleanup / `UnwindResume` / `unwindLCallStack` machinery therefore have no executable
MiniRust counterpart; their correspondence is with `Trusted`'s `startPanic` /
`applyUnwindAction` / `unwindFromCallStack` only, while `abort` (`IntrinsicOp::Abort`) and
`unreachable_unchecked` (`Terminator::Unreachable`) do have MiniRust counterparts (Section 8c). -/
theorem minirust_unwind_terminators_unsupported (m : Mach) (payload : Gen.ValueExpr)
    (blk : Gen.BbName) :
    (∃ what, Interp.evalTerminator m (.StartUnwind payload blk) = .error (.unsupported what)) ∧
      (∃ what, Interp.evalTerminator m (.StopUnwind blk) = .error (.unsupported what)) ∧
      (∃ what, Interp.evalTerminator m .ResumeUnwind = .error (.unsupported what)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end AdvEp2B4

end MiniRustSpec.Correspondence
