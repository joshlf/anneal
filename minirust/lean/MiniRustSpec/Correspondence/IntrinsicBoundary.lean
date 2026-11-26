/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
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
   `minimize` aborts translation. Even with `count = 0` Anneal rejects non-pointer
   `src` and `dst` operands with `.ub` (`bdCopyZeroScalars_ub`), `count = 1` copies
   between the two 4-byte `u32` locals (`bdCopy1_anneal_ret`), and an
   out-of-bounds `count = 2` (`8` bytes across 4-byte locals) faults with UB
   (`bdCopy2_anneal_ub`, `bdCopy2_not_noUB`).
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
   * The call form of `write_bytes` is modeled in `evalDirectRustIntrinsic?`
     (`evalWriteBytesCall`) and fails closed on an untracked destination
     pointer (`bdWriteBytes_untracked_unsupported`).
   * Unmodeled intrinsics (`cold_path`; `raw_eq` is modeled inline, `bdRawEq_inline_ub`) emit external
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
and multi-byte / `char` / slice-layout negative controls). Section 10 (`[adv ep2-B4]` /
`[adv ep2-A4]`) pins the remaining boundaries and closes all 30 `LIntrinsicOp` variants: MiniRust's
executable spec runs every unwinding terminator (`StartUnwind`, `StopUnwind`,
`ResumeUnwind`) and `Statement::SetDiscriminant` across both `Mach` and
`MachTB`, so `panicUnwind` has no single `IntrinsicOp` counterpart (MiniRust
models unwinding with those terminators, and no simulation between them and
`startPanic` is proved here),
`RigidTy.str` wide pointers (`&str` / `*const str`) match `Type.layout (.Slice
(.Int u8))`, missing `nextBlock = none` / `target = none` raises UB on value-returning intrinsics in
both semantics, and `lintrinsicOp_exhaustive_minirust_classification` partitions all 30
`LIntrinsicOp` constructors across their four verified correspondence regimes.
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

local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

private theorem runA_isSome_noUB (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : (runA body fuel s).isSome = true) : MirNoUBTree (mirTree body s) := by
  cases hr : runA body fuel s with
  | none => rw [hr] at h; cases h
  | some p => exact runA_noUB body fuel s p.1 p.2 hr

private theorem runA_exists_mem_sound (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (tr : List (Event MirEffect)) (v : Value)
    (h : (runA body fuel s).map (fun (tr', o) =>
      match o with
      | .normal (v', _) => some (tr', v')
      | _ => none) = some (some (tr, v))) :
    ∃ mem, ReachesRet (mirTree body s) tr (.normal (v, mem)) := by
  cases hr : runA body fuel s with
  | none => rw [hr] at h; cases h
  | some p =>
    rcases p with ⟨tr', o⟩
    cases o with
    | normal vm =>
      rcases vm with ⟨v', mem⟩
      rw [hr] at h
      injection h with h1
      injection h1 with h2
      injection h2 with htr hv
      cases htr; cases hv
      exact ⟨mem, runA_sound body fuel s _ _ hr⟩
    | _ => rw [hr] at h; cases h

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
Anneal: `evalRvalue` evaluates `Rvalue.nullaryOp .ubChecks` at type `bool`
through `evalNullaryOp` (`Places.lean`) to `true`, Anneal's UB-checking
operational mode (the same flag that a call to `core::intrinsics::ub_checks`
returns, `bdUbChecksCall_anneal_ret`), so the body returns `true`
(`bdUbChecks_anneal_ret`); `NullOp.contractChecks` stays unsupported
(`bdNullaryOp_ubChecks_contractChecks`).

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

/-- In every state, Anneal evaluates the runtime UB-check flag `NullOp.ubChecks` at `bool` to
`true` (`1 : u8`) without touching the frame or memory, and rejects `NullOp.contractChecks` as
unsupported. -/
theorem bdNullaryOp_ubChecks_contractChecks (locals : List LocalSlot) (idx : LayoutIdx)
    (ty : Ty) (mem : Memory) (decls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.nullaryOp .ubChecks ⟨.bool, idx⟩) mem decls layouts =
        .ok (.scalar ⟨1, 1⟩) locals mem ∧
      evalRvalue locals (.nullaryOp .contractChecks ty) mem decls layouts = .unsupported :=
  ⟨rfl, rfl⟩

/-- Anneal runs `bdUbChecksBody` to completion, returning `true`. -/
theorem bdUbChecks_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdUbChecksBody []) [] (.normal (.scalar ⟨1, 1⟩, mem)) :=
  runA_exists_mem_sound bdUbChecksBody 10 _ _ _ (by kernel_rfl)

theorem bdNullaryOp_translateRvalue (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (targetTy : Option Ty) (op : NullOp) (ty : Ty) :
    translateRvalue layouts decls targetTy (.nullaryOp op ty) = none := rfl

theorem bdUbChecks_rejected :
    statementOk [boolDecl] (mkStmt (.assign (local_ 0) (.nullaryOp .ubChecks boolTy))) = false ∧
      inFragment bdUbChecksBody = false :=
  ⟨rfl, by decide +kernel⟩

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
  runA_exists_mem_sound (bdCopyBody 0) 30 _ _ _ (by kernel_rfl)

/-- `count = 1`: the argument `7` is copied into `_0` and returned. -/
theorem bdCopy1_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree (bdCopyBody 1) [.scalar ⟨7, 4⟩]) []
      (.normal (.scalar ⟨7, 4⟩, mem)) :=
  runA_exists_mem_sound (bdCopyBody 1) 30 _ _ _ (by kernel_rfl)

/-- `count = 2`: the copy requests `2 * size_of::<u32>() = 8` bytes, exceeding
the 4-byte bounds of `_1` and `_0`; post-Episode-1 `copyBytesSubplace` enforces
exact sub-place window bounds and faults with UB. -/
theorem bdCopy2_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree (bdCopyBody 2) [.scalar ⟨7, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound (bdCopyBody 2) 30 _ (by kernel_rfl)

/-- `bdCopyBody 2` is not UB-free in Anneal. -/
theorem bdCopy2_not_noUB : ¬ MirNoUBTree (mirCallTree (bdCopyBody 2) [.scalar ⟨7, 4⟩]) := by
  obtain ⟨tr, u, hr, hf⟩ := bdCopy2_anneal_ub
  exact fun hsafe => hsafe tr u hr hf

/-- A `copy_nonoverlapping` with `count = 0` and two non-pointer operands. -/
def bdCopyZeroScalars : MirAst.Statement :=
  mkStmt (.intrinsic (.copyNonOverlapping (constU32 0) (constU32 0) (bdConstUsize 0)))

/-- Even with `count = 0`, Anneal rejects the statement with `.ub` in every state:
neither `src` nor `dst` is statically a pointer (both are `u32` constants), so the
`copy_nonoverlapping` operands are ill-typed (`resolveCopyElemLayout = .ub`), and a
malformed `count` (wrong width for the target) is `.ub` as well (stated on the
64-bit `emptyLayoutTable`, where the `usize` count is well formed). -/
theorem bdCopyZeroScalars_ub (s : MachineState) (decls : List LocalDecl) :
    evalStmt s bdCopyZeroScalars decls emptyLayoutTable = MirStepNode.fail .ub :=
  rfl

theorem bdCopy_translateStatement (decls : List LocalDecl) (src dst count : Operand) :
    translateStatement decls (mkStmt (.intrinsic (.copyNonOverlapping src dst count))) = none ∧
      statementOk decls (mkStmt (.intrinsic (.copyNonOverlapping src dst count))) = false :=
  ⟨rfl, rfl⟩

/-- The fragment also has no type for the raw-pointer locals. -/
theorem bdCopy_rejected :
    scalarTypeOf bdRawConstU32Ty = none ∧ inFragment (bdCopyBody 1) = false :=
  ⟨rfl, by decide +kernel⟩

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
  runA_exists_mem_sound (bdOffsetBody 1) 30 _ _ _ (by kernel_rfl)

/-- `k = -1` (bits `2^64 - 1`): moving `-4` bytes before the start of `_1`
faults with UB in Anneal, matching MiniRust's `InBounds::Yes` `ptr_offset`. -/
theorem bdOffsetNeg1_anneal_ub :
    ∃ tr u,
      Reaches (mirCallTree (bdOffsetBody 18446744073709551615) [.scalar ⟨7, 4⟩]) tr u ∧
      FaultNow u :=
  faultsA_sound (bdOffsetBody 18446744073709551615) 30 _ (by kernel_rfl)

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
  ⟨rfl, rfl, by decide +kernel⟩

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
  runA_exists_mem_sound bdArithOffsetCaller 10 _ _ _ (by kernel_rfl)

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

/-- Anneal evaluates the call form of `write_bytes` inline (`evalWriteBytesCall`): the
destination pointer of `bdWriteBytesArgs` carries no Tree Borrows entry in the initial state, so
its target place (and hence its alignment and validity) is unknown and the call fails closed with
`MirStepNode.unsupported`, never reaching `minimize`'s `span_bug!`. -/
theorem bdWriteBytes_untracked_unsupported :
    stepMirFn bdWriteBytesCaller (initMachineState bdWriteBytesCaller bdWriteBytesArgs) =
      MirStepNode.unsupported :=
  rfl

/-- Anneal: unmodeled intrinsics with a return target and no body in
`Memory.callees` (`cold_path`) emit `MirStepNode.extCall` with `typeArgs` preserved,
whereas `ctpop` and `exact_div` evaluate inline via `evalDirectRustIntrinsic?` and `abort` returns
`MirOutcome.abort`. Since Episode 1 of `ws-tcb-core-mem-and-ptr-intrinsics`, `raw_eq` is also
evaluated inline (`evalRawEqCall`); on the dangling, unbacked argument pointers `bdRawEqArgs`
(allocations `1` and `2` do not exist) it is undefined behavior (`bdRawEq_inline_ub`). -/

theorem bdRawEq_inline_ub :
    stepMirFn bdRawEqCaller (initMachineState bdRawEqCaller bdRawEqArgs) = MirStepNode.fail .ub :=
  rfl

theorem bdColdPath_extCall :
    ∃ k, stepMirFn bdColdPathCaller (initMachineState bdColdPathCaller []) =
      MirStepNode.extCall
        { defPath := "core::intrinsics::cold_path", typeArgs := [], args := [],
          memory := (initMachineState bdColdPathCaller []).memory } k :=
  ⟨_, rfl⟩

theorem bdCtpop_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdCtpopCaller bdCtpopArgs) []
      (.normal (.scalar ⟨4, 4⟩, mem)) :=
  runA_exists_mem_sound bdCtpopCaller 10 _ _ _ (by kernel_rfl)

theorem bdExactDivI32_anneal_ret :
    ∃ mem, ReachesRet (mirCallTree bdExactDivI32Caller bdExactDivArgs) []
      (.normal (.scalar ⟨4294967294, 4⟩, mem)) :=
  runA_exists_mem_sound bdExactDivI32Caller 10 _ _ _ (by kernel_rfl)

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
  ⟨runA_exists_mem_sound bdCtpopCaller 10 _ _ _ (by kernel_rfl), rfl,
   runA_exists_mem_sound bdCtpopI8Caller 10 _ _ _ (by kernel_rfl), rfl⟩

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
  ⟨runA_exists_mem_sound bdExactDivI32Caller 10 _ _ _ (by kernel_rfl),
   faultsA_sound bdExactDivU32Caller 10 _ (by kernel_rfl),
   faultsA_sound bdExactDivI32Caller 10 _ (by kernel_rfl),
   rfl,
   faultsA_sound bdExactDivI32Caller 10 _ (by kernel_rfl),
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

* `core::intrinsics::write_bytes`: `stepMirFn` evaluates the call inline
  (`evalWriteBytesCall`); on the untracked destination pointer of
  `bdWriteBytesArgs` it fails closed (`bdWriteBytes_untracked_unsupported`), so
  Anneal certifies no execution of the caller
  (`bdWriteBytes_untracked_not_noUB`), while `minimize`'s
  `translate_rs_intrinsic` (`bb.rs:429-694`) has no `sym::write_bytes` arm and
  hits `span_bug!` (`bb.rs:615`).
* `core::intrinsics::ub_checks`: appears in two MIR forms. Inline
  `Rvalue.nullaryOp .ubChecks` evaluates to `true` in Anneal
  (`bdNullaryOp_ubChecks_contractChecks`, `bdUbChecks_anneal_ret`) and is
  rejected by `translateRvalue` (`bdNullaryOp_translateRvalue`). An unlowered
  `TerminatorKind.call` to `core::intrinsics::ub_checks` instead emits
  `MirStepNode.extCall` (`bdUbChecksCall_extCall`), and `ubChecksHandler flag`
  supplies the session-configured `bool` matching `minimize`'s
  `build::const_bool(self.tcx.sess.ub_checks())` (`bb.rs:607-610`,
  `bdUbChecksCall_handled`).
-/

/-- Anneal certifies no execution of `bdWriteBytesCaller` on `bdWriteBytesArgs`: its first step
fails closed (`bdWriteBytes_untracked_unsupported`), independently of any external-call handler,
and `progInFragment` rejects the caller (`bdExtCallers_rejected`). -/
theorem bdWriteBytes_untracked_not_noUB :
    ¬ MirNoUBTree (mirCallTree bdWriteBytesCaller bdWriteBytesArgs) := by
  obtain ⟨tr, u, hr, hf⟩ :=
    faultsA_sound bdWriteBytesCaller 1 (initMachineState bdWriteBytesCaller bdWriteBytesArgs) (by kernel_rfl)
  exact fun hsafe => hsafe tr u hr hf

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
  runA_exists_mem_sound bdUbChecksCallCaller 10 _ _ _ (by kernel_rfl)

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
  faultsA_sound bdUnreachCaller 1 _ (by kernel_rfl)

/-- MiniRust's `Terminator::Unreachable` raises UB in every machine
(`Interp.evalTerminator`). -/
theorem bd_minirust_unreachable_ub (m : Mach) :
    Interp.evalTerminator m .Unreachable = .error (.ub "reached unreachable code") := rfl

theorem bdUnreach_rejected :
    progInFragment bdUnreachCaller [] = false ∧ translateProg bdUnreachCaller [] = none :=
  ⟨by decide +kernel, rfl⟩

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
  ⟨rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

/-- Runtime fail-closed execution for polymorphic callee mismatches in Anneal's
`stepMirFn`:
1. Even when `Memory.callees` links `fbBlackBoxCallee` (`typeParamCount = 0`),
   a caller passing unmonomorphized `tys = [.param 0 "T"]` (`bdPolyBlackBoxCaller`)
   is **not** dispatched to `fbBlackBoxCallee` (`lookupCallee = none`); since
   Episode 1 of `ws-tcb-core-mem-and-ptr-intrinsics` `black_box` is evaluated inline
   (`evalBlackBoxCall`), which fails closed with `MirStepNode.unsupported` on the
   unmonomorphized `T` instead of silently pushing a frame with erased type arguments.
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
    stepMirFn bdPolyBlackBoxCaller
        (initMachineStateWithCallees bdPolyBlackBoxCaller [.scalar ⟨7, 4⟩] [fbBlackBoxCallee]) =
      MirStepNode.unsupported ∧
    stepMirFn bdExactDivParamCaller
        (initMachineState bdExactDivParamCaller bdExactDivArgs) = MirStepNode.unsupported ∧
    stepMirFn bdExactDivAliasCaller
        (initMachineState bdExactDivAliasCaller bdExactDivArgs) = MirStepNode.unsupported :=
  ⟨rfl, rfl, rfl⟩

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
  ⟨by decide +kernel, rfl, rfl, by decide +kernel, rfl, rfl⟩

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
  refine ⟨rfl, ?_, fun t => ?_, rfl, by decide +kernel⟩
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
  ⟨rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

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
  exact Nat.mod_eq_of_lt (Nat.mod_lt u (by decide +kernel))

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
      Nat.pow_lt_pow_right (by decide +kernel) (by omega)
    have hPowPos : 0 < 2 ^ (8 * it.size.bytes) := Nat.pow_pos (by decide +kernel)
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
    have hBitsPos : 0 < 8 * sz := Nat.mul_pos (by decide +kernel) hgood.pos
    have hHalfPos : 0 < 2 ^ (8 * sz - 1) := Nat.pow_pos (by decide +kernel)
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
  have hHalf8 : signedHalfModulus 8 = 2 ^ 63 := by decide +kernel
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
The statement itself mentions no MiniRust term: MiniRust has no `IntrinsicOp`
for an unwinding panic. It models unwinding with the terminators `StartUnwind`
/ `StopUnwind` / `ResumeUnwind`, which both `Interp.evalTerminator` (`Mach`)
and `Interp.evalTerminatorM` (`MachTB`) execute
(`minirust_unwind_terminators_supported`, `minirust_unwind_concrete_witnesses`,
Section 10). No simulation between those terminators and `panicUnwind` is
proved in this module, so the only semantic counterpart established here is
`Trusted`'s `startPanic` / `applyUnwindAction`. -/
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
  refine ⟨rfl, fun _ => ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
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

/-! ## 10. `[adv ep2-B4]` / `[adv ep2-A4]` MiniRust unwinding boundary, `str` layout bridge,
`target = none` UB boundary, and exhaustive 30-variant `LIntrinsicOp` classification -/

section AdvEp2B4

set_option autoImplicit false

/-- `Machine::mutate_active_thread` on a machine whose active thread is `t`:
the closure runs on `t` and its result replaces `t` in the thread list. -/
private theorem mutateActiveThread_eq {α : Type} {m : Mach} {t : Gen.Thread BM}
    (f : Gen.Thread BM → Interp (α × Gen.Thread BM))
    (ht : Interp.activeThread m = .ok t) :
    Interp.mutateActiveThread m f =
      (f t >>= fun r =>
        pure (r.1, { m with threads := m.threads.set m.active_thread.toNat r.2 })) := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  have hlt : m.active_thread.toNat < m.threads.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  unfold Interp.mutateActiveThread
  rw [ht]
  simp only [ok_bind]
  cases f t with
  | error e => rfl
  | ok r =>
    obtain ⟨out, t'⟩ := r
    simp [listSet, hge, hlt]

/-- Replacing the active thread makes the replacement the active thread. -/
private theorem activeThread_set {m : Mach} {t : Gen.Thread BM} (t' : Gen.Thread BM)
    (ht : Interp.activeThread m = .ok t) :
    Interp.activeThread { m with threads := m.threads.set m.active_thread.toNat t' } =
      .ok t' := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  exact listIndex_set_self t' hge hget _

/-- `Machine::jump_to_block` on a machine whose active thread is `t` with top
frame `fr`: only the program counter of `fr` changes, and every non-active
thread in `m.threads` is preserved. -/
private theorem jumpToBlock_activeThread {m : Mach} {t : Gen.Thread BM} {fr : Frame}
    (b : Gen.BbName) (ht : Interp.activeThread m = .ok t)
    (hfr : t.stack.getLast? = some fr) :
    ∃ m', Interp.jumpToBlock m b = .ok m' ∧
      Interp.activeThread m' = .ok
        { t with stack := t.stack.dropLast ++ [{ fr with next_block := b, next_stmt := 0 }] } ∧
      m'.mem = m.mem ∧
      m'.threads.length = m.threads.length ∧
      (∀ i, i ≠ m.active_thread.toNat → m'.threads[i]? = m.threads[i]?) := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  have hlt : m.active_thread.toNat < m.threads.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  refine ⟨_, ?_, activeThread_set _ ht, rfl, List.length_set,
    fun i hne => List.getElem?_set_ne (Ne.symm hne)⟩
  unfold Interp.jumpToBlock Interp.mutateCurFrame
  rw [ht]
  simp [hfr, listSet, hge, hlt]

/-- `Machine::jump_to_block` fails with `specPanic` when the active thread's
stack is empty. -/
private theorem jumpToBlock_empty_stack {m : Mach} {t : Gen.Thread BM}
    (b : Gen.BbName) (ht : Interp.activeThread m = .ok t) (hemp : t.stack = []) :
    Interp.jumpToBlock m b =
      .error (.specPanic "`try_mutate_cur_frame` called on empty stack!") := by
  unfold Interp.jumpToBlock Interp.mutateCurFrame
  rw [ht]
  simp [hemp, specPanic]

/-- `StackFrame::storage_dead` changes only the `locals` of the frame. -/
private theorem storageDead_stack_pop_action {fr fr' : Frame}
    {cm cm' : Gen.ConcurrentMemory BM} {l : Gen.LocalName}
    (h : Interp.storageDead fr cm l = .ok (fr', cm')) :
    fr'.stack_pop_action = fr.stack_pop_action := by
  unfold Interp.storageDead at h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := interpBind_ok h
    cases h
    rfl
  · cases h
    rfl

/-- The teardown loop of `Terminator::Return` and `Terminator::ResumeUnwind`
changes only the `locals` of the frame. -/
private theorem deallocAll_stack_pop_action :
    ∀ (fuel : Nat) {fr fr' : Frame} {cm cm' : Gen.ConcurrentMemory BM},
      Interp.deallocAll fuel fr cm = .ok (fr', cm') →
      fr'.stack_pop_action = fr.stack_pop_action
  | 0, fr, _, _, _, h => by
    unfold Interp.deallocAll at h
    rcases hent : fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> simp only [hent] at h
    · cases h
      rfl
    · cases h
  | fuel + 1, fr, _, _, _, h => by
    unfold Interp.deallocAll at h
    rcases hent : fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩ <;> simp only [hent] at h
    · cases h
      rfl
    · obtain ⟨⟨fr1, cm1⟩, hsd, h⟩ := interpBind_ok h
      exact (deallocAll_stack_pop_action fuel h).trans (storageDead_stack_pop_action hsd)

/-- Polymorphic `Machine::mutate_active_thread` on a machine whose active
thread is `t`: the closure runs on `t` and replaces `t` in the thread list. -/
private theorem mutateActiveThreadM_eq {M : Type} [Gen.Memory M] {α : Type}
    {m : Gen.Machine M} {t : Gen.Thread M}
    (f : Gen.Thread M → Interp (α × Gen.Thread M))
    (ht : Interp.activeThreadM m = .ok t) :
    Interp.mutateActiveThreadM m f =
      (f t >>= fun r =>
        pure (r.1, { m with threads := m.threads.set m.active_thread.toNat r.2 })) := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  have hlt : m.active_thread.toNat < m.threads.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  unfold Interp.mutateActiveThreadM
  rw [ht]
  simp only [ok_bind]
  cases f t with
  | error e => rfl
  | ok r =>
    obtain ⟨out, t'⟩ := r
    simp [listSet, hge, hlt]

/-- Replacing the active thread makes the replacement the active thread
(polymorphic `Machine M`). -/
private theorem activeThreadM_set {M : Type} [Gen.Memory M]
    {m : Gen.Machine M} {t : Gen.Thread M} (t' : Gen.Thread M)
    (ht : Interp.activeThreadM m = .ok t) :
    Interp.activeThreadM { m with threads := m.threads.set m.active_thread.toNat t' } =
      .ok t' := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  exact listIndex_set_self t' hge hget _

/-- Polymorphic `Machine::jump_to_block` on a machine whose active thread is `t`
with top frame `fr`: only the program counter of `fr` changes, and every
non-active thread in `m.threads` is preserved. -/
private theorem jumpToBlockM_activeThread {M : Type} [Gen.Memory M]
    {m : Gen.Machine M} {t : Gen.Thread M} {fr : Gen.StackFrame M}
    (b : Gen.BbName) (ht : Interp.activeThreadM m = .ok t)
    (hfr : t.stack.getLast? = some fr) :
    ∃ m', Interp.jumpToBlockM m b = .ok m' ∧
      Interp.activeThreadM m' = .ok
        { t with stack := t.stack.dropLast ++ [{ fr with next_block := b, next_stmt := 0 }] } ∧
      m'.mem = m.mem ∧
      m'.threads.length = m.threads.length ∧
      (∀ i, i ≠ m.active_thread.toNat → m'.threads[i]? = m.threads[i]?) := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get ht
  have hlt : m.active_thread.toNat < m.threads.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  refine ⟨_, ?_, activeThreadM_set _ ht, rfl, List.length_set,
    fun i hne => List.getElem?_set_ne (Ne.symm hne)⟩
  unfold Interp.jumpToBlockM Interp.mutateCurFrameM
  rw [ht]
  simp [hfr, listSet, hge, hlt]

/-- Polymorphic `Machine::jump_to_block` fails with `specPanic` when the active
thread's stack is empty. -/
private theorem jumpToBlockM_empty_stack {M : Type} [Gen.Memory M]
    {m : Gen.Machine M} {t : Gen.Thread M}
    (b : Gen.BbName) (ht : Interp.activeThreadM m = .ok t) (hemp : t.stack = []) :
    Interp.jumpToBlockM m b =
      .error (.specPanic "`try_mutate_cur_frame` called on empty stack!") := by
  unfold Interp.jumpToBlockM Interp.mutateCurFrameM
  rw [ht]
  simp [hemp, specPanic]

/-- Polymorphic `StackFrame::storage_dead` preserves `stack_pop_action` and
`extra`. -/
private theorem storageDeadM_preserves {M : Type} [Gen.Memory M] [Interp.MemoryOps M]
    {fr fr' : Gen.StackFrame M} {cm cm' : Gen.ConcurrentMemory M} {l : Gen.LocalName}
    (h : Interp.storageDeadM fr cm l = .ok (fr', cm')) :
    fr'.stack_pop_action = fr.stack_pop_action ∧ fr'.extra = fr.extra := by
  unfold Interp.storageDeadM at h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  obtain ⟨_, _, h⟩ := interpBind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := interpBind_ok h
    cases h
    exact ⟨rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl⟩

/-- Polymorphic `deallocAllM` preserves `stack_pop_action` and `extra`. -/
private theorem deallocAllM_preserves {M : Type} [Gen.Memory M] [Interp.MemoryOps M] :
    ∀ (fuel : Nat) {fr fr' : Gen.StackFrame M} {cm cm' : Gen.ConcurrentMemory M},
      Interp.deallocAllM fuel fr cm = .ok (fr', cm') →
      fr'.stack_pop_action = fr.stack_pop_action ∧ fr'.extra = fr.extra
  | 0, fr, _, _, _, h => by
    unfold Interp.deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> simp only [hent] at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | fuel + 1, fr, _, _, _, h => by
    unfold Interp.deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩ <;> simp only [hent] at h
    · cases h
      exact ⟨rfl, rfl⟩
    · obtain ⟨⟨fr1, cm1⟩, hsd, h⟩ := interpBind_ok h
      obtain ⟨hspa1, hext1⟩ := storageDeadM_preserves hsd
      obtain ⟨hspa2, hext2⟩ := deallocAllM_preserves fuel h
      exact ⟨hspa2.trans hspa1, hext2.trans hext1⟩

/-- **MiniRust's executable spec runs the unwinding terminators on both `Mach`
and polymorphic `Machine M` (`MachTB`)
(`minirust_unwind_terminators_supported`)**:
for every target block `blk`, both `Interp.evalTerminator` (`Mach`) and
`Interp.evalTerminatorM` (`Machine M`, instantiating `MachTB`) execute
`StartUnwind`, `StopUnwind`, and `ResumeUnwind` faithfully instead of stopping
with `.unsupported`:
- `StartUnwind` propagates any `evalValue` / `evalValueM` error unchanged; on a
  thin raw pointer payload it appends `p.thin_pointer` at the back of the
  active thread's `unwind_payloads` and jumps to `blk` without touching memory,
  while any other `(val, ty)` pair (wide raw pointers, safe references, boxes,
  fn pointers, integers, Booleans, etc.) raises `specPanic`;
- `StopUnwind` raises UB on an empty payload stack, and otherwise pops the back
  payload (LIFO) and jumps to `blk`;
- `ResumeUnwind` raises `specPanic "stack.pop().unwrap()"` on an empty call
  stack; otherwise it pops the top frame, runs `deallocAll` / `deallocAllM`,
  and on `Machine M` runs `ConcurrentMemory.end_call cm fr.extra` before
  inspecting `stack_pop_action` (so any `end_call` failure preempts both
  `BottomOfStack` and missing `unwind_block`), then raises UB on
  `BottomOfStack` or `unwind_block = none`, raises `specPanic` if
  `BackToCaller _ (some ubBlk) _` has no caller frame left after popping, and
  otherwise leaves `unwind_payloads` intact and jumps to `unwind_block` in the
  caller frame. Every successful unwinding terminator leaves all non-active
  threads untouched.

Concrete non-vacuous witnesses discharging every branch on both `Mach` and
`MachTB` (including live-local teardown and Tree Borrows protector release) are
in `minirust_unwind_concrete_witnesses`. Anneal's lowered `panicUnwind` (routed
to `startPanic` by `evalLIntrinsic_panicUnwind_minirust_correspondence`) has no
single `IntrinsicOp` counterpart; no simulation between these terminators and
`Trusted`'s `startPanic` / `applyUnwindAction` is proved in this module. -/
theorem minirust_unwind_terminators_supported (m : Mach) (blk : Gen.BbName) :
    ((∀ (payload : Gen.ValueExpr) (p : Gen.Pointer Prov) (m1 : Mach) (t : Gen.Thread BM)
        (fr : Frame),
      Interp.evalValue m payload = .ok ((.Ptr p, .Ptr (.Raw .None)), m1) →
      Interp.activeThread m1 = .ok t → t.stack.getLast? = some fr →
      ∃ m', Interp.evalTerminator m (.StartUnwind payload blk) = .ok m' ∧
        Interp.activeThread m' = .ok
          { stack := t.stack.dropLast ++ [{ fr with next_block := blk, next_stmt := 0 }],
            state := t.state,
            unwind_payloads := t.unwind_payloads ++ [p.thin_pointer] } ∧
        m'.mem = m1.mem ∧
        m'.threads.length = m1.threads.length ∧
        (∀ i, i ≠ m1.active_thread.toNat → m'.threads[i]? = m1.threads[i]?)) ∧
    (∀ (payload : Gen.ValueExpr) (v : Val) (ty : Gen.Type) (m1 : Mach),
      (¬ ∃ p, v = .Ptr p ∧ ty = .Ptr (.Raw .None)) →
      Interp.evalValue m payload = .ok ((v, ty), m1) →
      Interp.evalTerminator m (.StartUnwind payload blk) =
        .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer")) ∧
    (∀ (payload : Gen.ValueExpr) (e : Interp.Stop),
      Interp.evalValue m payload = .error e →
      Interp.evalTerminator m (.StartUnwind payload blk) = .error e) ∧
    (∀ (t : Gen.Thread BM),
      Interp.activeThread m = .ok t → t.unwind_payloads = [] →
      Interp.evalTerminator m (.StopUnwind blk) =
        .error (.ub "StopUnwind: the payload stack is empty")) ∧
    (∀ (t : Gen.Thread BM) (ps : List Ptr) (q : Ptr) (fr : Frame),
      Interp.activeThread m = .ok t → t.unwind_payloads = ps ++ [q] →
      t.stack.getLast? = some fr →
      ∃ m', Interp.evalTerminator m (.StopUnwind blk) = .ok m' ∧
        Interp.activeThread m' = .ok
          { stack := t.stack.dropLast ++ [{ fr with next_block := blk, next_stmt := 0 }],
            state := t.state,
            unwind_payloads := ps } ∧
        m'.mem = m.mem ∧
        m'.threads.length = m.threads.length ∧
        (∀ i, i ≠ m.active_thread.toNat → m'.threads[i]? = m.threads[i]?)) ∧
    (∀ (t : Gen.Thread BM),
      Interp.activeThread m = .ok t → t.stack = [] →
      Interp.evalTerminator m .ResumeUnwind =
        .error (.specPanic "stack.pop().unwrap()")) ∧
    (∀ (t : Gen.Thread BM) (fr fr' : Frame) (cm : Gen.ConcurrentMemory BM),
      Interp.activeThread m = .ok t → t.stack.getLast? = some fr →
      Interp.deallocAll fr.locals.entries.length fr m.mem = .ok (fr', cm) →
      (fr.stack_pop_action = .BottomOfStack →
        Interp.evalTerminator m .ResumeUnwind =
          .error (.ub "the function at the bottom of the stack must not unwind")) ∧
      (∀ nextBlock retPtr, fr.stack_pop_action = .BackToCaller nextBlock none retPtr →
        Interp.evalTerminator m .ResumeUnwind =
          .error (.ub
            "unwinding from a function where the caller did not specify an unwind_block")) ∧
      (∀ nextBlock unwindBlock retPtr,
        fr.stack_pop_action = .BackToCaller nextBlock (some unwindBlock) retPtr →
        t.stack.dropLast = [] →
        Interp.evalTerminator m .ResumeUnwind =
          .error (.specPanic "`try_mutate_cur_frame` called on empty stack!")) ∧
      (∀ nextBlock unwindBlock retPtr (caller : Frame),
        fr.stack_pop_action = .BackToCaller nextBlock (some unwindBlock) retPtr →
        t.stack.dropLast.getLast? = some caller →
        ∃ m', Interp.evalTerminator m .ResumeUnwind = .ok m' ∧
          Interp.activeThread m' = .ok
            { stack := t.stack.dropLast.dropLast ++
                [{ caller with next_block := unwindBlock, next_stmt := 0 }],
              state := t.state,
              unwind_payloads := t.unwind_payloads } ∧
          m'.mem = cm ∧
          m'.threads.length = m.threads.length ∧
          (∀ i, i ≠ m.active_thread.toNat → m'.threads[i]? = m.threads[i]?)))) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (mM : Gen.Machine M),
      (∀ (payload : Gen.ValueExpr) (p : Gen.Pointer (Gen.Memory.Provenance M))
          (m1 : Gen.Machine M) (t : Gen.Thread M) (fr : Gen.StackFrame M),
        Interp.evalValueM mM payload = .ok ((.Ptr p, .Ptr (.Raw .None)), m1) →
        Interp.activeThreadM m1 = .ok t → t.stack.getLast? = some fr →
        ∃ m', Interp.evalTerminatorM mM (.StartUnwind payload blk) = .ok m' ∧
          Interp.activeThreadM m' = .ok
            { stack := t.stack.dropLast ++ [{ fr with next_block := blk, next_stmt := 0 }],
              state := t.state,
              unwind_payloads := t.unwind_payloads ++ [p.thin_pointer] } ∧
          m'.mem = m1.mem ∧
          m'.threads.length = m1.threads.length ∧
          (∀ i, i ≠ m1.active_thread.toNat → m'.threads[i]? = m1.threads[i]?)) ∧
      (∀ (payload : Gen.ValueExpr) (v : Gen.Value M) (ty : Gen.Type) (m1 : Gen.Machine M),
        (¬ ∃ p, v = .Ptr p ∧ ty = .Ptr (.Raw .None)) →
        Interp.evalValueM mM payload = .ok ((v, ty), m1) →
        Interp.evalTerminatorM mM (.StartUnwind payload blk) =
          .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer")) ∧
      (∀ (payload : Gen.ValueExpr) (e : Interp.Stop),
        Interp.evalValueM mM payload = .error e →
        Interp.evalTerminatorM mM (.StartUnwind payload blk) = .error e) ∧
      (∀ (t : Gen.Thread M),
        Interp.activeThreadM mM = .ok t → t.unwind_payloads = [] →
        Interp.evalTerminatorM mM (.StopUnwind blk) =
          .error (.ub "StopUnwind: the payload stack is empty")) ∧
      (∀ (t : Gen.Thread M) (ps : List (Gen.ThinPointer (Gen.Memory.Provenance M)))
          (q : Gen.ThinPointer (Gen.Memory.Provenance M)) (fr : Gen.StackFrame M),
        Interp.activeThreadM mM = .ok t → t.unwind_payloads = ps ++ [q] →
        t.stack.getLast? = some fr →
        ∃ m', Interp.evalTerminatorM mM (.StopUnwind blk) = .ok m' ∧
          Interp.activeThreadM m' = .ok
            { stack := t.stack.dropLast ++ [{ fr with next_block := blk, next_stmt := 0 }],
              state := t.state,
              unwind_payloads := ps } ∧
          m'.mem = mM.mem ∧
          m'.threads.length = mM.threads.length ∧
          (∀ i, i ≠ mM.active_thread.toNat → m'.threads[i]? = mM.threads[i]?)) ∧
      (∀ (t : Gen.Thread M),
        Interp.activeThreadM mM = .ok t → t.stack = [] →
        Interp.evalTerminatorM mM .ResumeUnwind =
          .error (.specPanic "stack.pop().unwrap()")) ∧
      (∀ (t : Gen.Thread M) (fr fr' : Gen.StackFrame M) (cm1 : Gen.ConcurrentMemory M),
        Interp.activeThreadM mM = .ok t → t.stack.getLast? = some fr →
        Interp.deallocAllM fr.locals.entries.length fr mM.mem = .ok (fr', cm1) →
        (∀ e, Interp.ConcurrentMemory.end_call cm1 fr.extra = .error e →
          Interp.evalTerminatorM mM .ResumeUnwind = .error e) ∧
        (∀ cm2, Interp.ConcurrentMemory.end_call cm1 fr.extra = .ok cm2 →
          (fr.stack_pop_action = .BottomOfStack →
            Interp.evalTerminatorM mM .ResumeUnwind =
              .error (.ub "the function at the bottom of the stack must not unwind")) ∧
          (∀ nextBlock retPtr, fr.stack_pop_action = .BackToCaller nextBlock none retPtr →
            Interp.evalTerminatorM mM .ResumeUnwind =
              .error (.ub
                "unwinding from a function where the caller did not specify an unwind_block")) ∧
          (∀ nextBlock unwindBlock retPtr,
            fr.stack_pop_action = .BackToCaller nextBlock (some unwindBlock) retPtr →
            t.stack.dropLast = [] →
            Interp.evalTerminatorM mM .ResumeUnwind =
              .error (.specPanic "`try_mutate_cur_frame` called on empty stack!")) ∧
          (∀ nextBlock unwindBlock retPtr (caller : Gen.StackFrame M),
            fr.stack_pop_action = .BackToCaller nextBlock (some unwindBlock) retPtr →
            t.stack.dropLast.getLast? = some caller →
            ∃ m', Interp.evalTerminatorM mM .ResumeUnwind = .ok m' ∧
              Interp.activeThreadM m' = .ok
                { stack := t.stack.dropLast.dropLast ++
                    [{ caller with next_block := unwindBlock, next_stmt := 0 }],
                  state := t.state,
                  unwind_payloads := t.unwind_payloads } ∧
              m'.mem = cm2 ∧
              m'.threads.length = mM.threads.length ∧
              (∀ i, i ≠ mM.active_thread.toNat → m'.threads[i]? = mM.threads[i]?))))) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro payload p m1 t fr hev ht hfr
    obtain ⟨m', hj, hact, hmem, hlen, hne⟩ := jumpToBlock_activeThread (fr := fr) blk
      (activeThread_set
        { t with unwind_payloads := t.unwind_payloads ++ [p.thin_pointer] } ht) hfr
    refine ⟨m', ?_, hact, hmem, hlen.trans List.length_set, fun i hi =>
      (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
    simp only [Interp.evalTerminator, hev, ok_bind]
    rw [mutateActiveThread_eq _ ht]
    exact hj
  · intro payload v ty m1 hnot hev
    simp only [Interp.evalTerminator, hev, ok_bind]
    cases v with
    | Ptr p =>
      cases ty with
      | Ptr pt =>
        cases pt with
        | Raw mk =>
          cases mk with
          | None => exact absurd ⟨p, rfl, rfl⟩ hnot
          | ElementCount => rfl
          | VTablePointer _ => rfl
        | Ref _ _ => rfl
        | Box _ => rfl
        | FnPtr => rfl
        | VTablePtr _ => rfl
      | Int _ => rfl
      | Bool => rfl
      | Tuple _ _ _ => rfl
      | Array _ _ => rfl
      | Slice _ => rfl
      | Union _ _ _ _ => rfl
      | Enum _ _ _ _ _ => rfl
      | TraitObject _ => rfl
    | Int _ => rfl
    | Bool _ => rfl
    | Tuple _ => rfl
    | Union _ => rfl
    | Variant _ _ => rfl
  · intro payload e herr
    simp [Interp.evalTerminator, herr, error_bind]
  · intro t ht hemp
    simp only [Interp.evalTerminator]
    rw [mutateActiveThread_eq _ ht]
    simp [hemp, ub]
  · intro t ps q fr ht hps hfr
    obtain ⟨m', hj, hact, hmem, hlen, hne⟩ := jumpToBlock_activeThread (fr := fr) blk
      (activeThread_set { t with unwind_payloads := ps } ht) hfr
    refine ⟨m', ?_, hact, hmem, hlen.trans List.length_set, fun i hi =>
      (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
    simp only [Interp.evalTerminator]
    rw [mutateActiveThread_eq _ ht]
    simp only [hps, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_concat, pure_ok, ok_bind]
    exact hj
  · intro t ht hemp
    simp only [Interp.evalTerminator, Interp.evalResumeUnwind]
    rw [ht]
    simp [hemp, specPanic]
  · intro t fr fr' cm ht hfr hdealloc
    obtain ⟨hge, hget⟩ := listIndex_ok_get ht
    have hlt : m.active_thread.toNat < m.threads.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have hspa := deallocAll_stack_pop_action _ hdealloc
    have hpop : Interp.evalTerminator m .ResumeUnwind =
        (match fr'.stack_pop_action with
          | .BottomOfStack => ub "the function at the bottom of the stack must not unwind"
          | .BackToCaller _ unwindBlock _ =>
            match unwindBlock with
            | some unwindBlock =>
              Interp.jumpToBlock
                { m with
                  threads := m.threads.set m.active_thread.toNat
                    { t with stack := t.stack.dropLast },
                  mem := cm } unwindBlock
            | none =>
              ub "unwinding from a function where the caller did not specify an unwind_block") := by
      simp only [Interp.evalTerminator, Interp.evalResumeUnwind]
      rw [ht]
      simp only [ok_bind, hfr, pure_ok, listSet, hge, hlt, and_self, ↓reduceIte, hdealloc]
      cases fr'.stack_pop_action with
      | BottomOfStack => rfl
      | BackToCaller _ unwindBlock _ => cases unwindBlock <;> rfl
    refine ⟨fun hbot => ?_, fun nextBlock retPtr hback => ?_,
      fun nextBlock unwindBlock retPtr hback hemp => ?_,
      fun nextBlock unwindBlock retPtr caller hback hcaller => ?_⟩
    · rw [hpop, hspa, hbot]
      rfl
    · rw [hpop, hspa, hback]
      rfl
    · have hact : Interp.activeThread
          { m with
            threads := m.threads.set m.active_thread.toNat { t with stack := t.stack.dropLast },
            mem := cm } = .ok { t with stack := t.stack.dropLast } :=
        activeThread_set (m := { m with mem := cm }) _ ht
      rw [hpop, hspa, hback]
      exact jumpToBlock_empty_stack unwindBlock hact hemp
    · have hact : Interp.activeThread
          { m with
            threads := m.threads.set m.active_thread.toNat { t with stack := t.stack.dropLast },
            mem := cm } = .ok { t with stack := t.stack.dropLast } :=
        activeThread_set (m := { m with mem := cm }) _ ht
      obtain ⟨m', hj, hact', hmem, hlen, hne⟩ := jumpToBlock_activeThread (fr := caller) unwindBlock
        hact hcaller
      refine ⟨m', ?_, hact', hmem, hlen.trans List.length_set, fun i hi =>
        (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
      rw [hpop, hspa, hback]
      exact hj
  · intro M _ _ mM
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro payload p m1 t fr hev ht hfr
      obtain ⟨m', hj, hact, hmem, hlen, hne⟩ := jumpToBlockM_activeThread (fr := fr) blk
        (activeThreadM_set
          { t with unwind_payloads := t.unwind_payloads ++ [p.thin_pointer] } ht) hfr
      refine ⟨m', ?_, hact, hmem, hlen.trans List.length_set, fun i hi =>
        (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
      simp only [Interp.evalTerminatorM, hev, ok_bind]
      rw [mutateActiveThreadM_eq _ ht]
      exact hj
    · intro payload v ty m1 hnot hev
      simp only [Interp.evalTerminatorM, hev, ok_bind]
      cases v with
      | Ptr p =>
        cases ty with
        | Ptr pt =>
          cases pt with
          | Raw mk =>
            cases mk with
            | None => exact absurd ⟨p, rfl, rfl⟩ hnot
            | ElementCount => rfl
            | VTablePointer _ => rfl
          | Ref _ _ => rfl
          | Box _ => rfl
          | FnPtr => rfl
          | VTablePtr _ => rfl
        | Int _ => rfl
        | Bool => rfl
        | Tuple _ _ _ => rfl
        | Array _ _ => rfl
        | Slice _ => rfl
        | Union _ _ _ _ => rfl
        | Enum _ _ _ _ _ => rfl
        | TraitObject _ => rfl
      | Int _ => rfl
      | Bool _ => rfl
      | Tuple _ => rfl
      | Union _ => rfl
      | Variant _ _ => rfl
    · intro payload e herr
      simp [Interp.evalTerminatorM, herr, error_bind]
    · intro t ht hemp
      simp only [Interp.evalTerminatorM]
      rw [mutateActiveThreadM_eq _ ht]
      simp [hemp, ub]
    · intro t ps q fr ht hps hfr
      obtain ⟨m', hj, hact, hmem, hlen, hne⟩ := jumpToBlockM_activeThread (fr := fr) blk
        (activeThreadM_set { t with unwind_payloads := ps } ht) hfr
      refine ⟨m', ?_, hact, hmem, hlen.trans List.length_set, fun i hi =>
        (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
      simp only [Interp.evalTerminatorM]
      rw [mutateActiveThreadM_eq _ ht]
      simp only [hps, List.getLast?_append, List.getLast?_singleton, Option.some_or,
        List.dropLast_concat, pure_ok, ok_bind]
      exact hj
    · intro t ht hemp
      simp only [Interp.evalTerminatorM, Interp.evalResumeUnwindM]
      rw [ht]
      simp [hemp, specPanic]
    · intro t fr fr' cm1 ht hfr hdealloc
      obtain ⟨hge, hget⟩ := listIndex_ok_get ht
      have hlt : mM.active_thread.toNat < mM.threads.length :=
        (List.getElem?_eq_some_iff.mp hget).1
      obtain ⟨hspa, hext⟩ := deallocAllM_preserves _ hdealloc
      have hpre : Interp.evalTerminatorM mM .ResumeUnwind =
          (Interp.ConcurrentMemory.end_call cm1 fr.extra >>= fun cm2 =>
            match fr.stack_pop_action with
            | .BottomOfStack => ub "the function at the bottom of the stack must not unwind"
            | .BackToCaller _ unwindBlock _ =>
              match unwindBlock with
              | some unwindBlock =>
                Interp.jumpToBlockM
                  { mM with
                    threads := mM.threads.set mM.active_thread.toNat
                      { t with stack := t.stack.dropLast },
                    mem := cm2 } unwindBlock
              | none => ub
                "unwinding from a function where the caller did not specify an unwind_block") := by
        simp only [Interp.evalTerminatorM, Interp.evalResumeUnwindM]
        rw [ht]
        simp only [ok_bind, hfr, pure_ok, listSet, hge, hlt, and_self, ↓reduceIte, hdealloc,
          hext, hspa]
        cases Interp.ConcurrentMemory.end_call cm1 fr.extra with
        | error e => rfl
        | ok cm2 =>
          simp only [ok_bind]
          cases fr.stack_pop_action with
          | BottomOfStack => rfl
          | BackToCaller _ unwindBlock _ => cases unwindBlock <;> rfl
      refine ⟨fun e herr => ?_, fun cm2 hok => ?_⟩
      · rw [hpre, herr]
        rfl
      · refine ⟨fun hbot => ?_, fun nextBlock retPtr hback => ?_,
          fun nextBlock unwindBlock retPtr hback hemp => ?_,
          fun nextBlock unwindBlock retPtr caller hback hcaller => ?_⟩
        · rw [hpre, hok, ok_bind, hbot]
          rfl
        · rw [hpre, hok, ok_bind, hback]
          rfl
        · have hact : Interp.activeThreadM
              { mM with
                threads := mM.threads.set mM.active_thread.toNat
                  { t with stack := t.stack.dropLast },
                mem := cm2 } = .ok { t with stack := t.stack.dropLast } :=
            activeThreadM_set (m := { mM with mem := cm2 }) _ ht
          rw [hpre, hok, ok_bind, hback]
          exact jumpToBlockM_empty_stack unwindBlock hact hemp
        · have hact : Interp.activeThreadM
              { mM with
                threads := mM.threads.set mM.active_thread.toNat
                  { t with stack := t.stack.dropLast },
                mem := cm2 } = .ok { t with stack := t.stack.dropLast } :=
            activeThreadM_set (m := { mM with mem := cm2 }) _ ht
          obtain ⟨m', hj, hact', hmem, hlen, hne⟩ := jumpToBlockM_activeThread (fr := caller)
            unwindBlock hact hcaller
          refine ⟨m', ?_, hact', hmem, hlen.trans List.length_set, fun i hi =>
            (hne i hi).trans (List.getElem?_set_ne (Ne.symm hi))⟩
          rw [hpre, hok, ok_bind, hback]
          exact hj

/-! ### Unwinding and `SetDiscriminant`: concrete witnesses and general laws -/

private def uwEmptyProg : Gen.Program :=
  { functions := ⟨[]⟩
    start := ⟨⟨0⟩⟩
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

private def uwFn (locals : List (Gen.LocalName × Gen.Type)) : Gen.Function :=
  { locals := ⟨locals⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwMachBM (allocs : List (Gen.Allocation Unit Unit))
    (stack : List Frame) (payloads : List Ptr) : Mach :=
  { prog := uwEmptyProg
    mem := { memory := { allocations := allocs, _phantom := ⟨⟩ }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := stack, state := .Enabled, unwind_payloads := payloads }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def uwMachTB (allocs : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra))
    (stack : List (Gen.StackFrame TBM))
    (payloads : List (Gen.ThinPointer Gen.TreeBorrowsProvenance)) : MachTB :=
  { prog := uwEmptyProg
    mem :=
      { memory :=
          { params := { implicit_writes := false }
            mem := { allocations := allocs, _phantom := ⟨⟩ } }
        accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := stack, state := .Enabled, unwind_payloads := payloads }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def uwRawThinPtrExpr (addr : Int) : Gen.ValueExpr :=
  .Constant (.PointerWithoutProvenance addr) (.Ptr (.Raw .None))

private def uwLiveStackAllocBM (addr : Int) : Gen.Allocation Unit Unit :=
  { data := [.Init 0x42 none]
    addr := addr
    align := ⟨1⟩
    kind := .Stack
    live := true
    extra := () }

private def uwLiveAllocTB (addr : Int) (kind : Gen.AllocationKind) (root : Gen.Node) :
    Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
  { data := [.Init 0x42 none]
    addr := addr
    align := ⟨1⟩
    kind := kind
    live := true
    extra := { root := root } }

private def uwProtNode (prot : Gen.Protected) (perm : Gen.Permission) : Gen.Node :=
  { children := [], permissions := [perm], «protected» := prot }

private def uwRootWithChildren (cs : List Gen.Node) : Gen.Node :=
  { children := cs, permissions := [.Unprot .Unique], «protected» := .No }

/-- **Non-vacuous concrete unwinding witnesses across `Mach` and `MachTB`
(`minirust_unwind_concrete_witnesses`)**: kernel-checked executions without any
conditional hypotheses exercising:
1. 2-deep LIFO unwind payload cycle (`StartUnwind` push `0x1000` → `StartUnwind`
   push `0x2000` → `GetUnwindPayload` yields `0x2000` → `StopUnwind` pops
   `0x2000` → `GetUnwindPayload` yields `0x1000` → `StopUnwind` pops `0x1000` →
   third `StopUnwind` raises UB `"StopUnwind: the payload stack is empty"`) on
   both `Mach` and `MachTB`, plus concrete `StartUnwind` `specPanic` rejections
   of non-raw (`Ref`), wide-raw (`ElementCount`), and integer payloads;
2. `ResumeUnwind` on `Mach` tearing down a live stack local (`live` flips
   `true → false`), popping the callee, jumping the caller to `unwind_block`
   while preserving `unwind_payloads`, plus concrete `BottomOfStack` UB,
   missing-`unwind_block` UB, and empty-stack `specPanic`;
3. `ResumeUnwind` on `MachTB` (Tree Borrows):
   - live local teardown (`alloc 1` becomes `live = false`) **and** `end_call`
     releasing a strong protector on caller `alloc 0` (`protected` transitions
     `.Strong → .No`, permission `.Prot (.Frozen true) → .Unprot .Frozen`)
     while jumping the caller to `unwind_block`;
   - `deallocAllM` raising Tree Borrows UB when unwinding tries to deallocate a
     strongly protected local
     (`"Tree Borrows: deallocating strongly protected allocation"`);
   - `end_call` raising Tree Borrows protector-conflict UB when releasing a
     `Prot .Unique` protector conflicts with a strongly protected
     `Prot (.Frozen true)` sibling, **preempting** `BottomOfStack` UB (proving
     `end_call` executes before inspecting `stack_pop_action`);
   - `BottomOfStack` and missing-`unwind_block` UB on `MachTB` when `end_call`
     succeeds. -/
theorem minirust_unwind_concrete_witnesses :
    let p1 : Ptr := ⟨0x1000, none⟩
    let p2 : Ptr := ⟨0x2000, none⟩
    let p1TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, none⟩
    let p2TB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x2000, none⟩
    let baseFrameBM : Frame :=
      { func := uwFn [], locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
        next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
    let baseFrameTB : Gen.StackFrame TBM :=
      { func := uwFn [], locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
        next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
    let m0BM := uwMachBM [] [baseFrameBM] []
    let m0TB := uwMachTB [] [baseFrameTB] []
    let rawTy : Gen.Type := .Ptr (.Raw .None)
    let badIntPayload : Gen.ValueExpr := .Constant (.Int 7) (.Int u8)
    let widePairTy : Gen.Type :=
      .Tuple [(⟨0⟩, .Ptr (.Raw .None)), (⟨8⟩, .Int IntType.usize_ty)] ⟨⟨16⟩, ⟨8⟩, none⟩ none
    let badWidePayload : Gen.ValueExpr :=
      .UnOp (.Cast (.Transmute (.Ptr (.Raw .ElementCount))))
        (.Tuple [uwRawThinPtrExpr 0x1000, .Constant (.Int 0) (.Int IntType.usize_ty)] widePairTy)
    let badRefPayload : Gen.ValueExpr :=
      .Constant (.PointerWithoutProvenance 0x1000)
        (.Ptr (.Ref .Immutable ⟨.Sized ⟨0⟩ ⟨1⟩, true, .Sized [], true, true⟩))
    let lifoBM := do
      let m1 ← Interp.evalTerminator m0BM (.StartUnwind (uwRawThinPtrExpr 0x1000) ⟨⟨1⟩⟩)
      let m2 ← Interp.evalTerminator m1 (.StartUnwind (uwRawThinPtrExpr 0x2000) ⟨⟨2⟩⟩)
      let (top2, m2') ← Interp.evalIntrinsic m2 .GetUnwindPayload [] rawTy
      let m3 ← Interp.evalTerminator m2' (.StopUnwind ⟨⟨3⟩⟩)
      let (top1, m3') ← Interp.evalIntrinsic m3 .GetUnwindPayload [] rawTy
      let m4 ← Interp.evalTerminator m3' (.StopUnwind ⟨⟨4⟩⟩)
      pure (top2, top1, m4)
    let lifoTB := do
      let m1 ← Interp.evalTerminatorM m0TB (.StartUnwind (uwRawThinPtrExpr 0x1000) ⟨⟨1⟩⟩)
      let m2 ← Interp.evalTerminatorM m1 (.StartUnwind (uwRawThinPtrExpr 0x2000) ⟨⟨2⟩⟩)
      let (top2, m2') ← Interp.evalIntrinsicM m2 .GetUnwindPayload [] rawTy
      let m3 ← Interp.evalTerminatorM m2' (.StopUnwind ⟨⟨3⟩⟩)
      let (top1, m3') ← Interp.evalIntrinsicM m3 .GetUnwindPayload [] rawTy
      let m4 ← Interp.evalTerminatorM m3' (.StopUnwind ⟨⟨4⟩⟩)
      pure (top2, top1, m4)
    let calleeFn := uwFn [(⟨⟨1⟩⟩, .Int u8)]
    let calleeFrameBM : Frame :=
      { func := calleeFn
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x4000, some (⟨0⟩, ())⟩)]⟩
        stack_pop_action := .BackToCaller none (some ⟨⟨9⟩⟩) ⟨0, none⟩
        next_block := ⟨⟨5⟩⟩
        next_stmt := 0
        extra := () }
    let mResumeBM := uwMachBM [uwLiveStackAllocBM 0x4000] [baseFrameBM, calleeFrameBM] [p1]
    let mNoUnwindBM := uwMachBM []
      [baseFrameBM,
        { calleeFrameBM with
          locals := ⟨[]⟩
          stack_pop_action := .BackToCaller (some ⟨⟨7⟩⟩) none ⟨0, none⟩ }] [p1]
    let mEmptyStackBM := uwMachBM [] [] []
    let tbCallerAlloc := uwLiveAllocTB 0x3000 .Stack
      (uwRootWithChildren [uwProtNode .Strong (.Prot (.Frozen true))])
    let tbCalleeAlloc := uwLiveAllocTB 0x4000 .Stack (uwRootWithChildren [])
    let calleeFrameTB : Gen.StackFrame TBM :=
      { func := calleeFn
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x4000, some (⟨1⟩, [])⟩)]⟩
        stack_pop_action := .BackToCaller none (some ⟨⟨9⟩⟩) ⟨0, none⟩
        next_block := ⟨⟨5⟩⟩
        next_stmt := 0
        extra := { protectors := [(⟨0⟩, [0])] } }
    let mResumeTB := uwMachTB [tbCallerAlloc, tbCalleeAlloc]
      [baseFrameTB, calleeFrameTB] [p1TB]
    let tbProtDeallocAlloc := uwLiveAllocTB 0x3000 .Stack
      (uwProtNode .Strong (.Prot .Unique))
    let mProtDeallocTB := uwMachTB [tbProtDeallocAlloc]
      [baseFrameTB,
        { calleeFrameTB with
          locals := ⟨[(⟨⟨1⟩⟩, ⟨0x3000, some (⟨0⟩, [])⟩)]⟩
          extra := { protectors := [] } }] [p1TB]
    let tbConflictAlloc := uwLiveAllocTB 0x5000 .Stack
      (uwRootWithChildren
        [uwProtNode .Strong (.Prot .Unique),
         uwProtNode .Strong (.Prot (.Frozen true))])
    let mEndCallConflictTB := uwMachTB [tbConflictAlloc]
      [{ baseFrameTB with extra := { protectors := [(⟨0⟩, [0])] } }] [p1TB]
    let mNoUnwindTB := uwMachTB []
      [baseFrameTB,
        { calleeFrameTB with
          locals := ⟨[]⟩
          stack_pop_action := .BackToCaller (some ⟨⟨7⟩⟩) none ⟨0, none⟩
          extra := { protectors := [] } }] [p1TB]
    (∃ m4, lifoBM = .ok (.Ptr ⟨p2, none⟩, .Ptr ⟨p1, none⟩, m4) ∧
      Interp.activeThread m4 = .ok
        { stack := [{ baseFrameBM with next_block := ⟨⟨4⟩⟩, next_stmt := 0 }],
          state := .Enabled, unwind_payloads := [] } ∧
      Interp.evalTerminator m4 (.StopUnwind ⟨⟨5⟩⟩) =
        .error (.ub "StopUnwind: the payload stack is empty")) ∧
    (∃ m4, lifoTB = .ok (.Ptr ⟨p2TB, none⟩, .Ptr ⟨p1TB, none⟩, m4) ∧
      Interp.activeThreadM m4 = .ok
        { stack := [{ baseFrameTB with next_block := ⟨⟨4⟩⟩, next_stmt := 0 }],
          state := .Enabled, unwind_payloads := [] } ∧
      Interp.evalTerminatorM m4 (.StopUnwind ⟨⟨5⟩⟩) =
        .error (.ub "StopUnwind: the payload stack is empty")) ∧
    (Interp.evalTerminator m0BM (.StartUnwind badIntPayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer") ∧
     Interp.evalTerminator m0BM (.StartUnwind badWidePayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer") ∧
     Interp.evalTerminator m0BM (.StartUnwind badRefPayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer") ∧
     Interp.evalTerminatorM m0TB (.StartUnwind badIntPayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer") ∧
     Interp.evalTerminatorM m0TB (.StartUnwind badWidePayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer") ∧
     Interp.evalTerminatorM m0TB (.StartUnwind badRefPayload ⟨⟨1⟩⟩) =
      .error (.specPanic "StartUnwind: the unwind payload is not a raw pointer")) ∧
    (∃ m', Interp.evalTerminator mResumeBM .ResumeUnwind = .ok m' ∧
      m'.mem.memory.allocations.map (·.live) = [false] ∧
      Interp.activeThread m' = .ok
        { stack := [{ baseFrameBM with next_block := ⟨⟨9⟩⟩, next_stmt := 0 }],
          state := .Enabled, unwind_payloads := [p1] }) ∧
    (Interp.evalTerminator m0BM .ResumeUnwind =
      .error (.ub "the function at the bottom of the stack must not unwind") ∧
     Interp.evalTerminator mNoUnwindBM .ResumeUnwind =
      .error (.ub "unwinding from a function where the caller did not specify an unwind_block") ∧
     Interp.evalTerminator mEmptyStackBM .ResumeUnwind =
      .error (.specPanic "stack.pop().unwrap()")) ∧
    (∃ m', Interp.evalTerminatorM mResumeTB .ResumeUnwind = .ok m' ∧
      m'.mem.memory.mem.allocations.map (·.live) = [true, false] ∧
      (m'.mem.memory.mem.allocations[0]?.bind (fun a => a.extra.root.children[0]?)) =
        some (uwProtNode .No (.Unprot .Frozen)) ∧
      Interp.activeThreadM m' = .ok
        { stack := [{ baseFrameTB with next_block := ⟨⟨9⟩⟩, next_stmt := 0 }],
          state := .Enabled, unwind_payloads := [p1TB] }) ∧
    (Interp.evalTerminatorM mProtDeallocTB .ResumeUnwind =
      .error (.ub "Tree Borrows: deallocating strongly protected allocation") ∧
     Interp.evalTerminatorM mEndCallConflictTB .ResumeUnwind =
      .error (.ub
        "Tree Borrows: foreign write of protected Frozen reference which had a local read") ∧
     Interp.evalTerminatorM m0TB .ResumeUnwind =
      .error (.ub "the function at the bottom of the stack must not unwind") ∧
     Interp.evalTerminatorM mNoUnwindTB .ResumeUnwind =
      .error (.ub
        "unwinding from a function where the caller did not specify an unwind_block")) := by
  refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

private def sdPayloadBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0xAA none, .Init 0xBB none, .Init 0xCC none, .Init 0xDD none,
   .Init 0xEE none, .Init 0xFF none, .Init 0x11 none, .Init 0x22 none]

private def sdExpectedBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0x03 none, .Init 0xBB none, .Init 0xCC none, .Init 0xDD none,
   .Init 0x78 none, .Init 0x56 none, .Init 0x11 none, .Init 0x22 none]

private def sdEnumTy : Gen.Type :=
  let v7 : Gen.Variant :=
    { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
      tagger := ⟨[(⟨0⟩, (u8, 0x03)), (⟨4⟩, (u16, 0x5678))]⟩ }
  let vNiche : Gen.Variant :=
    { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
      tagger := ⟨[]⟩ }
  let vOob : Gen.Variant :=
    { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
      tagger := ⟨[(⟨16⟩, (u8, 1))]⟩ }
  let disc : Gen.Discriminator :=
    .Branch ⟨0⟩ u8 .Invalid
      ⟨[((3, 4), .Branch ⟨4⟩ u16 .Invalid ⟨[((0x5678, 0x5679), .Known 7)]⟩)]⟩
  .Enum ⟨[(7, v7), (8, vNiche), (9, vOob)]⟩ u8 disc ⟨8⟩ ⟨4⟩

/-- **MiniRust `Statement::SetDiscriminant` semantics on `Mach` and `MachTB`
(`minirust_setDiscriminant_supported`)**: combines universal error-ordering and
empty-tagger laws (across `Mach` and polymorphic `Machine M`) with concrete
kernel-checked witnesses on both `Mach` and `MachTB`:
- Universal laws (both `evalStatement` and `evalStatementM`):
  1. Any `evalPlace` / `evalPlaceM` error propagates unchanged;
  2. Non-enum destination raises `specPanic` before checking alignment;
  3. Misaligned enum destination raises `ub` before looking up `value`;
  4. Missing variant `value` raises
     `specPanic s!"setting an invalid discriminant ({value})"`;
  5. Empty `tagger` (niche variant) returns `m1` unchanged with zero stores;
- Concrete witnesses (`Mach` and `MachTB`):
  6. Multi-entry tagger writes `u8` (`0x03`) at offset `0` and little-endian
     `u16` (`0x5678` → `[0x78, 0x56]`) at offset `4`, leaving all five payload
     bytes (`0xBB, 0xCC, 0xDD, 0x11, 0x22`) untouched, recording the two
     `Store` accesses in `tagger.entries` order, and round-tripping through
     `decodeDiscriminant` to `some 7`;
  7. Concrete negative controls on both `Mach` and `MachTB`: misaligned enum
     with missing variant `99` (UB wins over missing variant), misaligned
     non-enum (`specPanic` wins over misaligned UB), missing negative
     discriminant `-1`, empty-tagger niche variant through an aligned raw
     pointer without provenance (succeeds with zero accesses: nothing is
     stored, so the missing provenance never matters), and out-of-bounds
     tagger offset (`ptr_offset_inbounds` UB);
  8. Concrete Tree Borrows per-byte aliasing witnesses on `MachTB`:
     `SetDiscriminant` through a `Frozen` pointer raises
     `"Tree Borrows: local write of Frozen reference"`, while a pointer that is
     `Unique` on tag bytes `{0, 4, 5}` and `Frozen` on payload bytes
     `{1, 2, 3, 6, 7}` succeeds (confirming only tag bytes are accessed). -/
theorem minirust_setDiscriminant_supported :
    (∀ (m : Mach) (dst : Gen.PlaceExpr) (value : Int) (e : Interp.Stop),
      Interp.evalPlace m dst = .error e →
      Interp.evalStatement m (.SetDiscriminant dst value) = .error e) ∧
    (∀ (m m1 : Mach) (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place BM) (ty : Gen.Type),
      Interp.evalPlace m dst = .ok ((place, ty), m1) →
      (∀ (vs : Map Int Gen.Variant) dt d sz al, ty ≠ .Enum vs dt d sz al) →
      Interp.evalStatement m (.SetDiscriminant dst value) =
        .error (.specPanic
          "setting the discriminant type of a non-enum contradicts well-formedness")) ∧
    (∀ (m m1 : Mach) (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place BM)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align),
      Interp.evalPlace m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      (place.aligned = false →
        Interp.evalStatement m (.SetDiscriminant dst value) =
          .error (.ub "setting the discriminant of a place based on a misaligned pointer")) ∧
      (place.aligned = true → mapGet vs value = none →
        Interp.evalStatement m (.SetDiscriminant dst value) =
          .error (.specPanic s!"setting an invalid discriminant ({value})")) ∧
      (∀ vTy, place.aligned = true → mapGet vs value = some ⟨vTy, ⟨[]⟩⟩ →
        Interp.evalStatement m (.SetDiscriminant dst value) = .ok m1)) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (m : Gen.Machine M)
        (dst : Gen.PlaceExpr) (value : Int) (e : Interp.Stop),
      Interp.evalPlaceM m dst = .error e →
      Interp.evalStatementM m (.SetDiscriminant dst value) = .error e) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (m m1 : Gen.Machine M)
        (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place M) (ty : Gen.Type),
      Interp.evalPlaceM m dst = .ok ((place, ty), m1) →
      (∀ (vs : Map Int Gen.Variant) dt d sz al, ty ≠ .Enum vs dt d sz al) →
      Interp.evalStatementM m (.SetDiscriminant dst value) =
        .error (.specPanic
          "setting the discriminant type of a non-enum contradicts well-formedness")) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (m m1 : Gen.Machine M)
        (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place M)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align),
      Interp.evalPlaceM m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      (place.aligned = false →
        Interp.evalStatementM m (.SetDiscriminant dst value) =
          .error (.ub "setting the discriminant of a place based on a misaligned pointer")) ∧
      (place.aligned = true → mapGet vs value = none →
        Interp.evalStatementM m (.SetDiscriminant dst value) =
          .error (.specPanic s!"setting an invalid discriminant ({value})")) ∧
      (∀ vTy, place.aligned = true → mapGet vs value = some ⟨vTy, ⟨[]⟩⟩ →
        Interp.evalStatementM m (.SetDiscriminant dst value) = .ok m1)) ∧
    (let fnEnum := uwFn [(⟨⟨1⟩⟩, sdEnumTy)]
     let allocBM : Gen.Allocation Unit Unit :=
       { data := sdPayloadBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true,
         extra := () }
     let frBM : Frame :=
       { func := fnEnum, locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]⟩,
         stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
     let mBM := uwMachBM [allocBM] [frBM] []
     let rootAllUnique : Gen.Node :=
       { children := [], permissions := List.replicate 8 (.Unprot .Unique), «protected» := .No }
     let rootAllFrozen : Gen.Node :=
       { children := [], permissions := List.replicate 8 (.Unprot .Frozen), «protected» := .No }
     let rootTagOnlyUnique : Gen.Node :=
       { children := []
         permissions :=
           [.Unprot .Unique, .Unprot .Frozen, .Unprot .Frozen, .Unprot .Frozen,
            .Unprot .Unique, .Unprot .Unique, .Unprot .Frozen, .Unprot .Frozen]
         «protected» := .No }
     let mkAllocTB (r : Gen.Node) : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
       { data := sdPayloadBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true,
         extra := { root := r } }
     let frTB : Gen.StackFrame TBM :=
       { func := fnEnum, locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩)]⟩,
         stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
     let mTB := uwMachTB [mkAllocTB rootAllUnique] [frTB] []
     let mTBFrozen := uwMachTB [mkAllocTB rootAllFrozen] [frTB] []
     let mTBTagOnly := uwMachTB [mkAllocTB rootTagOnlyUnique] [frTB] []
     let loc : Gen.PlaceExpr := .Local ⟨⟨1⟩⟩
     let misalignEnum : Gen.PlaceExpr := .Deref (uwRawThinPtrExpr 0x101) sdEnumTy
     let misalignNonEnum : Gen.PlaceExpr := .Deref (uwRawThinPtrExpr 0x101) (.Int u32)
     let noProvAlignedEnum : Gen.PlaceExpr := .Deref (uwRawThinPtrExpr 0x100) sdEnumTy
     let expectedAccs : List Gen.Access :=
       [⟨.Store, .None, 0x100, ⟨1⟩⟩, ⟨.Store, .None, 0x104, ⟨2⟩⟩]
     let disc : Gen.Discriminator :=
       .Branch ⟨0⟩ u8 .Invalid
         ⟨[((3, 4), .Branch ⟨4⟩ u16 .Invalid ⟨[((0x5678, 0x5679), .Known 7)]⟩)]⟩
     (∃ m', Interp.evalStatement mBM (.SetDiscriminant loc 7) = .ok m' ∧
       m'.mem.memory.allocations.map (·.data) = [sdExpectedBytes] ∧
       m'.mem.accesses = expectedAccs ∧
       Interp.decodeDiscriminant
         (fun _ off sz => do pure (← subsliceWithLength sdExpectedBytes off.bytes sz.bytes, ()))
         disc () = .ok (some 7, ())) ∧
     (∃ m', Interp.evalStatementM mTB (.SetDiscriminant loc 7) = .ok m' ∧
       m'.mem.memory.mem.allocations.map (·.data) = [sdExpectedBytes] ∧
       m'.mem.accesses = expectedAccs) ∧
     (Interp.evalStatement mBM (.SetDiscriminant misalignEnum 99) =
       .error (.ub "setting the discriminant of a place based on a misaligned pointer") ∧
      Interp.evalStatement mBM (.SetDiscriminant misalignNonEnum 7) =
       .error (.specPanic
         "setting the discriminant type of a non-enum contradicts well-formedness") ∧
      Interp.evalStatement mBM (.SetDiscriminant loc (-1)) =
       .error (.specPanic "setting an invalid discriminant (-1)") ∧
      Interp.evalStatement mBM (.SetDiscriminant noProvAlignedEnum 8) = .ok mBM ∧
      Interp.evalStatement mBM (.SetDiscriminant loc 9) =
       .error (.ub "dereferencing pointer outside the bounds of its allocation")) ∧
     (Interp.evalStatementM mTB (.SetDiscriminant misalignEnum 99) =
       .error (.ub "setting the discriminant of a place based on a misaligned pointer") ∧
      Interp.evalStatementM mTB (.SetDiscriminant misalignNonEnum 7) =
       .error (.specPanic
         "setting the discriminant type of a non-enum contradicts well-formedness") ∧
      Interp.evalStatementM mTB (.SetDiscriminant loc (-1)) =
       .error (.specPanic "setting an invalid discriminant (-1)") ∧
      Interp.evalStatementM mTB (.SetDiscriminant noProvAlignedEnum 8) = .ok mTB ∧
      Interp.evalStatementM mTB (.SetDiscriminant loc 9) =
       .error (.ub "dereferencing pointer outside the bounds of its allocation")) ∧
     (Interp.evalStatementM mTBFrozen (.SetDiscriminant loc 7) =
       .error (.ub "Tree Borrows: local write of Frozen reference") ∧
      ∃ m', Interp.evalStatementM mTBTagOnly (.SetDiscriminant loc 7) = .ok m' ∧
        m'.mem.memory.mem.allocations.map (·.data) = [sdExpectedBytes])) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨_, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, _, rfl, rfl⟩⟩
  · intro m dst value e herr
    simp [Interp.evalStatement, Interp.evalSetDiscriminant, herr, error_bind]
  · intro m m1 dst value place ty hp hne
    simp only [Interp.evalStatement, Interp.evalSetDiscriminant, hp, ok_bind]
    cases ty with
    | Enum vs dt d sz al => exact absurd rfl (hne vs dt d sz al)
    | Int _ => rfl
    | Bool => rfl
    | Ptr _ => rfl
    | Tuple _ _ _ => rfl
    | Array _ _ => rfl
    | Slice _ => rfl
    | Union _ _ _ _ => rfl
    | TraitObject _ => rfl
  · intro m m1 dst value place vs dt d sz al hp
    refine ⟨fun hna => ?_, fun ha hnone => ?_, fun vTy ha hsome => ?_⟩
    · simp [Interp.evalStatement, Interp.evalSetDiscriminant, hp, hna, ub]
    · simp [Interp.evalStatement, Interp.evalSetDiscriminant, hp, ha, hnone, specPanic]
    · simp [Interp.evalStatement, Interp.evalSetDiscriminant, hp, ha, hsome,
        Interp.encodeDiscriminant]
  · intro M _ _ m dst value e herr
    simp [Interp.evalStatementM, Interp.evalSetDiscriminantM, herr, error_bind]
  · intro M _ _ m m1 dst value place ty hp hne
    simp only [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, ok_bind]
    cases ty with
    | Enum vs dt d sz al => exact absurd rfl (hne vs dt d sz al)
    | Int _ => rfl
    | Bool => rfl
    | Ptr _ => rfl
    | Tuple _ _ _ => rfl
    | Array _ _ => rfl
    | Slice _ => rfl
    | Union _ _ _ _ => rfl
    | TraitObject _ => rfl
  · intro M _ _ m m1 dst value place vs dt d sz al hp
    refine ⟨fun hna => ?_, fun ha hnone => ?_, fun vTy ha hsome => ?_⟩
    · simp [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, hna, ub]
    · simp [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, ha, hnone, specPanic]
    · simp [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, ha, hsome,
        Interp.encodeDiscriminantM]

/-- An enum whose variants list their tags in an order that differs from the
order of the tag offsets: variant `1` lists the tag at offset `4` before the
tag at offset `0`, and variants `2` and `3` each pair an out-of-bounds tag
(offset `16` in an 8-byte enum) with an in-bounds tag (offset `0`), in
opposite orders. -/
private def sdOrderEnumTy : Gen.Type :=
  let mk (tagger : List (Gen.Offset × (Gen.IntType × Int))) : Gen.Variant :=
    { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none, tagger := ⟨tagger⟩ }
  .Enum
    ⟨[(1, mk [(⟨4⟩, (u16, 0x5678)), (⟨0⟩, (u8, 0x03))]),
      (2, mk [(⟨16⟩, (u8, 1)), (⟨0⟩, (u8, 0x03))]),
      (3, mk [(⟨0⟩, (u8, 0x03)), (⟨16⟩, (u8, 1))])]⟩
    u8 .Invalid ⟨8⟩ ⟨4⟩

/-- **`Statement::SetDiscriminant` writes its tags in `tagger.entries` order
(`minirust_setDiscriminant_tagger_order`)**: the witnesses of
`minirust_setDiscriminant_supported` list their tags by ascending offset, so
they cannot tell the order of the entries from the order of the offsets.
Here the two differ:
1. on `Mach` and `MachTB`, a variant listing the `u16` tag at offset `4`
   before the `u8` tag at offset `0` produces the same bytes, but records its
   two `Store` accesses as `0x104` then `0x100`: entry order, not address
   order;
2. on `MachTB` through an all-`Frozen` pointer, where both the out-of-bounds
   tag and the in-bounds tag fail, the tag listed first decides the UB: the
   bounds error of `ptr_offset_inbounds` when the out-of-bounds tag comes
   first, the Tree Borrows write error when the in-bounds tag comes first.
   So the reported `Stop` is that of the first failing entry in list
   order. -/
theorem minirust_setDiscriminant_tagger_order :
    let fnEnum := uwFn [(⟨⟨1⟩⟩, sdOrderEnumTy)]
    let allocBM : Gen.Allocation Unit Unit :=
      { data := sdPayloadBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true,
        extra := () }
    let frBM : Frame :=
      { func := fnEnum, locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]⟩,
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
    let mBM := uwMachBM [allocBM] [frBM] []
    let mkAllocTB (perm : Gen.Permission) :
        Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
      { data := sdPayloadBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true,
        extra :=
          { root :=
              { children := [], permissions := List.replicate 8 perm, «protected» := .No } } }
    let frTB : Gen.StackFrame TBM :=
      { func := fnEnum, locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩)]⟩,
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
    let mTB := uwMachTB [mkAllocTB (.Unprot .Unique)] [frTB] []
    let mTBFrozen := uwMachTB [mkAllocTB (.Unprot .Frozen)] [frTB] []
    let loc : Gen.PlaceExpr := .Local ⟨⟨1⟩⟩
    let entryOrderAccs : List Gen.Access :=
      [⟨.Store, .None, 0x104, ⟨2⟩⟩, ⟨.Store, .None, 0x100, ⟨1⟩⟩]
    (∃ m', Interp.evalStatement mBM (.SetDiscriminant loc 1) = .ok m' ∧
      m'.mem.memory.allocations.map (·.data) = [sdExpectedBytes] ∧
      m'.mem.accesses = entryOrderAccs) ∧
    (∃ m', Interp.evalStatementM mTB (.SetDiscriminant loc 1) = .ok m' ∧
      m'.mem.memory.mem.allocations.map (·.data) = [sdExpectedBytes] ∧
      m'.mem.accesses = entryOrderAccs) ∧
    (Interp.evalStatementM mTBFrozen (.SetDiscriminant loc 2) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
     Interp.evalStatementM mTBFrozen (.SetDiscriminant loc 3) =
      .error (.ub "Tree Borrows: local write of Frozen reference")) :=
  ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The `Store` access that `SetDiscriminant` records for one tagger entry of
a place whose pointer has address `base`: it starts at the entry's offset from
`base` and is as long as the entry's integer type. -/
private def sdTagAccess (base : Int) (e : Gen.Offset × (Gen.IntType × Int)) : Gen.Access :=
  ⟨.Store, .None, base + (e.1.bytes : Int), ⟨e.2.1.size.bytes⟩⟩

/-- `Type.encodeInt` at `ity` yields exactly `ity.size.bytes` bytes. -/
private theorem encodeInt_length {ity : Gen.IntType} {v : Val} {bytes : List Byte}
    (h : Interp.Type.encodeInt ity v = .ok bytes) : bytes.length = ity.size.bytes := by
  obtain ⟨signed, size⟩ := ity
  cases v with
  | Int i =>
    simp only [Interp.Type.encodeInt] at h
    cases henc : Interp.Endianness.encode Interp.x86_64.ENDIANNESS signed size i with
    | none => simp [henc, specPanic] at h
    | some data =>
      simp only [henc, pure_ok, Except.ok.injEq] at h
      subst h
      simp only [Interp.Endianness.encode] at henc
      split at henc
      · simp only [Option.some.injEq] at henc
        subst henc
        simp [Interp.x86_64.ENDIANNESS, leBytes_length]
      · cases henc
  | _ => simp [Interp.Type.encodeInt, specPanic] at h

/-- Polymorphic `Type.encodeIntM` at `ity` yields exactly `ity.size.bytes`
bytes. -/
private theorem encodeIntM_length {M : Type} [Gen.Memory M] {ity : Gen.IntType}
    {v : Gen.Value M} {bytes : List (Gen.AbstractByte (Gen.Memory.Provenance M))}
    (h : Interp.Type.encodeIntM (M := M) ity v = .ok bytes) :
    bytes.length = ity.size.bytes := by
  obtain ⟨signed, size⟩ := ity
  cases v with
  | Int i =>
    simp only [Interp.Type.encodeIntM] at h
    cases henc : Interp.Endianness.encode Interp.x86_64.ENDIANNESS signed size i with
    | none => simp [henc, specPanic] at h
    | some data =>
      simp only [henc, pure_ok, Except.ok.injEq] at h
      subst h
      simp only [Interp.Endianness.encode] at henc
      split at henc
      · simp only [Option.some.injEq] at henc
        subst henc
        simp [Interp.x86_64.ENDIANNESS, leBytes_length]
      · cases henc
  | _ => simp [Interp.Type.encodeIntM, specPanic] at h

/-- When every accessor call changes only `mem` and appends one `Store` of the
written bytes at its offset from `base`, `encodeDiscriminant` changes only
`mem` and appends one such `Store` per tagger entry, in entry order. -/
private theorem encodeDiscriminant_accesses
    {acc : Mach → Gen.Offset → List Byte → Interp Mach} (base : Int)
    (hacc : ∀ s offset bytes s', acc s offset bytes = .ok s' →
      (∃ cm, s' = { s with mem := cm }) ∧
      s'.mem.accesses = s.mem.accesses ++
        [⟨.Store, .None, base + (offset.bytes : Int), ⟨bytes.length⟩⟩])
    (tagger : Map Gen.Offset (Gen.IntType × Int)) {s s' : Mach}
    (h : Interp.encodeDiscriminant acc tagger s = .ok s') :
    (∃ cm, s' = { s with mem := cm }) ∧
    s'.mem.accesses = s.mem.accesses ++ tagger.entries.map (sdTagAccess base) := by
  unfold Interp.encodeDiscriminant at h
  generalize tagger.entries = entries at h ⊢
  induction entries generalizing s with
  | nil =>
    cases h
    exact ⟨⟨_, rfl⟩, by simp⟩
  | cons e es ih =>
    obtain ⟨offset, valueType, value⟩ := e
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := interpBind_ok h
    obtain ⟨bytes, henc, h1⟩ := interpBind_ok h1
    obtain ⟨⟨cm1, rfl⟩, hacc1⟩ := hacc _ _ _ _ h1
    obtain ⟨⟨cm2, rfl⟩, hacc2⟩ := ih h
    refine ⟨⟨cm2, rfl⟩, ?_⟩
    rw [hacc2, hacc1, encodeInt_length henc]
    simp [sdTagAccess]

/-- Polymorphic counterpart of `encodeDiscriminant_accesses`. -/
private theorem encodeDiscriminantM_accesses {M : Type} [Gen.Memory M]
    {acc : Gen.Machine M → Gen.Offset → List (Gen.AbstractByte (Gen.Memory.Provenance M)) →
      Interp (Gen.Machine M)} (base : Int)
    (hacc : ∀ s offset bytes s', acc s offset bytes = .ok s' →
      (∃ cm, s' = { s with mem := cm }) ∧
      s'.mem.accesses = s.mem.accesses ++
        [⟨.Store, .None, base + (offset.bytes : Int), ⟨bytes.length⟩⟩])
    (tagger : Map Gen.Offset (Gen.IntType × Int)) {s s' : Gen.Machine M}
    (h : Interp.encodeDiscriminantM (M := M) acc tagger s = .ok s') :
    (∃ cm, s' = { s with mem := cm }) ∧
    s'.mem.accesses = s.mem.accesses ++ tagger.entries.map (sdTagAccess base) := by
  unfold Interp.encodeDiscriminantM at h
  generalize tagger.entries = entries at h ⊢
  induction entries generalizing s with
  | nil =>
    cases h
    exact ⟨⟨_, rfl⟩, by simp⟩
  | cons e es ih =>
    obtain ⟨offset, valueType, value⟩ := e
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := interpBind_ok h
    obtain ⟨bytes, henc, h1⟩ := interpBind_ok h1
    obtain ⟨⟨cm1, rfl⟩, hacc1⟩ := hacc _ _ _ _ h1
    obtain ⟨⟨cm2, rfl⟩, hacc2⟩ := ih h
    refine ⟨⟨cm2, rfl⟩, ?_⟩
    rw [hacc2, hacc1, encodeIntM_length henc]
    simp [sdTagAccess]

/-- **`Statement::SetDiscriminant` stores exactly the tags, in entry order
(`minirust_setDiscriminant_accesses_law`)**: the concrete witnesses show on
particular enums that only tag bytes are written. This is the general
statement, for every machine, place, and enum type, on `Mach` and on
polymorphic `Machine M` (`MachTB`): whenever `SetDiscriminant` succeeds on an
aligned enum place with variant `value`,
- the machine differs from the one `eval_place` returned only in `mem`, and
- the access log grows by exactly one non-atomic `Store` per entry of the
  variant's `tagger`, in the order of `tagger.entries`, each starting at the
  entry's offset from the place and as long as the entry's integer type.

So `SetDiscriminant` issues no load and no store outside the tag ranges, and
never touches threads, frames, or the payload stack. The law is about which
stores are issued. That a tag range is disjoint from the bytes of the
variant's fields is a well-formedness property of the enum type, which
`SetDiscriminant` does not check: the stores listed here are issued whether
or not a tag range overlaps a field. -/
theorem minirust_setDiscriminant_accesses_law :
    (∀ (m m1 m' : Mach) (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place BM)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align) (variant : Gen.Variant),
      Interp.evalPlace m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      place.aligned = true → mapGet vs value = some variant →
      Interp.evalStatement m (.SetDiscriminant dst value) = .ok m' →
      (∃ cm, m' = { m1 with mem := cm }) ∧
      m'.mem.accesses = m1.mem.accesses ++
        variant.tagger.entries.map (sdTagAccess place.ptr.thin_pointer.addr)) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (m m1 m' : Gen.Machine M)
        (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place M)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align) (variant : Gen.Variant),
      Interp.evalPlaceM m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      place.aligned = true → mapGet vs value = some variant →
      Interp.evalStatementM m (.SetDiscriminant dst value) = .ok m' →
      (∃ cm, m' = { m1 with mem := cm }) ∧
      m'.mem.accesses = m1.mem.accesses ++
        variant.tagger.entries.map (sdTagAccess place.ptr.thin_pointer.addr)) := by
  refine ⟨?_, ?_⟩
  · intro m m1 m' dst value place vs dt d sz al variant hp ha hsome h
    simp only [Interp.evalStatement, Interp.evalSetDiscriminant, hp, ok_bind, ha,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsome] at h
    refine encodeDiscriminant_accesses place.ptr.thin_pointer.addr
      (fun s offset bytes s' hs => ?_) variant.tagger h
    obtain ⟨ptr, hptr, hs⟩ := interpBind_ok hs
    obtain ⟨cm, hst, hs⟩ := interpBind_ok hs
    cases hs
    have haddr : ptr.addr = place.ptr.thin_pointer.addr + (offset.bytes : Int) := by
      unfold Interp.ptrOffsetInbounds at hptr
      obtain ⟨_, _, hptr⟩ := interpBind_ok hptr
      split at hptr
      · cases hptr
      · split at hptr
        · cases hptr
        · cases hptr
          rfl
    have hlog : cm.accesses = s.mem.accesses ++ [⟨.Store, .None, ptr.addr, ⟨bytes.length⟩⟩] := by
      unfold Interp.CM.store at hst
      obtain ⟨_, _, hst⟩ := interpBind_ok hst
      cases hst
      rfl
    exact ⟨⟨cm, rfl⟩, by rw [hlog, haddr]⟩
  · intro M _ _ m m1 m' dst value place vs dt d sz al variant hp ha hsome h
    simp only [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, ok_bind, ha,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsome] at h
    refine encodeDiscriminantM_accesses place.ptr.thin_pointer.addr
      (fun s offset bytes s' hs => ?_) variant.tagger h
    obtain ⟨ptr, hptr, hs⟩ := interpBind_ok hs
    obtain ⟨cm, hst, hs⟩ := interpBind_ok hs
    cases hs
    have haddr : ptr.addr = place.ptr.thin_pointer.addr + (offset.bytes : Int) := by
      unfold Interp.ptrOffsetInboundsM at hptr
      obtain ⟨_, _, hptr⟩ := interpBind_ok hptr
      split at hptr
      · cases hptr
      · split at hptr
        · cases hptr
        · cases hptr
          rfl
    have hlog : cm.accesses = s.mem.accesses ++ [⟨.Store, .None, ptr.addr, ⟨bytes.length⟩⟩] := by
      unfold Interp.ConcurrentMemory.store at hst
      obtain ⟨_, _, hst⟩ := interpBind_ok hst
      cases hst
      rfl
    exact ⟨⟨cm, rfl⟩, by rw [hlog, haddr]⟩

/-- Whether byte index `k` of an allocation at `allocAddr` lies inside the byte
range written by tagger entry `e` for a place at address `base`. -/
private def sdInTagRange (base allocAddr : Int)
    (e : Gen.Offset × (Gen.IntType × Int)) (k : Nat) : Prop :=
  base + (e.1.bytes : Int) ≤ allocAddr + (k : Int) ∧
    allocAddr + (k : Int) < base + (e.1.bytes : Int) + (e.2.1.size.bytes : Int)

/-- `writeSubsliceAtIndex` preserves list length and every element outside
`[start, start + src.length)`, and writes `src[i]` at `start + i`. -/
private theorem writeSubsliceAtIndex_spec {T : Type} {xs src xs' : List T} {start : Int}
    (h : Interp.writeSubsliceAtIndex xs start src = .ok xs') :
    0 ≤ start ∧
    start.toNat + src.length ≤ xs.length ∧
    xs'.length = xs.length ∧
    (∀ k : Nat, k < start.toNat ∨ start.toNat + src.length ≤ k → xs'[k]? = xs[k]?) ∧
    (∀ i : Nat, i < src.length → xs'[start.toNat + i]? = src[i]?) := by
  unfold Interp.writeSubsliceAtIndex at h
  split at h
  · rename_i hcond
    cases h
    have hle : start.toNat + src.length ≤ xs.length := by omega
    have htake : (xs.take start.toNat).length = start.toNat :=
      List.length_take_of_le (by omega)
    refine ⟨hcond.1, hle, ?_, ?_, ?_⟩
    · simp only [List.length_append, htake, List.length_drop]
      omega
    · intro k hk
      rcases hk with hlt | hge
      · rw [List.getElem?_append_left (by simp only [List.length_append, htake]; omega)]
        rw [List.getElem?_append_left (by rw [htake]; exact hlt)]
        exact List.getElem?_take_of_lt hlt
      · rw [List.getElem?_append_right (by simp only [List.length_append, htake]; exact hge)]
        simp only [List.length_append, htake, List.getElem?_drop]
        congr 1
        omega
    · intro i hi
      rw [List.getElem?_append_left (by simp only [List.length_append, htake]; omega)]
      rw [List.getElem?_append_right (by rw [htake]; omega)]
      rw [htake]
      simp
  · cases h

/-- Single-store frame and write law for `BM.store`: preserves allocation
count, every non-target allocation verbatim, target metadata, and every byte
outside `[ptr.addr, ptr.addr + bytes.length)`, and writes `bytes` in range. -/
private theorem bmStore_frame {mem mem' : BM} {ptr : Ptr} {bytes : List Byte}
    {align : LibSpecr.Align} (h : Interp.BM.store mem ptr bytes align = .ok mem') :
    mem'.allocations.length = mem.allocations.length ∧
    (∀ j : Nat, ptr.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
      mem'.allocations[j]? = mem.allocations[j]?) ∧
    (∀ (j : Nat) (a a' : Gen.Allocation Unit Unit),
      mem.allocations[j]? = some a → mem'.allocations[j]? = some a' →
      a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
      a'.data.length = a.data.length ∧
      (∀ k : Nat, ¬(ptr.addr ≤ a.addr + (k : Int) ∧
          a.addr + (k : Int) < ptr.addr + (bytes.length : Int)) →
        a'.data[k]? = a.data[k]?)) ∧
    (0 < bytes.length →
      ∃ (aid : Gen.AllocId) (pex : Unit) (a a' : Gen.Allocation Unit Unit),
        ptr.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
        mem.allocations[aid._0.toNat]? = some a ∧
        mem'.allocations[aid._0.toNat]? = some a' ∧
        0 ≤ ptr.addr - a.addr ∧
        ∀ i : Nat, i < bytes.length →
          a'.data[(ptr.addr - a.addr).toNat + i]? = bytes[i]?) := by
  unfold Interp.BM.store at h
  split at h
  · cases h
  · obtain ⟨chk, hchk, h⟩ := interpBind_ok h
    cases chk with
    | none =>
      cases h
      refine ⟨rfl, fun _ _ => rfl,
        fun j a a' ha ha' => by
          rw [ha] at ha'
          cases ha'
          exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
        fun hpos => ?_⟩
      unfold Interp.BM.check_ptr at hchk
      split at hchk
      · rename_i hzero
        simp only at hzero
        omega
      · cases hprov : ptr.provenance with
        | none => simp [hprov, ub] at hchk
        | some pp =>
          simp only [hprov] at hchk
          obtain ⟨a, _, hchk⟩ := interpBind_ok hchk
          split at hchk
          · cases hchk
          · split at hchk <;> cases hchk
    | some res =>
      obtain ⟨aid, pex, offset⟩ := res
      obtain ⟨a0, hidx, h⟩ := interpBind_ok h
      obtain ⟨data', hws, h⟩ := interpBind_ok h
      obtain ⟨allocs', hset, h⟩ := interpBind_ok h
      cases h
      unfold Interp.BM.check_ptr at hchk
      split at hchk
      · cases hchk
      · cases hprov : ptr.provenance with
        | none => simp [hprov, ub] at hchk
        | some pp =>
          obtain ⟨aid', pex'⟩ := pp
          simp only [hprov] at hchk
          obtain ⟨aChk, hidxChk, hchk⟩ := interpBind_ok hchk
          split at hchk
          · cases hchk
          · split at hchk
            · cases hchk
            · rename_i hnotoob
              cases hchk
              obtain ⟨hgeId, hget0⟩ := listIndex_ok_get hidx
              obtain ⟨_, hgetChk⟩ := listIndex_ok_get hidxChk
              rw [hget0] at hgetChk
              cases hgetChk
              unfold listSet at hset
              split at hset
              · rename_i hsetcond
                cases hset
                obtain ⟨_, _, hLenEq, hOut, hIn⟩ := writeSubsliceAtIndex_spec hws
                have htoNat :
                    (({ bytes := (ptr.addr - a0.addr).toNat } : LibSpecr.Size).bytes : Int).toNat =
                      (ptr.addr - a0.addr).toNat := rfl
                rw [htoNat] at hOut hIn
                have hoffGe : 0 ≤ ptr.addr - a0.addr :=
                  Int.not_lt.mp (fun hlt => hnotoob (Or.inl hlt))
                refine ⟨List.length_set, ?_, ?_, ?_⟩
                · intro j hne
                  have hij : aid._0.toNat ≠ j := by
                    intro heq
                    apply hne
                    simp only [Option.map_some, Option.some.injEq]
                    cases aid
                    simp only at hgeId heq ⊢
                    congr 1
                    omega
                  exact List.getElem?_set_ne hij
                · intro j a a' ha ha'
                  by_cases hij : aid._0.toNat = j
                  · subst hij
                    rw [hget0] at ha
                    cases ha
                    rw [List.getElem?_set_self hsetcond.2] at ha'
                    cases ha'
                    refine ⟨rfl, rfl, rfl, rfl, hLenEq, fun k hk => ?_⟩
                    let pa : Int := ptr.addr
                    let aa : Int := a0.addr
                    have hge0 : (0 : Int) ≤ pa - aa := hoffGe
                    have hk' : ¬(pa ≤ aa + (k : Int) ∧
                        aa + (k : Int) < pa + (bytes.length : Int)) := hk
                    have hko : k < (pa - aa).toNat ∨ (pa - aa).toNat + bytes.length ≤ k := by
                      omega
                    exact hOut k hko
                  · rw [List.getElem?_set_ne hij, ha] at ha'
                    cases ha'
                    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
                · intro _
                  refine ⟨aid, pex, a0, { a0 with data := data' }, rfl, hgeId, hget0,
                    List.getElem?_set_self hsetcond.2, hoffGe, fun i hi => hIn i hi⟩
              · cases hset

/-- Single-store frame and write law for polymorphic `BasicMemory.store`
(applied below to `TreeBorrowsMemory.store`): preserves allocation count, every
non-target allocation verbatim (including `extra`), target metadata, and every
byte outside `[ptr.addr, ptr.addr + bytes.length)`, and writes `bytes`. -/
private theorem basicMemoryStore_frame {ProvExtra AllocExtra : Type}
    {mem mem' : Gen.BasicMemory Gen.x86_64 ProvExtra AllocExtra}
    {ptr : Gen.ThinPointer (Gen.Provenance ProvExtra)}
    {bytes : List (Gen.AbstractByte (Gen.Provenance ProvExtra))}
    {align : LibSpecr.Align}
    {handleExtra : AllocExtra → ProvExtra → Gen.Offset → Interp AllocExtra}
    (h : Interp.BasicMemory.store mem ptr bytes align handleExtra = .ok mem') :
    mem'.allocations.length = mem.allocations.length ∧
    (∀ j : Nat, ptr.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
      mem'.allocations[j]? = mem.allocations[j]?) ∧
    (∀ (j : Nat) (a a' : Gen.Allocation ProvExtra AllocExtra),
      mem.allocations[j]? = some a → mem'.allocations[j]? = some a' →
      a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
      a'.data.length = a.data.length ∧
      (∀ k : Nat, ¬(ptr.addr ≤ a.addr + (k : Int) ∧
          a.addr + (k : Int) < ptr.addr + (bytes.length : Int)) →
        a'.data[k]? = a.data[k]?)) ∧
    (0 < bytes.length →
      ∃ (aid : Gen.AllocId) (pex : ProvExtra)
          (a a' : Gen.Allocation ProvExtra AllocExtra),
        ptr.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
        mem.allocations[aid._0.toNat]? = some a ∧
        mem'.allocations[aid._0.toNat]? = some a' ∧
        0 ≤ ptr.addr - a.addr ∧
        ∀ i : Nat, i < bytes.length →
          a'.data[(ptr.addr - a.addr).toNat + i]? = bytes[i]?) := by
  unfold Interp.BasicMemory.store at h
  split at h
  · cases h
  · obtain ⟨chk, hchk, h⟩ := interpBind_ok h
    cases chk with
    | none =>
      cases h
      refine ⟨rfl, fun _ _ => rfl,
        fun j a a' ha ha' => by
          rw [ha] at ha'
          cases ha'
          exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
        fun hpos => ?_⟩
      unfold Interp.BasicMemory.check_ptr at hchk
      split at hchk
      · rename_i hzero
        simp only at hzero
        omega
      · cases hprov : ptr.provenance with
        | none => simp [hprov, ub] at hchk
        | some pp =>
          simp only [hprov] at hchk
          obtain ⟨a, _, hchk⟩ := interpBind_ok hchk
          split at hchk
          · cases hchk
          · split at hchk <;> cases hchk
    | some res =>
      obtain ⟨aid, pex, offset⟩ := res
      obtain ⟨a0, hidx, h⟩ := interpBind_ok h
      obtain ⟨extra', _, h⟩ := interpBind_ok h
      obtain ⟨data', hws, h⟩ := interpBind_ok h
      obtain ⟨allocs', hset, h⟩ := interpBind_ok h
      cases h
      unfold Interp.BasicMemory.check_ptr at hchk
      split at hchk
      · cases hchk
      · cases hprov : ptr.provenance with
        | none => simp [hprov, ub] at hchk
        | some pp =>
          obtain ⟨aid', pex'⟩ := pp
          simp only [hprov] at hchk
          obtain ⟨aChk, hidxChk, hchk⟩ := interpBind_ok hchk
          split at hchk
          · cases hchk
          · split at hchk
            · cases hchk
            · rename_i hnotoob
              cases hchk
              obtain ⟨hgeId, hget0⟩ := listIndex_ok_get hidx
              obtain ⟨_, hgetChk⟩ := listIndex_ok_get hidxChk
              rw [hget0] at hgetChk
              cases hgetChk
              unfold listSet at hset
              split at hset
              · rename_i hsetcond
                cases hset
                obtain ⟨_, _, hLenEq, hOut, hIn⟩ := writeSubsliceAtIndex_spec hws
                have htoNat :
                    (({ bytes := (ptr.addr - a0.addr).toNat } : LibSpecr.Size).bytes : Int).toNat =
                      (ptr.addr - a0.addr).toNat := rfl
                rw [htoNat] at hOut hIn
                have hoffGe : 0 ≤ ptr.addr - a0.addr :=
                  Int.not_lt.mp (fun hlt => hnotoob (Or.inl hlt))
                refine ⟨List.length_set, ?_, ?_, ?_⟩
                · intro j hne
                  have hij : aid._0.toNat ≠ j := by
                    intro heq
                    apply hne
                    simp only [Option.map_some, Option.some.injEq]
                    cases aid
                    simp only at hgeId heq ⊢
                    congr 1
                    omega
                  exact List.getElem?_set_ne hij
                · intro j a a' ha ha'
                  by_cases hij : aid._0.toNat = j
                  · subst hij
                    rw [hget0] at ha
                    cases ha
                    rw [List.getElem?_set_self hsetcond.2] at ha'
                    cases ha'
                    refine ⟨rfl, rfl, rfl, rfl, hLenEq, fun k hk => ?_⟩
                    let pa : Int := ptr.addr
                    let aa : Int := a0.addr
                    have hge0 : (0 : Int) ≤ pa - aa := hoffGe
                    have hk' : ¬(pa ≤ aa + (k : Int) ∧
                        aa + (k : Int) < pa + (bytes.length : Int)) := hk
                    have hko : k < (pa - aa).toNat ∨ (pa - aa).toNat + bytes.length ≤ k := by
                      omega
                    exact hOut k hko
                  · rw [List.getElem?_set_ne hij, ha] at ha'
                    cases ha'
                    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
                · intro _
                  refine ⟨aid, pex, a0, { a0 with data := data', extra := extra' }, rfl, hgeId,
                    hget0, List.getElem?_set_self hsetcond.2, hoffGe, fun i hi => hIn i hi⟩
              · cases hset

/-- Inductive memory-frame and tag-write law for `encodeDiscriminant` on
`Mach`. -/
private theorem encodeDiscriminant_memory_frame (p : Ptr)
    (tagger : Map Gen.Offset (Gen.IntType × Int)) {s s' : Mach}
    (h : Interp.encodeDiscriminant
      (fun (m : Mach) offset bytes => do
        let ptr ← Interp.ptrOffsetInbounds m p (offset.bytes : Int)
        let cm ← Interp.CM.store m.mem ptr bytes ⟨1⟩ .None
        pure { m with mem := cm }) tagger s = .ok s') :
    s'.mem.memory.allocations.length = s.mem.memory.allocations.length ∧
    (∀ j : Nat, p.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
      s'.mem.memory.allocations[j]? = s.mem.memory.allocations[j]?) ∧
    (∀ (j : Nat) (a a' : Gen.Allocation Unit Unit),
      s.mem.memory.allocations[j]? = some a →
      s'.mem.memory.allocations[j]? = some a' →
      a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
      a'.data.length = a.data.length ∧
      (∀ k : Nat, (∀ e ∈ tagger.entries, ¬ sdInTagRange p.addr a.addr e k) →
        a'.data[k]? = a.data[k]?)) ∧
    (∀ pre off ity val post, tagger.entries = pre ++ (off, (ity, val)) :: post →
      ∃ bytes, Interp.Type.encodeInt ity (.Int val) = .ok bytes ∧
        (0 < ity.size.bytes →
          ∃ (aid : Gen.AllocId) (pex : Unit) (a a' : Gen.Allocation Unit Unit),
            p.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
            s.mem.memory.allocations[aid._0.toNat]? = some a ∧
            s'.mem.memory.allocations[aid._0.toNat]? = some a' ∧
            0 ≤ p.addr + (off.bytes : Int) - a.addr ∧
            ∀ i : Nat, i < bytes.length →
              (∀ e' ∈ post,
                ¬ sdInTagRange p.addr a.addr e'
                  ((p.addr + (off.bytes : Int) - a.addr).toNat + i)) →
              a'.data[(p.addr + (off.bytes : Int) - a.addr).toNat + i]? = bytes[i]?)) := by
  unfold Interp.encodeDiscriminant at h
  generalize tagger.entries = entries at h ⊢
  induction entries generalizing s with
  | nil =>
    cases h
    refine ⟨rfl, fun _ _ => rfl,
      fun j a a' ha ha' => by
        rw [ha] at ha'
        cases ha'
        exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun pre off ity val post hsplit => by
        cases pre <;> simp at hsplit⟩
  | cons e0 es ih =>
    obtain ⟨off0, ity0, val0⟩ := e0
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := interpBind_ok h
    obtain ⟨bytes0, henc0, h1⟩ := interpBind_ok h1
    obtain ⟨ptr0, hptr0, h1⟩ := interpBind_ok h1
    obtain ⟨cm1, hcm1, h1⟩ := interpBind_ok h1
    cases h1
    have hptrEq : ptr0 = { p with addr := p.addr + (off0.bytes : Int) } := by
      unfold Interp.ptrOffsetInbounds at hptr0
      obtain ⟨_, _, hptr0⟩ := interpBind_ok hptr0
      split at hptr0
      · cases hptr0
      · split at hptr0
        · cases hptr0
        · cases hptr0
          rfl
    subst hptrEq
    unfold Interp.CM.store at hcm1
    obtain ⟨mem1, hst1, hcm1⟩ := interpBind_ok hcm1
    cases hcm1
    obtain ⟨hlen1, hother1, hmeta1, hwr1⟩ := bmStore_frame hst1
    obtain ⟨hlen2, hother2, hmeta2, hwr2⟩ := ih h
    have hblen0 : bytes0.length = ity0.size.bytes := encodeInt_length henc0
    refine ⟨hlen2.trans hlen1,
      fun j hj => (hother2 j hj).trans (hother1 j hj),
      ?_, ?_⟩
    · intro j a a' ha ha'
      have hjlt : j < mem1.allocations.length := by
        rw [hlen1]
        exact (List.getElem?_eq_some_iff.mp ha).1
      let a1 := mem1.allocations[j]
      have ha1 : mem1.allocations[j]? = some a1 := List.getElem?_eq_getElem hjlt
      obtain ⟨haddr1, hal1, hk1, hl1, hd1, hout1⟩ := hmeta1 j a a1 ha ha1
      obtain ⟨haddr2, hal2, hk2, hl2, hd2, hout2⟩ := hmeta2 j a1 a' ha1 ha'
      refine ⟨haddr2.trans haddr1, hal2.trans hal1, hk2.trans hk1, hl2.trans hl1, hd2.trans hd1,
        fun k hk => ?_⟩
      have hk0 : ¬(p.addr + (off0.bytes : Int) ≤ a.addr + (k : Int) ∧
          a.addr + (k : Int) < p.addr + (off0.bytes : Int) + (bytes0.length : Int)) := by
        rw [hblen0]
        exact hk (off0, (ity0, val0)) (by simp)
      have hkes : ∀ e ∈ es, ¬ sdInTagRange p.addr a1.addr e k := by
        intro e he
        rw [haddr1]
        exact hk e (by simp [he])
      exact (hout2 k hkes).trans (hout1 k hk0)
    · intro pre off ity val post hsplit
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hsplit
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hsplit
        refine ⟨bytes0, henc0, fun hpos => ?_⟩
        obtain ⟨aid, pex, a, a1, hprov, hgeId, ha, ha1, hoffGe, hbytes1⟩ :=
          hwr1 (by omega)
        have hidlt : aid._0.toNat < s'.mem.memory.allocations.length := by
          rw [hlen2]
          exact (List.getElem?_eq_some_iff.mp ha1).1
        let a' := s'.mem.memory.allocations[aid._0.toNat]
        have ha' : s'.mem.memory.allocations[aid._0.toNat]? = some a' :=
          List.getElem?_eq_getElem hidlt
        obtain ⟨haddr1, _, _, _, _, _⟩ := hmeta1 aid._0.toNat a a1 ha ha1
        obtain ⟨_, _, _, _, _, hout2⟩ := hmeta2 aid._0.toNat a1 a' ha1 ha'
        refine ⟨aid, pex, a, a', hprov, hgeId, ha, ha', hoffGe, fun i hi hnotpost => ?_⟩
        have hpost1 : ∀ e' ∈ es,
            ¬ sdInTagRange p.addr a1.addr e' ((p.addr + (off0.bytes : Int) - a.addr).toNat + i) :=
          fun e' he' => by rw [haddr1]; exact hnotpost e' he'
        exact (hout2 _ hpost1).trans (hbytes1 i hi)
      | cons e0' pre' =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, htail⟩ := hsplit
        obtain ⟨bytes, henc, hrest⟩ := hwr2 pre' off ity val post htail
        refine ⟨bytes, henc, fun hpos => ?_⟩
        obtain ⟨aid, pex, a1, a', hprov, hgeId, ha1, ha', hoffGe, hbytes2⟩ := hrest hpos
        have hidlt : aid._0.toNat < s.mem.memory.allocations.length := by
          rw [← hlen1]
          exact (List.getElem?_eq_some_iff.mp ha1).1
        let a := s.mem.memory.allocations[aid._0.toNat]
        have ha : s.mem.memory.allocations[aid._0.toNat]? = some a :=
          List.getElem?_eq_getElem hidlt
        obtain ⟨haddr1, _, _, _, _, _⟩ := hmeta1 aid._0.toNat a a1 ha ha1
        refine ⟨aid, pex, a, a', hprov, hgeId, ha, ha', by rw [← haddr1]; exact hoffGe,
          fun i hi hnotpost => ?_⟩
        simpa [haddr1] using hbytes2 i hi (by simpa [haddr1] using hnotpost)

/-- Inductive memory-frame and tag-write law for `encodeDiscriminantM` on
`MachTB` (`TreeBorrowsMemory`). -/
private theorem encodeDiscriminantM_tb_memory_frame
    (p : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (tagger : Map Gen.Offset (Gen.IntType × Int)) {s s' : MachTB}
    (h : Interp.encodeDiscriminantM (M := TBM)
      (fun (m : MachTB) offset bytes => do
        let ptr ← Interp.ptrOffsetInboundsM m p (offset.bytes : Int)
        let cm ← Interp.ConcurrentMemory.store m.mem ptr bytes ⟨1⟩ .None
        pure { m with mem := cm }) tagger s = .ok s') :
    s'.mem.memory.params = s.mem.memory.params ∧
    s'.mem.memory.mem.allocations.length = s.mem.memory.mem.allocations.length ∧
    (∀ j : Nat, p.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
      s'.mem.memory.mem.allocations[j]? = s.mem.memory.mem.allocations[j]?) ∧
    (∀ (j : Nat) (a a' : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
      s.mem.memory.mem.allocations[j]? = some a →
      s'.mem.memory.mem.allocations[j]? = some a' →
      a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
      a'.data.length = a.data.length ∧
      (∀ k : Nat, (∀ e ∈ tagger.entries, ¬ sdInTagRange p.addr a.addr e k) →
        a'.data[k]? = a.data[k]?)) ∧
    (∀ pre off ity val post, tagger.entries = pre ++ (off, (ity, val)) :: post →
      ∃ bytes, Interp.Type.encodeIntM (M := TBM) ity (.Int val) = .ok bytes ∧
        (0 < ity.size.bytes →
          ∃ (aid : Gen.AllocId) (pex : Gen.Path)
              (a a' : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
            p.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
            s.mem.memory.mem.allocations[aid._0.toNat]? = some a ∧
            s'.mem.memory.mem.allocations[aid._0.toNat]? = some a' ∧
            0 ≤ p.addr + (off.bytes : Int) - a.addr ∧
            ∀ i : Nat, i < bytes.length →
              (∀ e' ∈ post,
                ¬ sdInTagRange p.addr a.addr e'
                  ((p.addr + (off.bytes : Int) - a.addr).toNat + i)) →
              a'.data[(p.addr + (off.bytes : Int) - a.addr).toNat + i]? = bytes[i]?)) := by
  unfold Interp.encodeDiscriminantM at h
  generalize tagger.entries = entries at h ⊢
  induction entries generalizing s with
  | nil =>
    cases h
    refine ⟨rfl, rfl, fun _ _ => rfl,
      fun j a a' ha ha' => by
        rw [ha] at ha'
        cases ha'
        exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun pre off ity val post hsplit => by
        cases pre <;> simp at hsplit⟩
  | cons e0 es ih =>
    obtain ⟨off0, ity0, val0⟩ := e0
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := interpBind_ok h
    obtain ⟨bytes0, henc0, h1⟩ := interpBind_ok h1
    obtain ⟨ptr0, hptr0, h1⟩ := interpBind_ok h1
    obtain ⟨cm1, hcm1, h1⟩ := interpBind_ok h1
    cases h1
    have hptrEq : ptr0 = { p with addr := p.addr + (off0.bytes : Int) } := by
      unfold Interp.ptrOffsetInboundsM at hptr0
      obtain ⟨_, _, hptr0⟩ := interpBind_ok hptr0
      split at hptr0
      · cases hptr0
      · split at hptr0
        · cases hptr0
        · cases hptr0
          rfl
    subst hptrEq
    unfold Interp.ConcurrentMemory.store at hcm1
    obtain ⟨tbm1, htbm1, hcm1⟩ := interpBind_ok hcm1
    cases hcm1
    change Interp.TreeBorrowsMemory.store s.mem.memory
      { p with addr := p.addr + (off0.bytes : Int) } bytes0 ⟨1⟩ = .ok tbm1 at htbm1
    unfold Interp.TreeBorrowsMemory.store at htbm1
    obtain ⟨mem1, hst1, htbm1⟩ := interpBind_ok htbm1
    cases htbm1
    obtain ⟨hlen1, hother1, hmeta1, hwr1⟩ := basicMemoryStore_frame hst1
    obtain ⟨hpar2, hlen2, hother2, hmeta2, hwr2⟩ := ih h
    have hblen0 : bytes0.length = ity0.size.bytes := encodeIntM_length henc0
    refine ⟨hpar2, hlen2.trans hlen1,
      fun j hj => (hother2 j hj).trans (hother1 j hj),
      ?_, ?_⟩
    · intro j a a' ha ha'
      have hjlt : j < mem1.allocations.length := by
        rw [hlen1]
        exact (List.getElem?_eq_some_iff.mp ha).1
      let a1 := mem1.allocations[j]
      have ha1 : mem1.allocations[j]? = some a1 := List.getElem?_eq_getElem hjlt
      obtain ⟨haddr1, hal1, hk1, hl1, hd1, hout1⟩ := hmeta1 j a a1 ha ha1
      obtain ⟨haddr2, hal2, hk2, hl2, hd2, hout2⟩ := hmeta2 j a1 a' ha1 ha'
      refine ⟨haddr2.trans haddr1, hal2.trans hal1, hk2.trans hk1, hl2.trans hl1, hd2.trans hd1,
        fun k hk => ?_⟩
      have hk0 : ¬(p.addr + (off0.bytes : Int) ≤ a.addr + (k : Int) ∧
          a.addr + (k : Int) < p.addr + (off0.bytes : Int) + (bytes0.length : Int)) := by
        rw [hblen0]
        exact hk (off0, (ity0, val0)) (by simp)
      have hkes : ∀ e ∈ es, ¬ sdInTagRange p.addr a1.addr e k := by
        intro e he
        rw [haddr1]
        exact hk e (by simp [he])
      exact (hout2 k hkes).trans (hout1 k hk0)
    · intro pre off ity val post hsplit
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hsplit
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hsplit
        refine ⟨bytes0, henc0, fun hpos => ?_⟩
        obtain ⟨aid, pex, a, a1, hprov, hgeId, ha, ha1, hoffGe, hbytes1⟩ :=
          hwr1 (by omega)
        have hidlt : aid._0.toNat < s'.mem.memory.mem.allocations.length := by
          rw [hlen2]
          exact (List.getElem?_eq_some_iff.mp ha1).1
        let a' := s'.mem.memory.mem.allocations[aid._0.toNat]
        have ha' : s'.mem.memory.mem.allocations[aid._0.toNat]? = some a' :=
          List.getElem?_eq_getElem hidlt
        obtain ⟨haddr1, _, _, _, _, _⟩ := hmeta1 aid._0.toNat a a1 ha ha1
        obtain ⟨_, _, _, _, _, hout2⟩ := hmeta2 aid._0.toNat a1 a' ha1 ha'
        refine ⟨aid, pex, a, a', hprov, hgeId, ha, ha', hoffGe, fun i hi hnotpost => ?_⟩
        have hpost1 : ∀ e' ∈ es,
            ¬ sdInTagRange p.addr a1.addr e' ((p.addr + (off0.bytes : Int) - a.addr).toNat + i) :=
          fun e' he' => by rw [haddr1]; exact hnotpost e' he'
        exact (hout2 _ hpost1).trans (hbytes1 i hi)
      | cons e0' pre' =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, htail⟩ := hsplit
        obtain ⟨bytes, henc, hrest⟩ := hwr2 pre' off ity val post htail
        refine ⟨bytes, henc, fun hpos => ?_⟩
        obtain ⟨aid, pex, a1, a', hprov, hgeId, ha1, ha', hoffGe, hbytes2⟩ := hrest hpos
        have hidlt : aid._0.toNat < s.mem.memory.mem.allocations.length := by
          rw [← hlen1]
          exact (List.getElem?_eq_some_iff.mp ha1).1
        let a := s.mem.memory.mem.allocations[aid._0.toNat]
        have ha : s.mem.memory.mem.allocations[aid._0.toNat]? = some a :=
          List.getElem?_eq_getElem hidlt
        obtain ⟨haddr1, _, _, _, _, _⟩ := hmeta1 aid._0.toNat a a1 ha ha1
        refine ⟨aid, pex, a, a', hprov, hgeId, ha, ha', by rw [← haddr1]; exact hoffGe,
          fun i hi hnotpost => ?_⟩
        simpa [haddr1] using hbytes2 i hi (by simpa [haddr1] using hnotpost)

/-- **Universal memory-contents and allocation-frame law for
`Statement::SetDiscriminant` on `Mach` and `MachTB`
(`minirust_setDiscriminant_memory_frame_law`)**: whereas
`minirust_setDiscriminant_accesses_law` characterizes only the concurrency
access log (`mem.accesses`), this theorem characterizes the actual memory state
produced by any successful `SetDiscriminant` on any aligned enum place, for
both `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`):
1. Allocation count (and `TreeBorrowsMemory.params` on `MachTB`) is preserved;
2. Every allocation whose `AllocId` is not `place.ptr.thin_pointer`'s
   provenance is preserved verbatim (including all bytes and, on `MachTB`, its
   entire Tree Borrows borrow tree); if the pointer carries no provenance, all
   allocations are preserved verbatim;
3. Every allocation preserves `addr`, `align`, `kind`, `live`, and
   `data.length`, and every byte index `k` outside every entry of
   `variant.tagger.entries` (`¬ sdInTagRange`) is preserved unchanged;
4. For every tagger entry `(off, (ity, val))` in `variant.tagger.entries =
   pre ++ (off, (ity, val)) :: post`, `Type.encodeInt` / `Type.encodeIntM`
   succeeds with `bytes`, and whenever `0 < ity.size.bytes` and no later entry
   in `post` covers byte `(base + off - a.addr) + i`, the resulting allocation
   holds `bytes[i]?` at that byte (exact last-write-wins tag semantics, and
   exact simultaneous tag bytes whenever tag ranges are pairwise disjoint).

Every clause compares against `m1`, the machine that `eval_place` returned
for `destination`, and not against the machine the statement started from:
evaluating `destination` can itself load from memory (the pointer operand of
a `Deref`), which is recorded in the access log and, on `MachTB`, is a read
access to a borrow tree. In clause 4, `base` is the address of the place and
`a` is the allocation that its provenance names. On `MachTB` the borrow tree
of that one allocation is outside this law: every tag store is a write access
that may update it, so for that allocation the law covers the bytes and the
listed metadata only. -/
theorem minirust_setDiscriminant_memory_frame_law :
    (∀ (m m1 m' : Mach) (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place BM)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align) (variant : Gen.Variant),
      Interp.evalPlace m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      place.aligned = true → mapGet vs value = some variant →
      Interp.evalStatement m (.SetDiscriminant dst value) = .ok m' →
      m'.mem.memory.allocations.length = m1.mem.memory.allocations.length ∧
      (∀ j : Nat, place.ptr.thin_pointer.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
        m'.mem.memory.allocations[j]? = m1.mem.memory.allocations[j]?) ∧
      (∀ (j : Nat) (a a' : Gen.Allocation Unit Unit),
        m1.mem.memory.allocations[j]? = some a →
        m'.mem.memory.allocations[j]? = some a' →
        a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
        a'.data.length = a.data.length ∧
        (∀ k : Nat,
          (∀ e ∈ variant.tagger.entries,
            ¬ sdInTagRange place.ptr.thin_pointer.addr a.addr e k) →
          a'.data[k]? = a.data[k]?)) ∧
      (∀ pre off ity val post,
        variant.tagger.entries = pre ++ (off, (ity, val)) :: post →
        ∃ bytes, Interp.Type.encodeInt ity (.Int val) = .ok bytes ∧
          (0 < ity.size.bytes →
            ∃ (aid : Gen.AllocId) (pex : Unit) (a a' : Gen.Allocation Unit Unit),
              place.ptr.thin_pointer.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
              m1.mem.memory.allocations[aid._0.toNat]? = some a ∧
              m'.mem.memory.allocations[aid._0.toNat]? = some a' ∧
              0 ≤ place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr ∧
              ∀ i : Nat, i < bytes.length →
                (∀ e' ∈ post,
                  ¬ sdInTagRange place.ptr.thin_pointer.addr a.addr e'
                    ((place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr).toNat + i)) →
                a'.data[(place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr).toNat + i]? =
                  bytes[i]?))) ∧
    (∀ (m m1 m' : MachTB) (dst : Gen.PlaceExpr) (value : Int) (place : Gen.Place TBM)
        (vs : Map Int Gen.Variant) (dt : Gen.IntType) (d : Gen.Discriminator)
        (sz : LibSpecr.Size) (al : LibSpecr.Align) (variant : Gen.Variant),
      Interp.evalPlaceM m dst = .ok ((place, .Enum vs dt d sz al), m1) →
      place.aligned = true → mapGet vs value = some variant →
      Interp.evalStatementM m (.SetDiscriminant dst value) = .ok m' →
      m'.mem.memory.params = m1.mem.memory.params ∧
      m'.mem.memory.mem.allocations.length = m1.mem.memory.mem.allocations.length ∧
      (∀ j : Nat, place.ptr.thin_pointer.provenance.map Prod.fst ≠ some ⟨(j : Int)⟩ →
        m'.mem.memory.mem.allocations[j]? = m1.mem.memory.mem.allocations[j]?) ∧
      (∀ (j : Nat) (a a' : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
        m1.mem.memory.mem.allocations[j]? = some a →
        m'.mem.memory.mem.allocations[j]? = some a' →
        a'.addr = a.addr ∧ a'.align = a.align ∧ a'.kind = a.kind ∧ a'.live = a.live ∧
        a'.data.length = a.data.length ∧
        (∀ k : Nat,
          (∀ e ∈ variant.tagger.entries,
            ¬ sdInTagRange place.ptr.thin_pointer.addr a.addr e k) →
          a'.data[k]? = a.data[k]?)) ∧
      (∀ pre off ity val post,
        variant.tagger.entries = pre ++ (off, (ity, val)) :: post →
        ∃ bytes, Interp.Type.encodeIntM (M := TBM) ity (.Int val) = .ok bytes ∧
          (0 < ity.size.bytes →
            ∃ (aid : Gen.AllocId) (pex : Gen.Path)
                (a a' : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra),
              place.ptr.thin_pointer.provenance = some (aid, pex) ∧ 0 ≤ aid._0 ∧
              m1.mem.memory.mem.allocations[aid._0.toNat]? = some a ∧
              m'.mem.memory.mem.allocations[aid._0.toNat]? = some a' ∧
              0 ≤ place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr ∧
              ∀ i : Nat, i < bytes.length →
                (∀ e' ∈ post,
                  ¬ sdInTagRange place.ptr.thin_pointer.addr a.addr e'
                    ((place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr).toNat + i)) →
                a'.data[(place.ptr.thin_pointer.addr + (off.bytes : Int) - a.addr).toNat + i]? =
                  bytes[i]?))) := by
  refine ⟨?_, ?_⟩
  · intro m m1 m' dst value place vs dt d sz al variant hp ha hsome h
    simp only [Interp.evalStatement, Interp.evalSetDiscriminant, hp, ok_bind, ha,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsome] at h
    exact encodeDiscriminant_memory_frame place.ptr.thin_pointer variant.tagger h
  · intro m m1 m' dst value place vs dt d sz al variant hp ha hsome h
    simp only [Interp.evalStatementM, Interp.evalSetDiscriminantM, hp, ok_bind, ha,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsome] at h
    exact encodeDiscriminantM_tb_memory_frame place.ptr.thin_pointer variant.tagger h

/-- **`ResumeUnwind` propagates a failing frame teardown
(`minirust_resumeUnwind_teardown_error`)**: this closes the case analysis of
`minirust_unwind_terminators_supported`, whose `ResumeUnwind` clauses assume
that `deallocAll` / `deallocAllM` succeeded. When `storage_dead` of a local of
the popped frame stops (for example with Tree Borrows UB on a strongly
protected local), `ResumeUnwind` stops with that same `Stop`. On `Machine M`
this is before `end_call` runs, and on both machines it is before
`stack_pop_action` is inspected, so a failing teardown preempts the UB of
unwinding out of the bottom of the stack and of a missing unwind block. -/
theorem minirust_resumeUnwind_teardown_error :
    (∀ (m : Mach) (t : Gen.Thread BM) (fr : Frame) (e : Interp.Stop),
      Interp.activeThread m = .ok t → t.stack.getLast? = some fr →
      Interp.deallocAll fr.locals.entries.length fr m.mem = .error e →
      Interp.evalTerminator m .ResumeUnwind = .error e) ∧
    (∀ {M : Type} [Gen.Memory M] [Interp.MemoryOps M] (mM : Gen.Machine M)
        (t : Gen.Thread M) (fr : Gen.StackFrame M) (e : Interp.Stop),
      Interp.activeThreadM mM = .ok t → t.stack.getLast? = some fr →
      Interp.deallocAllM fr.locals.entries.length fr mM.mem = .error e →
      Interp.evalTerminatorM mM .ResumeUnwind = .error e) := by
  refine ⟨?_, ?_⟩
  · intro m t fr e ht hfr hdealloc
    obtain ⟨hge, hget⟩ := listIndex_ok_get ht
    have hlt : m.active_thread.toNat < m.threads.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    simp only [Interp.evalTerminator, Interp.evalResumeUnwind]
    rw [ht]
    simp only [ok_bind, hfr, pure_ok, listSet, hge, hlt, and_self, ↓reduceIte, hdealloc,
      error_bind]
  · intro M _ _ mM t fr e ht hfr hdealloc
    obtain ⟨hge, hget⟩ := listIndex_ok_get ht
    have hlt : mM.active_thread.toNat < mM.threads.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    simp only [Interp.evalTerminatorM, Interp.evalResumeUnwindM]
    rw [ht]
    simp only [ok_bind, hfr, pure_ok, listSet, hge, hlt, and_self, ↓reduceIte, hdealloc,
      error_bind]

/-- Callee of `minirust_unwind_setDiscriminant_step_witness`: its entry block
brings an enum local to life, sets its discriminant, and starts unwinding into
the cleanup block, which resumes unwinding in the caller. -/
private def uwStepCalleeFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8), (⟨⟨1⟩⟩, sdEnumTy)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[.StorageLive ⟨⟨1⟩⟩, .SetDiscriminant (.Local ⟨⟨1⟩⟩) 7],
        .StartUnwind (uwRawThinPtrExpr 0x1000) ⟨⟨1⟩⟩, .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

/-- Caller of `minirust_unwind_setDiscriminant_step_witness`: it calls
`uwStepCalleeFn` with return block `1` and unwind block `2`; the unwind block
is a catch block that stops unwinding and continues in block `3`. -/
private def uwStepCallerFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[], .Call (fnPtrExpr (fnName 1)) .Rust [] (.Local ⟨⟨0⟩⟩)
        (some ⟨⟨1⟩⟩) (some ⟨⟨2⟩⟩), .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .Unreachable, .Regular⟩),
      (⟨⟨2⟩⟩, ⟨[], .StopUnwind ⟨⟨3⟩⟩, .Catch⟩),
      (⟨⟨3⟩⟩, ⟨[], .Unreachable, .Regular⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwStepProg : Gen.Program :=
  { functions := ⟨[(fnName 0, uwStepCallerFn), (fnName 1, uwStepCalleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

/-- `uwStepCallerFn` about to execute its `Call`, on `Mach`: one thread, one
frame, and the caller's `u8` return place live at `0x100`. -/
private def uwStepMachBM : Mach :=
  { uwMachBM [uwLiveStackAllocBM 0x100]
      [{ func := uwStepCallerFn, locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]⟩,
         stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0,
         extra := () }]
      [] with
    prog := uwStepProg
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩)]⟩ }

/-- `uwStepCallerFn` about to execute its `Call`, on `MachTB`: exact Tree
Borrows counterpart of `uwStepMachBM`, starting at the caller's `Call` with
only the caller's live `u8` return place at `0x100`. -/
private def uwStepMachTB : MachTB :=
  { uwMachTB [uwLiveAllocTB 0x100 .Stack (uwRootWithChildren [])]
      [{ func := uwStepCallerFn, locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩)]⟩,
         stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0,
         extra := ⟨[]⟩ }]
      [] with
    prog := uwStepProg
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩)]⟩ }

/-- Extract the `Stop` error from an `Interp` result so kernel `decide` can
check error outcomes without needing `DecidableEq` on the success type. -/
private def interpStopOf {α : Type} (r : Interp α) : Option Interp.Stop :=
  match r with
  | .error e => some e
  | .ok _ => none

private theorem eq_error_of_interpStopOf {α : Type} {r : Interp α} {e : Interp.Stop}
    (h : interpStopOf r = some e) : r = .error e := by
  cases r with
  | ok _ => cases h
  | error err => cases h; rfl

/-- The enum local of `uwStepCalleeFn` after `SetDiscriminant`: fresh storage
is uninitialized, and only the three tag bytes have been written. -/
private def uwStepEnumBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0x03 none, .Uninit, .Uninit, .Uninit,
   .Init 0x78 none, .Init 0x56 none, .Uninit, .Uninit]

/-- **Unwinding and `SetDiscriminant` through `Machine::step` on both `Mach`
and `MachTB` from the caller's `Call`
(`minirust_unwind_setDiscriminant_step_witness`)**: a two-function program runs
from the caller's `Call` through all 7 steps (`Call`, `StorageLive`,
`SetDiscriminant`, `StartUnwind`, `ResumeUnwind`, `StopUnwind`, `Unreachable`)
under both `Interp.steps` (`Mach`) and `Interp.stepsTB` (`MachTB`), so the new
statement and terminators are reached through the block lookup, program-counter
updates, real `Call`/`StorageLive` allocation, and data-race check of `step`.
Below, `pcs` is the `(next_block, next_stmt)` of every frame, bottom frame
first.
- after 3 steps (`Call`, `StorageLive`, `SetDiscriminant`) the callee's enum
  local holds exactly its three tag bytes and the callee is at statement `2`
  of its entry block;
- after 4 steps (`StartUnwind`) the payload stack is `[0x1000]`, the callee
  is in its cleanup block, and all three allocations are still live;
- after 5 steps (`ResumeUnwind`) the callee frame is gone, both of its locals
  are dead, the payload is still on the payload stack, and the caller is at
  the unwind block `2` named by its `Call`, not at the return block `1`;
- after 6 steps (`StopUnwind`) the payload stack is empty and the caller is
  in block `3`;
- the 7th step reaches the `Unreachable` of block `3`, so execution continued
  in the caller after the catch block. -/
theorem minirust_unwind_setDiscriminant_step_witness :
    let pcsBM (m : Mach) :=
      m.threads.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))
    let pcsTB (m : MachTB) :=
      m.threads.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))
    let payload : Ptr := ⟨0x1000, none⟩
    let payloadTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, none⟩
    ((Interp.steps 3 uwStepMachBM).toOption.map
          (fun m => (m.mem.memory.allocations.map (·.data), pcsBM m)) =
        some ([[.Uninit], [.Uninit], uwStepEnumBytes], [[(⟨⟨0⟩⟩, 0), (⟨⟨0⟩⟩, 2)]]) ∧
      (Interp.steps 4 uwStepMachBM).toOption.map
          (fun m => (m.threads.map (·.unwind_payloads), pcsBM m,
            m.mem.memory.allocations.map (·.live))) =
        some ([[payload]], [[(⟨⟨0⟩⟩, 0), (⟨⟨1⟩⟩, 0)]], [true, true, true]) ∧
      (Interp.steps 5 uwStepMachBM).toOption.map
          (fun m => (m.threads.map (·.unwind_payloads), pcsBM m,
            m.mem.memory.allocations.map (·.live))) =
        some ([[payload]], [[(⟨⟨2⟩⟩, 0)]], [true, false, false]) ∧
      (Interp.steps 6 uwStepMachBM).toOption.map
          (fun m => (m.threads.map (·.unwind_payloads), pcsBM m)) =
        some ([[]], [[(⟨⟨3⟩⟩, 0)]]) ∧
      Interp.steps 7 uwStepMachBM = .error (.ub "reached unreachable code")) ∧
    ((Interp.stepsTB 3 uwStepMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations.map (·.data)) =
        some [[.Uninit], [.Uninit], uwStepEnumBytes] ∧
      (Interp.stepsTB 3 uwStepMachTB).toOption.map pcsTB =
        some [[(⟨⟨0⟩⟩, 0), (⟨⟨0⟩⟩, 2)]] ∧
      (Interp.stepsTB 4 uwStepMachTB).toOption.map (fun m => m.threads.map (·.unwind_payloads)) =
        some [[payloadTB]] ∧
      (Interp.stepsTB 4 uwStepMachTB).toOption.map pcsTB =
        some [[(⟨⟨0⟩⟩, 0), (⟨⟨1⟩⟩, 0)]] ∧
      (Interp.stepsTB 4 uwStepMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations.map (·.live)) =
        some [true, true, true] ∧
      (Interp.stepsTB 5 uwStepMachTB).toOption.map (fun m => m.threads.map (·.unwind_payloads)) =
        some [[payloadTB]] ∧
      (Interp.stepsTB 5 uwStepMachTB).toOption.map pcsTB =
        some [[(⟨⟨2⟩⟩, 0)]] ∧
      (Interp.stepsTB 5 uwStepMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations.map (·.live)) =
        some [true, false, false] ∧
      (Interp.stepsTB 6 uwStepMachTB).toOption.map (fun m => m.threads.map (·.unwind_payloads)) =
        some [[]] ∧
      (Interp.stepsTB 6 uwStepMachTB).toOption.map pcsTB =
        some [[(⟨⟨3⟩⟩, 0)]] ∧
      Interp.stepsTB 7 uwStepMachTB = .error (.ub "reached unreachable code")) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, eq_error_of_interpStopOf (by decide +kernel)⟩⟩

private def uwProtRefPtrTy : Gen.PtrType :=
  .Ref .Immutable ⟨.Sized ⟨1⟩ ⟨1⟩, true, .Sized [], true, true⟩

private def uwProtCalleeFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8), (⟨⟨1⟩⟩, .Ptr uwProtRefPtrTy), (⟨⟨2⟩⟩, sdEnumTy)]⟩
    args := [⟨⟨1⟩⟩]
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[
          .Validate (.Local ⟨⟨1⟩⟩) true,
          .StorageLive ⟨⟨2⟩⟩,
          .SetDiscriminant (.Local ⟨⟨2⟩⟩) 7],
        .StartUnwind (uwRawThinPtrExpr 0x1000) ⟨⟨1⟩⟩, .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwProtCallerFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8), (⟨⟨1⟩⟩, .Int u8)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[],
        .Call (fnPtrExpr (fnName 1)) .Rust
          [.ByValue (.AddrOf (.Local ⟨⟨1⟩⟩) uwProtRefPtrTy)]
          (.Local ⟨⟨0⟩⟩) (some ⟨⟨1⟩⟩) (some ⟨⟨2⟩⟩), .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .Unreachable, .Regular⟩),
      (⟨⟨2⟩⟩, ⟨[], .StopUnwind ⟨⟨3⟩⟩, .Catch⟩),
      (⟨⟨3⟩⟩, ⟨[.Assign (.Local ⟨⟨1⟩⟩) (.Constant (.Int 0x63) (.Int u8))],
        .Unreachable, .Regular⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwProtProg : Gen.Program :=
  { functions := ⟨[(fnName 0, uwProtCallerFn), (fnName 1, uwProtCalleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

private def uwProtMachTB : MachTB :=
  let mkAlloc (addr : Int) (b : UInt8) :
      Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
    { data := [.Init b none]
      addr := addr
      align := ⟨1⟩
      kind := .Stack
      live := true
      extra := { root := uwRootWithChildren [] } }
  { uwMachTB [mkAlloc 0x100 0x00, mkAlloc 0x200 0x2A]
      [{ func := uwProtCallerFn
         locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]⟩
         stack_pop_action := .BottomOfStack
         next_block := ⟨⟨0⟩⟩
         next_stmt := 0
         extra := ⟨[]⟩ }]
      [] with
    prog := uwProtProg
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩)]⟩ }

private def uwAlloc1ProtStatus (m : MachTB) : Option (Gen.Protected × List Gen.Permission) :=
  m.mem.memory.mem.allocations[1]?.bind fun a =>
    a.extra.root.children[0]?.bind fun c0 =>
      c0.children[0]?.map fun c00 => (c00.«protected», c00.permissions)

/-- **End-to-end `MachTB` Tree Borrows protector lifecycle across `Call`,
`Validate`, `SetDiscriminant`, `StartUnwind`, `ResumeUnwind`, and `StopUnwind`
(`minirust_tb_call_validate_unwind_protector_step_witness`)**: runs a 9-step
program through `Interp.stepsTB` starting at the caller's `Call` passing
`&_1 : &u8`:
1. After 2 steps (`Call`, `Validate (.Local _1) true`), callee's
   `frame.extra.protectors` holds `(⟨1⟩, [0, 0])` and that borrow-tree node is
   `.Strong` / `[.Prot (.Frozen true)]`.
2. Negative control at step 2: writing to `_1` through caller's root provenance
   while the protector is active raises Tree Borrows foreign-write UB on the
   protected `Frozen` reference.
3. After 4 steps (`StorageLive`, `SetDiscriminant`), the callee's enum local
   holds `uwStepEnumBytes`.
4. After 6 steps (`StartUnwind`, `ResumeUnwind`), all three callee locals are
   dead (`[true, true, false, false, false]`), `TreeBorrowsMemory.end_call`
   releases the protector to `.No` / `[.Unprot .Frozen]`, `unwind_payloads`
   retains `[0x1000]`, and the caller stands at unwind block `2`.
5. After 8 steps (`StopUnwind`, caller `Assign _1 0x63`), mutating `_1` through
   caller's root provenance succeeds (`[.Init 0x63 none]`, child `[0, 0]` now
   `.No` / `[.Unprot .Disabled]`), proving `ResumeUnwind` released the
   protector, and step 9 hits `Unreachable`. -/
theorem minirust_tb_call_validate_unwind_protector_step_witness :
    let payloadTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, none⟩
    ((Interp.stepsTB 2 uwProtMachTB).toOption.map (fun m =>
        m.threads.map (fun t => t.stack.map (fun f => f.extra.protectors))) =
      some [[[], [(⟨1⟩, [0, 0])]]]) ∧
    ((Interp.stepsTB 2 uwProtMachTB).toOption.map uwAlloc1ProtStatus =
      some (some (.Strong, [.Prot (.Frozen true)]))) ∧
    ((Interp.stepsTB 2 uwProtMachTB) >>= fun m =>
        Interp.ConcurrentMemory.store m.mem ⟨0x200, some (⟨1⟩, [])⟩ [.Init 0x63 none] ⟨1⟩ .None) =
      .error (.ub
        "Tree Borrows: foreign write of protected Frozen reference which had a local read") ∧
    ((Interp.stepsTB 4 uwProtMachTB).toOption.map (fun m =>
        m.mem.memory.mem.allocations[4]?.map (·.data)) =
      some (some uwStepEnumBytes)) ∧
    ((Interp.stepsTB 6 uwProtMachTB).toOption.map (fun m =>
        m.mem.memory.mem.allocations.map (·.live)) =
      some [true, true, false, false, false]) ∧
    ((Interp.stepsTB 6 uwProtMachTB).toOption.map uwAlloc1ProtStatus =
      some (some (.No, [.Unprot .Frozen]))) ∧
    ((Interp.stepsTB 6 uwProtMachTB).toOption.map (fun m =>
        m.threads.map (·.unwind_payloads)) =
      some [[payloadTB]]) ∧
    ((Interp.stepsTB 6 uwProtMachTB).toOption.map (fun m =>
        m.threads.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))) =
      some [[(⟨⟨2⟩⟩, 0)]]) ∧
    ((Interp.stepsTB 8 uwProtMachTB).toOption.map (fun m =>
        m.mem.memory.mem.allocations[1]?.map (·.data)) =
      some (some [.Init 0x63 none])) ∧
    ((Interp.stepsTB 8 uwProtMachTB).toOption.map uwAlloc1ProtStatus =
      some (some (.No, [.Unprot .Disabled]))) ∧
    (Interp.stepsTB 9 uwProtMachTB = .error (.ub "reached unreachable code")) := by
  refine ⟨by decide +kernel, by decide +kernel,
    eq_error_of_interpStopOf (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, eq_error_of_interpStopOf (by decide +kernel)⟩

/-- Innermost function of `minirust_nested_unwind_step_witness`: it starts
unwinding at once and resumes it from its cleanup block. -/
private def uwNestInnerFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[], .StartUnwind (uwRawThinPtrExpr 0x1000) ⟨⟨1⟩⟩, .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

/-- Middle function of `minirust_nested_unwind_step_witness`: it calls
`uwNestInnerFn` with unwind block `2`, a cleanup block that only resumes
unwinding into its own caller. -/
private def uwNestMiddleFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[], .Call (fnPtrExpr (fnName 2)) .Rust [] (.Local ⟨⟨0⟩⟩)
        (some ⟨⟨1⟩⟩) (some ⟨⟨2⟩⟩), .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .Unreachable, .Regular⟩),
      (⟨⟨2⟩⟩, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

/-- Outermost function of `minirust_nested_unwind_step_witness`: it calls
`uwNestMiddleFn` with unwind block `2`, a catch block that reads the unwind
payload into the raw-pointer local `_1` and then, in block `3`, stops
unwinding and continues in block `4`. -/
private def uwNestOuterFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8), (⟨⟨1⟩⟩, .Ptr (.Raw .None))]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[], .Call (fnPtrExpr (fnName 1)) .Rust [] (.Local ⟨⟨0⟩⟩)
        (some ⟨⟨1⟩⟩) (some ⟨⟨2⟩⟩), .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .Unreachable, .Regular⟩),
      (⟨⟨2⟩⟩, ⟨[], .Intrinsic .GetUnwindPayload [] (.Local ⟨⟨1⟩⟩) (some ⟨⟨3⟩⟩), .Catch⟩),
      (⟨⟨3⟩⟩, ⟨[], .StopUnwind ⟨⟨4⟩⟩, .Catch⟩),
      (⟨⟨4⟩⟩, ⟨[], .Unreachable, .Regular⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwNestProg : Gen.Program :=
  { functions :=
      ⟨[(fnName 0, uwNestOuterFn), (fnName 1, uwNestMiddleFn), (fnName 2, uwNestInnerFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

/-- `uwNestOuterFn` about to execute its `Call`, on `Mach`: its `u8` return
place is live at `0x100` and its raw-pointer local `_1` at `0x200`. -/
private def uwNestMachBM : Mach :=
  { uwMachBM
      [uwLiveStackAllocBM 0x100,
       { data := List.replicate 8 .Uninit, addr := 0x200, align := ⟨8⟩, kind := .Stack,
         live := true, extra := () }]
      [{ func := uwNestOuterFn
         locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]⟩
         stack_pop_action := .BottomOfStack
         next_block := ⟨⟨0⟩⟩
         next_stmt := 0
         extra := () }]
      [] with
    prog := uwNestProg
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩), (fnName 2, ⟨0x8001, none⟩)]⟩ }

/-- The machine of `uwNestMachBM` on `MachTB`. -/
private def uwNestMachTB : MachTB :=
  { uwMachTB
      [uwLiveAllocTB 0x100 .Stack (uwRootWithChildren []),
       { data := List.replicate 8 .Uninit, addr := 0x200, align := ⟨8⟩, kind := .Stack,
         live := true,
         extra :=
           { root :=
               { children := [], permissions := List.replicate 8 (.Unprot .Unique),
                 «protected» := .No } } }]
      [{ func := uwNestOuterFn
         locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]⟩
         stack_pop_action := .BottomOfStack
         next_block := ⟨⟨0⟩⟩
         next_stmt := 0
         extra := ⟨[]⟩ }]
      [] with
    prog := uwNestProg
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩), (fnName 2, ⟨0x8001, none⟩)]⟩ }

/-- The payload pointer `0x1000` (without provenance) as `GetUnwindPayload`
stores it: eight little-endian bytes, none carrying provenance. -/
private def uwNestPayloadBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0x00 none, .Init 0x10 none, .Init 0 none, .Init 0 none,
   .Init 0 none, .Init 0 none, .Init 0 none, .Init 0 none]

/-- **Unwinding through two frames via `Machine::step` on `Mach` and `MachTB`
(`minirust_nested_unwind_step_witness`)**: every other witness of this section
unwinds exactly one frame. Here `uwNestOuterFn` calls `uwNestMiddleFn`, which
calls `uwNestInnerFn`, and the unwind started in the innermost frame travels
up through both callers. With `pcs` the `(next_block, next_stmt)` of every
frame, bottom frame first, `Interp.steps` and `Interp.stepsTB` agree:
- after 4 steps (`Call`, `Call`, `StartUnwind`, `ResumeUnwind`) the innermost
  frame is gone and its return local is dead, and the middle frame is at its
  cleanup block `2`, the unwind block of its own `Call`;
- after 5 steps (a second `ResumeUnwind`, now from that cleanup block) the
  middle frame is gone and its return local is dead as well, the outer frame
  is at its catch block `2`, and the payload pushed two frames further down
  is still on the payload stack;
- after 6 steps (`GetUnwindPayload` in the catch block) the outer local `_1`
  holds that payload pointer and the payload stack is unchanged: reading the
  payload does not pop it;
- after 7 steps (`StopUnwind`) the payload stack is empty and the outer frame
  is in block `4`;
- the 8th step reaches the `Unreachable` of block `4`.

The run has one thread and a payload pointer without provenance. -/
theorem minirust_nested_unwind_step_witness :
    let pcsBM (m : Mach) :=
      m.threads.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))
    let pcsTB (m : MachTB) :=
      m.threads.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))
    let payload : Ptr := ⟨0x1000, none⟩
    let payloadTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0x1000, none⟩
    ((Interp.steps 4 uwNestMachBM).toOption.map
          (fun m => (pcsBM m, m.threads.map (·.unwind_payloads),
            m.mem.memory.allocations.map (·.live))) =
        some ([[(⟨⟨0⟩⟩, 0), (⟨⟨2⟩⟩, 0)]], [[payload]], [true, true, true, false]) ∧
      (Interp.steps 5 uwNestMachBM).toOption.map
          (fun m => (pcsBM m, m.threads.map (·.unwind_payloads),
            m.mem.memory.allocations.map (·.live))) =
        some ([[(⟨⟨2⟩⟩, 0)]], [[payload]], [true, true, false, false]) ∧
      (Interp.steps 6 uwNestMachBM).toOption.map
          (fun m => (pcsBM m, m.threads.map (·.unwind_payloads),
            m.mem.memory.allocations[1]?.map (·.data))) =
        some ([[(⟨⟨3⟩⟩, 0)]], [[payload]], some uwNestPayloadBytes) ∧
      (Interp.steps 7 uwNestMachBM).toOption.map
          (fun m => (pcsBM m, m.threads.map (·.unwind_payloads))) =
        some ([[(⟨⟨4⟩⟩, 0)]], [[]]) ∧
      Interp.steps 8 uwNestMachBM = .error (.ub "reached unreachable code")) ∧
    ((Interp.stepsTB 4 uwNestMachTB).toOption.map pcsTB =
        some [[(⟨⟨0⟩⟩, 0), (⟨⟨2⟩⟩, 0)]] ∧
      (Interp.stepsTB 4 uwNestMachTB).toOption.map
          (fun m => m.threads.map (·.unwind_payloads)) =
        some [[payloadTB]] ∧
      (Interp.stepsTB 4 uwNestMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations.map (·.live)) =
        some [true, true, true, false] ∧
      (Interp.stepsTB 5 uwNestMachTB).toOption.map pcsTB = some [[(⟨⟨2⟩⟩, 0)]] ∧
      (Interp.stepsTB 5 uwNestMachTB).toOption.map
          (fun m => m.threads.map (·.unwind_payloads)) =
        some [[payloadTB]] ∧
      (Interp.stepsTB 5 uwNestMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations.map (·.live)) =
        some [true, true, false, false] ∧
      (Interp.stepsTB 6 uwNestMachTB).toOption.map pcsTB = some [[(⟨⟨3⟩⟩, 0)]] ∧
      (Interp.stepsTB 6 uwNestMachTB).toOption.map
          (fun m => m.threads.map (·.unwind_payloads)) =
        some [[payloadTB]] ∧
      (Interp.stepsTB 6 uwNestMachTB).toOption.map
          (fun m => m.mem.memory.mem.allocations[1]?.map (·.data)) =
        some (some uwNestPayloadBytes) ∧
      (Interp.stepsTB 7 uwNestMachTB).toOption.map pcsTB = some [[(⟨⟨4⟩⟩, 0)]] ∧
      (Interp.stepsTB 7 uwNestMachTB).toOption.map
          (fun m => m.threads.map (·.unwind_payloads)) =
        some [[]] ∧
      Interp.stepsTB 8 uwNestMachTB = .error (.ub "reached unreachable code")) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel,
     eq_error_of_interpStopOf (by decide +kernel)⟩⟩

private def sdStructTy : Gen.Type :=
  .Tuple [(⟨0⟩, .Int u32), (⟨4⟩, sdEnumTy), (⟨12⟩, .Int u32)] ⟨⟨16⟩, ⟨4⟩, none⟩ none

private def sdStructInitBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0x10 none, .Init 0x20 none, .Init 0x30 none, .Init 0x40 none] ++
    sdPayloadBytes ++
    [.Init 0x50 none, .Init 0x60 none, .Init 0x70 none, .Init 0x80 none]

private def sdStructExpectedBytes {P : Type} : List (Gen.AbstractByte P) :=
  [.Init 0x10 none, .Init 0x20 none, .Init 0x30 none, .Init 0x40 none] ++
    sdExpectedBytes ++
    [.Init 0x50 none, .Init 0x60 none, .Init 0x70 none, .Init 0x80 none]

private def sdBadEncodeEnumTy : Gen.Type :=
  let vBad : Gen.Variant :=
    { ty := .Tuple [] ⟨⟨8⟩, ⟨4⟩, none⟩ none
      tagger := ⟨[(⟨0⟩, (u8, 256)), (⟨16⟩, (u8, 1))]⟩ }
  .Enum ⟨[(1, vBad)]⟩ u8 .Invalid ⟨8⟩ ⟨4⟩

/-- **Projected `PlaceExpr.Field` `SetDiscriminant` and unrepresentable tagger
encoding (`minirust_setDiscriminant_field_and_encode_witness`)**:
1. On both `Mach` and `MachTB`, `SetDiscriminant` on
   `PlaceExpr.Field (.Local 1) 1` (an 8-byte enum nested at byte offset `4`
   inside a 16-byte struct at `0x100`) offsets each tag from the field's base
   pointer (`0x104 + 0` and `0x104 + 4`), leaving surrounding struct fields
   (bytes `0..3` and `12..15`) and the enum's five payload bytes untouched;
2. When a tagger entry's integer (`256`) does not fit its `IntType` (`u8`),
   `Type.encodeInt` raises `specPanic` before the accessor runs (preempting a
   subsequent out-of-bounds tagger entry at offset `16`), on both `Mach` and
   `MachTB`. -/
theorem minirust_setDiscriminant_field_and_encode_witness :
    let fnStruct := uwFn [(⟨⟨1⟩⟩, sdStructTy), (⟨⟨2⟩⟩, sdBadEncodeEnumTy)]
    let allocStructBM : Gen.Allocation Unit Unit :=
      { data := sdStructInitBytes, addr := 0x100, align := ⟨4⟩, kind := .Stack, live := true,
        extra := () }
    let allocBadBM : Gen.Allocation Unit Unit :=
      { data := sdPayloadBytes, addr := 0x200, align := ⟨4⟩, kind := .Stack, live := true,
        extra := () }
    let frBM : Frame :=
      { func := fnStruct
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨2⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]⟩
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
    let mBM := uwMachBM [allocStructBM, allocBadBM] [frBM] []
    let mkAllocTB (addr : Int) (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :
        Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
      { data := bs, addr := addr, align := ⟨4⟩, kind := .Stack, live := true,
        extra :=
          { root :=
              { children := [], permissions := List.replicate bs.length (.Unprot .Unique),
                «protected» := .No } } }
    let frTB : Gen.StackFrame TBM :=
      { func := fnStruct
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨2⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]⟩
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
    let mTB := uwMachTB
      [mkAllocTB 0x100 sdStructInitBytes, mkAllocTB 0x200 sdPayloadBytes] [frTB] []
    let fieldPlace : Gen.PlaceExpr := .Field (.Local ⟨⟨1⟩⟩) 1
    let expectedAccs : List Gen.Access :=
      [⟨.Store, .None, 0x104, ⟨1⟩⟩, ⟨.Store, .None, 0x108, ⟨2⟩⟩]
    let badEncMsg := "Endianness::encode(..).unwrap()"
    (∃ m', Interp.evalStatement mBM (.SetDiscriminant fieldPlace 7) = .ok m' ∧
      m'.mem.memory.allocations[0]?.map (·.data) = some sdStructExpectedBytes ∧
      m'.mem.accesses = expectedAccs) ∧
    (∃ m', Interp.evalStatementM mTB (.SetDiscriminant fieldPlace 7) = .ok m' ∧
      m'.mem.memory.mem.allocations[0]?.map (·.data) = some sdStructExpectedBytes ∧
      m'.mem.accesses = expectedAccs) ∧
    (Interp.evalStatement mBM (.SetDiscriminant (.Local ⟨⟨2⟩⟩) 1) =
      .error (.specPanic badEncMsg) ∧
     Interp.evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨2⟩⟩) 1) =
      .error (.specPanic badEncMsg)) :=
  ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private def uwMtCalleeFn : Gen.Function :=
  { locals := ⟨[(⟨⟨0⟩⟩, .Int u8), (⟨⟨1⟩⟩, .Ptr (.Raw .None))]⟩
    args := [⟨⟨1⟩⟩]
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[], .StartUnwind (.Load (.Local ⟨⟨1⟩⟩)) ⟨⟨1⟩⟩, .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .ResumeUnwind, .Cleanup⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwMtOuterFn : Gen.Function :=
  { locals :=
      ⟨[(⟨⟨0⟩⟩, .Int u16), (⟨⟨1⟩⟩, .Int u16),
        (⟨⟨2⟩⟩, .Ptr (.Raw .None)), (⟨⟨3⟩⟩, .Int u8)]⟩
    args := []
    ret := ⟨⟨0⟩⟩
    calling_convention := .Rust
    blocks := ⟨[
      (⟨⟨0⟩⟩, ⟨[],
        .Call (fnPtrExpr (fnName 1)) .Rust
          [.ByValue (.AddrOf (.Local ⟨⟨1⟩⟩) (.Raw .None))]
          (.Local ⟨⟨3⟩⟩) (some ⟨⟨1⟩⟩) (some ⟨⟨2⟩⟩), .Regular⟩),
      (⟨⟨1⟩⟩, ⟨[], .Unreachable, .Regular⟩),
      (⟨⟨2⟩⟩, ⟨[], .Intrinsic .GetUnwindPayload [] (.Local ⟨⟨2⟩⟩) (some ⟨⟨3⟩⟩), .Catch⟩),
      (⟨⟨3⟩⟩, ⟨[], .StopUnwind ⟨⟨4⟩⟩, .Catch⟩),
      (⟨⟨4⟩⟩, ⟨[.Assign (.Local ⟨⟨0⟩⟩) (.Load (.Deref (.Load (.Local ⟨⟨2⟩⟩)) (.Int u16)))],
        .Unreachable, .Regular⟩)]⟩
    start := ⟨⟨0⟩⟩
    implicit_writes := false }

private def uwMtProg : Gen.Program :=
  { functions := ⟨[(fnName 0, uwMtOuterFn), (fnName 1, uwMtCalleeFn)]⟩
    start := fnName 0
    globals := ⟨[]⟩
    traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

private def uwMtT0FrameBM : Frame :=
  { func := uwMtOuterFn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
    next_block := ⟨⟨9⟩⟩, next_stmt := 0, extra := () }

private def uwMtT0FrameTB : Gen.StackFrame TBM :=
  { func := uwMtOuterFn, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack,
    next_block := ⟨⟨9⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }

private def uwMtMachBM : Mach :=
  let a0 : Gen.Allocation Unit Unit :=
    { data := [.Init 0 none, .Init 0 none], addr := 0x100, align := ⟨2⟩, kind := .Stack,
      live := true, extra := () }
  let a1 : Gen.Allocation Unit Unit :=
    { data := [.Init 0xEF none, .Init 0xBE none], addr := 0x200, align := ⟨2⟩, kind := .Stack,
      live := true, extra := () }
  let a2 : Gen.Allocation Unit Unit :=
    { data := List.replicate 8 .Uninit, addr := 0x300, align := ⟨8⟩, kind := .Stack,
      live := true, extra := () }
  let a3 : Gen.Allocation Unit Unit :=
    { data := [.Init 0 none], addr := 0x400, align := ⟨1⟩, kind := .Stack,
      live := true, extra := () }
  let fr1 : Frame :=
    { func := uwMtOuterFn
      locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩),
                  (⟨⟨2⟩⟩, ⟨0x300, some (⟨2⟩, ())⟩), (⟨⟨3⟩⟩, ⟨0x400, some (⟨3⟩, ())⟩)]⟩
      stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
  { prog := uwMtProg
    mem := { memory := { allocations := [a0, a1, a2, a3], _phantom := ⟨⟩ }, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads :=
      [{ stack := [uwMtT0FrameBM], state := .Terminated, unwind_payloads := [⟨0x9000, none⟩] },
       { stack := [fr1], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩)]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

private def uwMtMachTB : MachTB :=
  let mkA (addr : Int) (al : Nat) (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :
      Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
    { data := bs, addr := addr, align := ⟨al⟩, kind := .Stack, live := true,
      extra :=
        { root :=
            { children := [], permissions := List.replicate bs.length (.Unprot .Unique),
              «protected» := .No } } }
  let fr1 : Gen.StackFrame TBM :=
    { func := uwMtOuterFn
      locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨1⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩),
                  (⟨⟨2⟩⟩, ⟨0x300, some (⟨2⟩, [])⟩), (⟨⟨3⟩⟩, ⟨0x400, some (⟨3⟩, [])⟩)]⟩
      stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
  { prog := uwMtProg
    mem :=
      { memory :=
          { params := { implicit_writes := false }
            mem :=
              { allocations :=
                  [mkA 0x100 2 [.Init 0 none, .Init 0 none],
                   mkA 0x200 2 [.Init 0xEF none, .Init 0xBE none],
                   mkA 0x300 8 (List.replicate 8 .Uninit),
                   mkA 0x400 1 [.Init 0 none]]
                _phantom := ⟨⟩ } }
        accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads :=
      [{ stack := [uwMtT0FrameTB], state := .Terminated, unwind_payloads := [⟨0x9000, none⟩] },
       { stack := [fr1], state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[(fnName 1, ⟨0x8000, none⟩)]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- **Provenance-carrying unwind payload, non-zero `active_thread = 1`
multi-thread isolation, and `Return` vs `ResumeUnwind` contrast on a non-main
thread (`minirust_unwind_provenance_multithread_step_witness`)**:
1. On a two-thread machine (`Mach` and `MachTB`) where thread `0` is
   `.Terminated` (holding its own stack frame and `unwind_payloads = [0x9000]`)
   and thread `1` is the sole `.Enabled` thread (`pickActiveThread` chooses
   `active_thread = 1`):
   - outer calls `uwMtCalleeFn` passing `AddrOf (.Local _1) (.Raw .None)` (a
     raw pointer carrying real provenance to the live `u16` `0xBEEF`);
   - callee loads that pointer via `.Load (.Local _1)` in `StartUnwind` and
     propagates via `ResumeUnwind`;
   - outer catches via `GetUnwindPayload`, clears via `StopUnwind`, and
     dereferences the caught pointer to load `0xBEEF` (`[0xEF, 0xBE]`) into
     `_0`, proving provenance survived the full unwind cycle (a provenance-free
     pointer would raise UB on dereference);
   - thread `0` is preserved (`m.threads[0]? = uwMtMachBM.threads[0]?`
     verbatim on `Mach`, and matching `state`, `unwind_payloads`, and every
     stack frame's `locals`, `stack_pop_action`, `next_block`, `next_stmt`, and
     `extra.protectors` on `MachTB`), and step `7` hits `Unreachable`.
2. Non-main thread `BottomOfStack` contrast (`active_thread = 1`): on both
   `Mach` and `MachTB`, `Terminator.Return` at `BottomOfStack` terminates
   thread `1` normally while leaving thread `0` verbatim untouched, whereas
   `Terminator.ResumeUnwind` on the exact same state raises UB
   `"the function at the bottom of the stack must not unwind"`. -/
theorem minirust_unwind_provenance_multithread_step_witness :
    let botFn := uwFn [(⟨⟨0⟩⟩, .Int u8)]
    let botFrBM : Frame :=
      { func := botFn, locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩)]⟩,
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
    let botMachBM : Mach :=
      { uwMachBM [uwLiveStackAllocBM 0x100] [] [] with
        threads :=
          [{ stack := [uwMtT0FrameBM], state := .Enabled, unwind_payloads := [⟨0x9000, none⟩] },
           { stack := [botFrBM], state := .Enabled, unwind_payloads := [] }]
        active_thread := 1 }
    let botFrTB : Gen.StackFrame TBM :=
      { func := botFn, locals := ⟨[(⟨⟨0⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩)]⟩,
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
    let botMachTB : MachTB :=
      { uwMachTB [uwLiveAllocTB 0x100 .Stack (uwRootWithChildren [])] [] [] with
        threads :=
          [{ stack := [uwMtT0FrameTB], state := .Enabled, unwind_payloads := [⟨0x9000, none⟩] },
           { stack := [botFrTB], state := .Enabled, unwind_payloads := [] }]
        active_thread := 1 }
    ((Interp.steps 6 uwMtMachBM).toOption.map (fun m =>
      (m.active_thread,
       m.mem.memory.allocations[0]?.map (·.data),
       m.mem.memory.allocations.map (·.live),
       m.threads.length,
       m.threads[1]?.map (fun t => (t.state, t.unwind_payloads, t.stack.length)))) =
      some (1, some [.Init 0xEF none, .Init 0xBE none],
        [true, true, true, true, false, false], 2, some (.Enabled, [], 1)) ∧
     (Interp.steps 6 uwMtMachBM).toOption.map (·.threads[0]?) = some uwMtMachBM.threads[0]? ∧
     Interp.steps 7 uwMtMachBM = .error (.ub "reached unreachable code")) ∧
    ((Interp.stepsTB 6 uwMtMachTB).toOption.map (·.active_thread) = some 1 ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.mem.memory.mem.allocations[0]?.map (·.data)) =
       some (some [.Init 0xEF none, .Init 0xBE none]) ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.mem.memory.mem.allocations.map (·.live)) =
       some [true, true, true, true, false, false] ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.threads.map (·.unwind_payloads)) =
       some [[⟨0x9000, none⟩], []] ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m => m.threads.map (·.state)) =
       some [.Terminated, .Enabled] ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m => m.threads.map (·.stack.length)) =
       some [1, 1] ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.threads[0]?.map (fun t => t.stack.map (fun f => f.locals.entries.isEmpty))) =
       some (some [true]) ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.threads[0]?.map (fun t => t.stack.map (fun f =>
         match f.stack_pop_action with
         | .BottomOfStack => true
         | .BackToCaller _ _ _ => false))) =
       some (some [true]) ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.threads[0]?.map (fun t => t.stack.map (fun f => (f.next_block, f.next_stmt)))) =
       some (some [(⟨⟨9⟩⟩, 0)]) ∧
     (Interp.stepsTB 6 uwMtMachTB).toOption.map (fun m =>
       m.threads[0]?.map (fun t => t.stack.map (fun f => f.extra.protectors))) =
       some (some [[]]) ∧
     Interp.stepsTB 7 uwMtMachTB = .error (.ub "reached unreachable code")) ∧
    ((Interp.evalTerminator botMachBM .Return).toOption.map (fun m =>
       (m.threads[0]?, m.threads[1]?.map (fun t => (t.state, t.unwind_payloads)))) =
       some (botMachBM.threads[0]?, some (.Terminated, [])) ∧
     Interp.evalTerminator botMachBM .ResumeUnwind =
       .error (.ub "the function at the bottom of the stack must not unwind") ∧
     (Interp.evalTerminatorM botMachTB .Return).toOption.map (fun m =>
       (m.threads[0]?, m.threads[1]?.map (fun t => (t.state, t.unwind_payloads)))) =
       some (botMachTB.threads[0]?, some (.Terminated, [])) ∧
     Interp.evalTerminatorM botMachTB .ResumeUnwind =
       .error (.ub "the function at the bottom of the stack must not unwind")) := by
  refine ⟨⟨rfl, rfl, rfl⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, eq_error_of_interpStopOf (by decide +kernel)⟩,
    ⟨rfl, rfl, rfl, rfl⟩⟩

private def sdPayloadEnumTy : Gen.Type :=
  let payloadTuple : Gen.Type :=
    .Tuple [(⟨2⟩, .Int u16)] ⟨⟨4⟩, ⟨2⟩, none⟩ none
  let v0 : Gen.Variant := { ty := payloadTuple, tagger := ⟨[(⟨0⟩, (u8, 0))]⟩ }
  let v1 : Gen.Variant := { ty := payloadTuple, tagger := ⟨[(⟨0⟩, (u8, 1))]⟩ }
  let disc : Gen.Discriminator :=
    .Branch ⟨0⟩ u8 .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩
  .Enum ⟨[(0, v0), (1, v1)]⟩ u8 disc ⟨4⟩ ⟨2⟩

/-- **`SetDiscriminant` + `ValueExpr.Load` full enum round-trip and error
propagation controls (`minirust_setDiscriminant_load_roundtrip_witness`)**:
1. On both `Mach` and `MachTB`, starting from a 4-byte enum carrying `u8` tag
   `0` at offset `0`, uninitialized padding at offset `1`, and `u16` payload
   `0xBEEF` at offset `2`, executing `Statement.SetDiscriminant (.Local 1) 1`
   writes only byte `0` (`0x01`) while preserving padding and payload, and
   `ValueExpr.Load (.Local 1)` decodes `.Variant 1 (.Tuple [.Int 0xBEEF])`;
2. Concrete error-propagation controls on both `Mach` and `MachTB`:
   `SetDiscriminant` on a dead local raises `.ub "access to a dead local"`, and
   `StartUnwind` with an uninitialized raw-pointer local raises `typedLoad` UB
   without pushing onto `unwind_payloads`. -/
theorem minirust_setDiscriminant_load_roundtrip_witness :
    let initBytes {P : Type} : List (Gen.AbstractByte P) :=
      [.Init 0x00 none, .Uninit, .Init 0xEF none, .Init 0xBE none]
    let afterBytes {P : Type} : List (Gen.AbstractByte P) :=
      [.Init 0x01 none, .Uninit, .Init 0xEF none, .Init 0xBE none]
    let fn := uwFn [(⟨⟨1⟩⟩, sdPayloadEnumTy), (⟨⟨2⟩⟩, sdPayloadEnumTy),
                    (⟨⟨3⟩⟩, .Ptr (.Raw .None))]
    let allocEnumBM : Gen.Allocation Unit Unit :=
      { data := initBytes, addr := 0x100, align := ⟨2⟩, kind := .Stack, live := true,
        extra := () }
    let allocPtrBM : Gen.Allocation Unit Unit :=
      { data := List.replicate 8 .Uninit, addr := 0x200, align := ⟨8⟩, kind := .Stack,
        live := true, extra := () }
    let frBM : Frame :=
      { func := fn
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, ())⟩), (⟨⟨3⟩⟩, ⟨0x200, some (⟨1⟩, ())⟩)]⟩
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := () }
    let mBM := uwMachBM [allocEnumBM, allocPtrBM] [frBM] []
    let mkAllocTB (addr : Int) (al : Nat)
        (bs : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :
        Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
      { data := bs, addr := addr, align := ⟨al⟩, kind := .Stack, live := true,
        extra :=
          { root :=
              { children := [], permissions := List.replicate bs.length (.Unprot .Unique),
                «protected» := .No } } }
    let frTB : Gen.StackFrame TBM :=
      { func := fn
        locals := ⟨[(⟨⟨1⟩⟩, ⟨0x100, some (⟨0⟩, [])⟩), (⟨⟨3⟩⟩, ⟨0x200, some (⟨1⟩, [])⟩)]⟩
        stack_pop_action := .BottomOfStack, next_block := ⟨⟨0⟩⟩, next_stmt := 0, extra := ⟨[]⟩ }
    let mTB := uwMachTB
      [mkAllocTB 0x100 2 initBytes, mkAllocTB 0x200 8 (List.replicate 8 .Uninit)] [frTB] []
    let loadUb := "load at type but the data in memory violates the language invariant"
    (∃ m1 m2,
      Interp.evalStatement mBM (.SetDiscriminant (.Local ⟨⟨1⟩⟩) 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some afterBytes ∧
      Interp.evalValue m1 (.Load (.Local ⟨⟨1⟩⟩)) =
        .ok ((.Variant 1 (.Tuple [.Int 0xBEEF]), sdPayloadEnumTy), m2)) ∧
    (∃ m1 m2,
      Interp.evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨1⟩⟩) 1) = .ok m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (·.data) = some afterBytes ∧
      Interp.evalValueM m1 (.Load (.Local ⟨⟨1⟩⟩)) =
        .ok ((.Variant 1 (.Tuple [.Int 0xBEEF]), sdPayloadEnumTy), m2)) ∧
    (Interp.evalStatement mBM (.SetDiscriminant (.Local ⟨⟨2⟩⟩) 1) =
      .error (.ub "access to a dead local") ∧
     Interp.evalStatementM mTB (.SetDiscriminant (.Local ⟨⟨2⟩⟩) 1) =
      .error (.ub "access to a dead local") ∧
     Interp.evalTerminator mBM (.StartUnwind (.Load (.Local ⟨⟨3⟩⟩)) ⟨⟨1⟩⟩) =
      .error (.ub loadUb) ∧
     Interp.evalTerminatorM mTB (.StartUnwind (.Load (.Local ⟨⟨3⟩⟩)) ⟨⟨1⟩⟩) =
      .error (.ub loadUb)) :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **`sizeOfVal` & `alignOfVal` on unsized `RigidTy.str` (`&str` / `*const str`) ↔ MiniRust
`Type.layout (.Slice (.Int u8))` (`evalLIntrinsic_sizeOfVal_alignOfVal_str_minirust_layout`,
`[adv ep2-A4]`)**: completes Section 9b's `evalLIntrinsic_sizeOfVal_alignOfVal_minirust_layout`
for `str` wide pointers (`ptr` + byte-length metadata `len < 2 ^ 64`):
- MiniRust's `Type.layout (.Slice (.Int u8)) >>= LayoutStrategy.compute_size_and_align ...
  (some (.ElementCount len))` computes `(⟨len⟩, ⟨1⟩)`;
- Anneal's `.sizeOfVal` returns `some (.scalar ⟨len, 8⟩)` and `.alignOfVal` returns
  `some (.scalar ⟨1, 8⟩)` iff `len < 2 ^ 63` (`isize::MAX` slice-size UB cutoff), faulting
  (`none`) when `len ≥ 2 ^ 63`. -/
theorem evalLIntrinsic_sizeOfVal_alignOfVal_str_minirust_layout
    (vtables : Interp.Ptr → Interp Gen.VTable)
    (p : ProvenancePtr) (len : Nat) (hlen : len < 2 ^ 64)
    (restTys : List RigidTy) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (flag : Bool) :
    (Interp.Type.layout (.Slice (.Int u8)) >>= fun ls =>
        Interp.LayoutStrategy.compute_size_and_align vtables ls
          (some (.ElementCount (len : Int)))) = .ok (⟨len⟩, ⟨1⟩) ∧
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .sizeOfVal (.str :: restTys) decls layouts
        argOps [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] flag =
      (if len < 2 ^ 63 then some (.scalar ⟨len, 8⟩) else none) ∧
    Anneal.Mir.AdtAndControl.evalLIntrinsicValue .alignOfVal (.str :: restTys) decls layouts
        argOps [.aggregate 0 [.ptr p 8, .scalar ⟨len, 8⟩]] flag =
      (if len < 2 ^ 63 then some (.scalar ⟨1, 8⟩) else none) := by
  have hLenWrap : wrapScalarBits len (scalarModulus 8) = len := by
    rw [wrapScalarBits_eq, scalarModulus_eq, Nat.mod_eq_of_lt hlen]
  have hHalf8 : signedHalfModulus 8 = 2 ^ 63 := by decide +kernel
  have hSlice1 : evalSliceSizeOfVal 1 ⟨len, 8⟩ =
      if len < 2 ^ 63 then some ⟨len, 8⟩ else none := by
    unfold evalSliceSizeOfVal
    dsimp only
    change (match Nat.ble (signedHalfModulus 8)
        (1 * wrapScalarBits len (scalarModulus 8)) with
      | true => (none : Option ScalarInt)
      | false => some (ScalarInt.mk (1 * wrapScalarBits len (scalarModulus 8)) 8)) = _
    rw [hLenWrap, Nat.one_mul, hHalf8, nat_ble_eq_decide]
    by_cases hlt : len < 2 ^ 63
    · rw [decide_eq_false (by omega : ¬(2 ^ 63 ≤ len))]
      simp only [hlt, ↓reduceIte]
    · rw [decide_eq_true (by omega : 2 ^ 63 ≤ len)]
      simp only [hlt, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · have hU8 := (evalLIntrinsic_sizeOfVal_alignOfVal_minirust_layout (rk := .uint .u8) (it := u8)
      rfl vtables p len hlen restTys decls layouts argOps flag).2.1
    dsimp only [u8] at hU8 ⊢
    rwa [Nat.mul_one] at hU8
  · change Option.map Value.scalar (evalSliceSizeOfVal 1 ⟨len, 8⟩) = _
    rw [hSlice1]
    by_cases hlt : len < 2 ^ 63 <;> simp [hlt]
  · change (match evalSliceSizeOfVal 1 ⟨len, 8⟩ with
      | some _ => some (Value.scalar ⟨1, 8⟩)
      | none => none) = _
    rw [hSlice1]
    by_cases hlt : len < 2 ^ 63 <;> simp [hlt]

/-- **Missing `target = none` / `nextBlock = none` UB correspondence for returning intrinsics
(`evalLoweredIntrinsicCall_target_none_minirust_ub`, `[adv ep2-A4]`)**:
1. In MiniRust (`Interp.evalTerminator`, `spec/lang/step/terminators.md`), whenever a
   `Terminator.Intrinsic` evaluates `retExpr`, `arguments`, `evalIntrinsic`, and `placeStore`
   successfully with `nextBlock = none`, execution raises `.error (.ub "return from an intrinsic
   where caller did not specify next block")`;
2. Correspondingly, in Anneal (`evalLoweredIntrinsicCall`), for **every** `op : LIntrinsicOp`
   other than `.abort` and `.panicUnwind` (all 28 value-returning, memory, and `unreachableUnchecked`
   intrinsics), calling `op` with `target = none` returns `none`. -/
theorem evalLoweredIntrinsicCall_target_none_minirust_ub
    (m m₁ m₂ m₃ m₄ : Mach) (mrOp : Gen.IntrinsicOp) (arguments : List Gen.ValueExpr)
    (retExpr : Gen.PlaceExpr) (retPlace : Gen.Place Interp.BM) (retTy : Gen.Type)
    (args : List (Val × Gen.Type)) (val : Val)
    (hPl : Interp.evalPlace m retExpr = .ok ((retPlace, retTy), m₁))
    (hArgs : Interp.evalArgs m₁ arguments = .ok (args, m₂))
    (hInt : Interp.evalIntrinsic m₂ mrOp args retTy = .ok (val, m₃))
    (hStore : Interp.placeStore m₃ retPlace val retTy = .ok m₄)
    (env : Anneal.Mir.AdtAndControl.CfgEnv) (body : Anneal.Mir.AdtAndControl.LBody)
    (bb : Nat) (inCleanup : Bool) (argOps : List Operand) (avs : List Value)
    (slots2 : List Anneal.Mir.PlaceAndRvalue.LocalSlotState) (dest : Place) (destTy : Ty)
    (unwind : UnwindAction) (unwinding : Option Nat)
    (op : Anneal.Mir.AdtAndControl.LIntrinsicOp) (typeArgs : List RigidTy)
    (hNotAbort : op ≠ .abort) (hNotPanic : op ≠ .panicUnwind) :
    Interp.evalTerminator m (.Intrinsic mrOp arguments retExpr none) =
      .error (.ub "return from an intrinsic where caller did not specify next block") ∧
    Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall env body bb inCleanup argOps avs slots2
      dest destTy none unwind unwinding op typeArgs = none := by
  refine ⟨?_, ?_⟩
  · simp [Interp.evalTerminator, hPl, hArgs, hInt, hStore, ub, Bind.bind, Except.bind]
  · cases op <;> simp only [Anneal.Mir.AdtAndControl.evalLoweredIntrinsicCall]
    all_goals
      first
      | exact absurd rfl hNotAbort
      | exact absurd rfl hNotPanic
      | rfl
      | (cases Anneal.Mir.AdtAndControl.unwindActionOk body inCleanup unwind <;> rfl)

/-- Correspondence regime of each `Anneal.Mir.AdtAndControl.LIntrinsicOp` variant across
`DeinitBridge` and `IntrinsicBoundary` (`[adv ep2-A4]`). -/
inductive LIntrinsicBridgeClass : Type where
  /-- Direct `MiniRustSpec.Interp` operator (`evalBinOp` / `evalUnOp` / `Endianness.decode`),
  pointer/layout helper (`ptr_offset` / `Type.layout` + `LayoutStrategy.compute_size_and_align`),
  or diverging primitive (`IntrinsicOp.Abort` / `Terminator.Unreachable`) — 22 variants. -/
  | interpDirect
  /-- Symbolic `leBits` + `CountOnes` conservation + `IntrinsicOp.Assume` nonzero precondition +
  `IntrinsicFallback` MIR expansion — 5 variants (`ctlz`, `ctlzNonzero`, `cttz`, `cttzNonzero`,
  `bitreverse`). -/
  | symbolicBitAndFallback
  /-- Call-form memory intrinsics (`copyNonOverlapping` shares `evalCopyNonOverlappingSubplace` with
  MIR `StatementKind::CopyNonOverlapping`; `writeBytes` is pinned as external `MirCallReq` in
  Section 3 and sub-place byte-fill in `AdtAndControl` Section 5c/5g) — 2 variants. -/
  | callFormMemory
  /-- Unwinding panic with no single MiniRust `IntrinsicOp` primitive: MiniRust
  models unwinding with the terminators `StartUnwind`/`StopUnwind`/
  `ResumeUnwind`, which `Interp.evalTerminator` (`Mach`) and
  `Interp.evalTerminatorM` (`MachTB`) execute
  (`minirust_unwind_terminators_supported`,
  `minirust_unwind_concrete_witnesses`). The correspondence proved in this
  module is with `Trusted`'s `startPanic` only; no simulation against those
  terminators is proved here — 1 variant (`panicUnwind`). -/
  | trustedOnlyUnwind
  deriving DecidableEq, Repr

/-- Map every `LIntrinsicOp` constructor to its `MiniRustSpec` correspondence regime. -/
def classifyLIntrinsicBridge : Anneal.Mir.AdtAndControl.LIntrinsicOp → LIntrinsicBridgeClass
  | .ctpop | .bswap | .exactDiv
  | .wrappingAdd | .wrappingSub | .wrappingMul
  | .saturatingAdd | .saturatingSub
  | .uncheckedAdd | .uncheckedSub | .uncheckedMul | .uncheckedDiv | .uncheckedRem
  | .uncheckedShl | .uncheckedShr
  | .threeWayCompare | .ubChecks | .arithOffset
  | .sizeOfVal | .alignOfVal
  | .unreachableUnchecked | .abort => .interpDirect
  | .ctlz | .ctlzNonzero | .cttz | .cttzNonzero | .bitreverse => .symbolicBitAndFallback
  | .copyNonOverlapping | .writeBytes => .callFormMemory
  | .panicUnwind => .trustedOnlyUnwind

/-- Canonical duplicate-free enumeration of all 30 `LIntrinsicOp` constructors. -/
def allLIntrinsicOps : List Anneal.Mir.AdtAndControl.LIntrinsicOp :=
  [.ctlz, .ctlzNonzero, .cttz, .cttzNonzero, .ctpop, .bswap, .bitreverse, .exactDiv,
   .wrappingAdd, .wrappingSub, .wrappingMul, .saturatingAdd, .saturatingSub,
   .uncheckedAdd, .uncheckedSub, .uncheckedMul, .uncheckedDiv, .uncheckedRem,
   .uncheckedShl, .uncheckedShr, .threeWayCompare, .ubChecks, .arithOffset,
   .sizeOfVal, .alignOfVal, .copyNonOverlapping, .writeBytes,
   .unreachableUnchecked, .abort, .panicUnwind]

/-- **Exhaustive 30-variant `LIntrinsicOp` classification (`lintrinsicOp_exhaustive_minirust_classification`,
`[adv ep2-A4]`)**: `allLIntrinsicOps` contains every `LIntrinsicOp` constructor without duplicates
(`30` total), partitioned into `22` direct `Interp` operator/layout/diverging ops, `5` symbolic
`leBits` / `Assume` / `IntrinsicFallback` ops, `2` call-form memory ops, and `1` `Trusted`-only
unwinding panic op. -/
theorem lintrinsicOp_exhaustive_minirust_classification :
    allLIntrinsicOps.length = 30 ∧
    allLIntrinsicOps.Nodup ∧
    (∀ op : Anneal.Mir.AdtAndControl.LIntrinsicOp, op ∈ allLIntrinsicOps) ∧
    (allLIntrinsicOps.filter (classifyLIntrinsicBridge · == .interpDirect)).length = 22 ∧
    (allLIntrinsicOps.filter (classifyLIntrinsicBridge · == .symbolicBitAndFallback)).length = 5 ∧
    (allLIntrinsicOps.filter (classifyLIntrinsicBridge · == .callFormMemory)).length = 2 ∧
    (allLIntrinsicOps.filter (classifyLIntrinsicBridge · == .trustedOnlyUnwind)).length = 1 := by
  refine ⟨rfl, by decide +kernel, fun op => ?_, rfl, rfl, rfl, rfl⟩
  cases op <;> decide

end AdvEp2B4

end MiniRustSpec.Correspondence
