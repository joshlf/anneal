/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Proto.ZeroCountCopyAlignProto
import Lean.Elab.Tactic

/-!
# Tests for the zero-count `copy_nonoverlapping` alignment / null-guard prototype

Kernel-checked concrete theorems for all six corner cases of
`Anneal.Proto.ZeroCountCopyAlign` (each contrasted with the legacy
`Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingWithCount`), the
`WitLM4_2.copyMisalignedZeroBody` counterexample replayed through `stepMirFn`
and `stepMirFnProto`, the `pass_copy_nonoverlapping_zero_count` regression
(`tests/miri-diff/corpus/src/lib.rs:532`), the `bdCopyZeroScalars`
(`MiniRustSpec/Correspondence/IntrinsicBoundary.lean:320`) non-pointer case, a
`V2026_08_01` bug-presence check, and a `#print axioms` audit.
-/

namespace Anneal.Proto.ZeroCountCopyAlign.Tests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Proto.ZeroCountCopyAlign

/-- Close an equality goal `lhs = rhs` by `Eq.refl lhs`, deferring the
definitional check entirely to the kernel (no `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-! ## 1. Fixtures -/

def tyOf (k : RigidTy) : Ty := { kind := k, layoutIdx := 0 }
def declOf (k : RigidTy) : LocalDecl := { mutability := .mut, ty := tyOf k, debugName := none }
def u8K : RigidTy := .uint .u8
def u32K : RigidTy := .uint .u32
def u64K : RigidTy := .uint .u64
def usizeK : RigidTy := .uint .usize
def unitK : RigidTy := .tuple []
def rawMutK (k : RigidTy) : RigidTy := .rawPtr .mut k
def rawConstK (k : RigidTy) : RigidTy := .rawPtr .not k
def loc (i : Nat) : Place := { local_ := i, projection := [] }
def cp (i : Nat) : Operand := .copy (loc i)
def constUsize (n : Nat) : Operand :=
  .constant { ty := tyOf usizeK, val := .scalar (.int ⟨n, 8⟩) }
def constU32 (n : Nat) : Operand :=
  .constant { ty := tyOf u32K, val := .scalar (.int ⟨n, 4⟩) }

/-- Locals: `_0 : ()`, `_1 : u64`, `_2 : *const S` (src), `_3 : *mut D` (dst),
`_4 : u8`. -/
def declsFor (srcK dstK : RigidTy) : List LocalDecl :=
  [declOf unitK, declOf u64K, declOf (rawConstK srcK), declOf (rawMutK dstK), declOf u8K]

/-- Tag `1` borrows `_1 : u64` (8-aligned); tag `2` borrows `_4 : u8`
(1-aligned); tag `3` borrows `_1` but is `.disabled` (no-op invariant). -/
def borrowsFix : List BorrowEntry :=
  [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique },
   { tag := 2, targetLocal := 4, targetProjection := [], perm := .unique },
   { tag := 3, targetLocal := 1, targetProjection := [], perm := .disabled }]

/-- Global allocation `9` (8-aligned, 16 bytes) and `10` (1-aligned). -/
def globalsFix : List CapturedAllocation :=
  [{ allocId := 9, bytes := List.replicate 16 (some 0), relocations := [],
     align := { bytes := 8 }, mutability := .not },
   { allocId := 10, bytes := List.replicate 16 (some 0), relocations := [],
     align := { bytes := 1 }, mutability := .not }]

/-- Fixture state: `_1 = 42_u64`, `_4 = 7_u8`, everything else uninit. -/
def st : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit,
                          .init (.scalar ⟨7, 1⟩)] }
    memory := { emptyMemory with borrows := borrowsFix, globals := globalsFix, nextTag := 4 } }

/-- Prototype evaluation on the fixture. -/
def proto (policy : ZeroCountNullPolicy) (srcK dstK : RigidTy) (srcVal dstVal : Value)
    (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCountProto policy st (cp 2) (cp 3) (declsFor srcK dstK)
    emptyLayoutTable srcVal dstVal count st.frame.locals

/-- Legacy evaluation on the fixture. -/
def legacy (srcK dstK : RigidTy) (srcVal dstVal : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCount st (cp 2) (cp 3) (declsFor srcK dstK) emptyLayoutTable srcVal
    dstVal count st.frame.locals

/-- The pure no-op step. -/
def noop : MirStepNode := MirStepNode.step (advanceStmt st st.frame.locals)

def stackPtr (off : Nat) : Value := .ptr ⟨1, off⟩ 8
def u8LocalPtr : Value := .ptr ⟨2, 0⟩ 8
def disabledPtr : Value := .ptr ⟨3, 0⟩ 8
def globalPtr (id off : Nat) : Value := .ptr ⟨id, off⟩ 8
def unbackedPtr (off : Nat) : Value := .ptr ⟨20, off⟩ 8
def danglingScalar (addr : Nat) : Value := .scalar ⟨addr, 8⟩

/-! ## 2. Layout resolution sanity -/

theorem layout_u64 :
    resolveCopyElemLayout (declsFor u64K u64K) emptyLayoutTable (cp 2) (cp 3) = .ok 8 8 := by
  decide +kernel

theorem layout_u8 :
    resolveCopyElemLayout (declsFor u8K u8K) emptyLayoutTable (cp 2) (cp 3) = .ok 1 1 := by
  decide +kernel

theorem layout_unit :
    resolveCopyElemLayout (declsFor unitK unitK) emptyLayoutTable (cp 2) (cp 3) = .ok 0 1 := by
  decide +kernel

/-! ## 3. Corner case 1 — live aligned `.ptr` steps as a pure no-op -/

/-- Live aligned stack pointer, `src == dst` (no overlap UB on zero bytes). -/
theorem cc1_stack_aligned_same_ptr :
    proto .rejectNull u64K u64K (stackPtr 0) (stackPtr 0) 0 = noop := by kernel_rfl

/-- A `.disabled` tag (and a `.uninit` target slot) is irrelevant for zero bytes:
no Tree Borrows access is performed. -/
theorem cc1_disabled_tag_noop :
    proto .rejectNull u64K u64K disabledPtr (stackPtr 0) 0 = noop := by kernel_rfl

/-- Live 8-aligned global allocation at offset `8`. -/
theorem cc1_global_aligned :
    proto .rejectNull u64K u64K (globalPtr 9 8) (globalPtr 9 0) 0 = noop := by kernel_rfl

/-- Unbacked / function-pointer-like provenance on `u8` (`elemAlign = 1`). -/
theorem cc1_unbacked_u8 :
    proto .rejectNull u8K u8K (unbackedPtr 3) (unbackedPtr 3) 0 = noop := by kernel_rfl

/-! ## 4. Corner case 2 — dangling non-null aligned `.scalar` (`NonNull::dangling()`) -/

/-- `NonNull::<u64>::dangling()` (address `8`). -/
theorem cc2_dangling_u64 :
    proto .rejectNull u64K u64K (danglingScalar 8) (danglingScalar 8) 0 = noop := by kernel_rfl

/-- `NonNull::<()>::dangling()` (address `1`), `count = 0`. -/
theorem cc2_dangling_unit_count0 :
    proto .rejectNull unitK unitK (danglingScalar 1) (danglingScalar 1) 0 = noop := by kernel_rfl

/-- **ZST generalization**: `copy_nonoverlapping::<()>(dangling, dangling, 5)`
(`totalBytes = 0`) steps in the prototype ... -/
theorem cc2_zst_count5_proto :
    proto .rejectNull unitK unitK (danglingScalar 1) (danglingScalar 1) 5 = noop := by kernel_rfl

/-- ... whereas the legacy evaluator spuriously faults (`countBits ≠ 0` branch
demands tracked `.ptr` borrows). -/
theorem cc2_zst_count5_legacy_spurious_ub :
    legacy unitK unitK (danglingScalar 1) (danglingScalar 1) 5 = MirStepNode.fail .ub := by
  kernel_rfl

/-! ## 5. Corner case 3 — null -/

theorem cc3_null_scalar_u64 :
    proto .rejectNull u64K u64K (danglingScalar 0) (danglingScalar 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

theorem cc3_null_scalar_u8 :
    proto .rejectNull u8K u8K (danglingScalar 1) (danglingScalar 0) 0 = MirStepNode.fail .ub := by
  kernel_rfl

theorem cc3_null_scalar_unit :
    proto .rejectNull unitK unitK (danglingScalar 0) (danglingScalar 0) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem cc3_null_ptr_u64 :
    proto .rejectNull u64K u64K (.ptr ⟨0, 0⟩ 8) (stackPtr 0) 0 = MirStepNode.fail .ub := by
  kernel_rfl

theorem cc3_null_ptr_u8 :
    proto .rejectNull u8K u8K (.ptr ⟨0, 0⟩ 8) (.ptr ⟨0, 0⟩ 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- A wrapped canonical address `2^64 ≡ 0` is null too (`allocId = 2^48`). -/
theorem cc3_wrapped_null_ptr_u8 :
    proto .rejectNull u8K u8K (.ptr ⟨281474976710656, 0⟩ 8) (danglingScalar 1) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- ZST `count > 0` with a null pointer is also rejected. -/
theorem cc3_null_zst_count5 :
    proto .rejectNull unitK unitK (danglingScalar 0) (danglingScalar 1) 5 =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- Raw-intrinsic policy (`lean-miri` / Rust 1.98 `ub_checks`): null accepted. -/
theorem cc3_null_allowRaw_u8 :
    proto .allowRawIntrinsicNull u8K u8K (danglingScalar 0) (danglingScalar 0) 0 = noop := by
  kernel_rfl

theorem cc3_null_allowRaw_u64 :
    proto .allowRawIntrinsicNull u64K u64K (danglingScalar 0) (danglingScalar 0) 0 = noop := by
  kernel_rfl

/-- The legacy evaluator accepts null (the bug). -/
theorem cc3_null_legacy_permissive :
    legacy u64K u64K (danglingScalar 0) (danglingScalar 0) 0 = noop := by kernel_rfl

/-! ## 6. Corner case 4 — misaligned -/

/-- Live `.ptr` at offset `1` of an 8-aligned `u64` local. -/
theorem cc4_misaligned_stack_ptr :
    proto .rejectNull u64K u64K (stackPtr 1) (stackPtr 0) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- Dangling-misaligned `.scalar ⟨9, 8⟩` on `*mut u64`. -/
theorem cc4_misaligned_scalar :
    proto .rejectNull u64K u64K (danglingScalar 8) (danglingScalar 9) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- Misaligned offset `4` into an 8-aligned global on `u64`. -/
theorem cc4_misaligned_global :
    proto .rejectNull u64K u64K (globalPtr 9 4) (globalPtr 9 0) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- Misaligned unbacked provenance offset. -/
theorem cc4_misaligned_unbacked :
    proto .rejectNull u64K u64K (unbackedPtr 3) (stackPtr 0) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- The raw policy also rejects misalignment (alignment is policy-independent). -/
theorem cc4_misaligned_allowRaw :
    proto .allowRawIntrinsicNull u64K u64K (danglingScalar 9) (danglingScalar 8) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- The legacy evaluator accepts misalignment (the bug). -/
theorem cc4_misaligned_legacy_permissive :
    legacy u64K u64K (stackPtr 1) (danglingScalar 9) 0 = noop := by kernel_rfl

/-! ## 7. Corner case 5 — wrong-width / non-pointer / uninit operands -/

theorem cc5_scalar_wrong_width :
    proto .rejectNull u64K u64K (.scalar ⟨8, 4⟩) (danglingScalar 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

theorem cc5_scalar_out_of_range :
    proto .rejectNull u8K u8K (.scalar ⟨18446744073709551616, 8⟩) (danglingScalar 8) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem cc5_unit :
    proto .rejectNull u8K u8K (danglingScalar 8) .unit 0 = MirStepNode.fail .ub := by kernel_rfl

theorem cc5_aggregate :
    proto .rejectNull u8K u8K (.aggregate 0 []) (danglingScalar 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

theorem cc5_uninit :
    proto .rejectNull u8K u8K (danglingScalar 8) .uninit 0 = MirStepNode.fail .ub := by kernel_rfl

theorem cc5_ptr_wrong_width :
    proto .rejectNull u8K u8K (.ptr ⟨1, 0⟩ 4) (danglingScalar 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- The legacy evaluator accepts a `.unit` operand (the bug). -/
theorem cc5_unit_legacy_permissive :
    legacy u8K u8K .unit .unit 0 = noop := by kernel_rfl

/-- `bdCopyZeroScalars` (`IntrinsicBoundary.lean:320`): `copy_nonoverlapping(0_u32,
0_u32, 0_usize)` steps in legacy `evalStmt` for every state, whereas the B1-hardened
prototype detects statically non-pointer (`u32`) operands and faults `.fail .ub`
even with `localDecls = []`. -/
def bdCopyZeroScalars : Statement :=
  { kind := .intrinsic (.copyNonOverlapping (constU32 0) (constU32 0) (constUsize 0)),
    span := "proto" }

theorem cc5_bdCopyZeroScalars_legacy (s : MachineState) (decls : List LocalDecl)
    (layouts : LayoutTable) :
    evalStmt s bdCopyZeroScalars decls layouts = MirStepNode.step (advanceStmt s s.frame.locals) :=
  rfl

/-- Even with empty `localDecls`, `bdCopyZeroScalars` faults `.fail .ub` (not merely
`.unsupported`), because `constU32 0` is statically a non-pointer `u32` (and 4 bytes). -/
theorem cc5_bdCopyZeroScalars_proto_ub :
    evalStmtProto .rejectNull st bdCopyZeroScalars [] emptyLayoutTable = MirStepNode.fail .ub := by
  kernel_rfl

/-- Even an 8-byte aligned scalar constant of static non-pointer type `u64`
(`copy_nonoverlapping(src_ptr_u64, 8_u64, 0_usize)`) must fault `.fail .ub`,
never stepping just because `src`'s pointee resolved to `u64`! -/
def constU64 (n : Nat) : Operand :=
  .constant { ty := tyOf u64K, val := .scalar (.int ⟨n, 8⟩) }

theorem cc5_nonptr_u64_dst_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull st (cp 2) (constU64 8) (declsFor u64K u64K)
        emptyLayoutTable (danglingScalar 8) (danglingScalar 8) 0 st.frame.locals =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- A malformed `.unit` operand with empty `localDecls` faults `.fail .ub`
(Corner Case 5 beats missing-decl `.unsupported`). -/
theorem cc5_unit_no_decls_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull st (cp 2) (cp 3) [] emptyLayoutTable
        .unit (danglingScalar 8) 0 st.frame.locals = MirStepNode.fail .ub := by
  kernel_rfl

/-- Statement-level count width check (missing in legacy `evalCopyNonOverlapping`):
a 4-byte `count = 0` scalar. -/
def countU32Zero : Operand := constU32 0

theorem cc5_count_wrong_width_proto :
    evalCopyNonOverlappingProto .rejectNull st (cp 1) (cp 1) countU32Zero
        (declsFor u64K u64K) emptyLayoutTable = MirStepNode.fail .ub := by
  kernel_rfl

/-- Statement-level out-of-range `count` (`bits = 2^64` on 64-bit) faults `.ub`. -/
def countOutOfRange : Operand := constUsize 18446744073709551616

theorem cc5_count_out_of_range_proto :
    evalCopyNonOverlappingProto .rejectNull st (cp 1) (cp 1) countOutOfRange
        (declsFor u64K u64K) emptyLayoutTable = MirStepNode.fail .ub := by
  kernel_rfl

/-! ## 8. Corner case 6 — unresolved / conflicting / under-aligned → `.unsupported` -/

/-- No local decls: pointee unresolved. -/
theorem cc6_no_decls :
    evalCopyNonOverlappingWithCountProto .rejectNull st (cp 2) (cp 3) [] emptyLayoutTable
        (danglingScalar 8) (danglingScalar 8) 0 st.frame.locals = MirStepNode.unsupported := by
  kernel_rfl

/-- Conflicting `*const u8` vs `*mut u64` pointees. -/
theorem cc6_conflicting_pointees :
    proto .rejectNull u8K u64K (danglingScalar 1) (danglingScalar 1) 0 =
      MirStepNode.unsupported := by
  kernel_rfl

/-- Under-aligned backing local: `&raw mut u8_local as *mut u64` (the virtual
`65536`-byte page must not count as alignment). -/
theorem cc6_under_aligned_local :
    proto .rejectNull u64K u64K u8LocalPtr (stackPtr 0) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- Under-aligned global (`align 1`) on `u64`. -/
theorem cc6_under_aligned_global :
    proto .rejectNull u64K u64K (globalPtr 10 0) (stackPtr 0) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- Unknown base alignment of unbacked provenance on `u64`. -/
theorem cc6_unbacked_u64 :
    proto .rejectNull u64K u64K (unbackedPtr 0) (stackPtr 0) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- Opaque ADT without a layout. -/
theorem cc6_opaque_adt :
    proto .rejectNull (.adt "opaque::Foo" []) (.adt "opaque::Foo" []) (danglingScalar 8)
        (danglingScalar 8) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- Unsized pointee (`[u8]`) is `.ub` for both `count = 0` and `count = 1`. -/
theorem cc6_unsized_slice_ub :
    proto .rejectNull (.slice u8K) (.slice u8K) (danglingScalar 8) (danglingScalar 8) 0 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem cc6_unsized_slice_count1_ub :
    proto .rejectNull (.slice u8K) (.slice u8K) (stackPtr 0) (stackPtr 0) 1 =
      MirStepNode.fail .ub := by
  kernel_rfl


/-! ## 9. Overflow -/

/-- `count * size_of::<u64>() > isize::MAX` is `.ub` (before any zero-byte or
legacy dispatch). -/
theorem overflow_u64 :
    proto .rejectNull u64K u64K (stackPtr 0) (stackPtr 0) 1152921504606846976 =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- ZST with `count = usize::MAX`: zero bytes, no overflow, steps. -/
theorem zst_count_max_no_overflow :
    proto .rejectNull unitK unitK (danglingScalar 1) (danglingScalar 1) 18446744073709551615 =
      noop := by
  kernel_rfl

/-! ## 10. `WitLM4_2.copyMisalignedZeroBody` (`WitLM4_2.lean:2386-2395`) -/

def mkStmt42 (k : StatementKind) : Statement := { kind := k, span := "lm-4.2-witness" }
def mkTerm42 (k : TerminatorKind) : Terminator := { kind := k, span := "lm-4.2-witness" }
def local42 (i : Nat) : Place := { local_ := i, projection := [] }
def constInt (k : RigidTy) (bits size : Nat) : ConstOperand :=
  { ty := tyOf k, val := .scalar (.int ⟨bits, size⟩) }
def rawMutU64K : RigidTy := .rawPtr .mut u64K
def rawMutU8K : RigidTy := .rawPtr .mut u8K

/-- `Witness.u64Layout` (`WitLM3_1.lean:191`). -/
def u64Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `Witness.fnAbiU64` (`WitLM3_1.lean:200`). -/
def fnAbiU64 : FnAbi :=
  { args := [], ret := { layout := u64Layout, mode := .direct }, conv := .rust,
    canUnwind := false }

/-- `WitnessLM4_2.ptr4Body` (`WitLM4_2.lean:801`). -/
def ptr4Body (d₀ d₂ d₃ : RigidTy) (stmts : List Statement) (term0 : TerminatorKind) :
    CapturedMir where
  defPath := "lm_4_2_witness::ptr4"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf d₀, declOf u64K, declOf d₂, declOf d₃]
  basicBlocks := [
    { statements := stmts, terminator := mkTerm42 term0, isCleanup := false },
    { statements := [], terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `WitnessLM4_2.ptr4AnnealPre` (`WitLM4_2.lean:816`). -/
def ptr4AnnealPre (b : CapturedMir) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] }
    memory := (initMachineState b []).memory }

/-- `WitnessLM4_2.copyStmt` (`WitLM4_2.lean:2075`). -/
def copyStmt (srcIdx dstIdx : Nat) (countBits : Nat) : Statement :=
  mkStmt42 (.intrinsic
    (.copyNonOverlapping (.copy (local42 srcIdx)) (.copy (local42 dstIdx))
      (.constant (constInt usizeK countBits 8))))

/-- Successor state of a silent step (or `dflt`). -/
def nextState (n : MirStepNode) (dflt : MachineState) : MachineState :=
  match n with
  | .tau (.running s') => s'
  | _ => dflt

/-- The `n`-th state of legacy `stepMirFn b` from `s₀` (silent steps only). -/
def runN (b : CapturedMir) (s₀ : MachineState) : Nat → MachineState
  | 0 => s₀
  | n + 1 => nextState (stepMirFn b (runN b s₀ n)) (runN b s₀ n)

/-- Exact reconstruction of `WitnessLM4_2.copyMisalignedZeroBody`: advance
`_2 : *mut u64` to misaligned `offsetBytes = 1`, then
`copy_nonoverlapping(copy _2, copy _2, 0_usize)`. -/
def copyMisalignedZeroBody : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU8K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     mkStmt42 (.assign (local42 3) (.cast .ptrToPtr (.copy (local42 2)) (tyOf rawMutU8K))),
     mkStmt42 (.assign (local42 3)
       (.binaryOp .offset (.copy (local42 3)) (.constant (constInt usizeK 1 8)))),
     mkStmt42 (.assign (local42 2) (.cast .ptrToPtr (.copy (local42 3)) (tyOf rawMutU64K))),
     copyStmt 2 2 0]
    .return_

/-- **Legacy `stepMirFn` unsoundly steps past statement 5** (the misaligned
zero-count copy), and **`stepMirFnProto` executes statements 1–4 identically
but faults with `.ub` at statement 5**. -/
theorem wit_copyMisalignedZero_legacy_steps_proto_ub :
    ∃ s₁ s₂ s₃ s₄ : MachineState,
      let b := copyMisalignedZeroBody
      stepMirFn b (ptr4AnnealPre b) = MirStepNode.step s₁ ∧
      stepMirFn b s₁ = MirStepNode.step s₂ ∧
      stepMirFn b s₂ = MirStepNode.step s₃ ∧
      stepMirFn b s₃ = MirStepNode.step s₄ ∧
      stepMirFnProto .rejectNull b (ptr4AnnealPre b) = MirStepNode.step s₁ ∧
      stepMirFnProto .rejectNull b s₁ = MirStepNode.step s₂ ∧
      stepMirFnProto .rejectNull b s₂ = MirStepNode.step s₃ ∧
      stepMirFnProto .rejectNull b s₃ = MirStepNode.step s₄ ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 2 = some (.init (.ptr ⟨1, 1⟩ 8)) ∧
      stepMirFn b s₄ = MirStepNode.step (advanceStmt s₄ s₄.frame.locals) ∧
      stepMirFnProto .rejectNull b s₄ = MirStepNode.fail .ub ∧
      stepMirFnProto .allowRawIntrinsicNull b s₄ = MirStepNode.fail .ub :=
  let b := copyMisalignedZeroBody
  let s₀ := ptr4AnnealPre b
  ⟨runN b s₀ 1, runN b s₀ 2, runN b s₀ 3, runN b s₀ 4, by kernel_rfl, by kernel_rfl,
    by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩


/-- `WitnessLM4_2.copySingleMutBody` (`WitLM4_2.lean:2081`). -/
def copySingleMutBody (countBits : Nat) : CapturedMir :=
  ptr4Body unitK rawMutU64K rawMutU64K
    [mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
     copyStmt 2 2 countBits]
    .return_

/-- `wit_lm4_2_copy_nonoverlapping_zero_ok` (`WitLM4_2.lean:2091`) survives the
fix: the aligned aliasing zero-count copy still steps as the same no-op under
`stepMirFnProto`, preserving `_1 = 42_u64`. -/
theorem wit_copy_zero_ok_survives :
    let b := copySingleMutBody 0
    let s₀ := ptr4AnnealPre b
    stepMirFnProto .rejectNull b s₀ = stepMirFn b s₀ ∧
    stepMirFnProto .rejectNull b (runN b s₀ 1) =
      MirStepNode.step (advanceStmt (runN b s₀ 1) (runN b s₀ 1).frame.locals) ∧
    stepMirFn b (runN b s₀ 1) =
      MirStepNode.step (advanceStmt (runN b s₀ 1) (runN b s₀ 1).frame.locals) ∧
    get? (runN b s₀ 1).frame.locals 1 = some (.init (.scalar ⟨42, 8⟩)) :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-! ## 11. `pass_copy_nonoverlapping_zero_count` (`tests/miri-diff/corpus/src/lib.rs:532`) -/

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Memory of a normal root return node (or `dflt`). -/
def retMemOf (n : MirStepNode) (dflt : Memory) : Memory :=
  match n with
  | .ret (.normal (_, m)) => m
  | _ => dflt

/-- ```
/// let mut x: u32 = 50;
/// let p: *mut u32 = &raw mut x;
/// copy_nonoverlapping(p as *const u32, p, 0);
/// x
/// ```
Locals: `_0 : u32`, `_1 : u32` (`x`), `_2 : *mut u32` (`p`), `_3 : *const u32`
(the `p as *const u32` temporary). Statement `6` is the zero-count copy with
`src == dst` (both denote `x`). -/
def passCopyZeroCountBody : CapturedMir where
  defPath := "corpus::pass_copy_nonoverlapping_zero_count"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf u32K, declOf u32K, declOf (rawMutK u32K), declOf (rawConstK u32K)]
  basicBlocks := [
    { statements :=
        [mkStmt42 (.storageLive 1),
         mkStmt42 (.storageLive 2),
         mkStmt42 (.storageLive 3),
         mkStmt42 (.assign (local42 1) (.use (constU32 50))),
         mkStmt42 (.assign (local42 2) (.rawPtr .mut (local42 1))),
         mkStmt42 (.assign (local42 3)
           (.cast .ptrToPtr (.copy (local42 2)) (tyOf (rawConstK u32K)))),
         mkStmt42 (.intrinsic
           (.copyNonOverlapping (.copy (local42 3)) (.copy (local42 2)) (constUsize 0))),
         mkStmt42 (.assign (local42 0) (.use (.copy (local42 1))))],
      terminator := mkTerm42 .return_, isCleanup := false }]
  fnAbi := { args := [], ret := { layout := u32Layout, mode := .direct }, conv := .rust,
             canUnwind := false }
  layouts := emptyLayoutTable
  allocations := []

/-- The prototype steps cleanly through the `src == dst` zero-count copy
(no overlap UB, no Tree Borrows access), agreeing with the legacy evaluator on
every step, leaves `x = 50`, and the function returns `50`. -/
theorem pass_copy_nonoverlapping_zero_count_proto :
    let b := passCopyZeroCountBody
    let s₀ := initMachineState b []
    stepMirFnProto .rejectNull b (runN b s₀ 0) = MirStepNode.step (runN b s₀ 1) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 1) = MirStepNode.step (runN b s₀ 2) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 2) = MirStepNode.step (runN b s₀ 3) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 3) = MirStepNode.step (runN b s₀ 4) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 4) = MirStepNode.step (runN b s₀ 5) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 5) = MirStepNode.step (runN b s₀ 6) ∧
    (runN b s₀ 6).frame.stmtIdx = 6 ∧
    get? (runN b s₀ 6).frame.locals 1 = some (.init (.scalar ⟨50, 4⟩)) ∧
    get? (runN b s₀ 6).frame.locals 2 = get? (runN b s₀ 6).frame.locals 3 ∧
    stepMirFnProto .rejectNull b (runN b s₀ 6) =
      MirStepNode.step (advanceStmt (runN b s₀ 6) (runN b s₀ 6).frame.locals) ∧
    stepMirFn b (runN b s₀ 6) =
      MirStepNode.step (advanceStmt (runN b s₀ 6) (runN b s₀ 6).frame.locals) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 7) = MirStepNode.step (runN b s₀ 8) ∧
    get? (runN b s₀ 8).frame.locals 0 = some (.init (.scalar ⟨50, 4⟩)) ∧
    stepMirFnProto .rejectNull b (runN b s₀ 8) =
      MirStepNode.retNormal (.scalar ⟨50, 4⟩)
        (retMemOf (stepMirFn b (runN b s₀ 8)) emptyMemory) :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    by kernel_rfl, by kernel_rfl⟩

/-! ## 11b. `#[repr(C)]` / `#[repr(packed)]` fields and caller frames -/

/-- A type whose `layoutIdx` is out of range (structural layout only). -/
def tyNL (k : RigidTy) : Ty := { kind := k, layoutIdx := 99 }
def declNL (k : RigidTy) : LocalDecl := { mutability := .mut, ty := tyNL k, debugName := none }
def reprCK : RigidTy := .adt "proto::ReprC" []
def packedK : RigidTy := .adt "proto::Packed" []

/-- `#[repr(C)] struct ReprC { a: u8, b: u64 }`: size 16, align 8, offsets [0, 8]. -/
def reprCLayout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := .single 0,
    isUninhabited := false }

/-- `#[repr(C, packed)] struct Packed { a: u8, b: u64 }`: size 9, align 1, offsets [0, 1]. -/
def packedLayout : TypeLayout :=
  { size := { bytes := 9 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 1 }] [0, 1], variants := .single 0,
    isUninhabited := false }

def adtLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [reprCLayout, packedLayout] }

/-- Locals: `_0 : ()`, `_1 : ReprC`, `_2 : *const u64`, `_3 : *mut u64`,
`_4 : Packed`, `_5 : *mut ReprC`. -/
def adtDecls : List LocalDecl :=
  [declNL unitK, { mutability := .mut, ty := { kind := reprCK, layoutIdx := 0 }, debugName := none },
   declNL (rawConstK u64K), declNL (rawMutK u64K),
   { mutability := .mut, ty := { kind := packedK, layoutIdx := 1 }, debugName := none },
   declNL (rawMutK reprCK)]

/-- Tag `1`: `&raw mut _1.b` (8-aligned field of `ReprC`); tag `2`:
`&raw mut _4.b` (misaligned field of `Packed`); tag `3`: `&raw mut _1`. -/
def adtState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := { emptyMemory with
      borrows :=
        [{ tag := 1, targetLocal := 1, targetProjection := [.field 1 (tyNL u64K)],
           perm := .unique },
         { tag := 2, targetLocal := 4, targetProjection := [.field 1 (tyNL u64K)],
           perm := .unique },
         { tag := 3, targetLocal := 1, targetProjection := [], perm := .unique }],
      nextTag := 4 } }

def protoAdt (srcOp dstOp : Operand) (srcVal dstVal : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCountProto .rejectNull adtState srcOp dstOp adtDecls adtLayouts srcVal
    dstVal count adtState.frame.locals

def noopAdt : MirStepNode := MirStepNode.step (advanceStmt adtState adtState.frame.locals)

theorem reprC_field_aligned :
    protoAdt (cp 2) (cp 3) (.ptr ⟨1, 0⟩ 8) (.ptr ⟨1, 0⟩ 8) 0 = noopAdt := by kernel_rfl

/-- `&raw mut packed.b` as `*mut u64` (offset `1` in an align-1 struct) is `.ub`. -/
theorem packed_field_misaligned_ub :
    protoAdt (cp 2) (cp 3) (.ptr ⟨2, 0⟩ 8) (.ptr ⟨1, 0⟩ 8) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- Whole `ReprC` local copied as `*mut ReprC` (`elemAlign = 8`). -/
theorem reprC_whole_aligned :
    protoAdt (cp 5) (cp 5) (.ptr ⟨3, 0⟩ 8) (.ptr ⟨3, 0⟩ 8) 0 = noopAdt := by kernel_rfl

/-- Legacy accepts the misaligned packed field (the bug). -/
theorem packed_field_legacy_permissive :
    evalCopyNonOverlappingWithCount adtState (cp 2) (cp 3) adtDecls adtLayouts (.ptr ⟨2, 0⟩ 8)
        (.ptr ⟨1, 0⟩ 8) 0 adtState.frame.locals = noopAdt := by
  kernel_rfl

/-- Caller body whose `_4` is a `u64` (in the active fixture body `_4 : u8`). -/
def callerBody : CapturedMir where
  defPath := "proto::caller"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [declOf unitK, declOf u64K, declOf u64K, declOf u64K, declOf u64K]
  basicBlocks := []
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Active frame at depth `1` (one saved caller frame at depth `0`). Tag `5`
borrows the **caller's** `_4 : u64` (`targetFrameDepth = 0`); tag `6` borrows
`_4` of a frame at depth `7` that already returned. -/
def callerState : MachineState :=
  { st with
    memory := { st.memory with
      callStack :=
        [{ callerBody := callerBody,
           frame := { blockIdx := 0, stmtIdx := 0,
                      locals := [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨5, 8⟩)] },
           destination := loc 0 }],
      borrows := borrowsFix ++
        [{ tag := 5, targetLocal := 4, targetProjection := [], perm := .unique,
           targetFrameDepth := 0 },
         { tag := 6, targetLocal := 4, targetProjection := [], perm := .unique,
           targetFrameDepth := 7, allocDead := true }] } }

def protoCaller (k : RigidTy) (srcVal dstVal : Value) : MirStepNode :=
  evalCopyNonOverlappingWithCountProto .rejectNull callerState (cp 2) (cp 3) (declsFor k k)
    emptyLayoutTable srcVal dstVal 0 callerState.frame.locals

def noopCaller : MirStepNode := MirStepNode.step (advanceStmt callerState callerState.frame.locals)

/-- Caller-frame borrow alignment uses the **caller's** decls (`_4 : u64`), not
the active frame's (`_4 : u8`, which would be under-aligned). -/
theorem caller_frame_u64_aligned :
    protoCaller u64K (.ptr ⟨5, 0⟩ 8) (.ptr ⟨5, 0⟩ 8) = noopCaller := by kernel_rfl

/-- ... and a misaligned offset into it is `.ub`. -/
theorem caller_frame_u64_misaligned :
    protoCaller u64K (.ptr ⟨5, 4⟩ 8) (.ptr ⟨5, 0⟩ 8) = MirStepNode.fail .ub := by kernel_rfl

/-- A tag of an already-returned frame: base alignment unknown on `u64`
(fail closed) ... -/
theorem returned_frame_u64_unsupported :
    protoCaller u64K (.ptr ⟨6, 0⟩ 8) (.ptr ⟨5, 0⟩ 8) = MirStepNode.unsupported := by kernel_rfl

/-- ... but a dangling non-null pointer is fine for a zero-byte `u8` copy. -/
theorem returned_frame_u8_noop :
    protoCaller u8K (.ptr ⟨6, 0⟩ 8) (.ptr ⟨6, 3⟩ 8) = noopCaller := by kernel_rfl

/-! ## 11c. B1 hardening: 32-bit targets, `fieldLayouts`, aligned ZSTs,
frame-depth reuse (`allocDead`), `fnPtrs`, over-aligned `131072`, nested packed,
and TCB / `MirFuelFree` downstream breakage witnesses -/

/-- 32-bit target layout table (`pointerBits = 32`, `ptrBytes = 4`). -/
def layouts32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [] }

def decls32 (k : RigidTy) : List LocalDecl :=
  [declOf unitK, declOf usizeK, declOf (rawConstK k), declOf (rawMutK k), declOf u8K]

def st32 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨7, 4⟩), .uninit, .uninit,
                          .init (.scalar ⟨1, 1⟩)] }
    memory := { emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }],
      nextTag := 2 } }

def proto32 (policy : ZeroCountNullPolicy) (k : RigidTy) (srcVal dstVal : Value) (count : Nat) :
    MirStepNode :=
  evalCopyNonOverlappingWithCountProto policy st32 (cp 2) (cp 3) (decls32 k) layouts32 srcVal dstVal
    count st32.frame.locals

def noop32 : MirStepNode := MirStepNode.step (advanceStmt st32 st32.frame.locals)

theorem target32_layout_usize :
    resolveCopyElemLayout (decls32 usizeK) layouts32 (cp 2) (cp 3) = .ok 4 4 := by decide +kernel

theorem target32_layout_rawptr :
    resolveCopyElemLayout (decls32 (rawConstK u8K)) layouts32 (cp 2) (cp 3) = .ok 4 4 := by
  decide +kernel

theorem target32_layout_wideptr :
    resolveCopyElemLayout (decls32 (rawConstK (.slice u8K))) layouts32 (cp 2) (cp 3) = .ok 8 4 := by
  decide +kernel

/-- On 32-bit, `NonNull::<usize>::dangling()` (addr `4`, width `4`) steps cleanly. -/
theorem target32_dangling_usize_aligned :
    proto32 .rejectNull usizeK (.scalar ⟨4, 4⟩) (.scalar ⟨4, 4⟩) 0 = noop32 := by kernel_rfl

/-- On 32-bit, `NonNull::<*const u8>::dangling()` (addr `4`, width `4`) steps cleanly. -/
theorem target32_dangling_rawptr_aligned :
    proto32 .rejectNull (rawConstK u8K) (.scalar ⟨4, 4⟩) (.scalar ⟨4, 4⟩) 0 = noop32 := by
  kernel_rfl

/-- On 32-bit, live stack `usize` local is 4-aligned and steps cleanly. -/
theorem target32_stack_usize_aligned :
    proto32 .rejectNull usizeK (.ptr ⟨1, 0⟩ 4) (.ptr ⟨1, 0⟩ 4) 0 = noop32 := by kernel_rfl

/-- On 32-bit, addr `2` is misaligned for `usize` (`align = 4`) → `.ub`. -/
theorem target32_misaligned_usize_ub :
    proto32 .rejectNull usizeK (.scalar ⟨2, 4⟩) (.scalar ⟨4, 4⟩) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- On 32-bit, `allocId = 65536` wraps `65536 * 65536 = 2^32 ≡ 0 (mod 2^32)` → null `.ub`. -/
theorem target32_wrapped_null_ub :
    proto32 .rejectNull u8K (.ptr ⟨65536, 0⟩ 4) (.scalar ⟨1, 4⟩) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- On 32-bit, an 8-byte scalar is wrong-width → `.ub`. -/
theorem target32_wrong_width_8_ub :
    proto32 .rejectNull usizeK (.scalar ⟨4, 8⟩) (.scalar ⟨4, 4⟩) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- On 32-bit, `count = 2^29` for `usize` (`4` bytes) gives `2^31 > i32::MAX` → `.ub`,
whereas `count = 2^28` (`2^30 ≤ i32::MAX`) does NOT overflow (A0 wrongly used `8` bytes). -/
theorem target32_overflow_usize_ub :
    proto32 .rejectNull usizeK (.ptr ⟨1, 0⟩ 4) (.ptr ⟨1, 0⟩ 4) 536870912 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem target32_no_overflow_2pow28 :
    268435456 * 4 ≤ isizeMaxBytes (layoutPointerBytes layouts32) ∧
    isizeMaxBytes (layoutPointerBytes layouts32) < 536870912 * 4 := by
  decide +kernel

/-- Pointer-only ADT (`fn copy_pair(src: *const Pair, dst: *mut Pair)` with **no** local
of type `Pair`): `ptrLayout.fieldLayouts = [0]` points directly to `Pair`'s layout at
`entries[0]`. -/
def ptrLayoutTo0 : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar (.union (.pointer 0)),
    fields := .primitive, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

def ptrOnlyAdtLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [reprCLayout, ptrLayoutTo0] }

def ptrOnlyAdtDecls : List LocalDecl :=
  [declNL unitK,
   { mutability := .not, ty := { kind := rawConstK reprCK, layoutIdx := 1 }, debugName := none },
   { mutability := .not, ty := { kind := rawMutK reprCK, layoutIdx := 1 }, debugName := none }]

theorem ptr_only_adt_fieldLayouts_layout :
    resolveCopyElemLayout ptrOnlyAdtDecls ptrOnlyAdtLayouts (cp 1) (cp 2) = .ok 16 8 := by
  decide +kernel

theorem ptr_only_adt_fieldLayouts_aligned_noop :
    evalCopyNonOverlappingWithCountProto .rejectNull st (cp 1) (cp 2) ptrOnlyAdtDecls
        ptrOnlyAdtLayouts (danglingScalar 8) (danglingScalar 8) 0 st.frame.locals = noop := by
  kernel_rfl

theorem ptr_only_adt_fieldLayouts_misaligned_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull st (cp 1) (cp 2) ptrOnlyAdtDecls
        ptrOnlyAdtLayouts (danglingScalar 4) (danglingScalar 8) 0 st.frame.locals =
      MirStepNode.fail .ub := by
  kernel_rfl

/-- Aligned ZST `[u64; 0]`: `size = 0`, `align = 8`. Even with `count = 5`, total bytes = `0`,
but alignment `8` is strictly enforced! -/
def alignedZstK : RigidTy := .array u64K 0

theorem aligned_zst_layout :
    resolveCopyElemLayout (declsFor alignedZstK alignedZstK) emptyLayoutTable (cp 2) (cp 3) =
      .ok 0 8 := by
  decide +kernel

theorem aligned_zst_count5_aligned_noop :
    proto .rejectNull alignedZstK alignedZstK (danglingScalar 8) (danglingScalar 8) 5 = noop := by
  kernel_rfl

theorem aligned_zst_count5_misaligned_ub :
    proto .rejectNull alignedZstK alignedZstK (danglingScalar 4) (danglingScalar 8) 5 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem aligned_zst_count5_null_reject_ub :
    proto .rejectNull alignedZstK alignedZstK (danglingScalar 0) (danglingScalar 8) 5 =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem aligned_zst_count5_null_allowRaw_noop :
    proto .allowRawIntrinsicNull alignedZstK alignedZstK (danglingScalar 0) (danglingScalar 8) 5 =
      noop := by
  kernel_rfl

/-- Frame-depth reuse soundness (`allocDead = true`): tag `7` is a dead borrow from a returned
callee at depth `0` (whose `_1` may have been `u8`), while the active frame at depth `0` has
`_1 : u64`. Tag `8` is a dead projected borrow. -/
def deadReuseState : MachineState :=
  { st with
    memory := { st.memory with
      borrows := borrowsFix ++
        [{ tag := 7, targetLocal := 1, targetProjection := [], perm := .disabled,
           targetFrameDepth := 0, allocDead := true },
         { tag := 8, targetLocal := 1, targetProjection := [.field 0 (tyOf u8K)],
           perm := .disabled, targetFrameDepth := 0, allocDead := true }],
      globals := globalsFix ++
        [{ allocId := 11, bytes := List.replicate 16 (some 0), relocations := [],
           align := { bytes := 12 }, mutability := .not }],
      fnPtrs := [{ allocId := 65536, defPath := "proto::fn_item" }] } }

def protoDead (k : RigidTy) (srcVal dstVal : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCountProto .rejectNull deadReuseState (cp 2) (cp 3) (declsFor k k)
    emptyLayoutTable srcVal dstVal count deadReuseState.frame.locals

def noopDead : MirStepNode :=
  MirStepNode.step (advanceStmt deadReuseState deadReuseState.frame.locals)

/-- Dead borrow at reused frame depth on `u64` fails closed `.unsupported` (must NOT trust
the active frame's `_1 : u64` decl!). -/
theorem reused_frame_dead_u8_borrow_u64_unsupported :
    protoDead u64K (.ptr ⟨7, 0⟩ 8) (stackPtr 0) 0 = MirStepNode.unsupported := by kernel_rfl

/-- Dead non-projected borrow on `u8` (`elemAlign = 1`) still steps as a zero-byte no-op. -/
theorem reused_frame_dead_borrow_u8_noop :
    protoDead u8K (.ptr ⟨7, 0⟩ 8) (.ptr ⟨7, 3⟩ 8) 0 = noopDead := by kernel_rfl

/-- Dead projected borrow fails closed `.unsupported` even on `u8` (projection offset cannot
trust the reused frame's `LocalDecl`). -/
theorem reused_frame_dead_projected_borrow_u8_unsupported :
    protoDead u8K (.ptr ⟨8, 0⟩ 8) (danglingScalar 1) 0 = MirStepNode.unsupported := by kernel_rfl

/-- Registered `FnPtrEntry` (`s.memory.fnPtrs`): `u8` steps, misaligned `u64` is `.ub`,
aligned `u64` is `.unsupported` (unknown function-pointer base alignment). -/
theorem cc1_fnptr_u8_noop :
    protoDead u8K (.ptr ⟨65536, 0⟩ 8) (.ptr ⟨65536, 0⟩ 8) 0 = noopDead := by kernel_rfl

theorem cc4_fnptr_misaligned_u64_ub :
    protoDead u64K (.ptr ⟨65536, 3⟩ 8) (stackPtr 0) 0 = MirStepNode.fail .ub := by kernel_rfl

theorem cc6_fnptr_aligned_u64_unsupported :
    protoDead u64K (.ptr ⟨65536, 0⟩ 8) (stackPtr 0) 0 = MirStepNode.unsupported := by kernel_rfl

/-- Global allocation with malformed non-power-of-two `align = 12` fails closed on `u32`. -/
theorem cc6_global_nonpow2_align_u32_unsupported :
    protoDead u32K (.ptr ⟨11, 0⟩ 8) (danglingScalar 4) 0 = MirStepNode.unsupported := by kernel_rfl

/-- Over-aligned `#[repr(align(131072))]` struct (exceeding the `65536`-byte virtual page)
and nested `#[repr(packed)]` inside `#[repr(align(8))]`:
* `OuterOff0 { p: Packed }` → `&raw mut outer.p.b` at offset `1` is `.ub`;
* `OuterOff7 { pad: [u8; 7], p: Packed }` → `&raw mut outer2.p.b` at offset `7 + 1 = 8` steps! -/
def overAlignK : RigidTy := .adt "proto::OverAlign131072" []
def outerOff0K : RigidTy := .adt "proto::OuterOff0" []
def outerOff7K : RigidTy := .adt "proto::OuterOff7" []

def overAlignLayout : TypeLayout :=
  { size := { bytes := 131072 }, align := { bytes := 131072 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0, isUninhabited := false }

def outerOff0Layout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def outerOff7Layout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 7 }] [0, 1], variants := .single 0,
    isUninhabited := false, fieldLayouts := [99, 1] }

def extAdtLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [reprCLayout, packedLayout, overAlignLayout, outerOff0Layout, outerOff7Layout] }

def extAdtDecls : List LocalDecl :=
  [declNL unitK,
   { mutability := .mut, ty := { kind := overAlignK, layoutIdx := 2 }, debugName := none },
   declNL (rawConstK overAlignK),
   declNL (rawMutK overAlignK),
   { mutability := .mut, ty := { kind := outerOff0K, layoutIdx := 3 }, debugName := none },
   { mutability := .mut, ty := { kind := outerOff7K, layoutIdx := 4 }, debugName := none },
   declNL (rawConstK u64K),
   declNL (rawMutK u64K)]

def extAdtState : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := List.replicate 8 .uninit }
    memory := { emptyMemory with
      borrows :=
        [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique },
         { tag := 2, targetLocal := 4,
           targetProjection := [.field 0 { kind := packedK, layoutIdx := 1 },
                                .field 1 (tyNL u64K)],
           perm := .unique },
         { tag := 3, targetLocal := 5,
           targetProjection := [.field 1 { kind := packedK, layoutIdx := 1 },
                                .field 1 (tyNL u64K)],
           perm := .unique }],
      nextTag := 4 } }

def noopExtAdt : MirStepNode :=
  MirStepNode.step (advanceStmt extAdtState extAdtState.frame.locals)

theorem overaligned_131072_aligned_noop :
    evalCopyNonOverlappingWithCountProto .rejectNull extAdtState (cp 2) (cp 3) extAdtDecls
        extAdtLayouts (.ptr ⟨1, 0⟩ 8) (.ptr ⟨1, 0⟩ 8) 0 extAdtState.frame.locals = noopExtAdt := by
  kernel_rfl

theorem overaligned_131072_offset65536_misaligned_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull extAdtState (cp 2) (cp 3) extAdtDecls
        extAdtLayouts (.ptr ⟨1, 65536⟩ 8) (.ptr ⟨1, 0⟩ 8) 0 extAdtState.frame.locals =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem nested_packed_in_align8_off1_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull extAdtState (cp 6) (cp 7) extAdtDecls
        extAdtLayouts (.ptr ⟨2, 0⟩ 8) (danglingScalar 8) 0 extAdtState.frame.locals =
      MirStepNode.fail .ub := by
  kernel_rfl

theorem nested_packed_in_align8_off8_noop :
    evalCopyNonOverlappingWithCountProto .rejectNull extAdtState (cp 6) (cp 7) extAdtDecls
        extAdtLayouts (.ptr ⟨3, 0⟩ 8) (.ptr ⟨3, 0⟩ 8) 0 extAdtState.frame.locals = noopExtAdt := by
  kernel_rfl

/-- **TCB downstream breakage witness (`evalStmt_storageRevive_old_ptr_deref_ub`)**:
with `count = 1` (`n + 1`) on ZST `()` and a disabled `allocDead = true` stack borrow,
the zero-byte copy is a valid no-op (matching Rust/Miri), NOT `.fail .ub`. Thus
`Statements.evalStmt_storageRevive_old_ptr_deref_ub` in BOTH `V2026_06_01` and
`V2026_08_01` must add a non-ZST hypothesis to its `copy_nonoverlapping` conjuncts! -/
theorem tcb_storageRevive_zst_count1_noop :
    protoDead unitK (.ptr ⟨7, 0⟩ 8) (.ptr ⟨7, 0⟩ 8) 1 = noopDead := by kernel_rfl

/-- **`MirFuelFree.evalCopyNonOverlappingWithCount_borrows_nil` breakage witness**:
with `s.memory.borrows = []`, `count = 5` (`Nat.beq 5 0 = false`) on ZST `()` steps as
a no-op instead of faulting, falsifying the old `Nat.beq countBits 0 = true` disjunct! -/
def emptyBorrowsState : MachineState :=
  { st with memory := { emptyMemory with borrows := [] } }

theorem mirFuelFree_borrows_nil_zst_count5_noop :
    evalCopyNonOverlappingWithCountProto .rejectNull emptyBorrowsState (cp 2) (cp 3)
        (declsFor unitK unitK) emptyLayoutTable (danglingScalar 1) (danglingScalar 1) 5
        emptyBorrowsState.frame.locals =
      MirStepNode.step (advanceStmt emptyBorrowsState emptyBorrowsState.frame.locals) := by
  kernel_rfl

/-! ## 11d. A1: target-dependent primitive alignment (32-bit, 16-bit) and alias operands

`align_of::<u64>()` / `f64` / `i64` is `4` on `i686` but `8` on `armv7`, and
`u128` varies across 32-bit targets; on 16-bit targets (AVR) even `u16`,
`usize`, and pointers are 1-aligned. A structural table that claims `8` for a
`u64` **place** on a 32-bit target over-estimates the backing local's alignment,
so an align-8 element (`AtomicU64`, `#[repr(align(8))]`) copied through a
pointer to a 4-aligned `u64` local would be accepted although it may be
misaligned (unsound). A1 makes target-dependent primitives unresolved off
64-bit targets (fail closed) unless a `LayoutTable` entry is available. -/

def atomic64K : RigidTy := .adt "core::sync::atomic::AtomicU64" []

/-- `AtomicU64` on `i686`: size 8, align 8 (whereas `u64` is only 4-aligned there). -/
def atomic64Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0], variants := .single 0, isUninhabited := false }

def layouts32a : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true, entries := [atomic64Layout, atomic64Layout] }

/-- Locals: `_0 : ()`, `_1 : u64` (no layout entry), `_2 : *const AtomicU64`,
`_3 : *mut AtomicU64`, `_4 : AtomicU64` (layout entry `1`), `_5 : *const u64`,
`_6 : *mut u64`, `_7 : PtrAlias` (unnormalized alias). -/
def decls32a : List LocalDecl :=
  [declNL unitK, declNL u64K, declNL (rawConstK atomic64K), declNL (rawMutK atomic64K),
   { mutability := .mut, ty := { kind := atomic64K, layoutIdx := 1 }, debugName := none },
   declNL (rawConstK u64K), declNL (rawMutK u64K), declNL (.alias "proto::PtrAlias" [])]

def st32a : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨7, 8⟩), .uninit, .uninit, .uninit, .uninit,
                          .uninit, .uninit] }
    memory := { emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }],
      nextTag := 2 } }

def proto32a (srcOp dstOp : Operand) (srcVal dstVal : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCountProto .rejectNull st32a srcOp dstOp decls32a layouts32a srcVal
    dstVal count st32a.frame.locals

def noop32a : MirStepNode := MirStepNode.step (advanceStmt st32a st32a.frame.locals)

theorem target32_atomic64_layout :
    resolveCopyElemLayout decls32a layouts32a (cp 2) (cp 3) = .ok 8 8 := by decide +kernel

/-- **Soundness (A1)**: an align-8 `AtomicU64` copied through `&raw mut x as
*mut AtomicU64` where `x : u64` lives in a 4-aligned (`i686`) local must not be
accepted; the backing alignment is unknown, so fail closed. -/
theorem target32_atomic64_over_u64_local_unsupported :
    proto32a (cp 2) (cp 3) (.ptr ⟨1, 0⟩ 4) (.ptr ⟨1, 0⟩ 4) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- A 32-bit `u64` pointee has target-dependent alignment: no `.ub` claim for a
4-aligned dangling `NonNull::<u64>::dangling()`-style address (fail closed). -/
theorem target32_u64_dangling4_unsupported :
    proto32a (cp 5) (cp 6) (.scalar ⟨4, 4⟩) (.scalar ⟨4, 4⟩) 0 = MirStepNode.unsupported := by
  kernel_rfl

/-- ... while the authoritative-layout `AtomicU64` still decides alignment
precisely on 32-bit dangling addresses. -/
theorem target32_atomic64_dangling8_noop :
    proto32a (cp 2) (cp 3) (.scalar ⟨8, 4⟩) (.scalar ⟨8, 4⟩) 0 = noop32a := by kernel_rfl

theorem target32_atomic64_dangling4_ub :
    proto32a (cp 2) (cp 3) (.scalar ⟨4, 4⟩) (.scalar ⟨8, 4⟩) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- An unnormalized alias-typed operand is **not** statically a non-pointer:
the pointee comes from the other operand (zero-byte no-op here) ... -/
theorem alias_operand_unknown_noop :
    proto32a (cp 7) (cp 3) (.scalar ⟨8, 4⟩) (.scalar ⟨8, 4⟩) 0 = noop32a := by kernel_rfl

theorem alias_operand_layout_unsupported :
    resolveCopyElemLayout decls32a layouts32a (cp 7) (cp 7) = .unsupported := by decide +kernel

/-- ... and a non-zero count with an alias-typed operand is delegated unchanged
to the legacy evaluator (B1 returned a spurious `.ub` here). -/
theorem alias_operand_nonzero_count_legacy :
    proto32a (cp 7) (cp 7) (.ptr ⟨1, 0⟩ 4) (.ptr ⟨1, 0⟩ 4) 1 =
      evalCopyNonOverlappingWithCount st32a (cp 7) (cp 7) decls32a layouts32a (.ptr ⟨1, 0⟩ 4)
        (.ptr ⟨1, 0⟩ 4) 1 st32a.frame.locals :=
  evalCopyNonOverlappingWithCountProto_unresolved_nonzero_count _ _ _ _ _ _ _ _ _ _
    alias_operand_layout_unsupported (by decide) rfl

/-! ### A1: pointer-width gate on the delegated non-zero path, and shape-first order -/

/-- Locals: `_0 : ()`, `_1 : u64 = 42`, `_2 : *const u64`, `_3 : *mut u64`,
`_4 : u8`, `_5 : u64 = 0`; tag `1` → `_1`, tag `4` → `_5`. -/
def declsW : List LocalDecl :=
  [declOf unitK, declOf u64K, declOf (rawConstK u64K), declOf (rawMutK u64K), declOf u8K,
   declOf u64K]

def stW : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0,
               locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit,
                          .init (.scalar ⟨7, 1⟩), .init (.scalar ⟨0, 8⟩)] }
    memory := { emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique },
                  { tag := 4, targetLocal := 5, targetProjection := [], perm := .unique }],
      nextTag := 5 } }

/-- Copied value in `_5` after a step (or `999`). -/
def slot5Of : MirStepNode → Nat
  | .tau (.running s') =>
    match get? s'.frame.locals 5 with
    | some (.init (.scalar sc)) => sc.bits
    | _ => 999
  | _ => 999

/-- The legacy non-zero path is **width-blind**: `.ptr p 1` / `.ptr p 99` on a
64-bit target still copy `42` into `_5`. -/
theorem nonzero_wrong_width_ptr_legacy_copies :
    slot5Of (evalCopyNonOverlappingWithCount stW (cp 2) (cp 3) declsW emptyLayoutTable
        (.ptr ⟨1, 0⟩ 1) (.ptr ⟨4, 0⟩ 99) 1 stW.frame.locals) = 42 := by
  decide +kernel

/-- The prototype rejects the malformed pointer values (`.ub`) on every count ... -/
theorem nonzero_wrong_width_ptr_proto_ub :
    evalCopyNonOverlappingWithCountProto .rejectNull stW (cp 2) (cp 3) declsW emptyLayoutTable
        (.ptr ⟨1, 0⟩ 1) (.ptr ⟨4, 0⟩ 99) 1 stW.frame.locals = MirStepNode.fail .ub := by
  kernel_rfl

/-- ... while delegating well-formed pointers unchanged (the copy still happens). -/
theorem nonzero_well_formed_ptr_proto_copies :
    slot5Of (evalCopyNonOverlappingWithCountProto .rejectNull stW (cp 2) (cp 3) declsW
        emptyLayoutTable (.ptr ⟨1, 0⟩ 8) (.ptr ⟨4, 0⟩ 8) 1 stW.frame.locals) = 42 := by
  decide +kernel

/-- **Shape-first order** (`Intrinsics.copyWith` reads both pointers before any
alignment check): `src` with unknown alignment (`&raw mut u8_local as *mut u64`)
and a non-pointer `dst` is `.ub` (B1: `.unsupported`). -/
theorem zero_shape_first_ub :
    proto .rejectNull u64K u64K u8LocalPtr .unit 0 = MirStepNode.fail .ub := by kernel_rfl

/-- A statically scalar operand (`u64`) is still rejected as `.ub`. -/
theorem nonptr_scalar_operand_still_ub :
    proto32a (cp 1) (cp 3) (.scalar ⟨8, 4⟩) (.scalar ⟨8, 4⟩) 0 = MirStepNode.fail .ub := by
  kernel_rfl

/-- 16-bit target (AVR-like, `pointerBits = 16`): `u16` / `usize` alignment is
target-dependent (AVR: `1`), so no structural alignment is claimed. -/
def layouts16 : LayoutTable := { pointerBits := 16, isLittleEndian := true, entries := [] }

theorem target16_u16_unresolved :
    resolveCopyElemLayout (declsFor u8K (.uint .u16)) layouts16 (cp 3) (cp 3) = .unsupported := by
  decide +kernel

theorem target16_usize_unresolved :
    resolveCopyElemLayout (declsFor usizeK usizeK) layouts16 (cp 2) (cp 3) = .unsupported := by
  decide +kernel

theorem target16_u8_resolved :
    resolveCopyElemLayout (declsFor u8K u8K) layouts16 (cp 2) (cp 3) = .ok 1 1 := by
  decide +kernel

/-- 64-bit targets keep the full structural table. -/
theorem target64_u64_resolved :
    resolveCopyElemLayout (declsFor u64K u64K) emptyLayoutTable (cp 2) (cp 3) = .ok 8 8 := by
  decide +kernel

/-! ## 12. Terminator-level call path inherits the fix -/

/-- `evalCopyNonOverlappingCallProto` with a misaligned dangling `src` faults
before `finishMemIntrinsicCall`. -/
theorem call_proto_misaligned_ub :
    evalCopyNonOverlappingCallProto .rejectNull st (declsFor u64K u64K) emptyLayoutTable
        [cp 2, cp 3, constUsize 0] [danglingScalar 9, danglingScalar 8, .scalar ⟨0, 8⟩]
        st.frame.locals (loc 0) 1 = MirStepNode.fail .ub := by
  kernel_rfl

/-- ... while the legacy terminator path accepts it. -/
theorem call_legacy_misaligned_permissive :
    evalCopyNonOverlappingCall st (declsFor u64K u64K) emptyLayoutTable
        [cp 2, cp 3, constUsize 0] [danglingScalar 9, danglingScalar 8, .scalar ⟨0, 8⟩]
        st.frame.locals (loc 0) 1 =
      finishMemIntrinsicCall st noop (loc 0) 1 := by
  kernel_rfl

/-! ## 13. `V2026_08_01` carries the identical bug -/

/-- `V2026_08_01.evalCopyNonOverlappingWithCount` also steps on `count = 0`
for *every* operand pair (here: two `.unit` values), so the TCB patch must be
applied to both snapshots. -/
theorem v2026_08_01_zero_count_permissive
    (s : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState)
    (src dst : Trusted.Rustc.V2026_08_01.MirAst.Operand)
    (decls : List Trusted.Rustc.V2026_08_01.MirAst.LocalDecl)
    (layouts : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (srcVal dstVal : Trusted.Rustc.V2026_08_01.MirSemantics.Value)
    (locals₃ : List Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot) :
    Trusted.Rustc.V2026_08_01.MirSemantics.evalCopyNonOverlappingWithCount s src dst decls layouts
        srcVal dstVal 0 locals₃ =
      Trusted.Rustc.V2026_08_01.MirSemantics.MirStepNode.step
        (Trusted.Rustc.V2026_08_01.MirSemantics.advanceStmt s locals₃) :=
  rfl

/-- Same for `V2026_06_01` (the bug the prototype fixes). -/
theorem v2026_06_01_zero_count_permissive
    (s : MachineState) (src dst : Operand) (decls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst decls layouts srcVal dstVal 0 locals₃ =
      MirStepNode.step (advanceStmt s locals₃) :=
  rfl


/-! ## 13b. Machine-checked dual-snapshot port audit (A1)

The TCB patch inserts the prototype's statement-level definitions into
`MirSemantics/Statements.lean` *before* `evalCopyNonOverlappingWithCount` in
**both** snapshots. This audit walks the transitive closure of
`evalCopyNonOverlappingProto` / `evalCopyNonOverlappingWithCountProto` through
`Anneal.Proto.ZeroCountCopyAlign.*`, collects every referenced
`Trusted.Rustc.V2026_06_01.*` constant, and checks that its `V2026_08_01`
counterpart (1) exists, (2) is not defined in a module that imports
`Statements` (`Terminators`, `Eval`, `Machine`), and (3) if defined in
`Statements`, starts no later than `V2026_08_01.evalCopyNonOverlappingWithCount`
(the patched definition itself, renamed in place). B1's `directTyLayout?` used
`layoutValidForResolvedAdt`, which exists only in `V2026_06_01` — this audit
fails on that commit. -/

open Lean Elab Command in
/-- Collect the `Trusted.Rustc.V2026_06_01.*` constants reachable from `roots`
through constants under `Anneal.Proto.ZeroCountCopyAlign`. -/
partial def protoTrustedDeps (env : Environment) (roots : List Name) : NameSet := Id.run do
  let protoPfx : Name := `Anneal.Proto.ZeroCountCopyAlign
  let trustedPfx : Name := `Trusted.Rustc.V2026_06_01
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := roots
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if trustedPfx.isPrefixOf n then
        out := out.insert n
      else if protoPfx.isPrefixOf n &&
          !(n.getString!.startsWith "_sparseCasesOn") then
        -- `_sparseCasesOn_k` auxiliaries are regenerated per snapshot by the
        -- match compiler; constructor-set differences are audited separately.
        match env.find? n with
        | some ci =>
          let consts := ci.type.getUsedConstants ++
            (match ci.value? with
             | some v => v.getUsedConstants
             | none => #[])
          todo := consts.toList ++ todo
        | none => pure ()
  return out

open Lean Elab Command in
/-- Map `Trusted.Rustc.V2026_06_01.x` to `Trusted.Rustc.V2026_08_01.x`. -/
def toV0801 (n : Name) : Name :=
  n.replacePrefix `Trusted.Rustc.V2026_06_01 `Trusted.Rustc.V2026_08_01

open Lean Elab Command in
elab "#zc_port_audit" : command => do
  let env ← getEnv
  let deps := protoTrustedDeps env
    [``Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingProto,
     ``Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto]
  let anchor := ``Trusted.Rustc.V2026_08_01.MirSemantics.evalCopyNonOverlappingWithCount
  let some anchorRange ← liftCoreM (findDeclarationRanges? anchor)
    | throwError "no declaration range for {anchor}"
  let anchorLine := anchorRange.range.pos.line
  let banned : List Name :=
    [`Trusted.Rustc.V2026_08_01.MirSemantics.Terminators,
     `Trusted.Rustc.V2026_08_01.MirSemantics.Eval,
     `Trusted.Rustc.V2026_08_01.MirSemantics.Machine]
  let stmtMod : Name := `Trusted.Rustc.V2026_08_01.MirSemantics.Statements
  let mut problems : Array String := #[]
  for n in deps.toList do
    let n' := toV0801 n
    match env.getModuleIdxFor? n' with
    | none => problems := problems.push s!"missing {n'}"
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if banned.contains mod then
        problems := problems.push s!"{n'} defined in {mod} (imports Statements)"
      else if mod == stmtMod then
        match ← liftCoreM (findDeclarationRanges? n') with
        | some r =>
          if r.range.pos.line > anchorLine then
            problems := problems.push s!"{n'} defined after the patch point (line {r.range.pos.line})"
        | none =>
          -- Auxiliary (`match_k`, structure projections, constructors) of an
          -- earlier declaration: check its parent declaration instead.
          match ← liftCoreM (findDeclarationRanges? n'.getPrefix) with
          | some r =>
            if r.range.pos.line > anchorLine then
              problems := problems.push s!"{n'} defined after the patch point"
          | none => problems := problems.push s!"no range for {n'}"
  -- Constructor-set differences of every inductive type the prototype matches on.
  let mut inducts : NameSet := {}
  for n in deps.toList do
    match env.find? n with
    | some (.ctorInfo c) => inducts := inducts.insert c.induct
    | some (.recInfo _) => inducts := inducts.insert n.getPrefix
    | some (.inductInfo _) => inducts := inducts.insert n
    | _ =>
      if n.getString! == "casesOn" then inducts := inducts.insert n.getPrefix
  let mut ctorDiffs : Array String := #[]
  for i in inducts.toList do
    match env.find? i, env.find? (toV0801 i) with
    | some (.inductInfo a), some (.inductInfo b) =>
      let an := a.ctors.map (·.getString!)
      let bn := b.ctors.map (·.getString!)
      let onlyA := an.filter (fun c => !bn.contains c)
      let onlyB := bn.filter (fun c => !an.contains c)
      if !onlyA.isEmpty || !onlyB.isEmpty then
        ctorDiffs := ctorDiffs.push
          s!"{i.getString!}: only V2026_06_01 {onlyA}, only V2026_08_01 {onlyB}"
    | some (.inductInfo _), _ => ctorDiffs := ctorDiffs.push s!"missing inductive {toV0801 i}"
    | _, _ => pure ()
  if deps.size < 100 then
    problems := problems.push s!"suspiciously few dependencies ({deps.size})"
  let sorted := problems.qsort (· < ·)
  let sortedD := ctorDiffs.qsort (· < ·)
  logInfo m!"port audit problems: {sorted.toList}; constructor-set differences: {sortedD.toList}"

/--
info: port audit problems: []; constructor-set differences: [Value: only V2026_06_01 [uninit], only V2026_08_01 []]
-/
#guard_msgs in
#zc_port_audit

/-! ## 14. Generic refinement / equivalence corollaries -/

/-- Concrete instance of the soundness refinement on the fixture. -/
example :
    proto .allowRawIntrinsicNull u64K u64K (stackPtr 0) (stackPtr 0) 0 = noop :=
  evalCopyNonOverlappingWithCountProto_rejectNull_refines _ _ _ _ _ _ _ _ _ _
    cc1_stack_aligned_same_ptr

/-- `NonNull::<u64>::dangling()` vs. `lean-miri` on the resolved fragment. -/
example : protoFragment .allowRawIntrinsicNull 8 0 8 (exactView 8 8) (exactView 8 8) =
    some (miriCopyWithRef 8 0 8 8 8 8) :=
  protoFragment_allowRaw_eq_miri 8 0 8 8 8 8 rfl

example : miriCopyWithRef 8 0 8 8 8 9 = .ub := rfl
example : miriCopyWithRef 8 0 8 8 0 0 = .noop := rfl
example : corePtrCopyRef false 8 0 1 1 0 0 = .ub := rfl
example : corePtrCopyRef true 8 0 1 1 0 0 = .noop := rfl

/-- Bundle of the top-level guarantees (for the axiom audit), including end-to-end
`evalCopyNonOverlappingWithCountProto` ↔ `lean-miri` / `core::ptr` equivalence,
lifted `stepMirFnProto` / `evalCopyNonOverlappingCallProto` soundness refinement,
`resolveCopyElemLayout_align_pow2`, and `copyIsUnsizedRigidTy_eq`. -/
theorem zeroCountCopyAlignProto_bundle :
    (∀ s s' src dst ld ly sv dv c l,
      evalCopyNonOverlappingWithCountProto .rejectNull s src dst ld ly sv dv c l =
          MirStepNode.step s' →
        evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst ld ly sv dv c l =
          MirStepNode.step s') ∧
    (∀ body s s',
      stepMirFnProto .rejectNull body s = MirStepNode.step s' →
        stepMirFnProto .allowRawIntrinsicNull body s = MirStepNode.step s') ∧
    (∀ s s' ld ly ao av l' dst bb,
      evalCopyNonOverlappingCallProto .rejectNull s ld ly ao av l' dst bb = MirStepNode.step s' →
        evalCopyNonOverlappingCallProto .allowRawIntrinsicNull s ld ly ao av l' dst bb =
          MirStepNode.step s') ∧
    (∀ s src dst ld ly sb db c sz al l3,
      resolveCopyElemLayout ld ly src dst = .ok sz al →
      c * sz = 0 →
      sb < scalarModulus (layoutPointerBytes ly) →
      db < scalarModulus (layoutPointerBytes ly) →
      evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst ld ly
          (.scalar ⟨sb, layoutPointerBytes ly⟩) (.scalar ⟨db, layoutPointerBytes ly⟩) c l3 =
        refOutcomeToStep s l3
          (.some (miriCopyWithRef (layoutPointerBytes ly) c sz al sb db))) ∧
    (∀ s src dst ld ly sb db c sz al l3,
      resolveCopyElemLayout ld ly src dst = .ok sz al →
      c * sz = 0 →
      sb < scalarModulus (layoutPointerBytes ly) →
      db < scalarModulus (layoutPointerBytes ly) →
      evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst ld ly
          (.scalar ⟨sb, layoutPointerBytes ly⟩) (.scalar ⟨db, layoutPointerBytes ly⟩) c l3 =
        refOutcomeToStep s l3
          (.some (corePtrCopyRef true (layoutPointerBytes ly) c sz al sb db))) ∧
    (∀ s src dst ld ly sb db c sz al l3,
      resolveCopyElemLayout ld ly src dst = .ok sz al →
      c * sz = 0 →
      sb < scalarModulus (layoutPointerBytes ly) →
      db < scalarModulus (layoutPointerBytes ly) →
      evalCopyNonOverlappingWithCountProto .rejectNull s src dst ld ly
          (.scalar ⟨sb, layoutPointerBytes ly⟩) (.scalar ⟨db, layoutPointerBytes ly⟩) c l3 =
        refOutcomeToStep s l3
          (.some (corePtrCopyRef false (layoutPointerBytes ly) c sz al sb db))) ∧
    (∀ ld ly src dst sz al,
      resolveCopyElemLayout ld ly src dst = .ok sz al →
      isPowTwoAlign al = true ∧ 1 ≤ al) ∧
    (∀ fuel ty, copyIsUnsizedRigidTy fuel ty = isUnsizedRigidTy fuel ty) :=
  ⟨evalCopyNonOverlappingWithCountProto_rejectNull_refines,
    stepMirFnProto_rejectNull_refines,
    evalCopyNonOverlappingCallProto_rejectNull_refines,
    evalCopyNonOverlappingWithCountProto_scalar_allowRaw_eq_miri,
    evalCopyNonOverlappingWithCountProto_scalar_allowRaw_eq_corePtr,
    evalCopyNonOverlappingWithCountProto_scalar_rejectNull_eq_corePtrStrict,
    resolveCopyElemLayout_align_pow2,
    copyIsUnsizedRigidTy_eq⟩

/-! ## 15. Standard-axioms audit -/

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.zeroCountCopyAlignProto_bundle' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms zeroCountCopyAlignProto_bundle

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_policy_difference' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_policy_difference

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_scalar_rejectNull_refines_miri' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_scalar_rejectNull_refines_miri

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.zeroPtrView_stack_live_addr_eq_ptrAddress?' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.zeroPtrView_stack_live_addr_eq_ptrAddress?

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.cc5_bdCopyZeroScalars_proto_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.cc5_bdCopyZeroScalars_proto_ub

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.target32_dangling_usize_aligned' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.target32_dangling_usize_aligned

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.ptr_only_adt_fieldLayouts_aligned_noop' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.ptr_only_adt_fieldLayouts_aligned_noop

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.reused_frame_dead_u8_borrow_u64_unsupported' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.reused_frame_dead_u8_borrow_u64_unsupported

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.tcb_storageRevive_zst_count1_noop' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.tcb_storageRevive_zst_count1_noop


/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.wit_copyMisalignedZero_legacy_steps_proto_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.wit_copyMisalignedZero_legacy_steps_proto_ub

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.pass_copy_nonoverlapping_zero_count_proto' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.pass_copy_nonoverlapping_zero_count_proto

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.packed_field_misaligned_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.packed_field_misaligned_ub

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.caller_frame_u64_aligned' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.caller_frame_u64_aligned

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.cc3_null_ptr_u8' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.cc3_null_ptr_u8

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.cc2_zst_count5_proto' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.cc2_zst_count5_proto

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.stepMirFn_eq_of_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.stepMirFn_eq_of_copy

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.stepMirFnProto_eq_of_not_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.stepMirFnProto_eq_of_not_copy

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_zero_noop' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_zero_noop

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_nonzero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_nonzero

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_unresolved_nonzero_count' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_unresolved_nonzero_count

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.protoFragment_policy_difference' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.protoFragment_policy_difference

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.protoFragment_overflow_eq_miri' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.protoFragment_overflow_eq_miri

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.target32_atomic64_over_u64_local_unsupported' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.target32_atomic64_over_u64_local_unsupported

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.alias_operand_nonzero_count_legacy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.alias_operand_nonzero_count_legacy

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.target16_u16_unresolved' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.target16_u16_unresolved

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.copyLayoutValidForResolvedAdt_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.copyLayoutValidForResolvedAdt_eq

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_malformed_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.evalCopyNonOverlappingWithCountProto_malformed_ub

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.zeroByteCopyPrecheck_eq_views' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.zeroByteCopyPrecheck_eq_views

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.nonzero_wrong_width_ptr_proto_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.nonzero_wrong_width_ptr_proto_ub

/-- info: 'Anneal.Proto.ZeroCountCopyAlign.Tests.zero_shape_first_ub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.Proto.ZeroCountCopyAlign.Tests.zero_shape_first_ub

end Anneal.Proto.ZeroCountCopyAlign.Tests
