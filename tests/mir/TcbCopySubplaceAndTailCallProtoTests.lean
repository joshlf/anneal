import Anneal.TcbCopySubplaceAndTailCallPrototype

/-!
# TCB Subplace `copy_nonoverlapping` & `tailCall` / `opaqueCast` Prototype Canary Suite

Positive and negative non-vacuity canaries, edge-case regression tests, and
`#print axioms` audits for `Anneal.TcbCopySubplaceAndTailCallPrototype`.
-/

namespace Anneal.TcbCopySubplaceAndTailCallProtoTests

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.TcbCopySubplaceAndTailCallPrototype

/-! ## 1. Bug 1 Canaries: Multi-Element Subplace `copy_nonoverlapping` -/

/--
Canary 1A (Campaign #14): Unpatched `Trusted` returns `19`, while repaired
prototype returns `112` (`5 ^ (22 ^ 99)`), matching live Miri.
-/
theorem canary_bug1_campaign14_unpatched_vs_repaired :
    evalMirDiffTagBounded 512
      Campaign14_pass_transmute_u32_byte_array_le__b0_c6.body
      (initMachineStateWithMemoryAndCallees
        Campaign14_pass_transmute_u32_byte_array_le__b0_c6.body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 19 1 ∧
    evalMirDiffTagBoundedProto 512
      Campaign14_pass_transmute_u32_byte_array_le__b0_c6.body
      (initMachineStateWithMemoryAndCallees
        Campaign14_pass_transmute_u32_byte_array_le__b0_c6.body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 112 1 :=
  ⟨Campaign14_pass_transmute_u32_byte_array_le__b0_c6.unpatched_tag_pass_transmute_u32_byte_array_le__b0_c6,
   Campaign14_pass_transmute_u32_byte_array_le__b0_c6.confirm_repaired_tag_pass_transmute_u32_byte_array_le__b0_c6⟩

/--
Canary 1B (Campaign #15): Unpatched `Trusted` returns `70`, while repaired
prototype returns `4` (`30 ^ (88 ^ 66)`), matching live Miri.
-/
theorem canary_bug1_campaign15_unpatched_vs_repaired :
    evalMirDiffTagBounded 512
      Campaign15_pass_enum_discriminant_valid__b2_c9.body
      (initMachineStateWithMemoryAndCallees
        Campaign15_pass_enum_discriminant_valid__b2_c9.body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 70 1 ∧
    evalMirDiffTagBoundedProto 512
      Campaign15_pass_enum_discriminant_valid__b2_c9.body
      (initMachineStateWithMemoryAndCallees
        Campaign15_pass_enum_discriminant_valid__b2_c9.body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 4 1 :=
  ⟨Campaign15_pass_enum_discriminant_valid__b2_c9.unpatched_tag_pass_enum_discriminant_valid__b2_c9,
   Campaign15_pass_enum_discriminant_valid__b2_c9.confirm_repaired_tag_pass_enum_discriminant_valid__b2_c9⟩

private def mkU32 (n : Nat) : Value := .scalar { bits := n, sizeBytes := 4 }

private def dummySrcOp : Operand := .copy ⟨1, []⟩
private def dummyDstOp : Operand := .copy ⟨2, []⟩

/--
Canary 1C (Non-zero source and destination subplace indices):
Copying `2` elements from `&raw const src[1]` (`src = [10, 20, 30, 40]`) into
`&raw mut dst[1]` (`dst = [1, 2, 3, 4]`) preserves `dst[0] = 1` and `dst[3] = 4`
while updating `dst[1..3]` to `[20, 30]`.
-/
theorem canary_bug1_nonzero_subplace_indices :
    let srcArr : Value := .aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40]
    let dstArr : Value := .aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4]
    let locals : List LocalSlot := [.init srcArr, .init dstArr]
    let srcEntry : BorrowEntry := {
      tag := 10, targetLocal := 0, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 1 4 false], perm := .cell
      rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := 11, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 1 4 false], perm := .unique
      rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry], nextTag := 12 }
    }
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 10, offsetBytes := 0 }
      { allocId := 11, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.step {
      s with
      frame := {
        blockIdx := 0
        stmtIdx := 1
        locals := [
          .init srcArr,
          .init (.aggregate 0 [mkU32 1, mkU32 20, mkU32 30, mkU32 4])
        ]
      }
    } := by
  rfl

/--
Canary 1D (Nested struct field containing an array `.field 1 _ :: .constantIndex 0 2 false`):
Copying `2` elements from `&raw const s1.arr[0]` into `&raw mut s2.arr[0]`
updates `s2.arr` in-place while preserving `s2.header = 999`.
-/
theorem canary_bug1_nested_struct_field_array :
    let dummyTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let s1Val : Value := .aggregate 0 [mkU32 100, .aggregate 0 [mkU32 55, mkU32 66]]
    let s2Val : Value := .aggregate 0 [mkU32 999, .aggregate 0 [mkU32 0, mkU32 0]]
    let locals : List LocalSlot := [.init s1Val, .init s2Val]
    let srcEntry : BorrowEntry := {
      tag := 20, targetLocal := 0, targetFrameDepth := 0, allocDead := false
      targetProjection := [.field 1 dummyTy, .constantIndex 0 2 false]
      perm := .cell, rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := 21, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [.field 1 dummyTy, .constantIndex 0 2 false]
      perm := .unique, rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry], nextTag := 22 }
    }
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 20, offsetBytes := 0 }
      { allocId := 21, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.step {
      s with
      frame := {
        blockIdx := 0
        stmtIdx := 1
        locals := [
          .init s1Val,
          .init (.aggregate 0 [mkU32 999, .aggregate 0 [mkU32 55, mkU32 66]])
        ]
      }
    } := by
  rfl

/--
Canary 1E (Disjoint vs Overlapping slices within the SAME array container,
including same-tag pointer arithmetic `p` vs `p.add(2)`):
1. Copying `2` elements from `arr[0..2]` to `arr[2..4]` of `arr = [10, 20, 30, 40]`
   via the SAME provenance tag (`tag = 30`, `srcPtr.offsetBytes = 0`, `dstPtr.offsetBytes = 2`)
   succeeds and produces `[10, 20, 10, 20]`.
2. Copying `2` elements from `arr[0..2]` to overlapping `arr[1..3]` faults with `.ub`.
-/
theorem canary_bug1_same_array_disjoint_vs_overlapping :
    let arrVal : Value := .aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40]
    let locals : List LocalSlot := [.init arrVal]
    let entry0 : BorrowEntry := {
      tag := 30, targetLocal := 0, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 0 4 false], perm := .cell
      rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [entry0], nextTag := 31 }
    }
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 30, offsetBytes := 0 }
      { allocId := 30, offsetBytes := 2 }
      entry0 entry0 2 locals =
    MirStepNode.step {
      s with
      frame := {
        blockIdx := 0
        stmtIdx := 1
        locals := [.init (.aggregate 0 [mkU32 10, mkU32 20, mkU32 10, mkU32 20])]
      }
    } ∧
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 30, offsetBytes := 0 }
      { allocId := 30, offsetBytes := 1 }
      entry0 entry0 2 locals =
    MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

/--
Canary 1F (Tree Borrows Subrange Invalidation & Protector Precision):
When `copy_nonoverlapping` writes `2` elements to `dst[0..2]` of `dst = [1, 2, 3, 4]`:
1. An unrelated shared borrow `tag = 42` of `dst[1]` (inside `[0, 2)`) is disabled,
   whereas a shared borrow `tag = 43` of disjoint element `dst[3]` (outside `[0, 2)`)
   remains `.frozen`!
2. If `tag = 43` (`dst[3]`) is in `activeProtectors`, the copy to `dst[0..2]` succeeds;
   if `tag = 42` (`dst[1]`) is in `activeProtectors`, the copy to `dst[0..2]` faults with `.ub`.
-/
theorem canary_bug1_tree_borrows_subslice_invalidation_and_protector :
    let srcArr : Value := .aggregate 0 [mkU32 70, mkU32 80]
    let dstArr : Value := .aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4]
    let locals : List LocalSlot := [.init srcArr, .init dstArr]
    let srcEntry : BorrowEntry := {
      tag := 40, targetLocal := 0, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 0 2 false], perm := .cell
      rangeOffset := 0, rangeLen := 0, parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := 41, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 0 4 false], perm := .cell
      rangeOffset := 0, rangeLen := 0, parentTag := .none
    }
    let borrowInside : BorrowEntry := {
      tag := 42, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 1 4 false], perm := .frozen
      rangeOffset := 0, rangeLen := 0, protector := .some 42, parentTag := .none
    }
    let borrowDisjoint : BorrowEntry := {
      tag := 43, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [.constantIndex 3 4 false], perm := .frozen
      rangeOffset := 0, rangeLen := 0, protector := .some 43, parentTag := .none
    }
    let borrows0 := [srcEntry, dstEntry, borrowInside, borrowDisjoint]
    let sProtectedDisjoint : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := borrows0, activeProtectors := [43], nextTag := 44 }
    }
    let sProtectedInside : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := borrows0, activeProtectors := [42], nextTag := 44 }
    }
    evalCopyNonOverlappingPermOkProto
      sProtectedDisjoint dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 40, offsetBytes := 0 }
      { allocId := 41, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.step {
      sProtectedDisjoint with
      frame := {
        blockIdx := 0
        stmtIdx := 1
        locals := [.init srcArr, .init (.aggregate 0 [mkU32 70, mkU32 80, mkU32 3, mkU32 4])]
      }
      memory := {
        sProtectedDisjoint.memory with
        borrows := [
          srcEntry,
          dstEntry,
          { borrowInside with perm := .disabled },
          borrowDisjoint
        ]
      }
    } ∧
    evalCopyNonOverlappingPermOkProto
      sProtectedInside dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 40, offsetBytes := 0 }
      { allocId := 41, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

/--
Canary 1G (Negative test: `copy_nonoverlapping` with `count = 2` on a scalar
`u32` local faults with `.ub` instead of silently copying 1 element via `copyViaBytes`).
-/
theorem canary_bug1_scalar_multi_count_faults_ub :
    let locals : List LocalSlot := [.init (mkU32 42), .init (mkU32 0)]
    let srcEntry : BorrowEntry := {
      tag := 50, targetLocal := 0, targetFrameDepth := 0, allocDead := false
      targetProjection := [], perm := .cell
      rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := 51, targetLocal := 1, targetFrameDepth := 0, allocDead := false
      targetProjection := [], perm := .unique
      rangeOffset := 0, rangeLen := 4, parentTag := .none
    }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry], nextTag := 52 }
    }
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 50, offsetBytes := 0 }
      { allocId := 51, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.fail .ub := by
  rfl

/-! ## 2. Bug 2 Canaries: `DIV-LM-TAILCALL-NOUNWIND-UNWIND` -/

/--
Canary 2A: All 4 caller `UnwindAction` variants (`.cleanup 3`, `.continue_`,
`.unreachable`, `.terminate`) are narrowed to `.unreachable` when `enterTailCalleeFrameProto`
enters a `canUnwind = false` tail callee, causing `unwindFromCallStackProto` to
fault with `.faulted .ub`.
-/
theorem canary_bug2_all_four_caller_unwind_actions_fault_ub
    (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame)
    (mem memAtUnwind : Memory)
    (calleeBody : CapturedMir)
    (args : List Value)
    (hNoUnwind : calleeBody.fnAbi.canUnwind = false) :
    (unwindFromCallStackProto
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .cleanup 3 } :: rest }
        calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStackProto
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .continue_ } :: rest }
        calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStackProto
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .unreachable } :: rest }
        calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStackProto
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .terminate } :: rest }
        calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) :=
  ⟨tailCall_leanMiri_nounwind_callee_simulation _ rest _ calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ calleeBody args memAtUnwind hNoUnwind rfl⟩

/-!
Canary 2B (End-to-end execution of `caller -> call f (canUnwind := true, returnUnwind := .cleanup 1) -> tailCall g (canUnwind := false) -> unwindResume`):
- Under unpatched `Trusted` (`execN`), `g` unwinding enters `caller`'s cleanup block `bb1` and returns `999` (`.halted (.normal (999, _))`) instead of faulting!
- Under repaired `execNProto`, `g` unwinding immediately faults with `.faulted .ub`.
- Meanwhile, at the modular root (`callStack = []`), `f -> tailCall g -> unwindResume` still halts with `.halted .panic` (`MODEL-LM-TAILCALL-MODULAR-ROOT` preserved).
-/
section Bug2EndToEndCanary

private def u64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
private def u64Decl : LocalDecl := { mutability := .mut, ty := u64Ty, debugName := none }
private def u64Const (n : Nat) : Operand :=
  .constant { ty := u64Ty, val := .scalar (.int { bits := n, sizeBytes := 8 }) }
private def fnConst (path : String) : Operand :=
  .constant { ty := { kind := .fnDef path [], layoutIdx := 0 }, val := .zeroSized }

private def mkAbi (canUnwind : Bool) : FnAbi := {
  args := []
  ret := {
    layout := {
      size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory
      fields := .primitive, variants := .single 0, isUninhabited := false
    }
    mode := .direct
  }
  conv := .rust
  canUnwind := canUnwind
}

/-- Tail callee `g_nounwind` (`canUnwind = false`) that executes `unwindResume`. -/
def gNoUnwindBody : CapturedMir := {
  defPath := "test::g_nounwind"
  phase := .runtimeOptimized
  role := .subject
  argCount := 0
  localDecls := [u64Decl]
  basicBlocks := [
    { statements := [], terminator := ⟨.unwindResume, "g"⟩, isCleanup := true }
  ]
  fnAbi := mkAbi false
  layouts := emptyLayoutTable
  allocations := []
}

/-- Middle function `f_canunwind` (`canUnwind = true`) that tail-calls `g_nounwind`. -/
def fCanUnwindBody : CapturedMir := {
  defPath := "test::f_canunwind"
  phase := .runtimeOptimized
  role := .subject
  argCount := 0
  localDecls := [u64Decl]
  basicBlocks := [
    { statements := []
      terminator := ⟨.tailCall (fnConst "test::g_nounwind") [], "f"⟩
      isCleanup := false }
  ]
  fnAbi := mkAbi true
  layouts := emptyLayoutTable
  allocations := []
}

/-- Outer caller `caller_with_cleanup` (`canUnwind = true`) that calls `f_canunwind` with `.cleanup 1`. -/
def callerWithCleanupBody : CapturedMir := {
  defPath := "test::caller_with_cleanup"
  phase := .runtimeOptimized
  role := .subject
  argCount := 0
  localDecls := [u64Decl]
  basicBlocks := [
    { statements := []
      terminator := ⟨.call (fnConst "test::f_canunwind") [] ⟨0, []⟩ (some 2) (.cleanup 1), "caller"⟩
      isCleanup := false },
    { statements := [⟨.assign ⟨0, []⟩ (.use (u64Const 999)), "cleanup"⟩]
      terminator := ⟨.return_, "cleanup"⟩
      isCleanup := true },
    { statements := []
      terminator := ⟨.return_, "normal"⟩
      isCleanup := false }
  ]
  fnAbi := mkAbi true
  layouts := emptyLayoutTable
  allocations := []
}

theorem canary_bug2_nested_tailcall_nounwind_faults_ub :
    let mem0 : Memory := { emptyMemory with callees := [fCanUnwindBody, gNoUnwindBody] }
    let s0 := initMachineStateWithMemoryProto callerWithCleanupBody [] mem0
    execNProto callerWithCleanupBody 3 (.running s0) = some (.faulted .ub) ∧
    execNProto fCanUnwindBody 2
      (.running (initMachineStateWithMemoryProto fCanUnwindBody [] mem0)) =
      some (.halted .panic) := by
  exact ⟨rfl, rfl⟩

end Bug2EndToEndCanary

/-! ## 3. Bug 3 Canaries: `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW` -/

/--
Canary 3A: Witness confirmation on `fCrBody`, `fRdBody`, and `fDangleBody`.
-/
theorem canary_bug3_caller_referent_read_and_dangling_ub :
    (match execNProto
        TailCallCallerReferentWitnesses.fCrBody 3
        (.running (initMachineStateWithMemoryProto
          TailCallCallerReferentWitnesses.fCrBody
          [TailCallCallerReferentWitnesses.crPtrArg]
          TailCallCallerReferentWitnesses.crMem)) with
     | some (.halted (.normal (v, _))) => some v
     | _ => none) = some (.scalar { bits := 42, sizeBytes := 8 }) ∧
    execNProto
      TailCallCallerReferentWitnesses.fDangleBody 6
      (.running (initMachineStateWithMemoryProto
        TailCallCallerReferentWitnesses.fDangleBody []
        { emptyMemory with callees := [TailCallCallerReferentWitnesses.gReadBody] })) =
      some (.faulted .ub) :=
  ⟨TailCallCallerReferentWitnesses.tailCall_repaired_root_caller_referent_returns_42.2,
   TailCallCallerReferentWitnesses.tailCall_repaired_dangling_frame_local_faults_ub⟩

/-!
Canary 3B (Write-through & Child Reborrow on Caller-Owned Referent in Tail Callee):
When `f_cr` tail-calls `g_write_and_reborrow(p)` where `p` targets `callerLocals[2] = 42`
and `g_write_and_reborrow` has its own local `_2 = 137`:
1. Writing `*p = 77` updates `callerLocals[2]` to `77` while leaving `g`'s local `_2 = 137` untouched!
2. Reborrowing `let r = &mut *p` (`_3 = &mut (*_1)`) and reading `*r` returns `77` (not `137`)!
-/
section Bug3WriteAndReborrowCanary

private def u64Ty3 : Ty := { kind := .uint .u64, layoutIdx := 0 }
private def u64PtrTy3 : Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }
private def u64Decl3 : LocalDecl := { mutability := .mut, ty := u64Ty3, debugName := none }
private def u64PtrDecl3 : LocalDecl := { mutability := .mut, ty := u64PtrTy3, debugName := none }
private def u64Const3 (n : Nat) : Operand :=
  .constant { ty := u64Ty3, val := .scalar (.int { bits := n, sizeBytes := 8 }) }
private def fnConst3 (path : String) : Operand :=
  .constant { ty := { kind := .fnDef path [], layoutIdx := 0 }, val := .zeroSized }

private def abi3 : FnAbi := {
  args := []
  ret := {
    layout := {
      size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := .memory
      fields := .primitive, variants := .single 0, isUninhabited := false
    }
    mode := .direct
  }
  conv := .rust
  canUnwind := false
}

/--
Tail callee `g_write_reborrow(p: *mut u64) -> u64` (`4` locals: `_0`, `_1 = p`, `_2`, `_3`):
- `StorageLive(_2); StorageLive(_3)`
- `_2 = 137` (writes to its own local `_2`)
- `*_1 = 77` (writes through caller-referent pointer `p` into `callerLocals[2]`)
- `_3 = &mut (*_1)` (reborrows `*p`)
- `_0 = *_3` (returns `77` via `*_3` read while `_2 = 137`).
-/
def gWriteReborrowBody : CapturedMir := {
  defPath := "test::g_write_reborrow"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [u64Decl3, u64PtrDecl3, u64Decl3, u64PtrDecl3]
  basicBlocks := [
    { statements := [
        ⟨.storageLive 2, "sl2"⟩,
        ⟨.storageLive 3, "sl3"⟩,
        ⟨.assign ⟨2, []⟩ (.use (u64Const3 137)), "s0"⟩,
        ⟨.assign ⟨1, [.deref]⟩ (.use (u64Const3 77)), "s1"⟩,
        ⟨.assign ⟨3, []⟩ (.ref (.mut false) ⟨1, [.deref]⟩), "s2"⟩,
        ⟨.assign ⟨0, []⟩ (.use (.copy ⟨3, [.deref]⟩)), "s3"⟩
      ]
      terminator := ⟨.return_, "ret"⟩
      isCleanup := false }
  ]
  fnAbi := abi3
  layouts := emptyLayoutTable
  allocations := []
}

def fCallWriteReborrowBody : CapturedMir := {
  defPath := "test::f_call_write_reborrow"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [u64Decl3, u64PtrDecl3]
  basicBlocks := [
    { statements := []
      terminator := ⟨.tailCall (fnConst3 "test::g_write_reborrow") [.move ⟨1, []⟩], "tail"⟩
      isCleanup := false }
  ]
  fnAbi := abi3
  layouts := emptyLayoutTable
  allocations := []
}

theorem canary_bug3_write_through_and_reborrow_caller_referent :
    let mem0 : Memory := {
      TailCallCallerReferentWitnesses.crMem with
      callees := [gWriteReborrowBody]
    }
    let s0 :=
      initMachineStateWithMemoryProto
        fCallWriteReborrowBody
        [TailCallCallerReferentWitnesses.crPtrArg]
        mem0
    (match execNProto fCallWriteReborrowBody 8 (.running s0) with
     | some (.halted (.normal (retVal, memOut))) =>
       some (retVal, get? memOut.callerLocals 2)
     | _ => none) =
    some (.scalar { bits := 77, sizeBytes := 8 },
          some (.init (.scalar { bits := 77, sizeBytes := 8 }))) := by
  rfl

end Bug3WriteAndReborrowCanary

/-! ## 4. Bug 4 Canaries: `DIV-TR-OPAQUECAST-ROOT-DISPATCH` -/

/--
Canary 4A (Stacked `.opaqueCast` on `.uninit` local assignment, move operand,
field-shell initialization, deinit, setDiscriminant, and drop):
1. Assigning `(_0 as u64 as u64) = 55` when `_0` is `.uninit` initializes `_0` to `.init 55`
   (whereas unpatched `evalStmt` faults with `MirStepNode.fail .ub`).
2. `evalOperandProto [.init 55] (.move ⟨0, [.opaqueCast u64, .opaqueCast u64]⟩)` returns
   `.ok 55 [.uninit]` (whereas unpatched `evalOperand` leaves `_0` as `[.init 55]`).
3. `(_0 as PairU32).0 = 11` on `.uninit` `_0` initializes `_0` to `.aggregate 0 [11, .uninit]`
   via `uninitFieldWriteShellProto?`.
-/
theorem canary_bug4_stacked_opaqueCast_uninit_assign_and_move :
    let ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
    let v55 : Value := .scalar { bits := 55, sizeBytes := 8 }
    let const55 : Operand := .constant { ty := ty, val := .scalar (.int { bits := 55, sizeBytes := 8 }) }
    let sUninit : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
      memory := emptyMemory
    }
    let assignStacked : Statement :=
      ⟨.assign ⟨0, [.opaqueCast ty, .opaqueCast ty]⟩ (.use const55), "s"⟩
    evalStmt sUninit assignStacked [] emptyLayoutTable = MirStepNode.fail .ub ∧
    evalStmtProto sUninit assignStacked [] emptyLayoutTable =
      MirStepNode.step {
        sUninit with
        frame := { blockIdx := 0, stmtIdx := 1, locals := [.init v55] }
      } ∧
    evalOperand [.init v55] (.move ⟨0, [.opaqueCast ty, .opaqueCast ty]⟩) =
      .ok v55 [.init v55] ∧
    evalOperandProto [.init v55] (.move ⟨0, [.opaqueCast ty, .opaqueCast ty]⟩) =
      .ok v55 [.uninit] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
Canary 4B (Field-shell initialization on `.uninit` struct local through `.opaqueCast`):
Writing `(_0 as PairU32).0 = 11` when `_0` is `.uninit` and `localDecls[0]` is a
2-field ADT constructs the 2-field `.uninit` shell and writes field `0`.
-/
theorem canary_bug4_uninit_field_shell_through_opaqueCast :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairTy : Ty := { kind := .adt "PairU32" [], layoutIdx := 1 }
    let layouts : LayoutTable := {
      pointerBits := 64
      isLittleEndian := true
      entries := [
        { size := { bytes := 4 }, align := { bytes := 4 }
          backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
          fields := .primitive, variants := .single 0, isUninhabited := false },
        { size := { bytes := 8 }, align := { bytes := 4 }
          backendRepr := .memory
          fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
          variants := .single 0, isUninhabited := false
          fieldLayouts := [0, 0] }
      ]
    }
    let decls : List LocalDecl := [{ mutability := .mut, ty := pairTy, debugName := none }]
    let sUninit : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
      memory := emptyMemory
    }
    let const11 : Operand := .constant { ty := u32Ty, val := .scalar (.int { bits := 11, sizeBytes := 4 }) }
    let stmt : Statement :=
      ⟨.assign ⟨0, [.opaqueCast pairTy, .field 1 u32Ty]⟩ (.use const11), "s"⟩
    evalStmt sUninit stmt decls layouts = MirStepNode.fail .ub ∧
    evalStmtProto sUninit stmt decls layouts =
      MirStepNode.step {
        sUninit with
        frame := {
          blockIdx := 0
          stmtIdx := 1
          locals := [.init (.aggregate 0 [.unit, .scalar { bits := 11, sizeBytes := 4 }])]
        }
      } := by
  exact ⟨rfl, rfl⟩

/-! ## 5. Axiom Hygiene Audit (`#print axioms`) -/

#print axioms Campaign14_pass_transmute_u32_byte_array_le__b0_c6.confirm_repaired_tag_pass_transmute_u32_byte_array_le__b0_c6
#print axioms Campaign15_pass_enum_discriminant_valid__b2_c9.confirm_repaired_tag_pass_enum_discriminant_valid__b2_c9
#print axioms evalCopyNonOverlappingPermOkProto_subplace_constantIndex_slice
#print axioms evalCopyNonOverlappingPermOkProto_subplace_src_oob_ub
#print axioms evalCopyNonOverlappingPermOkProto_sameArray_overlap_ub
#print axioms evalCopyNonOverlappingPermOkProto_sameArray_disjoint_ok
#print axioms tailCall_leanMiri_nounwind_callee_simulation
#print axioms tailCall_nounwind_multihop_monotonicity
#print axioms tailCall_witness_root_caller_referent_simulation
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_root_caller_referent_returns_42
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_dangling_frame_local_faults_ub
#print axioms opaqueCast_trusted_root_dispatch_simulation
#print axioms opaqueCast_before_deref_stays_unsupported

end Anneal.TcbCopySubplaceAndTailCallProtoTests
