import Anneal.TcbCopySubplaceAndTailCallPrototype

/-!
# TCB Subplace `copy_nonoverlapping` & `tailCall` / `opaqueCast` Prototype Canary Suite

Positive and negative non-vacuity canaries, conservativity (no-regression)
canaries against unmodified `Trusted`, edge-case regression tests, and
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

/--
Canary 1H (Misaligned element pointer, typed program): copying `1` `u32` from
`(&raw const a as *const u8).add(2) as *const u32` (byte offset `2`, not a whole
`u32`) into `dst[0]`. Unpatched `Trusted` reinterprets the byte offset `2` as an
*element* index and silently copies `a[2] = 30`; the prototype faults with
`.ub` (Rust: `copy_nonoverlapping` requires aligned pointers).
-/
theorem canary_bug1_misaligned_byte_offset_faults_ub :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let arrTy : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }
    let decls : List LocalDecl := [
      { mutability := .mut, ty := arrTy, debugName := none },
      { mutability := .mut, ty := arrTy, debugName := none },
      { mutability := .mut, ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }, debugName := none },
      { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }, debugName := none }
    ]
    let srcArr : Value := .aggregate 0 [mkU32 10, mkU32 20, mkU32 30, mkU32 40]
    let dstArr : Value := .aggregate 0 [mkU32 0, mkU32 0, mkU32 0, mkU32 0]
    let locals : List LocalSlot := [.init srcArr, .init dstArr,
      .init (.ptr { allocId := 60, offsetBytes := 2 } 8), .init (.ptr { allocId := 61, offsetBytes := 0 } 8)]
    let srcEntry : BorrowEntry := {
      tag := 60, targetLocal := 0, targetProjection := [], perm := .cell }
    let dstEntry : BorrowEntry := {
      tag := 61, targetLocal := 1, targetProjection := [.constantIndex 0 4 false], perm := .unique }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry], nextTag := 62 }
    }
    let _ := u32Ty
    (match
      evalCopyNonOverlappingPermOk
        s (.copy ⟨2, []⟩) (.copy ⟨3, []⟩) decls emptyLayoutTable
        { allocId := 60, offsetBytes := 2 } { allocId := 61, offsetBytes := 0 }
        srcEntry dstEntry 1 locals
     with
     | .tau (.running s') => get? s'.frame.locals 1
     | _ => none) =
      some (.init (.aggregate 0 [mkU32 30, mkU32 0, mkU32 0, mkU32 0])) ∧
    evalCopyNonOverlappingPermOkProto
      s (.copy ⟨2, []⟩) (.copy ⟨3, []⟩) decls emptyLayoutTable
      { allocId := 60, offsetBytes := 2 } { allocId := 61, offsetBytes := 0 }
      srcEntry dstEntry 1 locals =
      MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

/--
Canary 1I (Tree Borrows source-read transition on a multi-element copy):
copying `2` elements from `src[0..2]` through tag `40` is a read of the source
window, and the activated sibling borrow `tag = 45` of `src` (`.unique`) is a
foreign borrow for that read, so it becomes `.frozen` (Tree Borrows
`Active --foreign read--> Frozen`), exactly as `Trusted`'s single-element path
(`borrowsAfterCopySingleDirect`) does; the destination `dst[0..2]` receives
`[70, 80]`. (A0's `borrowsAfterCopyAtProj` read transition was dead code, so
`tag = 45` stayed `.unique`; unpatched `Trusted` faults with a false `.ub` on this
untyped subplace copy.)
-/
theorem canary_bug1_multi_copy_source_read_freezes_foreign_active :
    let srcArr : Value := .aggregate 0 [mkU32 70, mkU32 80]
    let dstArr : Value := .aggregate 0 [mkU32 1, mkU32 2, mkU32 3, mkU32 4]
    let locals : List LocalSlot := [.init srcArr, .init dstArr]
    let srcEntry : BorrowEntry :=
      { tag := 40, targetLocal := 0, targetProjection := [.constantIndex 0 2 false], perm := .cell }
    let dstEntry : BorrowEntry :=
      { tag := 41, targetLocal := 1, targetProjection := [.constantIndex 0 4 false], perm := .unique }
    let activeSib : BorrowEntry :=
      { tag := 45, targetLocal := 0, targetProjection := [], perm := .unique }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry, activeSib], nextTag := 46 }
    }
    evalCopyNonOverlappingPermOk
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 40, offsetBytes := 0 } { allocId := 41, offsetBytes := 0 }
      srcEntry dstEntry 2 locals = MirStepNode.fail .ub ∧
    evalCopyNonOverlappingPermOkProto
      s dummySrcOp dummyDstOp [] emptyLayoutTable
      { allocId := 40, offsetBytes := 0 } { allocId := 41, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
    MirStepNode.step {
      s with
      frame := {
        blockIdx := 0
        stmtIdx := 1
        locals := [.init srcArr, .init (.aggregate 0 [mkU32 70, mkU32 80, mkU32 3, mkU32 4])]
      }
      memory := {
        s.memory with
        borrows := [srcEntry, dstEntry, { activeSib with perm := .frozen }]
      }
    } := by
  exact ⟨rfl, rfl⟩

/-! ## 2. Bug 2 Canaries: `DIV-LM-TAILCALL-NOUNWIND-UNWIND` -/

/--
Canary 2A: All 4 caller `UnwindAction` variants (`.cleanup 3`, `.continue_`,
`.unreachable`, `.terminate`) are narrowed to `.unreachable` when
`enterTailCalleeFrameProto` enters a `canUnwind = false` tail callee, so
`Trusted`'s own `unwindFromCallStack` faults with `.faulted .ub`.
-/
theorem canary_bug2_all_four_caller_unwind_actions_fault_ub
    (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame)
    (mem memAtUnwind : Memory)
    (ceiling : Bool)
    (calleeBody : CapturedMir)
    (args : List Value)
    (hNoUnwind : calleeBody.fnAbi.canUnwind = false) :
    (unwindFromCallStack
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .cleanup 3 } :: rest }
        ceiling calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStack
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .continue_ } :: rest }
        ceiling calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStack
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .unreachable } :: rest }
        ceiling calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) ∧
    (unwindFromCallStack
      (enterTailCalleeFrameProto
        { mem with callStack := { caller with returnUnwind := .terminate } :: rest }
        ceiling calleeBody args).memory.callStack
      memAtUnwind = .faulted .ub) :=
  ⟨tailCall_leanMiri_nounwind_callee_simulation _ rest _ ceiling calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ ceiling calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ ceiling calleeBody args memAtUnwind hNoUnwind rfl,
   tailCall_leanMiri_nounwind_callee_simulation _ rest _ ceiling calleeBody args memAtUnwind hNoUnwind rfl⟩

/-!
Canary 2B (end-to-end, `caller -> call f (canUnwind, unwind: cleanup bb1) -> become g (!canUnwind) -> resume`):
- Unpatched `Trusted`: `g`'s unwind enters `caller`'s cleanup block `bb1` and returns `999`.
- Repaired prototype: `g`'s unwind faults with `.faulted .ub`.
- Modular root `f -> become g -> resume`: unpatched `Trusted` halts with
  `.panic`; the prototype narrows the root unwind ceiling and faults with `.ub`
  (A0's prototype kept `.panic` here).
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

private def mem0 : Memory := { emptyMemory with callees := [fCanUnwindBody, gNoUnwindBody] }

theorem canary_bug2_nested_and_root_tailcall_nounwind_faults_ub :
    (match TailCallCallerReferentWitnesses.execN callerWithCleanupBody 5
        (.running (initMachineStateWithMemory callerWithCleanupBody [] mem0)) with
     | some (.halted (.normal (v, _))) => some v
     | _ => none) = some (.scalar { bits := 999, sizeBytes := 8 }) ∧
    execNProto callerWithCleanupBody 3
      (.running (initMachineStateWithMemory callerWithCleanupBody [] mem0)) = some (.faulted .ub) ∧
    TailCallCallerReferentWitnesses.execN fCanUnwindBody 2
      (.running (initMachineStateWithMemory fCanUnwindBody [] mem0)) = some (.halted .panic) ∧
    execNProto fCanUnwindBody 2
      (.running (initMachineStateWithMemory fCanUnwindBody [] mem0)) = some (.faulted .ub) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Bug2EndToEndCanary

/-! ## 3. Bug 3 Canaries: `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW` -/

open TailCallCallerReferentWitnesses in
/--
Canary 3A: the exact correspondence witnesses (`fcr`/`frd`/`fdangle`/`crMem`),
the non-`Use` read, inline calls, write-through + reborrow, and multi-hop.
-/
theorem canary_bug3_caller_referent_suite :
    haltedVal? (execNProto fCrBody 3 (crInit fCrBody)) = some (.scalar ⟨42, 4⟩) ∧
    haltedVal? (execNProto fCrAddBody 3 (crInit fCrAddBody)) = some (.scalar ⟨42, 4⟩) ∧
    haltedVal? (execNProto fCallBody 6 (crInit fCallBody)) = some (.scalar ⟨43, 4⟩) ∧
    haltedVal? (execNProto fCrCallBody 7 (crInit fCrCallBody)) = some (.scalar ⟨43, 4⟩) ∧
    haltedVal? (execNProto fHopBody 4 (crInit fHopBody)) = some (.scalar ⟨42, 4⟩) ∧
    execNProto fDangleBody 6 (.running (initMachineStateWithCallees fDangleBody [] [gReadBody])) =
      some (.faulted .ub) :=
  ⟨tailCall_repaired_root_caller_referent_returns_42.2.1,
   tailCall_repaired_root_caller_referent_binop.2,
   tailCall_repaired_caller_referent_inline_calls.2.1,
   tailCall_repaired_caller_referent_inline_calls.2.2,
   tailCall_repaired_caller_referent_multihop.2,
   tailCall_repaired_dangling_frame_local_faults_ub.2⟩

/--
Canary 3B (relocation is the identity when the tail callee is not wider, or when
no borrow names a caller-owned referent, e.g. Campaign-style roots without
pointer arguments).
-/
theorem canary_bug3_relocation_identity_cases (mem : Memory) :
    relocateRootCallerReferents mem 3 3 = mem ∧
    relocateRootCallerReferents mem 5 2 = mem ∧
    relocateRootCallerReferents { mem with borrows := [] } 1 9 = { mem with borrows := [] } :=
  ⟨relocateRootCallerReferents_not_wider mem 3 3 rfl,
   relocateRootCallerReferents_not_wider mem 5 2 rfl,
   relocateRootCallerReferents_no_referents { mem with borrows := [] } 1 9 rfl⟩

/-! ## 4. Bug 4 Canaries: `DIV-TR-OPAQUECAST-ROOT-DISPATCH` -/

/--
Canary 4A (Stacked `.opaqueCast` on `.uninit` local assignment and move):
1. Assigning `(_0 as u64 as u64) = 55` when `_0` is `.uninit` initializes `_0`
   (unpatched `evalStmt` faults with `MirStepNode.fail .ub`).
2. `evalOperandProto [.init 55] (.move ⟨0, [.opaqueCast u64, .opaqueCast u64]⟩)`
   de-initializes `_0` (unpatched `evalOperand` leaves it initialized).
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

private def pairLayouts : LayoutTable := {
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

/--
Canary 4B (Field-shell initialization on `.uninit` struct local through `.opaqueCast`):
writing `(_0 as PairU32).1 = 11` when `_0` is `.uninit` and declared `PairU32`
constructs the 2-field `.uninit` shell and writes field `1`.
-/
theorem canary_bug4_uninit_field_shell_through_opaqueCast :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairTy : Ty := { kind := .adt "PairU32" [], layoutIdx := 1 }
    let decls : List LocalDecl := [{ mutability := .mut, ty := pairTy, debugName := none }]
    let sUninit : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
      memory := emptyMemory
    }
    let const11 : Operand := .constant { ty := u32Ty, val := .scalar (.int { bits := 11, sizeBytes := 4 }) }
    let stmt : Statement :=
      ⟨.assign ⟨0, [.opaqueCast pairTy, .field 1 u32Ty]⟩ (.use const11), "s"⟩
    evalStmt sUninit stmt decls pairLayouts = MirStepNode.fail .ub ∧
    evalStmtProto sUninit stmt decls pairLayouts =
      MirStepNode.step {
        sUninit with
        frame := {
          blockIdx := 0
          stmtIdx := 1
          locals := [.init (.aggregate 0 [.unit, .scalar { bits := 11, sizeBytes := 4 }])]
        }
      } := by
  exact ⟨rfl, rfl⟩

/--
Canary 4C (the realistic opaque-type case): `_0` is declared with an *opaque
alias* type (`impl Trait`, `RigidTy.alias`) and `(_0 as PairU32).1 = 11` writes
into its revealed hidden type. The field shell must come from the cast type
`PairU32` (the post-borrowck erasure has `_0 : PairU32`): the prototype builds
it, whereas a shell keyed on the declared (alias) type — unpatched `Trusted`,
and A0's `uninitFieldWriteShellProto?` — faults with `.ub`.
-/
theorem canary_bug4_opaque_alias_field_shell_uses_cast_type :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairTy : Ty := { kind := .adt "PairU32" [], layoutIdx := 1 }
    let aliasTy : Ty := { kind := .alias "test::Opaque::{opaque#0}" [], layoutIdx := 1 }
    let decls : List LocalDecl := [{ mutability := .mut, ty := aliasTy, debugName := none }]
    let sUninit : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
      memory := emptyMemory
    }
    let const11 : Operand := .constant { ty := u32Ty, val := .scalar (.int { bits := 11, sizeBytes := 4 }) }
    let stmt : Statement :=
      ⟨.assign ⟨0, [.opaqueCast pairTy, .field 1 u32Ty]⟩ (.use const11), "s"⟩
    evalStmt sUninit stmt decls pairLayouts = MirStepNode.fail .ub ∧
    uninitFieldWriteShell? decls pairLayouts 0 (.field 1 u32Ty) [] = .none ∧
    evalStmtProto sUninit stmt decls pairLayouts =
      MirStepNode.step {
        sUninit with
        frame := {
          blockIdx := 0
          stmtIdx := 1
          locals := [.init (.aggregate 0 [.unit, .scalar { bits := 11, sizeBytes := 4 }])]
        }
      } := by
  exact ⟨rfl, rfl, rfl⟩

/--
Canary 4D (Cross-field struct byte-span copy fails closed with `.unsupported`, while
out-of-allocation struct read faults with `.ub`):
on an 8-byte `PairU32 { a: u32, b: u32 }`, copying `n = 2` `u32`s (`8` bytes <= `8`
bytes of the root struct) starting at `&raw const pair.0` returns
`MirStepNode.unsupported` (avoiding a false-positive `.ub` on a valid cross-field
`#[repr(C)]` read), whereas `n = 3` (`12` bytes > `8` bytes of the root struct)
faults with `MirStepNode.fail .ub`.
-/
theorem canary_bug1_cross_field_span_unsupported_vs_oob_ub :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairVal : Value := .aggregate 0 [mkU32 10, mkU32 20]
    let dstArr : Value := .aggregate 0 [mkU32 0, mkU32 0, mkU32 0]
    let locals : List LocalSlot := [.init pairVal, .init dstArr]
    let srcEntry : BorrowEntry :=
      { tag := 70, targetLocal := 0, targetProjection := [.field 0 u32Ty], perm := .cell }
    let dstEntry : BorrowEntry :=
      { tag := 71, targetLocal := 1, targetProjection := [], perm := .unique }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := { emptyMemory with borrows := [srcEntry, dstEntry], nextTag := 72 }
    }
    evalCopyNonOverlappingPermOkProto
      s (.copy ⟨0, []⟩) (.copy ⟨1, []⟩) [] emptyLayoutTable
      { allocId := 70, offsetBytes := 0 } { allocId := 71, offsetBytes := 0 }
      srcEntry dstEntry 2 locals =
      MirStepNode.unsupported ∧
    evalCopyNonOverlappingPermOkProto
      s (.copy ⟨0, []⟩) (.copy ⟨1, []⟩) [] emptyLayoutTable
      { allocId := 70, offsetBytes := 0 } { allocId := 71, offsetBytes := 0 }
      srcEntry dstEntry 3 locals =
      MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

open TailCallCallerReferentWitnesses in
/--
Canary 4E (`.opaqueCast` on `.call` return destination and `move` argument, plus
non-`Use` binaryOp `move (_1 as u32)`):
1. Calling `hadd(move (_1 as *mut u32))` returning into `(_0 as u32)` when `_0` is
   `.uninit` faults with `.ub` under unpatched `execN` (`writeReturnDestination`
   takes the projected branch on `.uninit` `_0`), whereas `execNProto` succeeds
   and returns `43`.
2. Evaluating `_0 = Add(move (_1 as u32), 10)` de-initializes `_1` under
   `evalStmtProto`, whereas unpatched `evalStmt` leaves `_1` initialized.
-/
theorem canary_bug4_call_destination_and_binop_move_opaqueCast :
    let fCallCastBody : CapturedMir :=
      mkBody "w::fcallcast" 1 [u32Decl "_0", ptrDecl "p"]
        [blk [] (.call (fnItem "w::hadd") [.move ⟨1, [.opaqueCast tyPtrMutU32]⟩]
            ⟨0, [.opaqueCast tyU32]⟩ (some 1) .continue_),
         blk [] .return_]
    let sBin : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (mkU32 32)] }
      memory := emptyMemory
    }
    let binStmt : Statement :=
      st (.assign (lc 0) (.binaryOp .add (.move ⟨1, [.opaqueCast tyU32]⟩) (cU32 10)))
    execN fCallCastBody 6 (crInit fCallCastBody) = some (.faulted .ub) ∧
    haltedVal? (execNProto fCallCastBody 6 (crInit fCallCastBody)) = some (.scalar ⟨43, 4⟩) ∧
    evalStmt sBin binStmt [] emptyLayoutTable =
      MirStepNode.step {
        sBin with
        frame := { blockIdx := 0, stmtIdx := 1, locals := [.init (mkU32 42), .init (mkU32 32)] }
      } ∧
    evalStmtProto sBin binStmt [] emptyLayoutTable =
      MirStepNode.step {
        sBin with
        frame := { blockIdx := 0, stmtIdx := 1, locals := [.init (mkU32 42), .uninit] }
      } := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. Conservativity Canaries (the prototype is `Trusted` wherever no repair applies) -/

open TailCallCallerReferentWitnesses in
/--
Canary 5A (Tree Borrows read through `Rvalue::Use` is kept): `x = 5; r = &mut x;
*r = 6; p = &raw const x; y = *p; *r = 7`. The read through `p` is a foreign
read for the activated `r`, which becomes `Frozen`, so `*r = 7` is UB in
Tree Borrows (Miri) and in `Trusted` (`freezeDerefReadBorrowsAt` in
`evalRvalue (.use)`). The prototype agrees; A0's `evalRvalueProto (.use)`
bypassed `Trusted.evalRvalue` and returned `6`.
-/
theorem canary_conservativity_use_keeps_tree_borrows_read :
    let tbBody : CapturedMir :=
      mkBody "w::tb" 0 [u32Decl "_0", u32Decl "x", ptrDecl "r", ptrDecl "p", u32Decl "y"]
        [blk [st (.storageLive 1), st (.storageLive 2), st (.storageLive 3), st (.storageLive 4),
              st (.assign (lc 1) (.use (cU32 5))),
              st (.assign (lc 2) (.ref (.mut false) (lc 1))),
              st (.assign ⟨2, [.deref]⟩ (.use (cU32 6))),
              st (.assign (lc 3) (.rawPtr .not (lc 1))),
              st (.assign (lc 4) (.use (.copy ⟨3, [.deref]⟩))),
              st (.assign ⟨2, [.deref]⟩ (.use (cU32 7))),
              st (.assign (lc 0) (.use (.copy (lc 4))))] .return_]
    execN tbBody 13 (.running (initMachineState tbBody [])) = some (.faulted .ub) ∧
    execNProto tbBody 13 (.running (initMachineState tbBody [])) = some (.faulted .ub) := by
  exact ⟨rfl, rfl⟩

/-! ## 6. Axiom Hygiene Audit (`#print axioms`) -/

#print axioms Campaign14_pass_transmute_u32_byte_array_le__b0_c6.confirm_repaired_tag_pass_transmute_u32_byte_array_le__b0_c6
#print axioms Campaign15_pass_enum_discriminant_valid__b2_c9.confirm_repaired_tag_pass_enum_discriminant_valid__b2_c9
#print axioms evalCopyNonOverlappingPermOkProto_singleDirect_eq
#print axioms evalCopyNonOverlappingPermOkProto_subplace_constantIndex_slice
#print axioms evalCopyNonOverlappingPermOkProto_subplace_src_oob_ub
#print axioms evalCopyNonOverlappingPermOkProto_sameArray_overlap_ub
#print axioms evalCopyNonOverlappingPermOkProto_sameArray_disjoint_ok
#print axioms evalCopyNonOverlappingPermOkProto_misaligned_src_ub
#print axioms canary_bug1_misaligned_byte_offset_faults_ub
#print axioms tailCall_leanMiri_nounwind_callee_simulation
#print axioms tailCall_nounwind_callee_unwindResume_ub
#print axioms tailCall_nounwind_multihop_monotonicity
#print axioms tailCall_root_unwind_ceiling
#print axioms rootUnwindCeiling_initial
#print axioms root_unwindResume_guarded
#print axioms TailCallCallerReferentWitnesses.tailCall_root_nounwind_callee_unwind_ub
#print axioms canary_bug2_nested_and_root_tailcall_nounwind_faults_ub
#print axioms isRootCallerReferentBorrow_shift
#print axioms relocateRootCallerReferents_readFrameLocalSlot
#print axioms relocateRootCallerReferents_readFrameLocalSlot_suspended
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_root_caller_referent_returns_42
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_root_caller_referent_binop
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_caller_referent_inline_calls
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_caller_referent_write_and_reborrow
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_caller_referent_multihop
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_dangling_frame_local_faults_ub
#print axioms TailCallCallerReferentWitnesses.tailCall_repaired_wide_narrow_wide_dead_local_not_relocated
#print axioms opaqueCast_trusted_root_dispatch_simulation
#print axioms opaqueCast_typed_root_write_validates_cast_type
#print axioms opaqueCast_uninit_field_shell_is_cast_type_shell
#print axioms opaqueCast_before_deref_stays_unsupported
#print axioms writeReturnDestinationProto_pure_opaqueCast_simulation
#print axioms canary_bug1_cross_field_span_unsupported_vs_oob_ub
#print axioms canary_bug4_opaque_alias_field_shell_uses_cast_type
#print axioms canary_bug4_call_destination_and_binop_move_opaqueCast
#print axioms canary_conservativity_use_keeps_tree_borrows_read

end Anneal.TcbCopySubplaceAndTailCallProtoTests
