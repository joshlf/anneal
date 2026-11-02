import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import MiniRust.LibSpecr
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

/-!
# `Correspondence.V2026_06_01.L3_PlacesAndBasicMem` — Places, `BasicMemory`, & Algebraic Bisection

Connects `Trusted.Rustc.V2026_06_01.MirSemantics` place and memory operations
(`readProjectedValue`, `writeProjectedValue`, `writePlaceValue`, `evalRvalue`) to
MiniRust's place projection and `BasicMemory` semantics (`spec/mem/basic.md`):

1. **Universal `MirSemantics` Place Projection & Write Theorems (`∀`)**:
   - `mir_readProjectedValue_nil`: reading at `.nil` projection returns `.ok val` for every `locals` and `val`.
   - `mir_writeProjectedValue_nil`: writing `newVal` at `.nil` projection returns `.ok newVal` for every `locals`, `oldVal`, and `newVal`.
   - `mir_readProjectedValue_downcast_mismatch_is_ub`: reading through a mismatched enum variant `.downcast` returns `.ub`.
   - `mir_writePlaceValue_dead_local_is_ub`: writing to a deallocated (`.dead`) stack local via `writePlaceValue` unconditionally faults with `.ub`.
   - `mir_dynamic_index_borrow_after_storage_dead_is_ub`: universal theorem directly over `Trusted.Rustc.V2026_06_01.MirSemantics.{evalRvalue,readProjectedValue}` proving that borrowing `local[idxLocal]` records unevaluated `.index idxLocal` in `BorrowEntry.targetProjection`, so reading after `StorageDead(idxLocal)` faults with `.ub` (`GAP-MR-0003`).
2. **MiniRust `BasicMemory` Spatial/Temporal Soundness & Algebraic Bisection**:
   - `basicMem_misaligned_access_is_ub`, `basicMem_dead_alloc_access_is_ub`, `basicMem_oob_access_is_ub`.
   - `memory_interface_bisection`: algebraically separates spatial/temporal/alignment faults in `BasicMemory` from pure aliasing faults in `TreeBorrows`.
-/

namespace Correspondence.V2026_06_01.L3_PlacesAndBasicMem

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open Correspondence

/-! ## 1. Universal Theorems Directly Over `Trusted.Rustc.V2026_06_01.MirSemantics` Place Operations -/

/--
**Theorem L3.1 (`mir_readProjectedValue_nil`)**:
For EVERY local slot environment `locals : List LocalSlot` and EVERY value `v : Value`,
Anneal's `readProjectedValue locals v []` returns `.ok v`.
-/
theorem mir_readProjectedValue_nil (locals : List LocalSlot) (v : Value) :
    readProjectedValue locals v .nil = .ok v :=
  rfl

/--
**Theorem L3.2 (`mir_writeProjectedValue_nil`)**:
For EVERY local slot environment `locals : List LocalSlot` and EVERY pair of values
`oldVal newVal : Value`, Anneal's `writeProjectedValue locals oldVal [] newVal`
returns `.ok newVal`.
-/
theorem mir_writeProjectedValue_nil (locals : List LocalSlot) (oldVal newVal : Value) :
    writeProjectedValue locals oldVal .nil newVal = .ok newVal :=
  rfl

/--
**Theorem L3.3 (`mir_readProjectedValue_field_zero_scalar`)**:
Reading field 0 of a transparent wrapper around a scalar `sc : ScalarVal` in
`readProjectedValue` preserves `.scalar sc` identically across any trailing
projection suffix `rest`.
-/
theorem mir_readProjectedValue_field_zero_scalar
    (locals : List LocalSlot) (sc : ScalarVal) (ty : Ty) (rest : List ProjectionElem) :
    readProjectedValue locals (.scalar sc) (.field 0 ty :: rest) =
      readProjectedValue locals (.scalar sc) rest :=
  rfl

/--
**Theorem L3.4 (`mir_readProjectedValue_downcast_mismatch_is_ub`)**:
For EVERY aggregate value `.aggregate actualVariant fields`, if the downcast
variant `targetVariant` does not match `actualVariant` (`Nat.beq actualVariant targetVariant = false`),
then Anneal's `readProjectedValue` immediately faults with `.ub` (matching MiniRust
invalid discriminant projection UB).
-/
theorem mir_readProjectedValue_downcast_mismatch_is_ub
    (locals : List LocalSlot) (actualVariant targetVariant : Nat)
    (fields : List Value) (variantName : String) (rest : List ProjectionElem)
    (h_mismatch : Nat.beq actualVariant targetVariant = false) :
    readProjectedValue locals (.aggregate actualVariant fields)
      (.downcast variantName targetVariant :: rest) = .ub := by
  simp [readProjectedValue, h_mismatch]

/--
**Theorem L3.5 (`mir_writePlaceValue_dead_local_is_ub`)**:
For EVERY borrow table `borrows : List BorrowEntry`, EVERY trailing local frame
`restLocals : List LocalSlot`, and EVERY value `v : Value`, writing directly to
deallocated local `0` (`.dead`) via `Trusted.Rustc.V2026_06_01.MirSemantics.writePlaceValue`
unconditionally faults with `.ub` (matching MiniRust's dead-allocation check).
-/
theorem mir_writePlaceValue_dead_local_is_ub
    (restLocals : List LocalSlot) (borrows : List BorrowEntry) (v : Value) :
    writePlaceValue (.dead :: restLocals) borrows { local_ := 0, projection := .nil } v = .ub :=
  rfl

/--
**Theorem L3.6 (`mir_dynamic_index_borrow_after_storage_dead_is_ub`)**:
Universal root-cause theorem for `GAP-MR-0003` proved directly over
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalRvalue,readProjectedValue}`:
For EVERY array `elems : List Value`, EVERY initial index scalar `idxSc : ScalarVal`,
and EVERY memory state `mem : Memory`, evaluating `Rvalue.ref .shared` on
`{ local_ := 0, projection := [.index 1] }` records the unevaluated projection
`[.index 1]` in the newly allocated `BorrowEntry`, and subsequent projection read
after `StorageDead(1)` (`localsAfterDead = [.init (.aggregate 0 elems), .dead]`)
unconditionally returns `ProjReadResult.ub`.
-/
theorem mir_dynamic_index_borrow_after_storage_dead_is_ub
    (elems : List Value) (idxSc : ScalarVal) (mem : Memory) :
    let arrVal := Value.aggregate 0 elems
    let localsAtBorrow : List LocalSlot := [.init arrVal, .init (.scalar idxSc)]
    let expectedEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := [.index 1]
      perm := .frozen
    }
    evalRvalue localsAtBorrow (.ref .shared { local_ := 0, projection := [.index 1] }) mem =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8)
        localsAtBorrow
        { mem with borrows := expectedEntry :: mem.borrows, nextTag := Nat.add mem.nextTag 1 } ∧
    readProjectedValue [.init arrVal, .dead] arrVal expectedEntry.targetProjection = .ub := by
  exact ⟨rfl, rfl⟩

/-! ## 2. MiniRust `BasicMemory` State Machine (`spec/mem/basic.md`) & Algebraic Bisection -/

/-- Allocation identifier in MiniRust memory models. -/
abbrev AllocId : Type := Nat

/-- Concrete pointer `(allocId, byteOffset, provenanceTag)`. -/
structure MrPointer : Type where
  allocId : AllocId
  offset : Nat
  tag : Option Nat := none
  deriving DecidableEq, Repr

/-- Single memory allocation record in `MiniRust.BasicMemory`. -/
structure MrAllocation : Type where
  id : AllocId
  align : Align
  size : Nat
  live : Bool
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- Complete `MiniRust.BasicMemory` state. -/
structure BasicMemory : Type where
  allocs : List MrAllocation
  nextAllocId : AllocId
  deriving DecidableEq, Repr

/-- Look up an allocation by `AllocId`. -/
@[reducible]
def BasicMemory.findAlloc (mem : BasicMemory) (id : AllocId) : Option MrAllocation :=
  mem.allocs.find? (fun a => a.id == id)

/--
MiniRust `BasicMemory::check_ptr` validation checking alignment, allocation existence,
liveness (`live = true`), and in-bounds range (`ptr.offset + len ≤ alloc.size`).
-/
@[reducible]
def basicMemCheckAccess
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) :
    Except TerminationInfo MrAllocation :=
  if !Align.isAligned ptr.offset reqAlign then
    .error (.ub "misaligned pointer access")
  else
    match mem.findAlloc ptr.allocId with
    | none => .error (.ub "dangling pointer to nonexistent allocation")
    | some alloc =>
      if !alloc.live then
        .error (.ub "dangling pointer to deallocated memory")
      else if decide (ptr.offset + len ≤ alloc.size) then
        .ok alloc
      else
        .error (.ub "pointer access out of bounds")

/-- Abstract aliasing oracle layered on top of `BasicMemory`. -/
structure AliasingOracle (State : Type) : Type where
  checkAccess : State → MrPointer → Nat → Except TerminationInfo State

/-- Classification of memory faults across the `BasicMemory` / `TreeBorrows` seam. -/
inductive MemoryFaultClass : Type where
  | basicSpatialOrTemporal
  | pureAliasingViolation
  deriving DecidableEq, Repr

/-- Execute a composite memory access checking `BasicMemory` first and then `AliasingOracle`. -/
@[reducible]
def evalCompositeAccess {AState : Type}
    (mem : BasicMemory) (oracle : AliasingOracle AState) (ast : AState)
    (ptr : MrPointer) (reqAlign : Align) (len : Nat) :
    Except (MemoryFaultClass × TerminationInfo) (MrAllocation × AState) :=
  match basicMemCheckAccess mem ptr reqAlign len with
  | .error e => .error (.basicSpatialOrTemporal, e)
  | .ok alloc =>
    match oracle.checkAccess ast ptr len with
    | .error e => .error (.pureAliasingViolation, e)
    | .ok ast' => .ok (alloc, ast')

theorem basicMem_misaligned_access_is_ub
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat)
    (h_unaligned : Align.isAligned ptr.offset reqAlign = false) :
    basicMemCheckAccess mem ptr reqAlign len = .error (.ub "misaligned pointer access") := by
  unfold basicMemCheckAccess
  rw [h_unaligned]
  rfl

theorem basicMem_dead_alloc_access_is_ub
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) (alloc : MrAllocation)
    (h_aligned : Align.isAligned ptr.offset reqAlign = true)
    (h_find : mem.findAlloc ptr.allocId = some alloc)
    (h_dead : alloc.live = false) :
    basicMemCheckAccess mem ptr reqAlign len =
      .error (.ub "dangling pointer to deallocated memory") := by
  unfold basicMemCheckAccess
  rw [h_aligned]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, h_find, h_dead]
  rfl

theorem basicMem_oob_access_is_ub
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (len : Nat) (alloc : MrAllocation)
    (h_aligned : Align.isAligned ptr.offset reqAlign = true)
    (h_find : mem.findAlloc ptr.allocId = some alloc)
    (h_live : alloc.live = true)
    (h_oob : alloc.size < ptr.offset + len) :
    basicMemCheckAccess mem ptr reqAlign len =
      .error (.ub "pointer access out of bounds") := by
  unfold basicMemCheckAccess
  rw [h_aligned]
  have h_not_le : decide (ptr.offset + len ≤ alloc.size) = false := by
    simp
    omega
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, h_find, h_live, h_not_le]

theorem memory_interface_bisection {AState : Type}
    (mem : BasicMemory) (oracle : AliasingOracle AState) (ast : AState)
    (ptr : MrPointer) (reqAlign : Align) (len : Nat) (info : TerminationInfo) :
    (evalCompositeAccess mem oracle ast ptr reqAlign len = .error (.basicSpatialOrTemporal, info) ↔
      basicMemCheckAccess mem ptr reqAlign len = .error info) ∧
    (evalCompositeAccess mem oracle ast ptr reqAlign len = .error (.pureAliasingViolation, info) ↔
      (∃ alloc, basicMemCheckAccess mem ptr reqAlign len = .ok alloc) ∧
      oracle.checkAccess ast ptr len = .error info) := by
  unfold evalCompositeAccess
  cases hbasic : basicMemCheckAccess mem ptr reqAlign len with
  | error e =>
    simp
  | ok alloc =>
    cases horacle : oracle.checkAccess ast ptr len with
    | error e =>
      simp
    | ok ast' =>
      simp

theorem l3_dynamic_index_borrow_gap_witnessed :
    gapLayer .GAP_MR_0003 = .L3_PlacesAndBasicMem ∧
    gapMiriDiffCrossRef .GAP_MR_0003 = some "pass_ref_array_elem_temp_index" ∧
    VerifiedDivergenceWitness
      (evalAnnealV2026_06_01 .dynamicArrayIndexBorrow defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .dynamicArrayIndexBorrow)
      .ub
      .normalUnit :=
  ⟨rfl, rfl, witness_GAP_MR_0003⟩

end Correspondence.V2026_06_01.L3_PlacesAndBasicMem
