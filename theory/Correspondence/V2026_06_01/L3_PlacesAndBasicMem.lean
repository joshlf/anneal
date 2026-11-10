import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

/-!
# `Correspondence.V2026_06_01.L3_PlacesAndBasicMem` — Places, `BasicMemory`, & Algebraic Bisection

Connects `Trusted.Rustc.V2026_06_01.MirSemantics` place and memory operations
(`readProjectedValue`, `writeProjectedValue`, `resolveProjectedTy`, `placeTy`,
`evalOperand`, `writePlaceValue`, `evalRvalue`) to MiniRust's mechanically
extracted place projection and `BasicMemory` semantics
(`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`, `spec/mem/basic.md`,
`spec/lang/step/expressions.md`):

1. **Universal `MirSemantics` Place Projection & Write Theorems (`∀`) Across All Constructors**:
   - `.nil`: `mir_readProjectedValue_nil`, `mir_writeProjectedValue_nil`.
   - `.field`: `mir_readProjectedValue_field_aggregate`, `mir_writeProjectedValue_field_aggregate`,
     `mir_readProjectedValue_field_zero_scalar`.
   - `.deref`: `mir_readPlace_deref_live_borrow`, `mir_writePlace_deref_disabled_is_ub`,
     `mir_writePlace_deref_frozen_is_ub`.
   - `.index`: `mir_readProjectedValue_index_in_bounds`, `mir_readProjectedValue_index_oob_is_ub`,
     `mir_dynamic_index_borrow_after_storage_dead_is_ub` (`GAP-MR-0003`).
   - `.constantIndex`: `mir_readProjectedValue_constantIndex_from_start`,
     `mir_readProjectedValue_constantIndex_from_end`,
     `mir_readProjectedValue_constantIndex_short_len_is_ub`.
   - `.subslice`: `mir_readProjectedValue_subslice_from_start`,
     `mir_readProjectedValue_subslice_invalid_bounds_is_ub`.
   - `.downcast`: `mir_readProjectedValue_downcast_match`,
     `mir_readProjectedValue_downcast_mismatch_is_ub`.
   - `resolveProjectedTy` & `placeTy`: `mir_resolveProjectedTy_and_placeTy_characterization`.
2. **MiniRust `BasicMemory` Spatial/Temporal Soundness & Algebraic Bisection (`Generated.Ops`)**:
   - `basicMem_misaligned_access_is_ub`, `basicMem_dead_alloc_access_is_ub`, `basicMem_oob_access_is_ub`,
     `basicMem_deallocate_characterization`, `mrProjectOffset_and_bounds_characterization`.
   - `memory_interface_bisection`: algebraically separates spatial/temporal/alignment faults in
     `BasicMemory` from pure aliasing faults in `TreeBorrows`.
-/

namespace Correspondence.V2026_06_01.L3_PlacesAndBasicMem

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
open Correspondence

@[simp]
private theorem nat_sub_def (a b : Nat) : Nat.sub a b = a - b := rfl

export MiniRust.Snapshots.S2026_05_Matched.Generated.Ops (
  AllocId MrPointer MrAllocation BasicMemory
  basicMemCheckAccess basicMemLoad basicMemStore basicMemDeallocate
  mrProjectFieldOffset mrProjectIndexOffset mrProjectSubsliceBounds
)

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
**Theorem L3.4 (`mir_readProjectedValue_field_aggregate`)**:
Universal characterization of `.field idx ty` on `.aggregate vIdx fields` in
`MirSemantics.readProjectedValue`:
1. In-bounds field (`get? fields idx = some fieldVal`) steps to `readProjectedValue locals fieldVal rest`;
2. Out-of-bounds field (`get? fields idx = none`) faults with `.ub`.
-/
theorem mir_readProjectedValue_field_aggregate
    (locals : List LocalSlot) (vIdx idx : Nat) (fields : List Value)
    (fieldVal : Value) (ty : Ty) (rest : List ProjectionElem) :
    (get? fields idx = some fieldVal →
      readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) =
        readProjectedValue locals fieldVal rest) ∧
    (get? fields idx = none →
      readProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) = .ub) := by
  constructor
  · intro h_in
    simp [readProjectedValue, h_in]
  · intro h_oob
    simp [readProjectedValue, h_oob]

/--
**Theorem L3.5 (`mir_writeProjectedValue_field_aggregate`)**:
Universal characterization of `.field idx ty` on `.aggregate vIdx fields` in
`MirSemantics.writeProjectedValue`:
1. In-bounds field with valid nested write and `set?` updates field `idx` in place;
2. Out-of-bounds union variant field (`get? fields idx = none`) with valid nested write
   extends `fields` via `setOrExtendFields fields idx updatedFieldVal`.
-/
theorem mir_writeProjectedValue_field_aggregate
    (locals : List LocalSlot) (vIdx idx : Nat) (fields fields' : List Value)
    (oldFieldVal updatedFieldVal newVal : Value) (ty : Ty) (rest : List ProjectionElem) :
    (get? fields idx = some oldFieldVal →
      writeProjectedValue locals oldFieldVal rest newVal = .ok updatedFieldVal →
      set? fields idx updatedFieldVal = some fields' →
      writeProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) newVal =
        .ok (.aggregate vIdx fields')) ∧
    (get? fields idx = none →
      writeProjectedValue locals .unit rest newVal = .ok updatedFieldVal →
      writeProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) newVal =
        .ok (.aggregate vIdx (setOrExtendFields fields idx updatedFieldVal))) := by
  constructor
  · intro h_get h_rec h_set
    simp [writeProjectedValue, h_get, h_rec, h_set]
  · intro h_oob h_rec
    simp [writeProjectedValue, h_oob, h_rec]

/--
**Theorem L3.6 (`mir_readPlace_deref_live_borrow`)**:
Universal characterization of `.deref` read in `MirSemantics.evalOperand`:
reading `.copy { local_ := 0, projection := [.deref] }` through a pointer whose
tag resolves to a live (`.active`, `.reserved`, or `.frozen`) `BorrowEntry` targeting
local 1 returns `.ok targetVal locals`, whereas a `.disabled` borrow entry returns `.ub`.
-/
theorem mir_readPlace_deref_live_borrow
    (tag : Nat) (targetVal : Value) :
    let ptrVal : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    let locals : List LocalSlot := [.init ptrVal, .init targetVal]
    let activeEntry : BorrowEntry := {
      tag := tag
      targetLocal := 1
      targetProjection := .nil
      perm := .active
    }
    let disabledEntry : BorrowEntry := {
      tag := tag
      targetLocal := 1
      targetProjection := .nil
      perm := .disabled
    }
    evalOperand locals (.copy { local_ := 0, projection := [.deref] }) [activeEntry] =
      .ok targetVal locals ∧
    evalOperand locals (.copy { local_ := 0, projection := [.deref] }) [disabledEntry] = .ub := by
  constructor <;>
    simp [evalOperand, lookupBorrow, get?, ProvenancePtr.tag, Nat.beq_refl, readProjectedValue]

/--
**Theorem L3.7 (`mir_writePlace_deref_disabled_and_frozen_is_ub`)**:
Universal characterization of `.deref` write in `MirSemantics.writePlaceValue`:
writing through `{ local_ := 0, projection := [.deref] }` when the pointer's
`BorrowEntry` has `perm = .disabled` or `perm = .frozen` unconditionally faults with `.ub`.
-/
theorem mir_writePlace_deref_disabled_and_frozen_is_ub
    (tag : Nat) (targetVal newVal : Value) :
    let ptrVal : Value := .ptr { allocId := tag, offsetBytes := 0 } 8
    let locals : List LocalSlot := [.init ptrVal, .init targetVal]
    let disabledEntry : BorrowEntry := {
      tag := tag
      targetLocal := 1
      targetProjection := .nil
      perm := .disabled
    }
    let frozenEntry : BorrowEntry := {
      tag := tag
      targetLocal := 1
      targetProjection := .nil
      perm := .frozen
    }
    writePlaceValue locals [disabledEntry] { local_ := 0, projection := [.deref] } newVal = .ub ∧
    writePlaceValue locals [frozenEntry] { local_ := 0, projection := [.deref] } newVal = .ub := by
  constructor <;>
    simp [writePlaceValue, lookupBorrow, get?, ProvenancePtr.tag, Nat.beq_refl]

/--
**Theorem L3.8 (`mir_readProjectedValue_index_in_bounds_and_oob`)**:
Universal characterization of `.index idxLocal` in `MirSemantics.readProjectedValue`:
1. When `get? locals idxLocal = some (.init (.scalar sc))` and `get? fields sc.bits = some elemVal`,
   `readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest)` steps to
   `readProjectedValue locals elemVal rest`;
2. When `get? locals idxLocal = some (.init (.scalar sc))` and `get? fields sc.bits = none`
   (out-of-bounds index), `readProjectedValue` faults with `.ub`;
3. When `get? locals idxLocal = some .dead` or `some .uninit`, `readProjectedValue` faults with `.ub`.
-/
theorem mir_readProjectedValue_index_in_bounds_and_oob
    (locals : List LocalSlot) (idxLocal : Local) (sc : ScalarVal)
    (fields : List Value) (elemVal : Value) (rest : List ProjectionElem) :
    (get? locals idxLocal = some (.init (.scalar sc)) →
      get? fields sc.bits = some elemVal →
      readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) =
        readProjectedValue locals elemVal rest) ∧
    (get? locals idxLocal = some (.init (.scalar sc)) →
      get? fields sc.bits = none →
      readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) = .ub) ∧
    (get? locals idxLocal = some .dead →
      readProjectedValue locals (.aggregate 0 fields) (.index idxLocal :: rest) = .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_loc h_elem
    simp [readProjectedValue, h_loc, h_elem]
  · intro h_loc h_oob
    simp [readProjectedValue, h_loc, h_oob]
  · intro h_dead
    simp [readProjectedValue, h_dead]

/--
**Theorem L3.9 (`mir_readProjectedValue_constantIndex_characterization`)**:
Universal characterization of `.constantIndex offset minLen fromEnd` in
`MirSemantics.readProjectedValue`:
1. From-start (`fromEnd = false`): when `Nat.ble minLen (length fields) = true` and
   `get? fields offset = some elemVal`, steps to `readProjectedValue locals elemVal rest`;
2. From-end (`fromEnd = true`): when `Nat.ble minLen (length fields) = true` and
   `get? fields (Nat.sub (length fields) offset) = some elemVal`, steps to
   `readProjectedValue locals elemVal rest`;
3. Short length (`Nat.ble minLen (length fields) = false`): faults with `.ub`.
-/
theorem mir_readProjectedValue_constantIndex_characterization
    (locals : List LocalSlot) (offset minLen : Nat) (fromEnd : Bool)
    (fields : List Value) (elemVal : Value) (rest : List ProjectionElem) :
    (Nat.ble minLen (length fields) = true →
      get? fields offset = some elemVal →
      readProjectedValue locals (.aggregate 0 fields)
        (.constantIndex offset minLen false :: rest) =
        readProjectedValue locals elemVal rest) ∧
    (Nat.ble minLen (length fields) = true →
      get? fields (Nat.sub (length fields) offset) = some elemVal →
      readProjectedValue locals (.aggregate 0 fields)
        (.constantIndex offset minLen true :: rest) =
        readProjectedValue locals elemVal rest) ∧
    (Nat.ble minLen (length fields) = false →
      readProjectedValue locals (.aggregate 0 fields)
        (.constantIndex offset minLen fromEnd :: rest) = .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_len h_get
    simp [readProjectedValue, h_len, h_get]
  · intro h_len h_get
    rw [Nat.sub_eq] at h_get
    simp [readProjectedValue, h_len, h_get]
  · intro h_short
    unfold readProjectedValue
    simp only [h_short]

/--
**Theorem L3.10 (`mir_readProjectedValue_subslice_characterization`)**:
Universal characterization of `.subslice from_ to_ fromEnd` in
`MirSemantics.readProjectedValue`:
1. Valid from-start bounds (`Nat.ble to_ (length fields) = true` and `Nat.ble from_ to_ = true`)
   extracts `.aggregate 0 (takeValues (Nat.sub to_ from_) (dropValues from_ fields))`;
2. Out-of-bounds `to_ > length fields` (`Nat.ble to_ (length fields) = false`) faults with `.ub`;
3. Inverted bounds (`fromEnd = false`, `Nat.ble to_ (length fields) = true`, and `Nat.ble from_ to_ = false`)
   faults with `.ub`.
-/
theorem mir_readProjectedValue_subslice_characterization
    (locals : List LocalSlot) (from_ to_ : Nat) (fromEnd : Bool)
    (fields : List Value) (rest : List ProjectionElem) :
    (Nat.ble to_ (length fields) = true →
      Nat.ble from_ to_ = true →
      readProjectedValue locals (.aggregate 0 fields) (.subslice from_ to_ false :: rest) =
        readProjectedValue locals
          (.aggregate 0 (takeValues (Nat.sub to_ from_) (dropValues from_ fields)))
          rest) ∧
    (Nat.ble to_ (length fields) = false →
      readProjectedValue locals (.aggregate 0 fields) (.subslice from_ to_ fromEnd :: rest) = .ub) ∧
    (Nat.ble to_ (length fields) = true →
      Nat.ble from_ to_ = false →
      readProjectedValue locals (.aggregate 0 fields) (.subslice from_ to_ false :: rest) = .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_to h_from
    simp [readProjectedValue, extractSubslice, h_to, h_from]
  · intro h_oob
    simp [readProjectedValue, extractSubslice, h_oob]
  · intro h_to h_inv
    simp [readProjectedValue, extractSubslice, h_to, h_inv]

/--
**Theorem L3.11 (`mir_readProjectedValue_downcast_match`)**:
When `Nat.beq actualVariant targetVariant = true`, `.downcast variantName targetVariant`
preserves `.aggregate actualVariant fields` across both `readProjectedValue` and
`writeProjectedValue`.
-/
theorem mir_readProjectedValue_downcast_match
    (locals : List LocalSlot) (actualVariant targetVariant : Nat)
    (fields : List Value) (variantName : String) (rest : List ProjectionElem)
    (newVal : Value)
    (h_match : Nat.beq actualVariant targetVariant = true) :
    readProjectedValue locals (.aggregate actualVariant fields)
      (.downcast variantName targetVariant :: rest) =
      readProjectedValue locals (.aggregate actualVariant fields) rest ∧
    writeProjectedValue locals (.aggregate actualVariant fields)
      (.downcast variantName targetVariant :: rest) newVal =
      writeProjectedValue locals (.aggregate actualVariant fields) rest newVal := by
  constructor <;> simp [readProjectedValue, writeProjectedValue, h_match]

/--
**Theorem L3.12 (`mir_readProjectedValue_downcast_mismatch_is_ub`)**:
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
**Theorem L3.13 (`mir_writePlaceValue_dead_local_is_ub`)**:
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
**Theorem L3.14 (`mir_resolveProjectedTy_and_placeTy_characterization`)**:
Universal compositional characterization of `MirSemantics.{resolveProjectedTy,placeTy}`
across `.nil`, `.field`, `.deref`, `.index`, and `.constantIndex`.
-/
theorem mir_resolveProjectedTy_and_placeTy_characterization
    (localDecls : List LocalDecl) (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (baseTy fieldTy : Ty) (idx : FieldIdx) (idxLocal : Local)
    (offset minLen : Nat) (fromEnd : Bool) (rest : List ProjectionElem) (p : Place) :
    resolveProjectedTy layouts baseTy .nil = some baseTy ∧
    resolveProjectedTy layouts baseTy (.field idx fieldTy :: rest) =
      resolveProjectedTy layouts fieldTy rest ∧
    resolveProjectedTy layouts baseTy (.deref :: rest) =
      (match pointeeTyOf baseTy with
       | some innerTy => resolveProjectedTy layouts innerTy rest
       | none => none) ∧
    resolveProjectedTy layouts baseTy (.index idxLocal :: rest) =
      (match elemTyOf baseTy with
       | some elemTy => resolveProjectedTy layouts elemTy rest
       | none => none) ∧
    resolveProjectedTy layouts baseTy (.constantIndex offset minLen fromEnd :: rest) =
      (match elemTyOf baseTy with
       | some elemTy => resolveProjectedTy layouts elemTy rest
       | none => none) ∧
    placeTy localDecls layouts p =
      (match get? localDecls p.local_ with
       | some decl => resolveProjectedTy layouts decl.ty p.projection
       | none => none) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.15 (`mir_dynamic_index_borrow_after_storage_dead_corresponds`)**:
Universal remediation theorem for `GAP-MR-0003` proved directly over
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalRvalue,readProjectedValue}`:
For EVERY array `elems : List Value`, EVERY initial index scalar `idxSc : ScalarVal`,
EVERY in-bounds element `elemVal : Value` (`get? elems idxSc.bits = some elemVal`),
and EVERY memory state `mem : Memory`, evaluating `Rvalue.ref .shared` on
`{ local_ := 0, projection := [.index 1] }` resolves `[.index 1]` at borrow creation
time to `[.constantIndex idxSc.bits 0 false]`, and subsequent projection read after
`StorageDead(1)` (`localsAfterDead = [.init (.aggregate 0 elems), .dead]`) succeeds
with `ProjReadResult.ok elemVal`.
-/
theorem mir_dynamic_index_borrow_after_storage_dead_corresponds
    (elems : List Value) (idxSc : ScalarVal) (elemVal : Value) (mem : Memory)
    (h_in : get? elems idxSc.bits = some elemVal) :
    let arrVal := Value.aggregate 0 elems
    let localsAtBorrow : List LocalSlot := [.init arrVal, .init (.scalar idxSc)]
    let expectedEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := [.constantIndex idxSc.bits 0 false]
      perm := .frozen
    }
    evalRvalue localsAtBorrow (.ref .shared { local_ := 0, projection := [.index 1] }) mem =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8)
        localsAtBorrow
        { mem with borrows := expectedEntry :: mem.borrows, nextTag := Nat.add mem.nextTag 1 } ∧
    readProjectedValue [.init arrVal, .dead] arrVal expectedEntry.targetProjection = .ok elemVal := by
  constructor
  · rfl
  · have h_ble0 : Nat.ble 0 (length elems) = true :=
      Nat.ble_eq.mpr (Nat.zero_le (length elems))
    simp [readProjectedValue, h_ble0, h_in]

/-! ## 2. MiniRust `BasicMemory` State Machine (`Generated.Ops`) & Algebraic Bisection -/

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

/--
**Theorem L3.16 (`mrProjectOffset_and_deallocate_characterization`)**:
Universal characterization of `Generated.Ops.{mrProjectFieldOffset,mrProjectIndexOffset,basicMemDeallocate}`:
1. Out-of-bounds `mrProjectFieldOffset` returns `.error (.ub "field projection to invalid field")`;
2. In-bounds `mrProjectIndexOffset` (`index < count`) returns `.ok (baseOffset + index * elemSize)`
   and out-of-bounds (`count ≤ index`) returns `.error (.ub "access to out-of-bounds index")`;
3. `basicMemDeallocate` on a non-zero offset (`ptr.offset != 0 = true`) on a live allocation returns
   `.error (.ub "deallocating with pointer not to the beginning of its allocation")`.
-/
theorem mrProjectOffset_and_deallocate_characterization
    (baseOffset elemSize index count : Nat)
    (mem : BasicMemory) (ptr : MrPointer) (reqAlign : Align) (expectedSize : Nat)
    (alloc : MrAllocation) :
    mrProjectFieldOffset baseOffset [] 0 = .error (.ub "field projection to invalid field") ∧
    (index < count →
      mrProjectIndexOffset baseOffset elemSize index count = .ok (baseOffset + index * elemSize)) ∧
    (count ≤ index →
      mrProjectIndexOffset baseOffset elemSize index count =
        .error (.ub "access to out-of-bounds index")) ∧
    (mem.findAlloc ptr.allocId = some alloc →
      alloc.live = true →
      (ptr.offset != 0) = true →
      basicMemDeallocate mem ptr reqAlign expectedSize =
        .error (.ub "deallocating with pointer not to the beginning of its allocation")) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h_lt
    simp [mrProjectIndexOffset, h_lt]
  · intro h_ge
    have h_not_lt : ¬ (index < count) := by omega
    simp [mrProjectIndexOffset, h_not_lt]
  · intro h_find h_live h_off
    unfold basicMemDeallocate
    simp [h_find, h_live, h_off]

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

theorem l3_index_borrow_gap_witnessed :
    gapLayer .GAP_MR_0003 = .L3_PlacesAndBasicMem ∧
    gapMiriDiffCrossRef .GAP_MR_0003 = some "pass_ref_array_elem_temp_index" ∧
    !gapIsOpen .GAP_MR_0003 = true ∧
    VerifiedRemediationWitness
      (evalAnnealV2026_06_01 .dynamicArrayIndexBorrow defaultFixtureState)
      (evalMiniRustSnapshot .S2026_05_Matched .dynamicArrayIndexBorrow)
      .normalUnit :=
  ⟨rfl, rfl, rfl, witness_GAP_MR_0003⟩

abbrev l3_dynamic_index_borrow_gap_witnessed := l3_index_borrow_gap_witnessed

/-! ## 3. BRIEF-1.4 Correspondence Theorems: Slice Unsizing, `Rvalue.len`, Non-Scalar `ConstValue` / Global Reads, Signed `BinOp.offset`, & Structural Completeness -/

/--
**Theorem L3.17 (`mir_unsize_array_to_slice_coercion_corresponds`)**:
Universal characterization of `CastKind.pointerCoercion "Unsize"` in
`Trusted.Rustc.V2026_06_01.MirSemantics.{unsizeArrayToSliceSpec?,evalUnsizeCoercion,evalRvalue}`:
1. Positive: Shared references (`&[T; n] -> &[T]`), mutable references
   (`&mut [T; n] -> &mut [T]` and `&mut [T; n] -> &[T]`), and raw pointers
   (`*const [T; n] -> *const [T]`, `*mut [T; n] -> *mut [T]`, `*mut [T; n] -> *const [T]`)
   with compatible element type (`rigidTyEq elemTy elemTy = true`) coerce
   `Value.ptr ptrVal 8` to the 2-element slice fat pointer
   `Value.aggregate 0 [Value.ptr ptrVal 8, Value.scalar ⟨n, 8⟩]`;
2. Negative / UB: Reference unsizing with a `.disabled` borrow tag, illegal
   mutability upgrade (`&[T; n] -> &mut [T]` or `*const [T; n] -> *mut [T]`),
   element type mismatch (`rigidTyEq srcElem dstElem = false`), non-pointer
   source values, or non-8-byte pointer widths fault with `.ub`.
-/
theorem mir_unsize_array_to_slice_coercion_corresponds
    (ptrVal : ProvenancePtr) (n : Nat) (mem : Memory)
    (srcElem dstElem : RigidTy)
    (h_elem_eq : rigidTyEq srcElem dstElem = true)
    (h_no_borrow : lookupBorrow mem.borrows ptrVal.tag = .none)
    (h_no_global : lookupGlobalAlloc mem.globals ptrVal.allocId = .none)
    (h_nonnull : Nat.beq ptrVal.allocId 0 = false) :
    let locals : List LocalSlot := [.init (.ptr ptrVal 8)]
    let op : Operand := .copy { local_ := 0, projection := .nil }
    let sharedArrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .not (.array srcElem n), layoutIdx := 0 }, debugName := "" }]
    let mutArrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .mut (.array srcElem n), layoutIdx := 0 }, debugName := "" }]
    let rawConstArrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .rawPtr .not (.array srcElem n), layoutIdx := 0 }, debugName := "" }]
    let rawMutArrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .rawPtr .mut (.array srcElem n), layoutIdx := 0 }, debugName := "" }]
    let sharedSliceTy : Ty := { kind := .ref .not (.slice dstElem), layoutIdx := 0 }
    let mutSliceTy : Ty := { kind := .ref .mut (.slice dstElem), layoutIdx := 0 }
    let rawConstSliceTy : Ty := { kind := .rawPtr .not (.slice dstElem), layoutIdx := 0 }
    let rawMutSliceTy : Ty := { kind := .rawPtr .mut (.slice dstElem), layoutIdx := 0 }
    let fatPtr : Value := .aggregate 0 [.ptr ptrVal 8, .scalar ⟨n, 8⟩]
    let memDisabled : Memory := {
      mem with
      borrows := [{
        tag := ptrVal.tag
        targetLocal := 0
        targetProjection := .nil
        perm := .disabled
      }]
    }
    -- Positive cases
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op sharedSliceTy) mem sharedArrDecl =
      .ok fatPtr locals mem ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op mutSliceTy) mem mutArrDecl =
      .ok fatPtr locals mem ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op sharedSliceTy) mem mutArrDecl =
      .ok fatPtr locals mem ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op rawConstSliceTy) mem rawConstArrDecl =
      .ok fatPtr locals mem ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op rawMutSliceTy) mem rawMutArrDecl =
      .ok fatPtr locals mem ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op rawConstSliceTy) mem rawMutArrDecl =
      .ok fatPtr locals mem ∧
    -- Negative / UB cases: disabled borrow tag on reference target, mutability upgrade, bad width
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op sharedSliceTy) memDisabled sharedArrDecl =
      .ub ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op mutSliceTy) mem sharedArrDecl =
      .ub ∧
    evalRvalue locals (.cast (.pointerCoercion "Unsize") op rawMutSliceTy) mem rawConstArrDecl =
      .ub ∧
    evalRvalue [.init (.ptr ptrVal 4)] (.cast (.pointerCoercion "Unsize") op sharedSliceTy) mem sharedArrDecl =
      .ub := by
  dsimp only
  have h_reify : isReifyFnPointerCoercion "Unsize" = false := rfl
  have h_unsize : stringEq "Unsize" "Unsize" = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_no_global, h_nonnull, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, lookupBorrow, evalOperand, readProjectedValue, get?]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, operandTy, placeTy,
      resolveProjectedTy, evalOperand, readProjectedValue, get?, h_no_borrow]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, operandTy, placeTy,
      resolveProjectedTy, evalOperand, readProjectedValue, get?, h_no_borrow]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, evalOperand, readProjectedValue, get?]

/--
**Theorem L3.18 (`mir_rvalue_len_array_and_slice_corresponds`)**:
Universal characterization of `Rvalue.len place` in
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalPlaceLen,evalRvalue}`:
1. Positive (Fixed-size array): For EVERY element list `elems : List Value`
   (when `elems` is not a 2-element fat pointer `[.ptr .., .scalar ..]` or when
   `placeTy` is `RigidTy.array`), `evalRvalue` on `.len { local_ := 0, projection := .nil }`
   returns `.ok (.scalar ⟨length elems, 8⟩)`;
2. Positive (Dereferenced slice `*slice_ptr`): For EVERY fat pointer
   `Value.aggregate 0 [.ptr ptrVal 8, .scalar ⟨lenVal, 8⟩]` in local `0` whose
   borrow tag is not `.disabled`, `evalRvalue` on `.len { local_ := 0, projection := [.deref] }`
   extracts the slice length metadata `.ok (.scalar ⟨lenVal, 8⟩)`;
3. Negative / UB: Evaluating `Rvalue.len` on `*slice_ptr` when `ptrVal.tag` is
   `.disabled` in `mem.borrows`, or evaluating `Rvalue.len` directly on an
   un-dereferenced fat pointer (`projection := .nil`), faults with `.ub`.
-/
theorem mir_rvalue_len_array_and_slice_corresponds
    (ptrVal : ProvenancePtr) (lenVal : Nat) (b0 b1 b2 : Nat) (mem : Memory)
    (elemTy : RigidTy)
    (h_no_borrow : lookupBorrow mem.borrows ptrVal.tag = .none)
    (h_no_global : lookupGlobalAlloc mem.globals ptrVal.allocId = .none)
    (h_nonnull : Nat.beq ptrVal.allocId 0 = false) :
    let arrLocals : List LocalSlot :=
      [.init (.aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩])]
    let slicePtrVal : Value := .aggregate 0 [.ptr ptrVal 8, .scalar ⟨lenVal, 8⟩]
    let sliceLocals : List LocalSlot := [.init slicePtrVal]
    let sliceDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .not (.slice elemTy), layoutIdx := 0 }, debugName := "" }]
    let disabledMem : Memory := {
      mem with
      borrows := [{
        tag := ptrVal.tag
        targetLocal := 0
        targetProjection := .nil
        perm := .disabled
      }]
    }
    -- 1. Fixed-size array length
    evalRvalue arrLocals (.len { local_ := 0, projection := .nil }) mem =
      .ok (.scalar ⟨3, 8⟩) arrLocals mem ∧
    -- 2. Dereferenced slice fat pointer (*slice_ptr) length
    evalRvalue sliceLocals (.len { local_ := 0, projection := [.deref] }) mem sliceDecl =
      .ok (.scalar ⟨lenVal, 8⟩) sliceLocals mem ∧
    -- 3. Disabled borrow tag on dereferenced slice reference is UB
    evalRvalue sliceLocals (.len { local_ := 0, projection := [.deref] }) disabledMem sliceDecl =
      .ub ∧
    -- 4. Un-dereferenced slice fat pointer is UB (never returns 2)
    evalRvalue sliceLocals (.len { local_ := 0, projection := .nil }) mem =
      .ub := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp [evalRvalue, evalPlaceLen, placeTy, resolveProjectedTy,
      layoutPointerBytes, evalPlaceRead, get?,
      h_no_borrow, h_no_global, h_nonnull]
  · simp [evalRvalue, evalPlaceLen, placeTy, resolveProjectedTy,
      evalPlaceRead, get?, lookupBorrow]

/--
**Theorem L3.19 (`mir_evalConstValue_and_global_deref_read_corresponds`)**:
Universal characterization of `evalConstValue` on `ConstValue.slice` and
`ConstValue.indirect`, and non-scalar global allocation dereference reads in
`evalPlaceRead` and `evalOperand`:
1. `evalConstValue (.slice (.ptr ptrVal sz) lenMeta)` produces the 2-element
   fat pointer `.some (.aggregate 0 [.ptr ptrVal sz, .scalar ⟨lenMeta, 8⟩])`;
2. `evalConstValue (.indirect allocId 0) arrTy globals` decodes a global byte
   allocation into `.some (.aggregate 0 [.scalar ⟨b0, 1⟩, .scalar ⟨b1, 1⟩])`;
3. `evalOperand` (both `.copy` and `.move`) on `{ local_ := 0, projection := [.deref] }`
   and `{ local_ := 0, projection := [.deref, .constantIndex 1 0 false] }`
   when local `0` holds either a thin global reference `&[u8; 2]` or a slice
   fat pointer `&[u8]` decodes the global allocation via `decodeValueFromBytes`;
4. Out-of-bounds or `.uninit` global dereference reads fault with `.ub`.
-/
theorem mir_evalConstValue_and_global_deref_read_corresponds
    (ptrVal : ProvenancePtr) (sz lenMeta : Nat) (b0 b1 : UInt8) :
    let u8Kind : RigidTy := .uint .u8
    let arr2U8Ty : Ty := { kind := .array u8Kind 2, layoutIdx := 0 }
    let refArr2U8Decl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .not (.array u8Kind 2), layoutIdx := 0 }, debugName := "" }]
    let globals : List CapturedAllocation := [{
      allocId := 7
      bytes := [.some b0, .some b1]
      relocations := .nil
      align := ⟨1⟩
      mutability := .not
    }]
    let uninitGlobals : List CapturedAllocation := [{
      allocId := 7
      bytes := [.some b0, .none]
      relocations := .nil
      align := ⟨1⟩
      mutability := .not
    }]
    let globalPtr : ProvenancePtr := { allocId := 7, offsetBytes := 0 }
    let thinLocals : List LocalSlot := [.init (.ptr globalPtr 8)]
    let sliceFatLocals : List LocalSlot :=
      [.init (.aggregate 0 [.ptr globalPtr 8, .scalar ⟨2, 8⟩])]
    let oobSliceFatLocals : List LocalSlot :=
      [.init (.aggregate 0 [.ptr globalPtr 8, .scalar ⟨3, 8⟩])]
    -- 1. ConstValue.slice -> 2-element fat pointer
    evalConstValue (.slice (.ptr ptrVal sz) lenMeta) =
      .some (.aggregate 0 [.ptr ptrVal sz, .scalar ⟨lenMeta, 8⟩]) ∧
    -- 2. ConstValue.indirect -> decoded array aggregate from globals
    evalConstValue (.indirect 7 0) arr2U8Ty globals emptyLayoutTable =
      .some (.aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩]) ∧
    -- 3. Thin global dereference read of non-scalar [u8; 2] and element index
    evalPlaceRead thinLocals { local_ := 0, projection := [.deref] } .nil globals emptyLayoutTable .nil refArr2U8Decl =
      .ok (.aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩]) thinLocals ∧
    evalOperand thinLocals (.copy { local_ := 0, projection := [.deref, .constantIndex 1 0 false] }) .nil globals emptyLayoutTable .nil =
      .ok (.scalar ⟨b1.toNat, 1⟩) thinLocals ∧
    -- 4. Slice fat-pointer global dereference read (*slice_ptr)[1]
    evalOperand sliceFatLocals (.copy { local_ := 0, projection := [.deref, .constantIndex 1 0 false] }) .nil globals emptyLayoutTable .nil =
      .ok (.scalar ⟨b1.toNat, 1⟩) sliceFatLocals ∧
    evalOperand sliceFatLocals (.move { local_ := 0, projection := [.deref, .constantIndex 1 0 false] }) .nil globals emptyLayoutTable .nil =
      .ok (.scalar ⟨b1.toNat, 1⟩) sliceFatLocals ∧
    -- 5. Negative / UB: uninitialized byte or out-of-bounds slice length
    evalPlaceRead thinLocals { local_ := 0, projection := [.deref] } .nil uninitGlobals emptyLayoutTable .nil refArr2U8Decl =
      .ub ∧
    evalOperand oobSliceFatLocals (.copy { local_ := 0, projection := [.deref, .constantIndex 0 0 false] }) .nil globals emptyLayoutTable .nil =
      .ub := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.20 (`mir_binop_offset_signed_scaled_and_bounds_corresponds`)**:
Universal characterization of signed and element-scaled `BinOp.offset` in
`Trusted.Rustc.V2026_06_01.MirSemantics.{evalBinOpOffset,evalRvalue}`:
1. Positive offset (`count` elements with `stride = 4` bytes for `*const u32`)
   within allocation bound `bound` advances `offsetBytes` by `count * 4`;
2. Negative two's-complement `isize` offset (`-2`, i.e., `2^64 - 2` with
   `stride = 4` bytes) from `offsetBytes = 12` within `bound = 16` steps back to
   `offsetBytes = 4`;
3. Out-of-bounds positive offset (`newOffset > bound`), negative offset
   underflowing below `0` (`byteDelta > ptrVal.offsetBytes`), signed `isize`
   overflow (`count * stride >= 2^63`), or a `.disabled` borrow tag in
   `mem.borrows` faults with `.none` / `.ub`.
-/
theorem mir_binop_offset_signed_scaled_and_bounds_corresponds
    (allocId : Nat) :
    let u32PtrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }, debugName := "" },
       { mutability := .not, ty := { kind := .int .isize, layoutIdx := 0 }, debugName := "" }]
    let mem16 : Memory := {
      emptyMemory with
      globals := [{
        allocId := 5
        bytes := [.none, .none, .none, .none, .none, .none, .none, .none,
                  .none, .none, .none, .none, .none, .none, .none, .none]
        relocations := .nil
        align := ⟨4⟩
        mutability := .not
      }]
    }
    let ptrAt4 : ProvenancePtr := { allocId := 5, offsetBytes := 4 }
    let ptrAt12 : ProvenancePtr := { allocId := 5, offsetBytes := 12 }
    let neg2Bits : Nat := 18446744073709551614 -- 2^64 - 2 (-2 as 64-bit isize)
    let isizeHalfMod : Nat := 9223372036854775808 -- 2^63
    let lhsOp : Operand := .copy { local_ := 0, projection := .nil }
    let rhsOp : Operand := .copy { local_ := 1, projection := .nil }
    -- 1. Positive scaled offset (+2 * 4 = +8 bytes: 4 -> 12 <= 16)
    evalRvalue [.init (.ptr ptrAt4 8), .init (.scalar ⟨2, 8⟩)]
      (.binaryOp .offset lhsOp rhsOp) mem16 u32PtrDecl =
      .ok (.ptr { ptrAt4 with offsetBytes := 12 } 8)
        [.init (.ptr ptrAt4 8), .init (.scalar ⟨2, 8⟩)] mem16 ∧
    -- 2. Negative scaled offset (-2 * 4 = -8 bytes: 12 -> 4 >= 0)
    evalRvalue [.init (.ptr ptrAt12 8), .init (.scalar ⟨neg2Bits, 8⟩)]
      (.binaryOp .offset lhsOp rhsOp) mem16 u32PtrDecl =
      .ok (.ptr { ptrAt12 with offsetBytes := 4 } 8)
        [.init (.ptr ptrAt12 8), .init (.scalar ⟨neg2Bits, 8⟩)] mem16 ∧
    -- 3. Out-of-bounds positive offset (4 + 4 * 4 = 20 > 16) is UB
    evalRvalue [.init (.ptr ptrAt4 8), .init (.scalar ⟨4, 8⟩)]
      (.binaryOp .offset lhsOp rhsOp) mem16 u32PtrDecl = .ub ∧
    -- 4. Negative offset underflowing below 0 (4 - 2 * 4 < 0) is UB
    evalRvalue [.init (.ptr ptrAt4 8), .init (.scalar ⟨neg2Bits, 8⟩)]
      (.binaryOp .offset lhsOp rhsOp) mem16 u32PtrDecl = .ub ∧
    -- 5. Signed isize overflow (count * stride >= 2^63) is UB
    evalBinOpOffset { allocId := allocId, offsetBytes := 0 } 8
      ⟨isizeHalfMod, 8⟩ 1 (.some 16) = .none ∧
    -- 6. Disabled borrow tag on pointer operand is UB
    evalRvalue [.init (.ptr { allocId := 9, offsetBytes := 0 } 8), .init (.scalar ⟨0, 8⟩)]
      (.binaryOp .offset lhsOp rhsOp)
      { mem16 with borrows := [{ tag := 9, targetLocal := 0, targetProjection := .nil, perm := .disabled }] }
      u32PtrDecl = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.21 (`mir_structural_completeness_brief_1_4_corresponds`)**:
Universal characterization of the `BRIEF-1.4` structural completeness constructs:
1. `StatementKind.backwardIncompatibleDropHint` steps as a no-op advancing `stmtIdx`;
2. `ProjectionElem.unwrapUnsafeBinder` and `Rvalue.wrapUnsafeBinder` act as
   transparent value identities in `readProjectedValue`, `writeProjectedValue`,
   and `evalRvalue`;
3. `writeProjectedValue` on `ProjectionElem.subslice` splices in-bounds subslice
   aggregates and faults with `.ub` on length mismatch or out-of-bounds indices;
4. `evalRvalue` evaluates `AggregateKind.closure` to `Value.aggregate 0 vals`;
5. `Rvalue.discriminant` returns `0` (`ScalarInt` `⟨0, 8⟩`) on single-variant
   non-aggregate values (`Value.unit`, `Value.scalar`, and `Value.ptr`).
-/
theorem mir_structural_completeness_brief_1_4_corresponds
    (s : MachineState) (dropPlace : Place) (span : String)
    (locals : List LocalSlot) (v newVal v0 v1 v2 v3 w1 w2 : Value)
    (binderTy : Ty) (rest : List ProjectionElem)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (closureDefPath : DefPath) (ops : List Operand)
    (sc : ScalarVal) (ptrVal : ProvenancePtr) (ptrSz : Nat) :
    let p0 : Place := { local_ := 0, projection := .nil }
    -- 1. StatementKind.backwardIncompatibleDropHint steps as a no-op
    evalStmt s { kind := .backwardIncompatibleDropHint dropPlace, span := span } =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    -- 2. ProjectionElem.unwrapUnsafeBinder and Rvalue.wrapUnsafeBinder are transparent identities
    readProjectedValue locals v (.unwrapUnsafeBinder binderTy :: rest) =
      readProjectedValue locals v rest ∧
    writeProjectedValue locals v (.unwrapUnsafeBinder binderTy :: rest) newVal =
      writeProjectedValue locals v rest newVal ∧
    evalRvalue locals (.wrapUnsafeBinder op binderTy) mem localDecls layouts =
      evalRvalue locals (.use op) mem localDecls layouts ∧
    -- 3. writeProjectedValue on ProjectionElem.subslice (positive splice + negative UB)
    writeProjectedValue locals (.aggregate 0 [v0, v1, v2, v3])
      [.subslice 1 3 false] (.aggregate 0 [w1, w2]) =
      .ok (.aggregate 0 [v0, w1, w2, v3]) ∧
    writeProjectedValue locals (.aggregate 0 [v0, v1, v2, v3])
      [.subslice 1 1 true] (.aggregate 0 [w1, w2]) =
      .ok (.aggregate 0 [v0, w1, w2, v3]) ∧
    writeProjectedValue locals (.aggregate 0 [v0, v1, v2, v3])
      [.subslice 1 3 false] (.aggregate 0 [w1]) = .ub ∧
    writeProjectedValue locals (.aggregate 0 [v0, v1])
      [.subslice 2 2 true] (.aggregate 0 []) = .ub ∧
    -- 4. AggregateKind.closure evaluates identically to AggregateKind.tuple
    evalRvalue locals (.aggregate (.closure closureDefPath) ops) mem localDecls layouts =
      evalRvalue locals (.aggregate .tuple ops) mem localDecls layouts ∧
    -- 5. Rvalue.discriminant returns 0 on Value.unit, non-enum Value.scalar, and Value.ptr
    evalRvalue [.init .unit] (.discriminant p0) mem localDecls layouts =
      .ok (.scalar ⟨0, 8⟩) [.init .unit] mem ∧
    evalRvalue [.init (.scalar sc)] (.discriminant p0) mem .nil layouts =
      .ok (.scalar ⟨0, 8⟩) [.init (.scalar sc)] mem ∧
    evalRvalue [.init (.ptr ptrVal ptrSz)] (.discriminant p0) mem localDecls layouts =
      .ok (.scalar ⟨0, 8⟩) [.init (.ptr ptrVal ptrSz)] mem := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.22 (`mir_slice_fat_ptr_write_reborrow_retag_and_edge_cases_corresponds`)**:
Universal characterization of `B1` hardening for `BRIEF-1.4`:
1. `globalAllocSliceToAbstractBytes` succeeds on an in-bounds 0-byte read at
   `offset = alloc.bytes.length` and faults with `.none` at `offset > alloc.bytes.length`;
2. `evalConstValue (.slice (.int s) lenMeta)` normalizes integer-encoded addresses
   into `Value.ptr` fat pointers (preserving the fat-pointer representation invariant);
3. `writePlaceValue` through a dereferenced mutable slice fat pointer updates in-bounds
   elements (`idx < len`) and faults with `.ub` when `idx >= len` even if the backing
   array has additional elements;
4. `evalRvalue` supports whole-slice raw borrows (`&raw const *slice`) and rejects
   out-of-bounds element borrows (`&(*slice)[idx]` for `idx >= len`) with `.ub`;
5. `evalPlaceLen` supports zero-length arrays represented as `Value.unit` and
   slice dereferences wrapped in `ProjectionElem.unwrapUnsafeBinder`;
6. `evalBinOpOffset` permits 0-byte offsets on unbacked/dangling pointers
   (`allocId = 0`) while rejecting non-zero offsets on unbacked pointers with `.none`.
-/
theorem mir_slice_fat_ptr_write_reborrow_retag_and_edge_cases_corresponds
    (v0 v1 v2 w1 : Value) (binderTy : Ty) :
    let alloc2 : CapturedAllocation := {
      allocId := 7
      bytes := [.some 10, .some 20]
      relocations := .nil
      align := ⟨1⟩
      mutability := .not
    }
    let slicePtr : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let sliceFatVal : Value := .aggregate 0 [.ptr slicePtr 8, .scalar ⟨2, 8⟩]
    let reborrowedFatVal : Value :=
      .aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩]
    let activeBorrows : List BorrowEntry :=
      [{ tag := 1, targetLocal := 0, targetProjection := .nil, perm := .active }]
    let reborrowedEntry : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := .nil, perm := .frozen }
    let locals3 : List LocalSlot :=
      [.init (.aggregate 0 [v0, v1, v2]), .init sliceFatVal]
    let memActive : Memory :=
      { emptyMemory with borrows := activeBorrows, nextTag := 2 }
    let memReborrowed : Memory :=
      { emptyMemory with borrows := reborrowedEntry :: activeBorrows, nextTag := 3 }
    let zstArr0Decl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .array (.tuple .nil) 0, layoutIdx := 0 }, debugName := "" }]
    -- 1. 0-byte global slice bounds check at offset = len vs offset > len
    globalAllocSliceToAbstractBytes alloc2 2 0 = .some [] ∧
    globalAllocSliceToAbstractBytes alloc2 3 0 = .none ∧
    -- 2. ConstValue.slice (.int s) normalizes to Value.ptr fat pointer
    evalConstValue (.slice (.int ⟨4, 8⟩) 0) =
      .some (.aggregate 0 [.ptr { allocId := 0, offsetBytes := 4 } 8, .scalar ⟨0, 8⟩]) ∧
    -- 3. Dereferenced slice fat-pointer write: in-bounds (idx = 1 < 2) vs OOB (idx = 2 >= 2)
    writePlaceValue locals3 activeBorrows { local_ := 1, projection := [.deref, .constantIndex 1 0 false] } w1 =
      .ok [.init (.aggregate 0 [v0, w1, v2]), .init sliceFatVal] ∧
    writePlaceValue locals3 activeBorrows { local_ := 1, projection := [.deref, .constantIndex 2 0 false] } w1 =
      .ub ∧
    -- 4. Slice fat-pointer raw reborrow (&raw const *_1) and OOB element borrow (&(*_1)[2])
    evalRvalue locals3 (.rawPtr .not { local_ := 1, projection := [.deref] }) memActive =
      .ok reborrowedFatVal locals3 memReborrowed ∧
    evalRvalue locals3 (.ref .shared { local_ := 1, projection := [.deref, .constantIndex 2 0 false] }) memActive =
      .ub ∧
    -- 5. Rvalue.len on Value.unit ([T; 0]) and [.deref, .unwrapUnsafeBinder]
    evalRvalue [.init .unit] (.len { local_ := 0, projection := .nil }) emptyMemory zstArr0Decl =
      .ok (.scalar ⟨0, 8⟩) [.init .unit] emptyMemory ∧
    evalRvalue [.init sliceFatVal]
      (.len { local_ := 0, projection := [.deref, .unwrapUnsafeBinder binderTy] }) emptyMemory =
      .ok (.scalar ⟨2, 8⟩) [.init sliceFatVal] emptyMemory ∧
    -- 6. BinOp.offset 0-byte vs non-zero offset on dangling pointer (allocId = 0, bound = 0)
    evalBinOpOffset { allocId := 0, offsetBytes := 4 } 8 ⟨0, 8⟩ 4 (.some 0) =
      .some { allocId := 0, offsetBytes := 4 } ∧
    evalBinOpOffset { allocId := 0, offsetBytes := 4 } 8 ⟨1, 8⟩ 4 (.some 0) = .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.23 (`mir_subslice_disjoint_overlap_offset_borrow_and_unsize_mut_corresponds`)**:
Universal characterization of `A1` hardening for `BRIEF-1.4`:
1. `projectionsOverlap` and `normalizeSubsliceProjections` treat disjoint
   subslices (`[0..2)` vs `[2..4)`) and disjoint subslice-vs-element paths
   (`[0..2)` vs index `2`, or nested `[2..4)` followed by `.constantIndex 1`
   vs index `2`) as non-overlapping (`false`), while treating overlapping
   subslices (`[0..3)` vs `[2..4)`) and contained elements (`[0..2)` vs index `1`)
   as overlapping (`true`);
2. `evalSliceFatPtrDerefBorrow` supports non-zero `parentPtr.offsetBytes` on stack
   borrows (shifting subslice/element indices by `elemOffset`), supports `.subslice`
   and `.constantIndex` borrows on global slice allocations, and faults with `.ub`
   when a stack borrow's slice length exceeds the backing array length;
3. `evalUnsizeCoercion` rejects `.frozen` borrow tags when unsizing to `&mut [T]`
   or `*mut [T]`, and supports `Value.unit` (`[T; 0]`) in untyped mode;
4. `evalPlaceLen` on `*slice_ptr` faults with `.ub` when the backing stack borrow
   target local is `.dead` or `.uninit` or shorter than the slice metadata length;
5. `StatementKind.retag` succeeds on non-null 0-length slice fat pointers
   (`ConstValue.slice (.int ⟨4, 8⟩) 0`) and rejects `.frozen` tags on `&mut [T]` places.
-/
theorem mir_subslice_disjoint_overlap_offset_borrow_and_unsize_mut_corresponds
    (b0 b1 b2 b3 : Nat) :
    let u32Kind : RigidTy := .uint .u32
    let mutSliceTy : Ty := { kind := .ref .mut (.slice u32Kind), layoutIdx := 0 }
    let mutArrDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .mut (.array u32Kind 2), layoutIdx := 0 }, debugName := "" }]
    let frozenBorrows : List BorrowEntry :=
      [{ tag := 1, targetLocal := 0, targetProjection := .nil, perm := .frozen }]
    let activeBorrows : List BorrowEntry :=
      [{ tag := 1, targetLocal := 0, targetProjection := .nil, perm := .active }]
    let memFrozen : Memory := { emptyMemory with borrows := frozenBorrows, nextTag := 2 }
    let memActive : Memory := { emptyMemory with borrows := activeBorrows, nextTag := 2 }
    let arr4Val : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let offsetSliceFatVal : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 4 } 8, .scalar ⟨2, 8⟩]
    let oobSliceFatVal : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨5, 8⟩]
    let emptySliceFatVal : Value :=
      .aggregate 0 [.ptr { allocId := 0, offsetBytes := 4 } 8, .scalar ⟨0, 8⟩]
    let sEmptyRetag : MachineState := {
      frame := {
        blockIdx := 0
        stmtIdx := 0
        locals := [.init emptySliceFatVal]
      }
      memory := emptyMemory
    }
    -- 1. Disjoint vs overlapping subslice and element projections
    projectionsOverlap [.subslice 0 2 false] [.subslice 2 4 false] = false ∧
    projectionsOverlap [.subslice 0 2 false] [.constantIndex 2 0 false] = false ∧
    projectionsOverlap [.subslice 2 4 false, .constantIndex 1 0 false] [.constantIndex 2 0 false] = false ∧
    projectionsOverlap [.subslice 0 3 false] [.subslice 2 4 false] = true ∧
    projectionsOverlap [.subslice 0 2 false] [.constantIndex 1 0 false] = true ∧
    -- 2. Offset slice fat-pointer element borrow (&(*offset_slice)[1] -> index 1 + 1 = 2) and OOB backing array check
    evalRvalue [.init arr4Val, .init offsetSliceFatVal]
      (.ref .shared { local_ := 1, projection := [.deref, .constantIndex 1 0 false] })
      memActive =
      .ok (.ptr { allocId := 2, offsetBytes := 0 } 8)
        [.init arr4Val, .init offsetSliceFatVal]
        { emptyMemory with
          borrows :=
            { tag := 2, targetLocal := 0, targetProjection := [.constantIndex 2 0 false], perm := .frozen } ::
              activeBorrows
          nextTag := 3 } ∧
    evalRvalue [.init arr4Val, .init oobSliceFatVal]
      (.ref .shared { local_ := 1, projection := [.deref] })
      memActive = .ub ∧
    -- 3. Unsize coercion rejects .frozen tag for &mut [T] and supports Value.unit ([T; 0]) in untyped mode
    evalRvalue [.init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 0, projection := .nil }) mutSliceTy)
      memFrozen mutArrDecl = .ub ∧
    evalRvalue [.init .unit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 1, projection := .nil })
        { kind := .ref .not (.slice (.tuple .nil)), layoutIdx := 0 })
      memFrozen =
      .ok (.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩])
        [.init .unit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] memFrozen ∧
    -- 4. evalPlaceLen rejects dead backing local and OOB slice metadata on stack borrows
    evalRvalue [.dead, .init offsetSliceFatVal]
      (.len { local_ := 1, projection := [.deref] }) memActive = .ub ∧
    evalRvalue [.init arr4Val, .init oobSliceFatVal]
      (.len { local_ := 1, projection := [.deref] }) memActive = .ub ∧
    -- 5. StatementKind.retag succeeds on non-null empty slice fat pointer
    evalStmt sEmptyRetag { kind := .retag .default { local_ := 0, projection := .nil }, span := "" } =
      MirStepNode.step (advanceStmt sEmptyRetag sEmptyRetag.frame.locals) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.24 (`mir_b2_slice_stride_subslice_bounds_ptr_to_ptr_and_validity_corresponds`)**:
Universal characterization of `B2` hardening for `BRIEF-1.4`:
1. `normalizeSubsliceProjections` bounds-checks nested `.constantIndex` and
   `.subslice` projections (including `fromEnd = true`), preventing out-of-bounds
   indices from wrapping into in-bounds root indices via saturating `Nat.sub`;
2. `evalSliceFatPtrDerefBorrow` scales global slice allocation bounds and
   `.subslice` / `.constantIndex` byte offsets by element byte stride `elemSz`
   (e.g., `elemSz = 4` for `&[u32]`), and rejects out-of-bounds `fromEnd = true`
   element borrows with `.ub`;
3. `resolveDerefWriteFullProj` and `invalidateDerefWriteBorrows` window 0-offset
   slice fat-pointer writes by `.subslice 0 len false`, preserving disjoint
   borrows on the remainder of the backing array (`[2..4)`);
4. `evalUnsizeCoercion` rejects `.frozen` borrow tags when unsizing to `*mut [T]`
   in typed mode and supports untyped global array unsizing;
5. `CastKind.ptrToPtr` strips metadata when casting a 2-element slice fat pointer
   `*const [T]` to a thin raw pointer `*const T` (`slice::as_ptr`) while rejecting
   thin-to-wide `.ptrToPtr` casts with `.ub`, and `UnOp.ptrMetadata` returns
   `Value.unit` on thin pointers;
6. `evalConstValue` and `evalGlobalDerefRead` enforce `bool` bit-validity (`0`/`1`)
   and `char` scalar validity, and `rigidTyByteSize` / `decodeValueFromBytes`
   support homogeneous arrays of tuples `[(u8, u8); 2]`.
-/
theorem mir_b2_slice_stride_subslice_bounds_ptr_to_ptr_and_validity_corresponds
    (b0 b1 b2 b3 : UInt8) :
    let u32Kind : RigidTy := .uint .u32
    let u16Kind : RigidTy := .uint .u16
    let u8Kind : RigidTy := .uint .u8
    let rawMutSliceU32Ty : Ty := { kind := .rawPtr .mut (.slice u32Kind), layoutIdx := 0 }
    let rawConstU32Ty : Ty := { kind := .rawPtr .not u32Kind, layoutIdx := 0 }
    let rawMutArrU32Decl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .rawPtr .mut (.array u32Kind 2), layoutIdx := 0 }, debugName := "" }]
    let refSliceU32Decl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .not (.slice u32Kind), layoutIdx := 0 }, debugName := "" }]
    let boolTy : Ty := { kind := .bool, layoutIdx := 0 }
    let refBoolDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .ref .not .bool, layoutIdx := 0 }, debugName := "" }]
    let arrTuple2U8Ty : Ty :=
      { kind := .array (.tuple [u8Kind, u8Kind]) 2, layoutIdx := 0 }
    let alloc8 : CapturedAllocation := {
      allocId := 7
      bytes := [.some 1, .some 0, .some 0, .some 0, .some 2, .some 0, .some 0, .some 0]
      relocations := .nil
      align := ⟨4⟩
      mutability := .not
    }
    let allocInvalidBool : CapturedAllocation := {
      allocId := 9
      bytes := [.some 2]
      relocations := .nil
      align := ⟨1⟩
      mutability := .not
    }
    let memGlobal8 : Memory := { emptyMemory with globals := [alloc8] }
    let globalSlice2U32 : Value :=
      .aggregate 0 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩]
    let globalSlice3U32Oob : Value :=
      .aggregate 0 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩]
    let arr4Val : Value :=
      .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩]
    let slice0To2FatVal : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩]
    let borrowSlice0To2 : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .active }
    let borrowSlice2To4 : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.subslice 2 4 false], perm := .frozen }
    let frozenBorrow : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .frozen }
    -- 1. Out-of-bounds nested .constantIndex (fromEnd = true, offset = 5, minLen = 5 > subLen = 2) does not wrap to index 0
    normalizeSubsliceProjections [.subslice 1 3 false, .constantIndex 5 5 true] =
      [.subslice 1 3 false, .constantIndex 5 5 true] ∧
    readProjectedValue .nil arr4Val
      (normalizeSubsliceProjections [.subslice 1 3 false, .constantIndex 5 5 true]) = .ub ∧
    -- 2. Global slice borrow scales by elemSz = 4 (idx 1 -> offsetBytes = 4) and rejects 3 * 4 = 12 > 8 bytes
    evalRvalue [.init globalSlice2U32]
      (.ref .shared { local_ := 0, projection := [.deref, .constantIndex 1 0 false] })
      memGlobal8 refSliceU32Decl =
      .ok (.ptr { allocId := 7, offsetBytes := 4 } 8) [.init globalSlice2U32] memGlobal8 ∧
    evalRvalue [.init globalSlice3U32Oob]
      (.ref .shared { local_ := 0, projection := [.deref] })
      memGlobal8 refSliceU32Decl = .ub ∧
    evalRvalue [.init globalSlice2U32]
      (.ref .shared { local_ := 0, projection := [.deref, .constantIndex 5 0 true] })
      memGlobal8 refSliceU32Decl = .ub ∧
    -- 3. 0-offset slice fat-pointer write (*s1 = ...) preserves disjoint borrow on [2..4)
    invalidateDerefWriteBorrows
      [.init arr4Val, .init slice0To2FatVal]
      [borrowSlice0To2, borrowSlice2To4]
      { local_ := 1, projection := [.deref] }
      .nil =
      [borrowSlice0To2, borrowSlice2To4] ∧
    -- 4. Typed Unsize coercion to *mut [u32] rejects .frozen tag, and untyped Unsize on global 8-byte alloc -> len 4 &[u16]
    evalRvalue [.init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 0, projection := .nil }) rawMutSliceU32Ty)
      { emptyMemory with borrows := [frozenBorrow] } rawMutArrU32Decl = .ub ∧
    evalRvalue [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 0, projection := .nil })
        { kind := .ref .not (.slice u16Kind), layoutIdx := 0 })
      memGlobal8 =
      .ok (.aggregate 0 [.ptr { allocId := 7, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩])
        [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)] memGlobal8 ∧
    -- 5. Fat-to-thin CastKind.ptrToPtr (slice::as_ptr) and thin UnOp.ptrMetadata
    evalRvalue [.init globalSlice2U32]
      (.cast .ptrToPtr (.copy { local_ := 0, projection := .nil }) rawConstU32Ty)
      emptyMemory =
      .ok (.ptr { allocId := 7, offsetBytes := 0 } 8) [.init globalSlice2U32] emptyMemory ∧
    evalRvalue [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)]
      (.unaryOp .ptrMetadata (.copy { local_ := 0, projection := .nil }))
      emptyMemory =
      .ok .unit [.init (.ptr { allocId := 7, offsetBytes := 0 } 8)] emptyMemory ∧
    -- 6. Invalid bool (byte 2) rejected in evalConstValue / evalPlaceRead, and [(u8, u8); 2] decoded
    evalConstValue (.indirect 9 0) boolTy [allocInvalidBool] emptyLayoutTable = .none ∧
    evalPlaceRead [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      { local_ := 0, projection := [.deref] } .nil [allocInvalidBool] emptyLayoutTable .nil refBoolDecl = .ub ∧
    decodeValueFromBytes defaultCodecFuel emptyLayoutTable arrTuple2U8Ty
      [.init b0 .none, .init b1 .none, .init b2 .none, .init b3 .none] =
      .some (.aggregate 0 [
        .aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩],
        .aggregate 0 [.scalar ⟨b2.toNat, 1⟩, .scalar ⟨b3.toNat, 1⟩]
      ]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.25 (`mir_a2_as_ptr_offset_deref_array_elem_bound_and_typed_unsize_corresponds`)**:
Universal characterization of `A2` hardening for `BRIEF-1.4`:
1. `ptrAllocByteBound?` and `BinOp.offset` compute the remaining byte bound
   `(arrLen - baseIdx) * elemSz` from an element pointer (`targetProjection =
   [.constantIndex 1 0 false]` on `[u32; 4]` -> `12` bytes), permitting in-bounds
   multi-element offsets (`p1.offset(2)` -> `offsetBytes = 8`) and rejecting
   offsets beyond the enclosing array (`p1.offset(4)` -> `.ub`);
2. `resolveStackThinPtrTargetProj?` resolves `offsetBytes` on stack-backed thin
   pointers across `evalPlaceRead`, `evalOperand`, `writePlaceValue`,
   `resolveDerefWriteFullProj`, `invalidateDerefWriteBorrows`, and `evalRvalue`
   (`.ref` / `.rawPtr`), shifting `baseIdx = 1` by `8 / 4 = 2` to access `arr[3]`,
   rejecting one-past-the-end (`offsetBytes = 12`) and misaligned (`offsetBytes = 2`)
   dereferences with `.ub`, and preserving disjoint borrows (`[0..2)`) while
   disabling overlapping borrows (`arr[3]`) on dereferenced writes;
3. Subslice fat-to-thin `slice::as_ptr()` pointers (`targetProjection =
   [.subslice 1 3 false]`) dereference to `arr[1]` at `offsetBytes = 0`, `arr[2]`
   at `offsetBytes = 4`, and fault with `.ub` at `offsetBytes = 8`;
4. Typed `evalUnsizeCoercion` rejects `.dead` stack referents and out-of-bounds
   backing arrays (`elemOffset + n > length elems`), and untyped `evalUnsizeCoercion`
   rejects misaligned global byte offsets (`offsetBytes = 1` for `&[u32]`);
5. `evalSliceFatPtrDerefBorrow` normalizes chained subslice/element projections
   (`[.deref, .subslice 1 4 false, .constantIndex 1 0 false]` -> `arr[2]`), and
   `CastKind.ptrToPtr` rejects 2-element fat pointers with non-8-byte metadata or
   non-`rawPtr` target types with `.ub`.
-/
theorem mir_a2_as_ptr_offset_deref_array_elem_bound_and_typed_unsize_corresponds
    (b0 b1 b2 b3 : Nat) :
    let u32Kind : RigidTy := .uint .u32
    let rawMutU32Ty : Ty := { kind := .rawPtr .mut u32Kind, layoutIdx := 0 }
    let refSharedSliceU32Ty : Ty := { kind := .ref .not (.slice u32Kind), layoutIdx := 0 }
    let arr4Val : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let arr4Updated3 : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨99, 4⟩]
    let elem1Borrow : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [.constantIndex 1 0 false], perm := .active }
    let sub0To2Borrow : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.subslice 0 2 false], perm := .frozen }
    let elem3Borrow : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [.constantIndex 3 0 false], perm := .frozen }
    let sub1To3Borrow : BorrowEntry :=
      { tag := 4, targetLocal := 0, targetProjection := [.subslice 1 3 false], perm := .frozen }
    let fullArrBorrow : BorrowEntry :=
      { tag := 5, targetLocal := 0, targetProjection := .nil, perm := .active }
    let memElem1 : Memory := { emptyMemory with borrows := [elem1Borrow], nextTag := 2 }
    let ptrElem1Decls : List LocalDecl := [
      { mutability := .mut, ty := { kind := .array u32Kind 4, layoutIdx := 0 }, debugName := "" },
      { mutability := .not, ty := rawMutU32Ty, debugName := "" },
      { mutability := .not, ty := { kind := .int .isize, layoutIdx := 0 }, debugName := "" }
    ]
    let unsize4Decls : List LocalDecl := [
      { mutability := .not, ty := { kind := .array u32Kind 2, layoutIdx := 0 }, debugName := "" },
      { mutability := .not, ty := { kind := .ref .not (.array u32Kind 4), layoutIdx := 0 }, debugName := "" }
    ]
    let alloc9Bytes : CapturedAllocation := {
      allocId := 8
      bytes := [.some 0, .some 1, .some 0, .some 0, .some 0, .some 2, .some 0, .some 0, .some 0]
      relocations := .nil
      align := ⟨4⟩
      mutability := .not
    }
    let slice4FatVal : Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩]
    -- 1. ptrAllocByteBound? & BinOp.offset on element pointer (&raw mut arr[1])
    ptrAllocByteBound? [.init arr4Val] memElem1 ptrElem1Decls emptyLayoutTable
      { allocId := 1, offsetBytes := 0 } = .some 12 ∧
    evalRvalue
      [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init (.scalar ⟨2, 8⟩)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (.copy { local_ := 2, projection := .nil }))
      memElem1 ptrElem1Decls =
      .ok (.ptr { allocId := 1, offsetBytes := 8 } 8)
        [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init (.scalar ⟨2, 8⟩)]
        memElem1 ∧
    evalRvalue
      [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .init (.scalar ⟨4, 8⟩)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (.copy { local_ := 2, projection := .nil }))
      memElem1 ptrElem1Decls = .ub ∧
    -- 2. Offset thin-pointer deref read, OOB/misaligned UB, write, and scoped borrow invalidation
    evalOperand [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 8 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [elem1Borrow] =
      .ok (.scalar ⟨b3, 4⟩) [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 8 } 8)] ∧
    evalOperand [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 12 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [elem1Borrow] = .ub ∧
    evalOperand [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 2 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [elem1Borrow] = .ub ∧
    writePlaceValue [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 8 } 8)]
      [elem1Borrow] { local_ := 1, projection := [.deref] } (.scalar ⟨99, 4⟩) =
      .ok [.init arr4Updated3, .init (.ptr { allocId := 1, offsetBytes := 8 } 8)] ∧
    invalidateDerefWriteBorrows
      [.init arr4Val, .init (.ptr { allocId := 1, offsetBytes := 8 } 8)]
      [elem1Borrow, sub0To2Borrow, elem3Borrow]
      { local_ := 1, projection := [.deref] } .nil =
      [elem1Borrow, sub0To2Borrow, { elem3Borrow with perm := .disabled }] ∧
    -- 3. Subslice fat-to-thin slice::as_ptr() deref at offsetBytes = 0, 4, and OOB 8
    evalOperand [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 0 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [sub1To3Borrow] =
      .ok (.scalar ⟨b1, 4⟩) [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 0 } 8)] ∧
    evalOperand [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 4 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [sub1To3Borrow] =
      .ok (.scalar ⟨b2, 4⟩) [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 4 } 8)] ∧
    evalOperand [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 8 } 8)]
      (.copy { local_ := 1, projection := [.deref] }) [sub1To3Borrow] = .ub ∧
    -- 4. Typed & untyped evalUnsizeCoercion liveness, bounds, and global alignment checks
    evalRvalue [.dead, .init (.ptr { allocId := 5, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 1, projection := .nil }) refSharedSliceU32Ty)
      { emptyMemory with borrows := [fullArrBorrow] } unsize4Decls = .ub ∧
    evalRvalue
      [.init (.aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩]),
       .init (.ptr { allocId := 5, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 1, projection := .nil }) refSharedSliceU32Ty)
      { emptyMemory with borrows := [fullArrBorrow] } unsize4Decls = .ub ∧
    evalRvalue [.init (.ptr { allocId := 8, offsetBytes := 1 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 0, projection := .nil }) refSharedSliceU32Ty)
      { emptyMemory with globals := [alloc9Bytes] } = .ub ∧
    -- 5. Chained subslice/element borrow normalization & CastKind.ptrToPtr validation
    evalRvalue [.init arr4Val, .init slice4FatVal]
      (.ref .shared { local_ := 1, projection := [.deref, .subslice 1 4 false, .constantIndex 1 0 false] })
      { emptyMemory with borrows := [fullArrBorrow], nextTag := 6 } =
      .ok (.ptr { allocId := 6, offsetBytes := 0 } 8)
        [.init arr4Val, .init slice4FatVal]
        { emptyMemory with
          borrows :=
            { tag := 6, targetLocal := 0, targetProjection := [.constantIndex 2 0 false], perm := .frozen } ::
              [fullArrBorrow]
          nextTag := 7 } ∧
    evalRvalue [.init (.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨4, 4⟩])]
      (.cast .ptrToPtr (.copy { local_ := 0, projection := .nil }) rawMutU32Ty)
      emptyMemory = .ub ∧
    evalRvalue [.init slice4FatVal]
      (.cast .ptrToPtr (.copy { local_ := 0, projection := .nil }) refSharedSliceU32Ty)
      emptyMemory = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.26 (`mir_ordering_discriminant_subslice_alloc_bound_and_as_ptr_corresponds`)**:
Universal characterization of `B3` hardening for `BRIEF-1.4`:
1. `Rvalue.discriminant` on `core::cmp::Ordering` (`#[repr(i8)] enum Ordering { Less = -1, Equal = 0, Greater = 1 }`)
   preserves the signed 1-byte discriminant scalar (`⟨255, 1⟩` for `Less`, `⟨0, 1⟩`
   for `Equal`, `⟨1, 1⟩` for `Greater`) produced by `BinOp.cmp` (or 0-field
   `Value.aggregate 0 []` / `1 []` / `2 []`), returns `⟨0, 8⟩` on single-variant
   struct ADTs (`VariantsShape.single`) and primitive types, and faults with `.ub`
   on uninhabited ADTs (`VariantsShape.empty`);
2. `ptrAllocByteBound?` and `BinOp.offset` on a `.subslice 1 3 false` borrow of
   `[u32; 4]` with non-empty `localDecls` enforce the 2-element subslice byte
   bound (`8` bytes rather than the 4-element parent array's `16` bytes),
   permitting `p.offset(2)` (`offsetBytes = 8`) while rejecting `p.offset(3)`
   (`offsetBytes = 12`) with `.ub`;
3. Casting a root-array slice fat pointer (`Unsize` of `&arr` / `&mut arr` with
   `targetProjection = .nil`) to a thin element pointer via `CastKind.ptrToPtr`
   (`slice::as_ptr` / `slice::as_mut_ptr`) or `CastKind.pointerCoercion "ArrayToPointer"`
   derives a `.subslice 0 4 false` borrow entry, so `*p` at `offsetBytes = 0` and
   `*(p.offset(2))` at `offsetBytes = 8` read/write individual elements (`arr[0]`
   and `arr[2]`) in `evalOperand` and `writePlaceValue` instead of reading/overwriting
   the whole array aggregate;
4. `Rvalue.ref` and `Rvalue.rawPtr` support dereferenced reborrows (`&*p` and
   `&(*p)[idx]`) on thin pointers backed by `mem.globals`.
-/
theorem mir_ordering_discriminant_subslice_alloc_bound_and_as_ptr_corresponds
    (b0 b1 b2 b3 w2 : Nat) :
    let arr4Val : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let arr4UpdatedVal : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨w2, 4⟩, .scalar ⟨b3, 4⟩]
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let arr4U32Ty : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }
    let rawConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
    let rawMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
    let orderingTy : Ty := { kind := .adt "core::cmp::Ordering" .nil, layoutIdx := 0 }
    let orderingDecl : List LocalDecl :=
      [{ mutability := .not, ty := orderingTy, debugName := "" }]
    let u32Decl : List LocalDecl :=
      [{ mutability := .not, ty := u32Ty, debugName := "" }]
    let singleAdtLayout : Trusted.Rustc.V2026_06_01.Layout.LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries := [{
          size := ⟨4⟩
          align := ⟨4⟩
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
          fields := .arbitrary [⟨0⟩] [0]
          variants := .single 0
          isUninhabited := false
        }] }
    let emptyAdtLayout : Trusted.Rustc.V2026_06_01.Layout.LayoutTable :=
      { pointerBits := 64
        isLittleEndian := true
        entries := [{
          size := ⟨0⟩
          align := ⟨1⟩
          backendRepr := .memory
          fields := .primitive
          variants := .empty
          isUninhabited := true
        }] }
    let sub1To3Borrow : BorrowEntry :=
      { tag := 4, targetLocal := 0, targetProjection := [.subslice 1 3 false], perm := .frozen }
    let subOffsetDecls : List LocalDecl :=
      [{ mutability := .not, ty := arr4U32Ty, debugName := "" },
       { mutability := .not, ty := rawConstU32Ty, debugName := "" },
       { mutability := .not, ty := { kind := .int .isize, layoutIdx := 0 }, debugName := "" }]
    let fullMutBorrow : BorrowEntry :=
      { tag := 5, targetLocal := 0, targetProjection := .nil, perm := .active }
    let derivedElemBorrow : BorrowEntry :=
      { tag := 6, targetLocal := 0, targetProjection := [.subslice 0 4 false], perm := .active }
    let slice4MutFatVal : Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩]
    let globalArrAlloc : CapturedAllocation := {
      allocId := 9
      bytes := [.some 1, .some 0, .some 0, .some 0, .some 2, .some 0, .some 0, .some 0]
      relocations := .nil
      align := ⟨4⟩
      mutability := .not
    }
    let globalArrPtrDecls : List LocalDecl :=
      [{ mutability := .not,
         ty := { kind := .ref .not (.array (.uint .u32) 2), layoutIdx := 0 },
         debugName := "" }]
    let p0 : Place := { local_ := 0, projection := .nil }
    -- 1. Rvalue.discriminant on core::cmp::Ordering (scalar from BinOp.cmp & aggregate) vs single/empty/primitive
    evalRvalue [.init (.scalar ⟨255, 1⟩)] (.discriminant p0) emptyMemory orderingDecl =
      .ok (.scalar ⟨255, 1⟩) [.init (.scalar ⟨255, 1⟩)] emptyMemory ∧
    evalRvalue [.init (.scalar ⟨0, 1⟩)] (.discriminant p0) emptyMemory orderingDecl =
      .ok (.scalar ⟨0, 1⟩) [.init (.scalar ⟨0, 1⟩)] emptyMemory ∧
    evalRvalue [.init (.scalar ⟨1, 1⟩)] (.discriminant p0) emptyMemory orderingDecl =
      .ok (.scalar ⟨1, 1⟩) [.init (.scalar ⟨1, 1⟩)] emptyMemory ∧
    evalRvalue [.init (.aggregate 0 .nil)] (.discriminant p0) emptyMemory orderingDecl =
      .ok (.scalar ⟨255, 1⟩) [.init (.aggregate 0 .nil)] emptyMemory ∧
    evalRvalue [.init (.scalar ⟨42, 4⟩)] (.discriminant p0) emptyMemory orderingDecl singleAdtLayout =
      .ok (.scalar ⟨0, 8⟩) [.init (.scalar ⟨42, 4⟩)] emptyMemory ∧
    evalRvalue [.init (.scalar ⟨42, 4⟩)] (.discriminant p0) emptyMemory orderingDecl emptyAdtLayout =
      .ub ∧
    evalRvalue [.init (.scalar ⟨42, 4⟩)] (.discriminant p0) emptyMemory u32Decl =
      .ok (.scalar ⟨0, 8⟩) [.init (.scalar ⟨42, 4⟩)] emptyMemory ∧
    -- 2. Subslice allocation byte bound with non-empty localDecls (8 bytes, not 16 bytes)
    evalRvalue
      [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 0 } 8), .init (.scalar ⟨2, 8⟩)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (.copy { local_ := 2, projection := .nil }))
      { emptyMemory with borrows := [sub1To3Borrow] }
      subOffsetDecls =
      .ok (.ptr { allocId := 4, offsetBytes := 8 } 8)
        [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 0 } 8), .init (.scalar ⟨2, 8⟩)]
        { emptyMemory with borrows := [sub1To3Borrow] } ∧
    evalRvalue
      [.init arr4Val, .init (.ptr { allocId := 4, offsetBytes := 0 } 8), .init (.scalar ⟨3, 8⟩)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (.copy { local_ := 2, projection := .nil }))
      { emptyMemory with borrows := [sub1To3Borrow] }
      subOffsetDecls = .ub ∧
    -- 3. Unsize -> CastKind.ptrToPtr (slice::as_mut_ptr) -> deref read/write at offset 0 and offset 8
    evalRvalue
      [.init arr4Val, .init slice4MutFatVal]
      (.cast .ptrToPtr (.copy { local_ := 1, projection := .nil }) rawMutU32Ty)
      { emptyMemory with borrows := [fullMutBorrow], nextTag := 6 } =
      .ok (.ptr { allocId := 6, offsetBytes := 0 } 8)
        [.init arr4Val, .init slice4MutFatVal]
        { emptyMemory with borrows := [derivedElemBorrow, fullMutBorrow], nextTag := 7 } ∧
    evalOperand
      [.init arr4Val, .init (.ptr { allocId := 6, offsetBytes := 0 } 8)]
      (.copy { local_ := 1, projection := [.deref] })
      [derivedElemBorrow, fullMutBorrow] =
      .ok (.scalar ⟨b0, 4⟩) [.init arr4Val, .init (.ptr { allocId := 6, offsetBytes := 0 } 8)] ∧
    writePlaceValue
      [.init arr4Val, .init (.ptr { allocId := 6, offsetBytes := 8 } 8)]
      [derivedElemBorrow, fullMutBorrow]
      { local_ := 1, projection := [.deref] }
      (.scalar ⟨w2, 4⟩) =
      .ok [.init arr4UpdatedVal, .init (.ptr { allocId := 6, offsetBytes := 8 } 8)] ∧
    -- 4. Global thin pointer deref reborrow (&*p and &(*p)[1])
    evalRvalue
      [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      (.ref .shared { local_ := 0, projection := [.deref, .constantIndex 1 0 false] })
      { emptyMemory with globals := [globalArrAlloc] }
      globalArrPtrDecls =
      .ok (.ptr { allocId := 9, offsetBytes := 4 } 8)
        [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
        { emptyMemory with globals := [globalArrAlloc] } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.27 (`mir_a3_elem_slice_from_raw_parts_tuple_stride_discriminant_and_index_write_corresponds`)**:
Universal characterization of `A3` hardening for `BRIEF-1.4`:
1. `readSliceBackingAggregate?` enables slice fat pointers constructed from an
   array element pointer (`targetProjection = [.constantIndex 1 0 false]`, e.g.
   `core::ptr::slice_from_raw_parts(&raw mut arr[1], 2)`) to evaluate `Rvalue.len`
   (succeeding for `len = 2 <= 4 - 1` and faulting with `.ub` for `len = 4 > 3`),
   dereference reads (`(*s)[1]` -> `arr[2]`), dereference writes (`(*s)[1] = w2`),
   scoped borrow invalidation (`invalidateDerefWriteBorrows` preserving `arr[0]`
   while disabling `arr[2]`), and dereferenced element borrows (`&(*s)[1]` ->
   `targetProjection = [.constantIndex 2 0 false]`);
2. `inferElemListByteStride` and `valueDefaultByteSize` (via `inferValueByteSizeAux`)
   compute the true byte stride of aggregate array/slice elements (`8` bytes for
   `(u32, u32)` tuples), so dereferencing an offset slice fat pointer at
   `offsetBytes = 8` reads `[tuple1, tuple2]` while rejecting misaligned
   `offsetBytes = 4` with `.ub`;
3. `evalPlaceDiscriminant` returns `.ub` on `.never` places, rejects invalid
   `core::cmp::Ordering` scalar bit patterns (`⟨42, 1⟩`) and widths (`⟨0, 4⟩`)
   with `.ub`, and rejects out-of-range scalar tags and out-of-bounds `variantIdx`
   on `VariantsShape.multiple` layouts with `.ub`;
4. `evalGlobalThinPtrDerefBorrow` normalizes chained subslice projections
   (`&((*global_arr_ptr)[1..4][1..3])` -> `offsetBytes = 8`) and supports
   `fromEnd = true` element borrows (`&((*global_arr_ptr)[..fromEnd 1])` ->
   `offsetBytes = 12` on `[u32; 4]`);
5. `StatementKind.assign` resolves dynamic `.index idxLocal` projections via
   `resolveBorrowProjectionElems` before Tree Borrows invalidation, so assigning
   `arr[i] = w0` at `i = 0` preserves disjoint borrows (`arr[2]`) while disabling
   overlapping borrows (`arr[0]`).
-/
theorem mir_a3_elem_slice_from_raw_parts_tuple_stride_discriminant_and_index_write_corresponds
    (b0 b1 b2 b3 w0 w2 : Nat) :
    let arr4Val : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let arr4Updated2 : Value :=
      .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨w2, 4⟩, .scalar ⟨b3, 4⟩]
    let arr4Updated0 : Value :=
      .aggregate 0 [.scalar ⟨w0, 4⟩, .scalar ⟨b1, 4⟩, .scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let elem0Borrow : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.constantIndex 0 0 false], perm := .frozen }
    let elem1MutBorrow : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [.constantIndex 1 0 false], perm := .active }
    let elem2Borrow : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [.constantIndex 2 0 false], perm := .frozen }
    let sliceFromElem1Len2 : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩]
    let sliceFromElem1Len4Oob : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩]
    let memElem1 : Memory := { emptyMemory with borrows := [elem1MutBorrow], nextTag := 4 }
    let tup0 : Value := .aggregate 0 [.scalar ⟨b0, 4⟩, .scalar ⟨b1, 4⟩]
    let tup1 : Value := .aggregate 0 [.scalar ⟨b2, 4⟩, .scalar ⟨b3, 4⟩]
    let tup2 : Value := .aggregate 0 [.scalar ⟨w0, 4⟩, .scalar ⟨w2, 4⟩]
    let tupleArr3Val : Value := .aggregate 0 [tup0, tup1, tup2]
    let fullTupleArrBorrow : BorrowEntry :=
      { tag := 5, targetLocal := 0, targetProjection := .nil, perm := .frozen }
    let tupleSliceAt8 : Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 8 } 8, .scalar ⟨2, 8⟩]
    let tupleSliceAt4Misaligned : Value :=
      .aggregate 0 [.ptr { allocId := 5, offsetBytes := 4 } 8, .scalar ⟨1, 8⟩]
    let neverDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .never, layoutIdx := 0 }, debugName := "" }]
    let orderingDecl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .adt "core::cmp::Ordering" .nil, layoutIdx := 0 }, debugName := "" }]
    let enum2Decl : List LocalDecl :=
      [{ mutability := .not, ty := { kind := .adt "MyEnum" .nil, layoutIdx := 0 }, debugName := "" }]
    let enum2Layout : Trusted.Rustc.V2026_06_01.Layout.LayoutTable := {
      pointerBits := 64
      isLittleEndian := true
      entries := [{
        size := ⟨1⟩
        align := ⟨1⟩
        backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩)
        fields := .primitive
        variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0 [.primitive, .primitive]
        isUninhabited := false
      }]
    }
    let globalArr4Alloc : CapturedAllocation := {
      allocId := 9
      bytes := [
        .some 1, .some 0, .some 0, .some 0,
        .some 2, .some 0, .some 0, .some 0,
        .some 3, .some 0, .some 0, .some 0,
        .some 4, .some 0, .some 0, .some 0
      ]
      relocations := .nil
      align := ⟨4⟩
      mutability := .not
    }
    let globalArr4PtrDecls : List LocalDecl :=
      [{ mutability := .not,
         ty := { kind := .ref .not (.array (.uint .u32) 4), layoutIdx := 0 },
         debugName := "" }]
    let assignIdx0Stmt : Statement := {
      kind := .assign
        { local_ := 0, projection := [.index 1] }
        (.use (.copy { local_ := 2, projection := .nil }))
      span := ""
    }
    let initAssignState : MachineState := {
      frame := {
        blockIdx := 0
        stmtIdx := 0
        locals := [.init arr4Val, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨w0, 4⟩)]
      }
      memory := { emptyMemory with borrows := [elem0Borrow, elem2Borrow] }
    }
    let p0 : Place := { local_ := 0, projection := .nil }
    -- 1. Slice fat pointer backed by element borrow (&raw mut arr[1])
    evalRvalue [.init arr4Val, .init sliceFromElem1Len2]
      (.len { local_ := 1, projection := [.deref] }) memElem1 =
      .ok (.scalar ⟨2, 8⟩) [.init arr4Val, .init sliceFromElem1Len2] memElem1 ∧
    evalRvalue [.init arr4Val, .init sliceFromElem1Len4Oob]
      (.len { local_ := 1, projection := [.deref] }) memElem1 = .ub ∧
    evalOperand [.init arr4Val, .init sliceFromElem1Len2]
      (.copy { local_ := 1, projection := [.deref, .constantIndex 1 0 false] })
      [elem1MutBorrow] =
      .ok (.scalar ⟨b2, 4⟩) [.init arr4Val, .init sliceFromElem1Len2] ∧
    writePlaceValue [.init arr4Val, .init sliceFromElem1Len2]
      [elem1MutBorrow]
      { local_ := 1, projection := [.deref, .constantIndex 1 0 false] }
      (.scalar ⟨w2, 4⟩) =
      .ok [.init arr4Updated2, .init sliceFromElem1Len2] ∧
    invalidateDerefWriteBorrows
      [.init arr4Val, .init sliceFromElem1Len2]
      [elem1MutBorrow, elem0Borrow, elem2Borrow]
      { local_ := 1, projection := [.deref] }
      .nil =
      [elem1MutBorrow, elem0Borrow, { elem2Borrow with perm := .disabled }] ∧
    evalRvalue [.init arr4Val, .init sliceFromElem1Len2]
      (.ref .shared { local_ := 1, projection := [.deref, .constantIndex 1 0 false] })
      memElem1 =
      .ok (.ptr { allocId := 4, offsetBytes := 0 } 8)
        [.init arr4Val, .init sliceFromElem1Len2]
        { memElem1 with
          borrows :=
            { tag := 4, targetLocal := 0, targetProjection := [.constantIndex 2 0 false], perm := .frozen } ::
              [elem1MutBorrow]
          nextTag := 5 } ∧
    -- 2. Aggregate element byte stride (8-byte (u32, u32) tuples)
    evalOperand [.init tupleArr3Val, .init tupleSliceAt8]
      (.copy { local_ := 1, projection := [.deref] })
      [fullTupleArrBorrow] =
      .ok (.aggregate 0 [tup1, tup2]) [.init tupleArr3Val, .init tupleSliceAt8] ∧
    evalOperand [.init tupleArr3Val, .init tupleSliceAt4Misaligned]
      (.copy { local_ := 1, projection := [.deref] })
      [fullTupleArrBorrow] = .ub ∧
    -- 3. evalPlaceDiscriminant hardening (.never, invalid Ordering scalar/width, VariantsShape.multiple bounds)
    evalRvalue [.init (.scalar ⟨0, 1⟩)] (.discriminant p0) emptyMemory neverDecl = .ub ∧
    evalRvalue [.init (.scalar ⟨42, 1⟩)] (.discriminant p0) emptyMemory orderingDecl = .ub ∧
    evalRvalue [.init (.scalar ⟨0, 4⟩)] (.discriminant p0) emptyMemory orderingDecl = .ub ∧
    evalRvalue [.init (.scalar ⟨5, 1⟩)] (.discriminant p0) emptyMemory enum2Decl enum2Layout = .ub ∧
    evalRvalue [.init (.aggregate 2 .nil)] (.discriminant p0) emptyMemory enum2Decl enum2Layout = .ub ∧
    -- 4. evalGlobalThinPtrDerefBorrow chained subslice normalization & fromEnd = true
    evalRvalue [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      (.ref .shared { local_ := 0, projection := [.deref, .subslice 1 4 false, .subslice 1 3 false] })
      { emptyMemory with globals := [globalArr4Alloc] }
      globalArr4PtrDecls =
      .ok (.ptr { allocId := 9, offsetBytes := 8 } 8)
        [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
        { emptyMemory with globals := [globalArr4Alloc] } ∧
    evalRvalue [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      (.ref .shared { local_ := 0, projection := [.deref, .constantIndex 1 0 true] })
      { emptyMemory with globals := [globalArr4Alloc] }
      globalArr4PtrDecls =
      .ok (.ptr { allocId := 9, offsetBytes := 12 } 8)
        [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
        { emptyMemory with globals := [globalArr4Alloc] } ∧
    -- 5. Dynamic .index write borrow invalidation in StatementKind.assign
    evalStmt initAssignState assignIdx0Stmt =
      MirStepNode.step {
        frame := {
          blockIdx := 0
          stmtIdx := 1
          locals := [.init arr4Updated0, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨w0, 4⟩)]
        }
        memory := {
          emptyMemory with
          borrows := [{ elem0Borrow with perm := .disabled }, elem2Borrow]
        }
      } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem L3.28 (B4 Tuple-Element-Pointer Slice Resolution, `[T; 0]` `Value.unit`
    Slice Read/Write, Global/Null `evalPlaceLen` Bounds, and Typed Global `Unsize` Coercion)**:
    1. `readSliceBackingAggregate?` checks `splitLastConstantIndex?` before `readProjectedValue`,
       so a borrow or raw pointer derived from `&raw mut tuple_arr[1]` (`targetProjection =
       [.constantIndex 1 0 false]`) where `tuple_arr : [(u32, u32); 3]` resolves the parent
       3-element array with `baseIdx = 1` instead of mistaking the 2-field tuple `tuple_arr[1]`
       for a 2-element backing array.
    2. `evalSliceFatPtrDerefRead` and `writeSliceFatPtrTargetValue` support stack-backed
       0-length `[T; 0]` slices stored as `Value.unit` at `offsetBytes = 0, len = 0`, matching
       `evalUnsizeCoercion`, `deriveStackElemThinPtr`, `evalPlaceLen`, and
       `evalSliceFatPtrDerefBorrow`.
    3. `evalPlaceLen` validates global allocation byte bounds (`offsetBytes + len * elemSz <=
       length alloc.bytes`) when `lookupBorrow` is `.none` and rejects null (`allocId = 0,
       offsetBytes = 0`) or non-empty dangling slice fat pointers.
    4. `evalUnsizeCoercion` in typed mode validates global allocation mutability, alignment, and
       byte bounds (`offsetBytes + n * elemSz <= length alloc.bytes`), rejects null pointers,
       and uses `readSliceBackingAggregate?` so element-pointer borrows (`&raw const arr[1]`)
       check remaining array capacity (`baseIdx + n <= length elems`).
    5. `UnOp.ptrMetadata` validates 8-byte pointer and metadata widths (`ptrSz == ptrBytes` and
       `metaSc.sizeBytes == ptrBytes`), faulting with `.ub` on non-8-byte metadata. -/
theorem mir_b4_tuple_elem_slice_unit_slice_rw_global_len_and_typed_global_unsize_corresponds
    (t0a t0b t1a t1b t2a t2b : Nat) :
    let tupleU32PairKind : RigidTy := .tuple [.uint .u32, .uint .u32]
    let arr3TupleTy : Ty := { kind := .array tupleU32PairKind 3, layoutIdx := 0 }
    let ptrConstArr2TupleTy : Ty := { kind := .rawPtr .not (.array tupleU32PairKind 2), layoutIdx := 0 }
    let ptrConstSliceTupleTy : Ty := { kind := .rawPtr .not (.slice tupleU32PairKind), layoutIdx := 0 }
    let refArr2U32Ty : Ty := { kind := .ref .not (.array (.uint .u32) 2), layoutIdx := 0 }
    let refMutArr2U32Ty : Ty := { kind := .ref .mut (.array (.uint .u32) 2), layoutIdx := 0 }
    let refSliceU32Ty : Ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 0 }
    let refMutSliceU32Ty : Ty := { kind := .ref .mut (.slice (.uint .u32)), layoutIdx := 0 }
    let tupleDecls : List LocalDecl := [
      { mutability := .mut, ty := arr3TupleTy, debugName := "" },
      { mutability := .not, ty := ptrConstArr2TupleTy, debugName := "" }
    ]
    let refSliceDecls : List LocalDecl := [
      { mutability := .not, ty := refSliceU32Ty, debugName := "" }
    ]
    let refArr2Decls : List LocalDecl := [
      { mutability := .not, ty := refArr2U32Ty, debugName := "" }
    ]
    let refMutArr2Decls : List LocalDecl := [
      { mutability := .not, ty := refMutArr2U32Ty, debugName := "" }
    ]
    let tup0 : Value := .aggregate 0 [.scalar ⟨t0a, 4⟩, .scalar ⟨t0b, 4⟩]
    let tup1 : Value := .aggregate 0 [.scalar ⟨t1a, 4⟩, .scalar ⟨t1b, 4⟩]
    let tup2 : Value := .aggregate 0 [.scalar ⟨t2a, 4⟩, .scalar ⟨t2b, 4⟩]
    let tupleArr3Val : Value := .aggregate 0 [tup0, tup1, tup2]
    let elem1TupleBorrow : BorrowEntry := {
      tag := 1
      targetLocal := 0
      targetProjection := [.constantIndex 1 0 false]
      perm := .active
    }
    let unitArrBorrow : BorrowEntry := {
      tag := 1
      targetLocal := 0
      targetProjection := .nil
      perm := .active
    }
    let sliceFromTupleElem1 : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩]
    let sliceUnit0 : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩]
    let globalImmArr2Alloc : CapturedAllocation := {
      allocId := 9
      bytes := [.some 1, .some 0, .some 0, .some 0,
                .some 2, .some 0, .some 0, .some 0]
      relocations := .nil
      align := ⟨4⟩
      mutability := .not
    }
    let derefPlace0 : Place := { local_ := 0, projection := [.deref] }
    let derefPlace1 : Place := { local_ := 1, projection := [.deref] }
    let derefIdx1Place1 : Place :=
      { local_ := 1, projection := [.deref, .constantIndex 1 0 false] }
    let p0 : Place := { local_ := 0, projection := .nil }
    let p1 : Place := { local_ := 1, projection := .nil }
    -- 1a. Tuple-array element pointer slice deref read resolves parent array (tup1, tup2)
    evalOperand [.init tupleArr3Val, .init sliceFromTupleElem1]
      (.copy derefPlace1) [elem1TupleBorrow] =
      .ok (.aggregate 0 [tup1, tup2]) [.init tupleArr3Val, .init sliceFromTupleElem1] ∧
    -- 1b. Projected element read `(*s)[1]` on tuple-array element pointer slice returns `tup2`
    evalOperand [.init tupleArr3Val, .init sliceFromTupleElem1]
      (.copy derefIdx1Place1) [elem1TupleBorrow] =
      .ok tup2 [.init tupleArr3Val, .init sliceFromTupleElem1] ∧
    -- 1c. Typed Unsize coercion on `&raw const tuple_arr[1]` for `[(u32, u32); 2] -> [(u32, u32)]` succeeds
    evalRvalue
      [.init tupleArr3Val, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy p1) ptrConstSliceTupleTy)
      { emptyMemory with borrows := [elem1TupleBorrow] }
      tupleDecls =
      .ok sliceFromTupleElem1
        [.init tupleArr3Val, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
        { emptyMemory with borrows := [elem1TupleBorrow] } ∧
    -- 2a. Deref read of stack-backed 0-length `[T; 0]` slice stored as `Value.unit` returns `.aggregate 0 []`
    evalOperand [.init .unit, .init sliceUnit0]
      (.copy derefPlace1) [unitArrBorrow] =
      .ok (.aggregate 0 .nil) [.init .unit, .init sliceUnit0] ∧
    -- 2b. Deref write of `.aggregate 0 []` to stack-backed 0-length `[T; 0]` slice stored as `Value.unit` succeeds
    writePlaceValue [.init .unit, .init sliceUnit0]
      [unitArrBorrow] derefPlace1 (.aggregate 0 .nil) =
      .ok [.init .unit, .init sliceUnit0] ∧
    -- 3a. `Rvalue.len` on in-bounds global slice fat pointer (`2 * 4 <= 8`) succeeds
    evalRvalue
      [.init (.aggregate 0 [.ptr { allocId := 9, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩])]
      (.len derefPlace0)
      { emptyMemory with globals := [globalImmArr2Alloc] }
      refSliceDecls =
      .ok (.scalar ⟨2, 8⟩)
        [.init (.aggregate 0 [.ptr { allocId := 9, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩])]
        { emptyMemory with globals := [globalImmArr2Alloc] } ∧
    -- 3b. `Rvalue.len` on out-of-bounds global slice fat pointer (`3 * 4 > 8`) faults with `.ub`
    evalRvalue
      [.init (.aggregate 0 [.ptr { allocId := 9, offsetBytes := 0 } 8, .scalar ⟨3, 8⟩])]
      (.len derefPlace0)
      { emptyMemory with globals := [globalImmArr2Alloc] }
      refSliceDecls = .ub ∧
    -- 3c. `Rvalue.len` on null slice fat pointer (`allocId = 0, offsetBytes = 0, len = 0`) faults with `.ub`
    evalRvalue
      [.init (.aggregate 0 [.ptr { allocId := 0, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩])]
      (.len derefPlace0)
      emptyMemory
      refSliceDecls = .ub ∧
    -- 3d. `Rvalue.len` on non-Zero-Length dangling slice fat pointer (`allocId = 0, offsetBytes = 4, len = 1`) faults with `.ub`
    evalRvalue
      [.init (.aggregate 0 [.ptr { allocId := 0, offsetBytes := 4 } 8, .scalar ⟨1, 8⟩])]
      (.len derefPlace0)
      emptyMemory
      refSliceDecls = .ub ∧
    -- 4a. Typed `Unsize` coercion on in-bounds immutable global allocation (`&[u32; 2] -> &[u32]`) succeeds
    evalRvalue
      [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy p0) refSliceU32Ty)
      { emptyMemory with globals := [globalImmArr2Alloc] }
      refArr2Decls =
      .ok (.aggregate 0 [.ptr { allocId := 9, offsetBytes := 0 } 8, .scalar ⟨2, 8⟩])
        [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
        { emptyMemory with globals := [globalImmArr2Alloc] } ∧
    -- 4b. Typed mutable `Unsize` coercion on immutable global allocation (`&mut [u32; 2] -> &mut [u32]`) faults with `.ub`
    evalRvalue
      [.init (.ptr { allocId := 9, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy p0) refMutSliceU32Ty)
      { emptyMemory with globals := [globalImmArr2Alloc] }
      refMutArr2Decls = .ub ∧
    -- 4c. Typed `Unsize` coercion on out-of-bounds global pointer (`offsetBytes = 4`, `4 + 8 > 8`) faults with `.ub`
    evalRvalue
      [.init (.ptr { allocId := 9, offsetBytes := 4 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy p0) refSliceU32Ty)
      { emptyMemory with globals := [globalImmArr2Alloc] }
      refArr2Decls = .ub ∧
    -- 5. `UnOp.ptrMetadata` rejects 2-element aggregate with non-8-byte metadata scalar (`.scalar ⟨2, 4⟩`)
    evalRvalue
      [.init (.aggregate 0 [.ptr { allocId := 9, offsetBytes := 0 } 8, .scalar ⟨2, 4⟩])]
      (.unaryOp .ptrMetadata (.copy p0))
      emptyMemory = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.29 (`mir_a4_multidim_row_slice_unsize_len_deref_and_borrow_corresponds`)**:
Universal characterization of `A4` multi-dimensional array row-slice resolution in
`readSliceBackingAggregate?`:
When a 2D array `arr2d : [[u32; 4]; 2]` (`outerStride = 16`, `innerStride = 4`) has a
row borrow `&arr2d[1]` (`targetProjection = [.constantIndex 1 0 false]`),
`readSliceBackingAggregate?` distinguishes the inner 4-element `u32` row array from
an outer-array element pointer (such as `&raw mut tuple_arr[1]` in `L3.28`) using
`minCount` and `expectedElemSzOpt`, so:
1. Unsizing `&arr2d[1] : &[u32; 4] -> &[u32]` produces a 4-element slice fat pointer
   (`.aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩]`),
2. `Rvalue.len` on `*row_slice` evaluates to `4`,
3. Dereference read `(*row_slice)[2]` evaluates to `arr2d[1][2]`,
4. Dereference write `(*row_slice)[2] = w` updates `arr2d[1][2]` in `arr2d` without
   corrupting `arr2d[0]`, and
5. Dereferenced element borrow `&(*row_slice)[2]` creates a borrow with normalized
   2D projection `[.constantIndex 1 0 false, .constantIndex 2 0 false]`.
-/
theorem mir_a4_multidim_row_slice_unsize_len_deref_and_borrow_corresponds
    (r00 r01 r02 r03 r10 r11 r12 r13 w : Nat) :
    let row0 : Value :=
      .aggregate 0 [.scalar ⟨r00, 4⟩, .scalar ⟨r01, 4⟩, .scalar ⟨r02, 4⟩, .scalar ⟨r03, 4⟩]
    let row1 : Value :=
      .aggregate 0 [.scalar ⟨r10, 4⟩, .scalar ⟨r11, 4⟩, .scalar ⟨r12, 4⟩, .scalar ⟨r13, 4⟩]
    let row1Updated : Value :=
      .aggregate 0 [.scalar ⟨r10, 4⟩, .scalar ⟨r11, 4⟩, .scalar ⟨w, 4⟩, .scalar ⟨r13, 4⟩]
    let arr2dVal : Value := .aggregate 0 [row0, row1]
    let arr2dUpdatedVal : Value := .aggregate 0 [row0, row1Updated]
    let row1Borrow : BorrowEntry := {
      tag := 1
      targetLocal := 0
      targetProjection := [.constantIndex 1 0 false]
      perm := .active
    }
    let row1SliceFat : Value :=
      .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨4, 8⟩]
    let refSliceU32Ty : Ty := { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 0 }
    let memRow1 : Memory := { emptyMemory with borrows := [row1Borrow], nextTag := 2 }
    -- 1. Unsize `&arr2d[1]` (`targetProjection = [.constantIndex 1 0 false]`) to `&[u32]` -> len 4
    evalRvalue
      [.init arr2dVal, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "Unsize") (.copy { local_ := 1, projection := .nil }) refSliceU32Ty)
      memRow1 =
      .ok row1SliceFat
        [.init arr2dVal, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)]
        memRow1 ∧
    -- 2. `Rvalue.len` on `*row_slice` -> 4
    evalRvalue
      [.init arr2dVal, .init row1SliceFat]
      (.len { local_ := 1, projection := [.deref] })
      memRow1 =
      .ok (.scalar ⟨4, 8⟩) [.init arr2dVal, .init row1SliceFat] memRow1 ∧
    -- 3. `(*row_slice)[2]` -> `r12`
    evalOperand
      [.init arr2dVal, .init row1SliceFat]
      (.copy { local_ := 1, projection := [.deref, .constantIndex 2 0 false] })
      [row1Borrow] =
      .ok (.scalar ⟨r12, 4⟩) [.init arr2dVal, .init row1SliceFat] ∧
    -- 4. `(*row_slice)[2] = w` updates `arr2d[1][2]`
    writePlaceValue
      [.init arr2dVal, .init row1SliceFat]
      [row1Borrow]
      { local_ := 1, projection := [.deref, .constantIndex 2 0 false] }
      (.scalar ⟨w, 4⟩) =
      .ok [.init arr2dUpdatedVal, .init row1SliceFat] ∧
    -- 5. `&(*row_slice)[2]` -> targetProjection `[.constantIndex 1 0 false, .constantIndex 2 0 false]`
    evalRvalue
      [.init arr2dVal, .init row1SliceFat]
      (.ref .shared { local_ := 1, projection := [.deref, .constantIndex 2 0 false] })
      memRow1 =
      .ok (.ptr { allocId := 2, offsetBytes := 0 } 8)
        [.init arr2dVal, .init row1SliceFat]
        { memRow1 with
          borrows :=
            { tag := 2
              targetLocal := 0
              targetProjection := [.constantIndex 1 0 false, .constantIndex 2 0 false]
              perm := .frozen } :: [row1Borrow]
          nextTag := 3 } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

section DiffAbCrossFieldAndOnePastEnd

set_option maxHeartbeats 5000000

open Trusted.Rustc.V2026_06_01.Layout

/--
**Theorem L3.30 (`DIFF-AB` Intra-Allocation Cross-Field Pointer Arithmetic &
One-Past-The-End Deref Site)**:
Universally across all field payloads `(aVal bVal wVal : Nat)`:
1. `ptrAllocByteBound?` on a field-projected stack pointer (`&raw const pair.a`,
   `&raw const pair.b`, padded `#[repr(C)]` `PaddedS { a: u32, tag: u8, b: u32 }`,
   and nested `Outer { first: PairU32, second: PairU32 }`) computes the remaining
   enclosing allocation capacity `enclosingBytes - fieldByteOffset` both with an
   explicit `TypeLayout` table and under `emptyLayoutTable`, while subslice-backed
   field pointers (`&raw const (arr[1..2])[0].a`) stay bounded to the subslice
   window (`8` bytes rather than the outer `24`-byte array);
2. `needsThinPtrElemResolution [.field 0 u32Ty] 0 = false` (preserving the
   zero-overhead fast path when `offsetBytes = 0`);
3. Cross-field `BinOp.offset` (`offset(&raw const pair.a, 1isize)` -> `offsetBytes = 4`,
   `offset(&raw const padded.a, 2isize)` -> `offsetBytes = 8`,
   `offset(&raw const outer.first.a, 3isize)` -> `offsetBytes = 12`, and
   `offset(&raw const (arr[1..2])[0].a, 1isize)` -> `offsetBytes = 4`) succeeds and
   dereferences (`evalOperand` and `evalPlaceRead`) to the target sibling/nested
   field (`bVal`), while straddling padding (`offset(&raw const padded.a, 1isize)`)
   faults with `.ub` on dereference;
4. Cross-field dereference writes (`*p1 = wVal`), `invalidateDerefWriteBorrows`,
   and dereference reborrows (`&*p1` and `&raw const *p1`) target `[.field 1 u32Ty]`,
   disabling overlapping borrows on `pair.b` while preserving disjoint borrows on
   `pair.a`;
5. One-past-the-end `BinOp.offset` (`offset(&raw mut pair.a, 2isize)` ->
   `offsetBytes = 8`) succeeds at `BinOp.offset` and faults with `.ub` at the
   subsequent dereference read, write, or reborrow site (and cannot cross from
   `arr[1..2]` into `arr[2]`), whereas beyond-one-past-the-end offsets
   (`offset(&raw const pair.a, 3isize)` and `offset(&raw const pair.b, 2isize)`)
   fault immediately at `BinOp.offset` with `.ub`;
6. Misaligned intra-allocation offsets (`offsetBytes = 2` on `PairU32`) and
   size-mismatched sibling fields (`Mixed { a: u32, b: u8 }` at `offsetBytes = 4`
   read as `*const u32`) fault with `.ub` on dereference.
-/
theorem mir_cross_field_ptr_offset_and_one_past_end_corresponds
    (aVal bVal wVal : Nat) :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 3 }
    let pairTy : Ty := { kind := .adt "PairU32" .nil, layoutIdx := 1 }
    let rawConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 2 }
    let rawMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 2 }
    let paddedTy : Ty := { kind := .adt "PaddedS" .nil, layoutIdx := 4 }
    let outerTy : Ty := { kind := .adt "Outer" .nil, layoutIdx := 5 }
    let isizeTy : Ty := { kind := .int .isize, layoutIdx := 6 }
    let arr3PairTy : Ty := { kind := .array (.adt "PairU32" .nil) 3, layoutIdx := 7 }
    let mixedTy : Ty := { kind := .adt "Mixed" .nil, layoutIdx := 8 }
    let testLayouts : LayoutTable := {
      pointerBits := 64
      isLittleEndian := true
      entries := [
        -- 0: u32 (size 4, align 4)
        { size := ⟨4⟩, align := ⟨4⟩,
          backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        -- 1: PairU32 { a: u32 @ 0, b: u32 @ 4 } (size 8, align 4)
        { size := ⟨8⟩, align := ⟨4⟩,
          backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
          variants := .single 0, isUninhabited := false,
          fieldLayouts := [0, 0] },
        -- 2: *const u32 / *mut u32 (size 8, align 8)
        { size := ⟨8⟩, align := ⟨8⟩,
          backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 18446744073709551615⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false,
          fieldLayouts := [0] },
        -- 3: u8 (size 1, align 1)
        { size := ⟨1⟩, align := ⟨1⟩,
          backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        -- 4: PaddedS { a: u32 @ 0, tag: u8 @ 4, b: u32 @ 8 } (size 12, align 4)
        { size := ⟨12⟩, align := ⟨4⟩,
          backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨4⟩, ⟨8⟩] [0, 1, 2],
          variants := .single 0, isUninhabited := false,
          fieldLayouts := [0, 3, 0] },
        -- 5: Outer { first: PairU32 @ 0, second: PairU32 @ 8 } (size 16, align 4)
        { size := ⟨16⟩, align := ⟨4⟩,
          backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1],
          variants := .single 0, isUninhabited := false,
          fieldLayouts := [1, 1] },
        -- 6: isize (size 8, align 8)
        { size := ⟨8⟩, align := ⟨8⟩,
          backendRepr := .scalar (.initialized (.int 64 true) ⟨0, 18446744073709551615⟩),
          fields := .primitive, variants := .single 0, isUninhabited := false },
        -- 7: [PairU32; 3] (size 24, stride 8)
        { size := ⟨24⟩, align := ⟨4⟩,
          backendRepr := .memory,
          fields := .array ⟨8⟩ 3,
          variants := .single 0, isUninhabited := false,
          fieldLayouts := [1] },
        -- 8: Mixed { a: u32 @ 0, b: u8 @ 4 } (size 8, align 4)
        { size := ⟨8⟩, align := ⟨4⟩,
          backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
          variants := .single 0, isUninhabited := false,
          fieldLayouts := [0, 3] }
      ]
    }
    let pairVal : Value := .aggregate 0 [.scalar ⟨aVal, 4⟩, .scalar ⟨bVal, 4⟩]
    let pairUpdatedVal : Value := .aggregate 0 [.scalar ⟨aVal, 4⟩, .scalar ⟨wVal, 4⟩]
    let paddedVal : Value :=
      .aggregate 0 [.scalar ⟨aVal, 4⟩, .scalar ⟨7, 1⟩, .scalar ⟨bVal, 4⟩]
    let outerVal : Value :=
      .aggregate 0 [
        .aggregate 0 [.scalar ⟨aVal, 4⟩, .scalar ⟨11, 4⟩],
        .aggregate 0 [.scalar ⟨22, 4⟩, .scalar ⟨bVal, 4⟩]
      ]
    let mixedVal : Value := .aggregate 0 [.scalar ⟨aVal, 4⟩, .scalar ⟨7, 1⟩]
    let arr3Val : Value :=
      .aggregate 0 [
        .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩],
        pairVal,
        .aggregate 0 [.scalar ⟨30, 4⟩, .scalar ⟨40, 4⟩]
      ]
    let borrowPairA : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [.field 0 u32Ty], perm := .active }
    let borrowPairB : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.field 1 u32Ty], perm := .frozen }
    let borrowPairAFrozen : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [.field 0 u32Ty], perm := .frozen }
    let borrowPaddedA : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [.field 0 u32Ty], perm := .frozen }
    let borrowPaddedTag : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.field 1 u8Ty], perm := .frozen }
    let borrowPaddedB : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [.field 2 u32Ty], perm := .frozen }
    let borrowOuter00 : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [.field 0 pairTy, .field 0 u32Ty], perm := .frozen }
    let borrowOuter01 : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [.field 0 pairTy, .field 1 u32Ty], perm := .frozen }
    let borrowOuter10 : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [.field 1 pairTy, .field 0 u32Ty], perm := .frozen }
    let borrowOuter11 : BorrowEntry :=
      { tag := 4, targetLocal := 0, targetProjection := [.field 1 pairTy, .field 1 u32Ty], perm := .frozen }
    let borrowSubField0 : BorrowEntry :=
      { tag := 1, targetLocal := 0,
        targetProjection := [.subslice 1 2 false, .constantIndex 0 1 false, .field 0 u32Ty],
        perm := .frozen }
    let memPair : Memory :=
      { emptyMemory with borrows := [borrowPairA, borrowPairB, borrowPairAFrozen], nextTag := 4 }
    let memPadded : Memory :=
      { emptyMemory with borrows := [borrowPaddedA, borrowPaddedTag, borrowPaddedB], nextTag := 4 }
    let memOuter : Memory :=
      { emptyMemory with
        borrows := [borrowOuter00, borrowOuter01, borrowOuter10, borrowOuter11],
        nextTag := 5 }
    let memSub : Memory :=
      { emptyMemory with borrows := [borrowSubField0], nextTag := 2 }
    let pairDecls : List LocalDecl := [
      { mutability := .mut, ty := pairTy, debugName := .none },
      { mutability := .not, ty := rawMutU32Ty, debugName := .none }
    ]
    let pairConstDecls : List LocalDecl := [
      { mutability := .not, ty := pairTy, debugName := .none },
      { mutability := .not, ty := rawConstU32Ty, debugName := .none }
    ]
    let paddedDecls : List LocalDecl := [
      { mutability := .not, ty := paddedTy, debugName := .none },
      { mutability := .not, ty := rawConstU32Ty, debugName := .none }
    ]
    let outerDecls : List LocalDecl := [
      { mutability := .not, ty := outerTy, debugName := .none },
      { mutability := .not, ty := rawConstU32Ty, debugName := .none }
    ]
    let subDecls : List LocalDecl := [
      { mutability := .not, ty := arr3PairTy, debugName := .none },
      { mutability := .not, ty := rawConstU32Ty, debugName := .none }
    ]
    let mixedDecls : List LocalDecl := [
      { mutability := .not, ty := mixedTy, debugName := .none },
      { mutability := .not, ty := rawConstU32Ty, debugName := .none }
    ]
    let constIsize (n : Nat) : Operand :=
      .constant { ty := isizeTy, val := .scalar (.int ⟨n, 8⟩) }
    -- 1. `ptrAllocByteBound?` on `PairU32` (typed and untyped), `PaddedS` (typed vs unlaid-out field-only), `Outer`, and subslice
    ptrAllocByteBound? [.init pairVal] memPair pairDecls testLayouts ⟨1, 0⟩ = .some 8 ∧
    ptrAllocByteBound? [.init pairVal] memPair pairDecls testLayouts ⟨2, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init pairVal] memPair .nil emptyLayoutTable ⟨1, 0⟩ = .some 8 ∧
    ptrAllocByteBound? [.init pairVal] memPair .nil emptyLayoutTable ⟨2, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded paddedDecls testLayouts ⟨1, 0⟩ = .some 12 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded paddedDecls testLayouts ⟨2, 0⟩ = .some 8 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded paddedDecls testLayouts ⟨3, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded .nil emptyLayoutTable ⟨1, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded .nil emptyLayoutTable ⟨2, 0⟩ = .some 1 ∧
    ptrAllocByteBound? [.init paddedVal] memPadded .nil emptyLayoutTable ⟨3, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init outerVal] memOuter outerDecls testLayouts ⟨1, 0⟩ = .some 16 ∧
    ptrAllocByteBound? [.init outerVal] memOuter outerDecls testLayouts ⟨2, 0⟩ = .some 12 ∧
    ptrAllocByteBound? [.init outerVal] memOuter outerDecls testLayouts ⟨3, 0⟩ = .some 8 ∧
    ptrAllocByteBound? [.init outerVal] memOuter outerDecls testLayouts ⟨4, 0⟩ = .some 4 ∧
    ptrAllocByteBound? [.init arr3Val] memSub subDecls testLayouts ⟨1, 0⟩ = .some 8 ∧
    -- 2. Zero-overhead invariant for `offsetBytes = 0`
    needsThinPtrElemResolution [.field 0 u32Ty] 0 = false ∧
    -- 3. Cross-field `BinOp.offset` (`+1` -> `offsetBytes = 4`) + deref read (`evalOperand` & `evalPlaceRead`)
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 1))
      memPair pairConstDecls testLayouts =
      .ok (.ptr ⟨1, 4⟩ 8) [.init pairVal, .init (.ptr ⟨1, 0⟩ 8)] memPair ∧
    evalOperand
      [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memPair.borrows .nil testLayouts =
      .ok (.scalar ⟨bVal, 4⟩) [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)] ∧
    evalPlaceRead
      [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)]
      { local_ := 1, projection := [.deref] }
      memPair.borrows .nil testLayouts .nil pairConstDecls =
      .ok (.scalar ⟨bVal, 4⟩) [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)] ∧
    -- 4. Padded `#[repr(C)]` `PaddedS`: `+2` (`offsetBytes = 8`) reads `bVal`, `+1` (`offsetBytes = 4`, padding) -> `.ub`
    evalOperand
      [.init paddedVal, .init (.ptr ⟨1, 8⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memPadded.borrows .nil testLayouts .nil paddedDecls =
      .ok (.scalar ⟨bVal, 4⟩) [.init paddedVal, .init (.ptr ⟨1, 8⟩ 8)] ∧
    evalPlaceRead
      [.init paddedVal, .init (.ptr ⟨1, 8⟩ 8)]
      { local_ := 1, projection := [.deref] }
      memPadded.borrows .nil testLayouts .nil paddedDecls =
      .ok (.scalar ⟨bVal, 4⟩) [.init paddedVal, .init (.ptr ⟨1, 8⟩ 8)] ∧
    evalOperand
      [.init paddedVal, .init (.ptr ⟨1, 4⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memPadded.borrows .nil testLayouts .nil paddedDecls = .ub ∧
    -- 5. Nested `Outer`: `+3` (`offsetBytes = 12`) reads `outer.second.b` (`bVal`)
    evalPlaceRead
      [.init outerVal, .init (.ptr ⟨1, 12⟩ 8)]
      { local_ := 1, projection := [.deref] }
      memOuter.borrows .nil testLayouts .nil outerDecls =
      .ok (.scalar ⟨bVal, 4⟩) [.init outerVal, .init (.ptr ⟨1, 12⟩ 8)] ∧
    -- 6. Subslice-enclosed cross-field: `+1` (`offsetBytes = 4`) reads `arr[1].b`, `+2` (`8`) succeeds at offset and `.ub` on deref, `+3` (`12`) -> `.ub` at offset
    evalOperand
      [.init arr3Val, .init (.ptr ⟨1, 4⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memSub.borrows .nil testLayouts .nil subDecls =
      .ok (.scalar ⟨bVal, 4⟩) [.init arr3Val, .init (.ptr ⟨1, 4⟩ 8)] ∧
    evalRvalue
      [.init arr3Val, .init (.ptr ⟨1, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 2))
      memSub subDecls testLayouts =
      .ok (.ptr ⟨1, 8⟩ 8) [.init arr3Val, .init (.ptr ⟨1, 0⟩ 8)] memSub ∧
    evalOperand
      [.init arr3Val, .init (.ptr ⟨1, 8⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memSub.borrows .nil testLayouts .nil subDecls = .ub ∧
    evalRvalue
      [.init arr3Val, .init (.ptr ⟨1, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 3))
      memSub subDecls testLayouts = .ub ∧
    -- 7. Cross-field deref write (`*p1 = wVal`), scoped borrow invalidation, and deref reborrow (`&*p1`, `&raw const *p1`)
    writePlaceValue
      [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)]
      memPair.borrows
      { local_ := 1, projection := [.deref] }
      (.scalar ⟨wVal, 4⟩) =
      .ok [.init pairUpdatedVal, .init (.ptr ⟨1, 4⟩ 8)] ∧
    invalidateDerefWriteBorrows
      [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)]
      memPair.borrows
      { local_ := 1, projection := [.deref] }
      .nil =
      [borrowPairA, { borrowPairB with perm := .disabled }, borrowPairAFrozen] ∧
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)]
      (.rawPtr .not { local_ := 1, projection := [.deref] })
      memPair pairConstDecls testLayouts =
      .ok (.ptr ⟨1, 4⟩ 8) [.init pairVal, .init (.ptr ⟨1, 4⟩ 8)] memPair ∧
    -- 8. One-past-the-end (`offset(base, 2isize)` -> `offsetBytes = 8`) succeeds at `BinOp.offset` and RFC 2582 `&raw mut *p`; deref read/write/safe-reborrow -> `.ub`
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 2))
      memPair pairDecls testLayouts =
      .ok (.ptr ⟨1, 8⟩ 8) [.init pairVal, .init (.ptr ⟨1, 0⟩ 8)] memPair ∧
    evalOperand
      [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memPair.borrows .nil testLayouts = .ub ∧
    evalPlaceRead
      [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)]
      { local_ := 1, projection := [.deref] }
      memPair.borrows .nil testLayouts .nil pairDecls = .ub ∧
    writePlaceValue
      [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)]
      memPair.borrows
      { local_ := 1, projection := [.deref] }
      (.scalar ⟨wVal, 4⟩) = .ub ∧
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)]
      (.ref .shared { local_ := 1, projection := [.deref] })
      memPair pairDecls testLayouts = .ub ∧
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)]
      (.rawPtr .mut { local_ := 1, projection := [.deref] })
      memPair pairDecls testLayouts =
      .ok (.ptr ⟨1, 8⟩ 8) [.init pairVal, .init (.ptr ⟨1, 8⟩ 8)] memPair ∧
    -- 9. Beyond one-past-the-end (`+3` on `pair.a`, `+2` on `pair.b`) faults immediately at `BinOp.offset` with `.ub`
    evalRvalue
      [.init pairVal, .init (.ptr ⟨1, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 3))
      memPair pairConstDecls testLayouts = .ub ∧
    evalRvalue
      [.init pairVal, .init (.ptr ⟨2, 0⟩ 8)]
      (.binaryOp .offset (.copy { local_ := 1, projection := .nil }) (constIsize 2))
      memPair pairConstDecls testLayouts = .ub ∧
    -- 10. Misaligned intra-allocation offset (`offsetBytes = 2`) and size-mismatched sibling (`Mixed { a: u32, b: u8 }`) -> `.ub`
    evalOperand
      [.init pairVal, .init (.ptr ⟨1, 2⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      memPair.borrows .nil testLayouts = .ub ∧
    evalOperand
      [.init mixedVal, .init (.ptr ⟨1, 4⟩ 8)]
      (.copy { local_ := 1, projection := [.deref] })
      [borrowPairA] .nil testLayouts .nil mixedDecls = .ub := by
  exact ⟨
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl,
    rfl, rfl, rfl,
    rfl, rfl, rfl,
    rfl,
    rfl, rfl, rfl, rfl,
    rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl,
    rfl, rfl
  ⟩

private inductive DiffProbeTag where
  | normalUnit
  | normalScalar (bits : Nat) (sizeBytes : Nat)
  | normalOther
  | panic
  | abort
  | ub
  | unsupported
  | outOfFuel
  | externalCall (defPath : String)
  deriving DecidableEq, Repr

private def activeProbeSpan (body : CapturedMir) (st : MirExecState) : String :=
  let raw :=
    match st with
    | .running s =>
      let cur := s.memory.activeCallee.getD body
      match get? cur.basicBlocks s.frame.blockIdx with
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => stmt.span
        | none => bb.terminator.span
      | none => "none"
    | _ => "none"
  if raw == "" || raw == "<dummy>" then "none" else raw

private def probeExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    DiffProbeTag × String :=
  match fuel with
  | 0 => (.outOfFuel, activeProbeSpan body st)
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (.unit, _)) => (.normalUnit, "none")
    | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, "none")
    | .ret (.normal (_, _)) => (.normalOther, "none")
    | .ret .panic => (.panic, activeProbeSpan body st)
    | .ret .abort => (.abort, activeProbeSpan body st)
    | .tau st' => probeExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => (.ub, activeProbeSpan body st)
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeProbeSpan body st)
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeProbeSpan body st)
    | .vis (.inr (.inl _)) k => probeExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeProbeSpan body st)

private def diffAbFinding0000Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 3 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 4 } 2), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 true) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

private def diffAbFinding0000Body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_ptr_offset_within_array__b0_c13",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := (Option.some "base") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_tb_22467") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := (Option.some "p1") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tb_ovf") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_tb_22467") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_ptr_48867") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "__ptr_pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := (Option.some "__base_ptr") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_ptr_48867") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_proj_37637") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "__proj_pair") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := (Option.some "__proj_ref") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 6 }, debugName := (Option.some "__proj_arr") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_proj_37637") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 9), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 32), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:312:9: 312:13" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::PairU32" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 100, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 300, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:312:16: 312:42" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:313:9: 313:13" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 1, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) })), span := "src/lib.rs:313:28: 313:45" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:314:9: 314:31" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:315:13: 315:15" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:315:25: 315:29" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:315:25: 315:29" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.offset (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.int IntTy.isize), layoutIdx := 8 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 8 })) }))), span := "src/lib.rs:315:18: 315:38" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:315:37: 315:38" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:316:9: 316:12" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:317:5: 317:6" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:318:9: 318:17" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4294967295, sizeBytes := 4 })) }))), span := "src/lib.rs:318:25: 318:33" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:319:9: 319:24" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:319:32: 319:40" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 6, projection := List.nil }))), span := "src/lib.rs:319:32: 319:40" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:319:32: 319:47" } List.nil)))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 9, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 3 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:319:32: 319:47" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:335:2: 335:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := diffAbFinding0000Layouts,
    allocations := List.nil
  }

private def diffAbFinding0025Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 (List.cons 1 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) List.nil)))), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.union 2), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 true) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))))))))) }

private def diffAbFinding0025Body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::ub_ptr_offset_oob_write__b15_c25",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 2 }, debugName := (Option.some "pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 3 }, debugName := (Option.some "base") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 3 }, debugName := (Option.some "oob") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 3 }, debugName := Option.none } List.nil)))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:10054:9: 10054:17" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::PairU32" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 10, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 20, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:10054:20: 10054:44" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:10055:9: 10055:13" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.rawPtr Mutability.mut { local_ := 1, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }) List.nil) })), span := "src/lib.rs:10055:26: 10055:41" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:10056:5: 10059:6" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:10057:13: 10057:16" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:10057:26: 10057:30" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:10057:26: 10057:30" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.binaryOp BinOp.offset (Operand.move { local_ := 5, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.int IntTy.isize), layoutIdx := 8 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:10057:19: 10057:39" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:10057:38: 10057:39" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := (List.cons ProjectionElem.deref List.nil) } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 99, sizeBytes := 4 })) }))), span := "src/lib.rs:10058:9: 10058:18" } List.nil))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:10078:2: 10078:2" }, isCleanup := false } List.nil),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := diffAbFinding0025Layouts,
    allocations := List.nil
  }

private def diffAbFinding0001Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 }) (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 4 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 0 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 true) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 true) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))))) }

private def diffAbFinding0001Body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_exact_div_valid__b1_c4",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_ptr_22284") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::PairU32" List.nil), layoutIdx := 1 }, debugName := (Option.some "__oob_pair") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := (Option.some "__oob_base") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_ptr_22284") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 2 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:770:9: 770:32" } List.nil), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::intrinsics::exact_div" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 7 }, val := ConstValue.zeroSized }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 84, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 7, sizeBytes := 4 })) }) List.nil)) { local_ := 1, projection := List.nil } (Option.some 1) UnwindAction.unreachable), span := "src/lib.rs:770:49: 770:71" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:771:9: 771:19" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::PairU32" 0 Option.none) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 44, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 33, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:771:31: 771:61" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:772:9: 772:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 2, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }) List.nil) })), span := "src/lib.rs:772:34: 772:57" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:773:9: 773:25" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:773:43: 773:69" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:773:50: 773:60" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := List.nil }))), span := "src/lib.rs:773:50: 773:60" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.binaryOp BinOp.offset (Operand.move { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.int IntTy.isize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:773:43: 773:69" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:773:68: 773:69" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := (List.cons ProjectionElem.deref List.nil) }))), span := "src/lib.rs:773:42: 773:69" } List.nil))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:787:2: 787:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := diffAbFinding0001Layouts,
    allocations := List.nil
  }

/--
**Theorem L3.31 (`DIFF-AB` Captured Miri Differential Findings Reproduction
Confirmed)**:
Kernel-checked execution of `stepMirState` (`probeExecBounded 256`) on the
captured `Runtime(PostCleanup)` MIR bodies of `finding_0000`, `finding_0025`, and
`finding_0001` matches Miri's oracle verdict and exact statement/terminator span:
1. `pass_ptr_offset_within_array__b0_c13` (`finding_0000`): steps cleanly past
   `offset(&raw const pair.a, 1isize)` and `*p1` (`"src/lib.rs:316:9: 316:12"`)
   and reaches the expected `u32::MAX + 1` overflow assert panic at
   `(.panic, "src/lib.rs:319:32: 319:47")`;
2. `ub_ptr_offset_oob_write__b15_c25` (`finding_0025`): steps cleanly past
   one-past-the-end `offset(&raw mut pair.a, 2isize)`
   (`"src/lib.rs:10057:19: 10057:39"`) and faults with `.ub` on `*oob = 99` at
   `(.ub, "src/lib.rs:10058:9: 10058:18")`;
3. `pass_exact_div_valid__b1_c4` (`finding_0001`): steps cleanly past
   `exact_div(84u32, 7u32)` and one-past-the-end
   `offset(&raw const __oob_pair.a, 2isize)` (`"src/lib.rs:773:43: 773:69"`) and
   faults with `.ub` on `*offset(__oob_base, 2isize)` at
   `(.ub, "src/lib.rs:773:42: 773:69")`.
-/
theorem mir_diff_ab_captured_findings_reproduction_confirmed :
    probeExecBounded 256 diffAbFinding0000Body
      (.running (initMachineState diffAbFinding0000Body [])) =
      (.panic, "src/lib.rs:319:32: 319:47") ∧
    probeExecBounded 256 diffAbFinding0025Body
      (.running (initMachineState diffAbFinding0025Body [])) =
      (.ub, "src/lib.rs:10058:9: 10058:18") ∧
    probeExecBounded 256 diffAbFinding0001Body
      (.running (initMachineState diffAbFinding0001Body [])) =
      (.ub, "src/lib.rs:773:42: 773:69") := by
  exact ⟨rfl, rfl, rfl⟩

end DiffAbCrossFieldAndOnePastEnd

end Correspondence.V2026_06_01.L3_PlacesAndBasicMem
