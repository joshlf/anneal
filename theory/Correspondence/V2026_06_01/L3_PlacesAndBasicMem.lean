import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
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
    (h_no_borrow : lookupBorrow mem.borrows ptrVal.tag = .none) :
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
      readProjectedValue, get?, h_no_borrow, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_no_borrow, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, unsizeArrayToSliceSpec?, operandTy, placeTy,
      resolveProjectedTy, layoutPointerBytes, evalOperand,
      readProjectedValue, get?, h_elem_eq]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, lookupBorrow, evalOperand, readProjectedValue, get?]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, operandTy, placeTy,
      resolveProjectedTy, evalOperand, readProjectedValue, get?, h_no_borrow]
  · simp [evalRvalue, evalReifyFnPointer, h_reify, h_unsize,
      evalUnsizeCoercion, operandTy, placeTy,
      resolveProjectedTy, evalOperand, readProjectedValue, get?]
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
    (h_no_borrow : lookupBorrow mem.borrows ptrVal.tag = .none) :
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
      layoutPointerBytes, evalPlaceRead, readProjectedValue, get?, h_no_borrow]
  · simp [evalRvalue, evalPlaceLen, placeTy, resolveProjectedTy,
       evalPlaceRead, readProjectedValue, get?, lookupBorrow]

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
    -- 5. Rvalue.discriminant returns 0 on Value.unit, Value.scalar, and Value.ptr
    evalRvalue [.init .unit] (.discriminant p0) mem localDecls layouts =
      .ok (.scalar ⟨0, 8⟩) [.init .unit] mem ∧
    evalRvalue [.init (.scalar sc)] (.discriminant p0) mem localDecls layouts =
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

end Correspondence.V2026_06_01.L3_PlacesAndBasicMem
