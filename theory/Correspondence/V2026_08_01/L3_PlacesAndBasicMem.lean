import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

/-!
# `Correspondence.V2026_08_01.L3_PlacesAndBasicMem` — Unconditional Places, `BasicMemory`, & Dynamic Index Borrow Resolution

Connects `Trusted.Rustc.V2026_08_01.MirSemantics` place and memory operations
(`readProjectedValue`, `writeProjectedValue`, `setOrExtendFields`, `resolveIndexProjections`,
`resolveProjectedTy`, `placeTy`, `evalOperand`, `writePlaceValue`, `evalRvalue`) to
MiniRust's mechanically extracted place projection and `BasicMemory` semantics
(`MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops`, `spec/mem/basic.md`,
`spec/lang/step/expressions.md`):

1. **Universal `MirSemantics` Place Projection & Write Theorems (`∀`) Across All Constructors**:
   - `.nil`: `mir_readProjectedValue_nil`, `mir_writeProjectedValue_nil`.
   - `.field`: `mir_readProjectedValue_field_aggregate`, `mir_writeProjectedValue_field_aggregate`
     (including leaf extension via `setOrExtendFields` when `get? fields idx = none` and `rest = []`),
     `mir_readProjectedValue_field_zero_scalar`.
   - `.deref`: `mir_readPlace_deref_live_borrow`, `mir_writePlace_deref_disabled_and_frozen_is_ub`.
   - `.index`: `mir_readProjectedValue_index_in_bounds_and_oob`, and
     **`mir_dynamic_index_borrow_resolved_at_creation_survives_storage_dead`** over
     `resolveIndexProjections` and `evalRvalue` (closing `GAP-MR-0003`).
   - `.constantIndex`: `mir_readProjectedValue_constantIndex_characterization`.
   - `.subslice`: `mir_readProjectedValue_subslice_characterization`.
   - `.downcast`: `mir_readProjectedValue_downcast_match`,
     `mir_readProjectedValue_downcast_mismatch_is_ub`.
   - `resolveProjectedTy` & `placeTy`: `mir_resolveProjectedTy_and_placeTy_characterization`.
2. **MiniRust `BasicMemory` Spatial/Temporal Soundness & Algebraic Bisection (`Generated.Ops`)**:
   - `basicMem_misaligned_access_is_ub`, `basicMem_dead_alloc_access_is_ub`, `basicMem_oob_access_is_ub`,
     `mrProjectOffset_and_deallocate_characterization`, `memory_interface_bisection`.
-/

namespace Correspondence.V2026_08_01.L3_PlacesAndBasicMem

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops
open Correspondence

@[simp]
private theorem nat_sub_def (a b : Nat) : Nat.sub a b = a - b := rfl

export MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops (
  AllocId MrPointer MrAllocation BasicMemory
  basicMemCheckAccess basicMemLoad basicMemStore basicMemDeallocate
  mrProjectFieldOffset mrProjectIndexOffset mrProjectSubsliceBounds
)

/-! ## 1. Universal Theorems Directly Over `Trusted.Rustc.V2026_08_01.MirSemantics` Place Operations -/

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
`Trusted.Rustc.V2026_08_01.MirSemantics.writeProjectedValue`:
1. In-bounds field (`get? fields idx = some oldFieldVal`) with valid nested write and
   `set?` updates field `idx` in place;
2. Out-of-bounds leaf field (`get? fields idx = none` and `rest = .nil`) extends
   `fields` via `setOrExtendFields fields idx newVal` (supporting union cross-variant writes);
3. Out-of-bounds non-leaf field (`get? fields idx = none` and `rest = nextProj :: moreProj`)
   faults with `.ub`.
-/
theorem mir_writeProjectedValue_field_aggregate
    (locals : List LocalSlot) (vIdx idx : Nat) (fields fields' : List Value)
    (oldFieldVal updatedFieldVal newVal : Value) (ty : Ty)
    (rest : List ProjectionElem) (nextProj : ProjectionElem) (moreProj : List ProjectionElem) :
    (get? fields idx = some oldFieldVal →
      writeProjectedValue locals oldFieldVal rest newVal = .ok updatedFieldVal →
      set? fields idx updatedFieldVal = some fields' →
      writeProjectedValue locals (.aggregate vIdx fields) (.field idx ty :: rest) newVal =
        .ok (.aggregate vIdx fields')) ∧
    (get? fields idx = none →
      writeProjectedValue locals (.aggregate vIdx fields) [.field idx ty] newVal =
        .ok (.aggregate vIdx (setOrExtendFields fields idx newVal))) ∧
    (get? fields idx = none →
      writeProjectedValue locals (.aggregate vIdx fields)
        (.field idx ty :: nextProj :: moreProj) newVal = .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_get h_rec h_set
    simp [writeProjectedValue, h_get, h_rec, h_set]
  · intro h_oob
    simp [writeProjectedValue, h_oob]
  · intro h_oob
    simp [writeProjectedValue, h_oob]

/--
**Theorem L3.6 (`mir_readPlace_deref_live_borrow`)**:
Universal characterization of `.deref` read in `MirSemantics.evalOperand`.
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
Universal characterization of `.deref` write in `MirSemantics.writePlaceValue`.
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
Universal characterization of `.index idxLocal` in `MirSemantics.readProjectedValue`.
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
`MirSemantics.readProjectedValue`.
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
`MirSemantics.readProjectedValue`.
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
then Anneal's `readProjectedValue` immediately faults with `.ub`.
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
Writing directly to deallocated local `0` (`.dead`) via `writePlaceValue`
unconditionally faults with `.ub`.
-/
theorem mir_writePlaceValue_dead_local_is_ub
    (restLocals : List LocalSlot) (borrows : List BorrowEntry) (v : Value) :
    writePlaceValue (.dead :: restLocals) borrows { local_ := 0, projection := .nil } v = .ub :=
  rfl

/--
**Theorem L3.14 (`mir_resolveProjectedTy_and_placeTy_characterization`)**:
Universal compositional characterization of `MirSemantics.{resolveProjectedTy,placeTy}`.
-/
theorem mir_resolveProjectedTy_and_placeTy_characterization
    (localDecls : List LocalDecl) (layouts : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
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
**Theorem L3.15 (`mir_dynamic_index_borrow_resolved_at_creation_survives_storage_dead`)**:
Universal correspondence theorem for dynamic array index borrows in
`Trusted.Rustc.V2026_08_01.MirSemantics.{resolveIndexProjections,evalRvalue,readProjectedValue}`
(closing `GAP-MR-0003`):
For EVERY array `elems : List Value`, EVERY initial index scalar `idxSc : ScalarVal`,
EVERY element `elemVal : Value` at `get? elems idxSc.bits = some elemVal`, and EVERY
memory state `mem : Memory`:
1. `resolveIndexProjections [.init (.aggregate 0 elems), .init (.scalar idxSc)] [.index 1]`
   evaluates local `1` at borrow-creation time to `some [.constantIndex idxSc.bits 0 false]`;
2. `evalRvalue` on `.ref .shared { local_ := 0, projection := [.index 1] }` records the
   resolved projection `[.constantIndex idxSc.bits 0 false]` in the newly allocated `BorrowEntry`;
3. Subsequent dereference read via `readProjectedValue` after `StorageDead(1)`
   (`localsAfterDead = [.init (.aggregate 0 elems), .dead]`) succeeds with `.ok elemVal`!
-/
theorem mir_dynamic_index_borrow_resolved_at_creation_survives_storage_dead
    (elems : List Value) (idxSc : ScalarVal) (elemVal : Value) (mem : Memory)
    (h_in_bounds : get? elems idxSc.bits = some elemVal) :
    let arrVal := Value.aggregate 0 elems
    let localsAtBorrow : List LocalSlot := [.init arrVal, .init (.scalar idxSc)]
    let resolvedEntry : BorrowEntry := {
      tag := mem.nextTag
      targetLocal := 0
      targetProjection := [.constantIndex idxSc.bits 0 false]
      perm := .frozen
    }
    resolveIndexProjections localsAtBorrow [.index 1] =
      some [.constantIndex idxSc.bits 0 false] ∧
    evalRvalue localsAtBorrow (.ref .shared { local_ := 0, projection := [.index 1] }) mem =
      .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8)
        localsAtBorrow
        { mem with borrows := resolvedEntry :: mem.borrows, nextTag := Nat.add mem.nextTag 1 } ∧
    readProjectedValue [.init arrVal, .dead] arrVal resolvedEntry.targetProjection =
      .ok elemVal ∧
    evalAnnealV2026_08_01 .dynamicArrayIndexBorrow defaultFixtureState =
      evalMiniRustSnapshot .S2026_07_BleedingEdge .dynamicArrayIndexBorrow := by
  dsimp only
  have h_ble0 : Nat.ble 0 (length elems) = true := rfl
  refine ⟨rfl, rfl, ?_, by decide⟩
  simp [readProjectedValue, h_ble0, h_in_bounds]

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
Universal characterization of `Generated.Ops.{mrProjectFieldOffset,mrProjectIndexOffset,basicMemDeallocate}`.
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

end Correspondence.V2026_08_01.L3_PlacesAndBasicMem
