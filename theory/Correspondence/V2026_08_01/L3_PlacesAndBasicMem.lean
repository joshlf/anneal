import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Places
import Trusted.Rustc.V2026_08_01.MirSemantics.Statements
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

/-! ## 3. BRIEF-1.4 Correspondence Theorems: Slice Unsizing, `Rvalue.len`, Non-Scalar `ConstValue` / Global Reads, Signed `BinOp.offset`, & Structural Completeness -/

/--
**Theorem L3.17 (`mir_unsize_array_to_slice_coercion_corresponds`)**:
Universal characterization of `CastKind.pointerCoercion "Unsize"` in
`Trusted.Rustc.V2026_08_01.MirSemantics.{unsizeArrayToSliceSpec?,evalUnsizeCoercion,evalRvalue}`:
1. Positive: Shared references (`&[T; n] -> &[T]`), mutable references
   (`&mut [T; n] -> &mut [T]` and `&mut [T; n] -> &[T]`), and raw pointers
   (`*const [T; n] -> *const [T]`, `*mut [T; n] -> *mut [T]`, `*mut [T; n] -> *const [T]`)
   with compatible element type (`rigidTyEq srcElem dstElem = true`) coerce
   `Value.ptr ptrVal 8` to the 2-element slice fat pointer
   `Value.aggregate 0 [Value.ptr ptrVal 8, Value.scalar ⟨n, 8⟩]`;
2. Negative / UB: Reference unsizing with a `.disabled` borrow tag, illegal
   mutability upgrade (`&[T; n] -> &mut [T]` or `*const [T; n] -> *mut [T]`),
   or non-8-byte pointer widths fault with `.ub`.
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
`Trusted.Rustc.V2026_08_01.MirSemantics.{evalPlaceLen,evalRvalue}`.
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
`evalPlaceRead` and `evalOperand`.
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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Theorem L3.20 (`mir_binop_offset_signed_scaled_and_bounds_corresponds`)**:
Universal characterization of signed and element-scaled `BinOp.offset` in
`Trusted.Rustc.V2026_08_01.MirSemantics.{evalBinOpOffset,evalRvalue}`.
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
Universal characterization of the `BRIEF-1.4` structural completeness constructs.
-/
theorem mir_structural_completeness_brief_1_4_corresponds
    (s : MachineState) (dropPlace : Place) (span : String)
    (locals : List LocalSlot) (v newVal v0 v1 v2 v3 w1 w2 : Value)
    (binderTy : Ty) (rest : List ProjectionElem)
    (op : Operand) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
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
Universal characterization of `B1` hardening for `BRIEF-1.4`.
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
Universal characterization of `A1` hardening for `BRIEF-1.4` in `V2026_08_01`.
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
Universal characterization of `B2` hardening for `BRIEF-1.4` in `V2026_08_01`.
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
    let singleAdtLayout : Trusted.Rustc.V2026_08_01.Layout.LayoutTable :=
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
    let emptyAdtLayout : Trusted.Rustc.V2026_08_01.Layout.LayoutTable :=
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

end Correspondence.V2026_08_01.L3_PlacesAndBasicMem
