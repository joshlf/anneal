/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.AllocLM2_1

/-!
# Lockstep Simulation for Homogeneous Arrays `[T; N]`, `Repeat`, `Len`, and `Index`/`ConstantIndex` Projections (`LM-2.1`)

Proves the forward lockstep simulation theorems for `LM-2.1`:

1. `WellTypedArrayTy`: well-typed homogeneous scalar array layout predicate.
2. `evalProjection_index_simulation`: `ProjectionElem.index idxLocal` bounds-checked
   offset calculation (`idx < count`) through vendor `Miri.Interpreter.projectionMemoryOffset`,
   element read correspondence, and out-of-bounds (`idx ≥ count`) / uninitialized / dead
   `idxLocal` UB equivalence across both immediate and memory-backed (`indirect`) `usize`
   index locals.
3. `evalProjection_constantIndex_simulation`: `ProjectionElem.constantIndex offset minLength fromEnd`
   for both `fromEnd = false` (`idx = offset`) and `fromEnd = true` (`idx = count - offset`),
   covering both in-bounds offset calculation (`minLength ≤ count`) and out-of-bounds
   (`count < minLength`) UB equivalence.
4. `evalRvalue_len_array_simulation`, `projectSubslice_array_unsupported`, &
   `annealReadImmediate_whole_array_unsupported`:
   `Rvalue.len place` on `[T; N]` via unforgeable `.UnwrapUnsafeBinder arraySliceMetaTyId`
   + `UnaryOp.PtrMetadata`, including dead/uninitialized array UB equivalence, while all
   array `Subslice` projections (both partial and whole-array) and ordinary whole-array
   immediate reads fail closed with `StepError.unsupported`.
5. `evalRvalue_repeat_simulation`: `Rvalue.repeat op count` vs `Miri.Interpreter.writeRepeat`
   (using vendor `aggregateWrappingOffset`), parametric over `count` (`0` and `> 0`) and `op`
   (including `const`, `copy`, and destructive `move` scalar operands), covering both fresh
   stack allocation and in-place overwrite of already-allocated array locals, plus
   dead/uninitialized UB equivalence.
6. `evalRvalue_aggregate_array_simulation`: `Rvalue.aggregate (.array elemTy) ops` vs
   `Miri.Interpreter.writeAggregate`, proved by parametric induction over `ops` (supporting
   `const`, `copy`, and destructive `move` scalar operands), covering both fresh stack
   allocation and in-place overwrite of already-allocated array locals, plus
   dead/uninitialized UB equivalence.
7. `step_assign_array_element_simulation`: indexed array element read (`dst = arr[i]`) and
   indexed array element write (`arr[i] = op`, including `move` scalar operands) for both
   `.index` and `.constantIndex`, preserving all `j ≠ idx` elements and
   `MemoryAllocDisjoint`, plus OOB/uninit/dead UB.
8. `step_stmt_lm2_1_array_simulation` & `step_stmt_lm2_1_simulation`: statement-level
   lockstep simulation uniting `LM-2.1` array statements, `LM-1.1` scalar statements, and
   `LM-1.4` storage/move statements, re-establishing `StepPreservesNodup`,
   `StepPreservesImmediate`, and `StepPreservesHighWater` (`MemoryHighWater.canReserveAllocId`)
   across multi-allocation mixed sequences.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `WellTypedArrayTy`, `LiveAllocsNodup` & Array Layout Helpers -/

/-- Well-typed homogeneous scalar array type `arrTy` (`[elemKind; count]`) under
layout table `layouts`. -/
structure WellTypedArrayTy
    (layouts : LayoutTable)
    (arrTy : Ty)
    (elemKind : RigidTy)
    (count : Nat) : Prop where
  arr_kind : arrTy.kind = .array elemKind count
  elem_prim :
    elemKind = .bool ∨ elemKind = .char ∨
      (∃ it, elemKind = .int it) ∨ (∃ ut, elemKind = .uint ut)
  arr_fields :
    (translateTy arrTy layouts).layout.fields =
      .Array (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
        (UInt64.ofNat count)
  arr_size :
    (translateTy arrTy layouts).layout.size =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (count *
            (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat))
  arr_align :
    (translateTy arrTy layouts).layout.align =
      (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.align
  arr_isSized : (translateTy arrTy layouts).layout.isSized = true
  elem_isSized : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.isSized = true
  elem_layout_eq :
    arrayElemLayoutOf layouts (translateTy arrTy layouts)
      (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateTy { kind := elemKind, layoutIdx := 0 } layouts
  elem_size_pos :
    0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
  elem_size_le_16 :
    (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat ≤ 16
  total_bytes_bound :
    count *
      (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat <
      2 ^ 32

namespace WellTypedArrayTy

/-- Count bound `count < 2 ^ 32` follows from `0 < elemSize` and `count * elemSize < 2 ^ 32`. -/
theorem count_lt_two_pow_32
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (h : WellTypedArrayTy layouts arrTy elemKind count) :
    count < 2 ^ 32 := by
  have hpos := h.elem_size_pos
  have htot := h.total_bytes_bound
  have hle : count * 1 ≤
      count * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat :=
    Nat.mul_le_mul_left count hpos
  omega

/-- `(UInt64.ofNat count).toNat = count`. -/
theorem uint64_ofNat_count_toNat
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (h : WellTypedArrayTy layouts arrTy elemKind count) :
    (UInt64.ofNat count).toNat = count := by
  have hlt := h.count_lt_two_pow_32
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using by omega)]

/-- The byte size of `translateTy arrTy layouts` as a `Nat` is `count * elemSize`. -/
theorem arr_size_toNat
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (h : WellTypedArrayTy layouts arrTy elemKind count) :
    (translateTy arrTy layouts).layout.size.bytes.toNat =
      count * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat := by
  have htot := h.total_bytes_bound
  rw [h.arr_size]
  simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using by omega)

/-- The element layout has `.Primitive` fields shape. -/
theorem elem_fields_primitive
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (h : WellTypedArrayTy layouts arrTy elemKind count) :
    (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.fields = .Primitive := by
  rcases h.elem_prim with rfl | rfl | ⟨it, rfl⟩ | ⟨ut, rfl⟩ <;> rfl

/-- Encoded array `TyId`s (`≥ 100`) never collide with `arraySliceMetaTyId` (`60`). -/
theorem ty_ne_arraySliceMetaTyId
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (h : WellTypedArrayTy layouts arrTy elemKind count) :
    ((translateTy arrTy layouts).ty == arraySliceMetaTyId) = false := by
  apply beq_false_of_ne
  change encodeTyId arrTy ≠ 60
  unfold encodeTyId Miri.MIR.TyId at *
  rw [h.arr_kind]
  dsimp only
  cases encodeScalarRigidTy elemKind <;> dsimp only <;> omega

end WellTypedArrayTy

/-- Ring cancellation `(a + b) - a = b` on `UInt64`. -/
theorem uint64_add_sub_cancel_left (a b : UInt64) : a + b - a = b := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add]
  rw [BitVec.add_comm a.toBitVec b.toBitVec, BitVec.add_sub_cancel]

/-- Ring cancellation `(a + b + c) - a = b + c` on `UInt64`. -/
theorem uint64_add_add_sub_cancel_left (a b c : UInt64) : a + b + c - a = b + c := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add]
  rw [BitVec.add_assoc, BitVec.add_comm a.toBitVec, BitVec.add_sub_cancel]

/-- Live allocation IDs in `mach.memory.live` are pairwise distinct. -/
def LiveAllocsNodup (mach : AnnealMachine) : Prop :=
  (mach.memory.live.toList.map Prod.fst).Nodup

/-- A `lean-miri` step result whose normal completion (`.ok true`) leaves the
post-state's live allocation IDs pairwise distinct.

`StateRel` says nothing about duplicate allocation IDs, yet the `LM-2.1` hooks
locate an array local's allocation with `find?` and `findIdx?`, which return the
allocation that `MemPlaceRel` describes only when IDs are unique
(`LiveAllocsNodup`). Each `LM-2.1` array theorem therefore assumes
`LiveAllocsNodup` before the step and re-establishes it after a normal step,
so that the theorems chain across consecutive statements. -/
def StepPreservesNodup (r : Miri.Interpreter.StepResult AnnealStepState Bool) : Prop :=
  r.2 = .ok true → LiveAllocsNodup r.1.machine

/-- A failing `lean-miri` step trivially satisfies `StepPreservesNodup`. -/
theorem StepPreservesNodup.of_error {st : AnnealStepState} {e : Miri.Interpreter.StepError} :
    StepPreservesNodup (st, .error e) := by
  intro h
  cases h

/-- A step whose post-state already satisfies `LiveAllocsNodup` satisfies
`StepPreservesNodup`. -/
theorem StepPreservesNodup.of_nodup {st : AnnealStepState}
    {r : Except Miri.Interpreter.StepError Bool}
    (h : LiveAllocsNodup st.machine) : StepPreservesNodup (st, r) :=
  fun _ => h

/-- A `lean-miri` step result from `m` whose normal completion (`.ok true`)
keeps every local `j` with `keep j` that is immediate in `m`'s single frame
immediate in the post-state's single frame.

Like `LiveAllocsNodup`, immediacy of scalar locals is not part of `StateRel`,
yet the `LM-2.1` theorems require scalar destinations and index locals to be
immediate (`IsImmediateFrameLocal`). Re-establishing it lets the theorems chain
across consecutive statements. -/
def StepPreservesImmediate (m : AnnealStepState) (keep : Nat → Prop)
    (r : Miri.Interpreter.StepResult AnnealStepState Bool) : Prop :=
  r.2 = .ok true →
    ∀ tf tf', m.stack.frames = #[tf] → r.1.stack.frames = #[tf'] →
      ∀ j, keep j → IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j

/-- A failing `lean-miri` step trivially satisfies `StepPreservesImmediate`. -/
theorem StepPreservesImmediate.of_error {m st : AnnealStepState} {keep : Nat → Prop}
    {e : Miri.Interpreter.StepError} :
    StepPreservesImmediate m keep (st, .error e) := by
  intro h
  cases h

/-- `StepPreservesImmediate` for more locals implies it for fewer. -/
theorem StepPreservesImmediate.mono {m : AnnealStepState} {keep keep' : Nat → Prop}
    {r : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hkeep : ∀ j, keep' j → keep j) (h : StepPreservesImmediate m keep r) :
    StepPreservesImmediate m keep' r :=
  fun hok tf tf' htf htf' j hj => h hok tf tf' htf htf' j (hkeep j hj)

/-- The destination local of an array-constructing assignment
(`Rvalue.aggregate (.array _)` or `Rvalue.repeat`), which `lean-miri` moves from
an immediate local into a fresh allocation. -/
def arrayConstructDest? (stmt : Statement) : Option Local :=
  match stmt.kind with
  | .assign ⟨dst, .nil⟩ (.aggregate (.array _) _) => some dst
  | .assign ⟨dst, .nil⟩ (.repeat _ _) => some dst
  | _ => none

/-- High-water invariant on `AnnealMemory`'s `AllocId` supply:
every issued, live, global, and dead allocation ID lies strictly below
`mem.nextAllocId`, which is nonzero (`0 < mem.nextAllocId.toNat`) and unexhausted,
with `sourceAllocIdWorldActive = false`.

`MemoryHighWater` implies `CanReserveAllocId mem` (`MemoryHighWater.canReserveAllocId`)
via vendor `Miri.Memory.MemoryState.reserve_of_highWater` and is preserved across every
statement covered by `step_stmt_lm2_1_simulation` (`StepPreservesHighWater`), advancing
`nextAllocId` by at most `1` on array-constructing statements and `0` on all others so
abstract multi-allocation chains re-establish `CanReserveAllocId` without concrete
memory unfolding. -/
structure MemoryHighWater (mem : AnnealMemory) : Prop where
  available : mem.idSupplyExhausted = false
  nonzero : 0 < mem.nextAllocId.toNat
  sourceInactive : mem.sourceAllocIdWorldActive = false
  issued_lt : ∀ id ∈ mem.issuedIds, id.value.toNat < mem.nextAllocId.toNat
  live_lt : ∀ row ∈ mem.live, row.1.value.toNat < mem.nextAllocId.toNat
  global_lt : ∀ row ∈ mem.globals, row.allocId.value.toNat < mem.nextAllocId.toNat
  dead_lt : ∀ row ∈ mem.dead, row.allocId.value.toNat < mem.nextAllocId.toNat

/-- `AnnealMachine.empty.memory` (`nextAllocId = 1`, empty tables) satisfies `MemoryHighWater`. -/
theorem MemoryHighWater.empty : MemoryHighWater AnnealMachine.empty.memory where
  available := rfl
  nonzero := by decide
  sourceInactive := rfl
  issued_lt := fun _ h => nomatch h
  live_lt := fun _ h => nomatch h
  global_lt := fun _ h => nomatch h
  dead_lt := fun _ h => nomatch h

/-- A `lean-miri` step result from `m` whose normal completion (`.ok true`)
preserves `MemoryHighWater` and advances `nextAllocId` by at most `allocBudget`
whenever `m.machine.memory.nextAllocId.toNat + allocBudget < 2 ^ 64`. -/
def StepPreservesHighWater (m : AnnealStepState) (allocBudget : Nat)
    (r : Miri.Interpreter.StepResult AnnealStepState Bool) : Prop :=
  r.2 = .ok true →
    MemoryHighWater m.machine.memory →
    m.machine.memory.nextAllocId.toNat + allocBudget < 2 ^ 64 →
    MemoryHighWater r.1.machine.memory ∧
    r.1.machine.memory.nextAllocId.toNat ≤ m.machine.memory.nextAllocId.toNat + allocBudget

/-- A failing `lean-miri` step trivially satisfies `StepPreservesHighWater`. -/
theorem StepPreservesHighWater.of_error {m st : AnnealStepState} {allocBudget : Nat}
    {e : Miri.Interpreter.StepError} :
    StepPreservesHighWater m allocBudget (st, .error e) := by
  intro h
  cases h

/-- A step that leaves `machine.memory` unchanged satisfies `StepPreservesHighWater` for any budget. -/
theorem StepPreservesHighWater.of_same_memory {m st : AnnealStepState} {allocBudget : Nat}
    {res : Except Miri.Interpreter.StepError Bool}
    (heq : st.machine.memory = m.machine.memory) :
    StepPreservesHighWater m allocBudget (st, res) := by
  intro _ hw _
  rw [heq]
  exact ⟨hw, Nat.le_add_right _ _⟩

/-- `StepPreservesHighWater` is monotonic in `allocBudget`. -/
theorem StepPreservesHighWater.mono_budget {m : AnnealStepState} {b₁ b₂ : Nat}
    {r : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hle : b₁ ≤ b₂) (h : StepPreservesHighWater m b₁ r) :
    StepPreservesHighWater m b₂ r := by
  intro hok hw hbound
  obtain ⟨hw', hnext⟩ := h hok hw (by omega)
  exact ⟨hw', by omega⟩

/-- Deallocating a local's stack allocation (`deallocLocalMemory`) preserves `MemoryHighWater`
without advancing `nextAllocId`. -/
theorem MemoryHighWater.deallocLocalMemory {mem : AnnealMemory}
    (hw : MemoryHighWater mem)
    (v : Miri.Interpreter.LocalValue AnnealProv) :
    MemoryHighWater (_root_.LeanMiriSpec.Correspondence.deallocLocalMemory mem v) ∧
    (_root_.LeanMiriSpec.Correspondence.deallocLocalMemory mem v).nextAllocId = mem.nextAllocId := by
  unfold _root_.LeanMiriSpec.Correspondence.deallocLocalMemory
  cases v with
  | dead => exact ⟨hw, rfl⟩
  | live op =>
    cases op with
    | immediate _ => exact ⟨hw, rfl⟩
    | indirect mp =>
      dsimp only
      cases mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => exact ⟨hw, rfl⟩
      | some id =>
        dsimp only
        refine ⟨⟨hw.available, hw.nonzero, hw.sourceInactive, hw.issued_lt, ?_, hw.global_lt, hw.dead_lt⟩, rfl⟩
        intro row hmem
        exact hw.live_lt row (Array.mem_of_mem_filter hmem)

/-- Reserving a fresh `AllocId` and pushing onto `live` in `stackAllocMachine`
preserves `LiveAllocsNodup`. -/
theorem LiveAllocsNodup.stackAllocMachine
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hnodup : LiveAllocsNodup mach)
    (hres : mach.memory.reserveAllocId = (mem', .ok id)) :
    LiveAllocsNodup (Correspondence.stackAllocMachine mach mem' id alloc) := by
  obtain ⟨hlive_eq, hfresh⟩ := reserveAllocId_ok_live hres
  unfold LiveAllocsNodup Correspondence.stackAllocMachine
  simp only [Array.toList_push, List.map_append, List.map_singleton, hlive_eq]
  rw [List.nodup_append]
  refine ⟨hnodup, by simp, ?_⟩
  intro x hx y hy heq
  subst heq
  simp only [List.mem_singleton] at hy
  subst hy
  rcases List.mem_map.mp hx with ⟨⟨a, la⟩, hmem, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have := (Array.any_eq_false.mp hfresh) i (by simpa using hi)
  simp only [Array.getElem_toList] at hget
  rw [hget] at this
  simp at this

theorem list_find?_of_nodup_fst {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} (hnodup : (l.map Prod.fst).Nodup)
    {k : α} {v : β} (hmem : (k, v) ∈ l) :
    l.find? (fun (a, _) => a == k) = some (k, v) := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with heq | htl
    · cases heq
      simp [List.find?]
    · have hne : a ≠ k := by
        intro h
        subst h
        exact hnodup.1 (List.mem_map.mpr ⟨(a, v), htl, rfl⟩)
      have hbeq : (a == k) = false := beq_false_of_ne hne
      simp only [List.find?, hbeq]
      exact ih hnodup.2 htl

theorem array_find?_of_nodup_fst
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hlive : (allocId, localAlloc) ∈ mach.memory.live.toList) :
    mach.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc) := by
  rw [← Array.find?_toList]
  exact list_find?_of_nodup_fst hnodup hlive

theorem list_findIdx?_of_nodup_fst {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} (hnodup : (l.map Prod.fst).Nodup)
    {k : α} {v : β} (hmem : (k, v) ∈ l) :
    ∃ idx : Nat,
      idx < l.length ∧
      l.findIdx? (fun (a, _) => a == k) = some idx ∧
      l[idx]? = some (k, v) ∧
      ∀ v' : β,
        ((l.set idx (k, v')).map Prod.fst).Nodup ∧
        (k, v') ∈ l.set idx (k, v') ∧
        ∀ k' v'', k' ≠ k → (k', v'') ∈ l → (k', v'') ∈ l.set idx (k, v') := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with heq | htl
    · injection heq with ha hb
      subst ha hb
      refine ⟨0, by simp, by simp [List.findIdx?_cons], rfl, fun v' => ⟨?_, by simp, ?_⟩⟩
      · simp [List.nodup_cons, hnodup.1, hnodup.2]
      · intro k' v'' hne hmem'
        rcases List.mem_cons.mp hmem' with heq' | htl'
        · injection heq' with hk' _; exact False.elim (hne hk')
        · exact List.mem_cons_of_mem _ htl'
    · have hne : a ≠ k := by
        intro h
        subst h
        exact hnodup.1 (List.mem_map.mpr ⟨(a, v), htl, rfl⟩)
      have hbeq : (a == k) = false := beq_false_of_ne hne
      obtain ⟨idx, hlt, hfind, hget, hset⟩ := ih hnodup.2 htl
      refine ⟨idx + 1, Nat.succ_lt_succ hlt, ?_, hget, fun v' => ?_⟩
      · simp [List.findIdx?_cons, hbeq, hfind]
      · obtain ⟨hnodup', hmem_set, hother⟩ := hset v'
        refine ⟨?_, List.mem_cons_of_mem _ hmem_set, ?_⟩
        · simp only [List.set_cons_succ, List.map_cons, List.nodup_cons]
          refine ⟨?_, hnodup'⟩
          intro hmem_a
          rcases List.mem_map.mp hmem_a with ⟨⟨x, y⟩, hxy, hxa⟩
          dsimp only at hxa
          subst hxa
          have hmem_orig : x ∈ tl.map Prod.fst := by
            rcases List.mem_or_eq_of_mem_set hxy with h_in | h_eq
            · exact List.mem_map.mpr ⟨(x, y), h_in, rfl⟩
            · injection h_eq with hx _; exact False.elim (hne hx)
          exact hnodup.1 hmem_orig
        · intro k' v'' hne' hmem'
          rcases List.mem_cons.mp hmem' with heq' | htl'
          · rw [heq']; simp
          · exact List.mem_cons_of_mem _ (hother k' v'' hne' htl')

/-- An initialized local holding `Value.aggregate 0 elems` at array type `arrTy`
cannot be `.immediate` in `LocalRel`, so it is always represented by
`LocalRel.indirect` with `MemPlaceRel`. -/
theorem LocalRel.array_init_is_indirect
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hk : decl.ty.kind = .array elemKind count)
    (hrel : LocalRel mach decl layouts (.init (.aggregate 0 elems)) mls) :
    ∃ mp cachedLayout,
      mls = ⟨.live (.indirect mp), cachedLayout⟩ ∧
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) ∧
      MemPlaceRel mach decl.ty layouts (some (.aggregate 0 elems)) mp := by
  cases hrel with
  | immediate _ imm cachedLayout hc himm =>
    rcases himm with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
    · cases h1
    · injection hv' with hv_eq
      subst hv_eq
      cases himm' with
      | scalarPair _ _ _ _ _ _ hagg _ =>
        rcases hagg with ⟨ts, ht⟩ | ⟨p, a, ht⟩ <;> (rw [hk] at ht; cases ht)
  | indirect _ mp cachedLayout hc _ hmp =>
    exact ⟨mp, cachedLayout, rfl, hc, hmp⟩

/-- Helper: `annealCheckIndirectInitialized` succeeds on any initialized `MemPlaceRel`
of an array type `arrTy` (`WellTypedArrayTy`). -/
theorem annealCheckIndirectInitialized_of_array_memPlaceRel
    {mach : AnnealMachine} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {layouts : LayoutTable} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp) :
    annealCheckIndirectInitialized mach mp (translateTy arrTy layouts).layout.size = .ok () := by
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase _ hptr _ _ hin _ _ _ harr =>
    obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by
        rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]
      cases relOffset; rfl
    have hinit := initMask_new_true_isRangeInitialized_inbounds hin
    unfold annealCheckIndirectInitialized
    rw [hprov]
    simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
      hslice.alloc_mask, hinit, pure, Except.pure]

/-- Helper: reading a projected array element `idx < count` via `annealReadImmediate`
succeeds and returns the `ImmediateRel`-matching scalar. -/
theorem annealReadImmediate_of_projected_array_elem
    {m : AnnealStepState} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {layouts : LayoutTable} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup m.machine)
    (hmp : MemPlaceRel m.machine arrTy layouts (some (.aggregate 0 elems)) mp)
    {idx : Nat} {elemVal : Value}
    (hget : get? elems idx = some elemVal) :
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy layouts).layout
    let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (idx * elemLay.size.bytes.toNat))
    let elemMp : Miri.Interpreter.MemPlace AnnealProv :=
      { mp with
        ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) }
        metadata := .none }
    ∃ sc msc,
      elemVal = .scalar sc ∧
      ImmediateRel elemTy layouts elemVal (.scalar (.fromScalarInt msc)) ∧
      annealReadImmediate ⟨.indirect elemMp, translateTy elemTy layouts⟩ m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy layouts⟩ m := by
  intro elemTy elemLay elemOff elemMp
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase _ hptr _ _ _ _ _ _ harr =>
    obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
    have hfind := array_find?_of_nodup_fst hnodup hlive
    obtain ⟨sc, msc, rfl, himm, hread⟩ := hslice.readScalar_get hget
    refine ⟨sc, msc, rfl, himm, ?_⟩
    have hrel_off :
        Miri.ABI.Size.ofBytes (elemMp.ptr.offset.bytes - baseAddr) =
          Miri.ABI.Size.ofBytes
            (relOffset.bytes + UInt64.ofNat (idx * elemLay.size.bytes.toNat)) := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by
        rw [hptr]; rfl
      dsimp only [elemMp, elemOff]
      simp only [Miri.ABI.Size.ofBytes, hbytes, uint64_add_add_sub_cancel_left]
    have hprov_elem : elemMp.ptr.provenance = some (.concrete allocId tag) := hprov
    unfold annealReadImmediate
    dsimp only [elemTy, elemLay] at hrel_off ⊢
    rw [hprov_elem, hwf.elem_fields_primitive]
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind]
    rw [hrel_off, hread]
    rfl

/-! ## 2. Pointer Arithmetic, `Index` and `ConstantIndex` Projection Simulation -/

/-- `annealPointerArithmetic.truncateToTargetUsize` is the identity on 64-bit `UInt64`s. -/
theorem annealPointerArithmetic_truncateToTargetUsize (val : UInt64) :
    annealPointerArithmetic.truncateToTargetUsize val = .ok val := by
  have htrunc :
      annealPointerArithmetic.truncateToTargetUsize val =
        (match ((Miri.ABI.Size.ofBytes 8).truncate (BitVec.ofNat 128 val.toNat)).mapError
            Miri.Memory.PointerError.sourceSizeError with
        | .error err => .error err
        | .ok v =>
          if v.toNat < 2 ^ 64 then .ok (UInt64.ofNat v.toNat)
          else .error .unsignedConversionOverflow) := by
    with_unfolding_all rfl
  have hw : (Miri.ABI.Size.ofBytes 8).truncate (BitVec.ofNat 128 val.toNat) =
      .ok (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 val.toNat))) := by
    with_unfolding_all rfl
  have hlt64 : val.toNat < 2 ^ 64 := by simpa [UInt64.size] using val.toBitVec.isLt
  have hlt128 : val.toNat < 2 ^ 128 := by omega
  have hnat :
      (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 val.toNat))).toNat =
        val.toNat := by
    simp [BitVec.zeroExtend, BitVec.extractLsb, BitVec.toNat_setWidth,
      BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hlt64]
  rw [htrunc, hw]
  dsimp only [Except.mapError]
  rw [hnat]
  simp [hlt64, UInt64.ofNat_toNat]

/-- `Pointer.wrappingOffset` under `annealPointerArithmetic` wraps at 64 bits. -/
theorem pointer_wrappingOffset_anneal_eq {Prov : Type}
    (ptr : Miri.Memory.Pointer Prov) (sz : Miri.ABI.Size) :
    ptr.wrappingOffset sz annealPointerArithmetic =
      .ok { ptr with offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes + sz.bytes) } := by
  unfold Miri.Memory.Pointer.wrappingOffset
  rw [annealPointerArithmetic_truncateToTargetUsize]
  rfl

/-- Vendor `Miri.Interpreter.aggregateWrappingOffset` instantiated with
`annealPointerArithmetic` adds `sz.bytes` wrapping at 64 bits while preserving provenance. -/
theorem aggregateWrappingOffset_anneal_eq
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (sz : Miri.ABI.Size) :
    Miri.Interpreter.aggregateWrappingOffset annealPointerArithmetic ptr sz =
      .ok { ptr with offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes + sz.bytes) } := by
  unfold Miri.Interpreter.aggregateWrappingOffset
  rw [pointer_wrappingOffset_anneal_eq]
  rfl

private def fitsI64Copy (value : Int) : Bool :=
  -(2 ^ 63 : Int) ≤ value && value < (2 ^ 63 : Int)

private theorem checkedBounds_def
    (target : Miri.Memory.PointerArithmetic) (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size) (signedSize : Int)
    (message : Miri.Memory.CheckInAllocMsg) :
    Miri.Memory.checkedBounds target id allocationSize offset signedSize message =
      (do
        if !fitsI64Copy signedSize then
          throw (.signedSizeOutsideI64 signedSize)
        let offsetNat := offset.bytes.toNat
        let allocationNat := allocationSize.bytes.toNat
        let inBounds := if signedSize >= 0 then
            offsetNat + signedSize.toNat ≤ allocationNat
          else
            let amount := (-signedSize).toNat
            amount ≤ offsetNat && offsetNat ≤ allocationNat
        if !inBounds then
          let signedOffset ←
            (target.signExtendToTargetIsize offset.bytes).mapError
              Miri.Memory.AccessError.pointerArithmetic
          throw (.pointerOutOfBounds id allocationSize signedOffset.toInt signedSize message)
        pure ()) := by
  with_unfolding_all rfl

private theorem checkAndDerefPtr_def {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup =
      (do
        if !fitsI64Copy signedSize then
          throw (.signedSizeOutsideI64 signedSize)
        if signedSize == 0 then return none
        let resolved ← match resolve ptr signedSize with
          | .ok resolved => pure resolved
          | .error address => throw (.danglingIntegerPointer address signedSize message)
        let allocation ← match lookup resolved.allocId with
          | .ok allocation => pure allocation
          | .error (.deadAllocation id) => throw (.allocationLookup (.deadAllocation id))
          | .error (.unavailable id) => throw (.allocationLookup (.unavailable id))
        if allocation.kind == .dead then
          throw (.allocationLookup (.deadAllocation resolved.allocId))
        Miri.Memory.checkedBounds target resolved.allocId allocation.size resolved.offset
          signedSize message
        return some ⟨resolved, allocation⟩) := by
  with_unfolding_all rfl

private theorem fitsI64_nat_of_lt {n : Nat} (hn : n < 2 ^ 63) :
    (Int64.ofInt (n : Int)).toInt = (n : Int) ∧
    fitsI64Copy (n : Int) = true := by
  have h1 : (-(2 ^ 63 : Int)) ≤ (n : Int) := by omega
  have h2 : (n : Int) < (2 ^ 63 : Int) := by omega
  refine ⟨Int64.toInt_ofInt_of_le h1 h2, ?_⟩
  unfold fitsI64Copy
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true h1, decide_eq_true h2⟩

private theorem checkedBounds_inbounds_nat
    (target : Miri.Memory.PointerArithmetic)
    (allocId : Miri.Memory.AllocId) (allocSize relOffset : Miri.ABI.Size) (n : Nat)
    (hfits : fitsI64Copy (n : Int) = true)
    (hin : relOffset.bytes.toNat + n ≤ allocSize.bytes.toNat) :
    Miri.Memory.checkedBounds target allocId
      allocSize relOffset (n : Int) .inboundsPointerArithmetic = .ok () := by
  rw [checkedBounds_def]
  have hge0 : ((0 : Int) ≤ (n : Int)) := Int.natCast_nonneg _
  have hin_le : relOffset.bytes.toNat + (n : Int).toNat ≤ allocSize.bytes.toNat := hin
  dsimp only [GE.ge]
  simp only [hfits, hge0, hin_le, ↓reduceIte, decide_true, Bool.not_true,
    Bool.false_eq_true, pure, Except.pure]

private theorem checkAndDerefPtr_ok_zero {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (hfits : fitsI64Copy signedSize = true)
    (hz : (signedSize == 0) = true) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup = .ok none := by
  rw [checkAndDerefPtr_def]
  simp only [hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz, pure, Except.pure]

private theorem checkAndDerefPtr_ok_nonzero {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (resolved : Miri.Memory.ResolvedPointer ProvExtra)
    (allocation : Miri.Memory.AllocationInfo)
    (hfits : fitsI64Copy signedSize = true)
    (hne0 : (signedSize == 0) = false)
    (hres : resolve ptr signedSize = .ok resolved)
    (hlook : lookup resolved.allocId = .ok allocation)
    (hnot_dead : (allocation.kind == .dead) = false)
    (hbounds :
      Miri.Memory.checkedBounds target resolved.allocId allocation.size resolved.offset
        signedSize message = .ok ()) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize message resolve lookup =
      .ok (some ⟨resolved, allocation⟩) := by
  rw [checkAndDerefPtr_def]
  simp only [hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne0, hres, hlook,
    hnot_dead, hbounds, pure, Except.pure, bind, Except.bind]

private theorem checkPtrAccessSigned_eq_of_deref {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Int64) (message : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    {s : Int} {res : Option (Miri.Memory.CheckedPointerAccess ProvExtra)}
    (hs : size.toInt = s)
    (hd : Miri.Memory.checkAndDerefPtr target ptr s message resolve lookup = .ok res) :
    Miri.Memory.checkPtrAccessSigned target ptr size message resolve lookup = .ok () := by
  unfold Miri.Memory.checkPtrAccessSigned
  rw [hs, hd]
  rfl

private theorem checkPtrAccessSigned_inbounds_nat
    {Prov ProvExtra : Type}
    (ptr : Miri.Memory.Pointer (Option Prov)) (n : Nat)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (hn : n < 2 ^ 63)
    (hbody : n ≠ 0 →
      ∃ allocId relOffset extra allocSize align mutability,
        resolve ptr (n : Int) = .ok ⟨allocId, relOffset, extra⟩ ∧
        lookup allocId = .ok ⟨allocSize, align, .liveData, mutability⟩ ∧
        relOffset.bytes.toNat + n ≤ allocSize.bytes.toNat) :
    Miri.Memory.checkPtrAccessSigned annealPointerArithmetic ptr
      (Int64.ofInt (n : Int)) .inboundsPointerArithmetic resolve lookup = .ok () := by
  obtain ⟨hi64_toInt, hfits⟩ := fitsI64_nat_of_lt hn
  by_cases hz : n = 0
  · have hz0 : ((n : Int) == 0) = true := beq_iff_eq.mpr (congrArg Nat.cast hz)
    exact checkPtrAccessSigned_eq_of_deref _ _ _ _ _ _ hi64_toInt
      (checkAndDerefPtr_ok_zero _ _ _ _ _ _ hfits hz0)
  · obtain ⟨allocId, relOffset, extra, allocSize, align, mutability, hres, hlook, hin⟩ :=
      hbody hz
    have hne0 : ((n : Int) == 0) = false :=
      beq_false_of_ne (by intro h; exact hz (Int.ofNat.inj h))
    have hbounds_ok :=
      checkedBounds_inbounds_nat annealPointerArithmetic allocId allocSize relOffset n hfits hin
    exact checkPtrAccessSigned_eq_of_deref _ _ _ _ _ _ hi64_toInt
      (checkAndDerefPtr_ok_nonzero _ _ _ _ _ _ _ _ hfits hne0 hres hlook rfl hbounds_ok)

private theorem checkPtrAccessSigned_inbounds_of_memPlaceRel
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {offset : Miri.ABI.Size}
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach ty layouts optVal mp)
    (hoff_le : offset.bytes.toNat ≤ (translateTy ty layouts).layout.size.bytes.toNat)
    (hoff_i64 : offset.bytes.toNat < 2 ^ 63) :
    Miri.Memory.checkPtrAccessSigned
      annealPointerArithmetic mp.ptr
      (Int64.ofInt (offset.bytes.toNat : Int))
      .inboundsPointerArithmetic
      (annealPointerResolver mach)
      (annealLiveAllocationLookup mach) = .ok () := by
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase hno_ovf hptr _ _ hin _ _ _ _ =>
    refine checkPtrAccessSigned_inbounds_nat mp.ptr offset.bytes.toNat
      (annealPointerResolver mach) (annealLiveAllocationLookup mach) hoff_i64 (fun _ => ?_)
    have hbase_le : baseAddr ≤ mp.ptr.offset.bytes := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      have hsz_lt : baseAddr.toNat + relOffset.bytes.toNat < UInt64.size := by
        simpa [UInt64.size] using hno_ovf
      rw [hbytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt hsz_lt]
      exact Nat.le_add_right _ _
    have hrel_eq : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]
      cases relOffset; rfl
    have hres_ptr :
        annealPointerResolver mach mp.ptr (offset.bytes.toNat : Int) =
          .ok ⟨allocId, relOffset, ()⟩ := by
      dsimp only [annealPointerResolver]
      rw [hprov]
      simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hbase_le,
        ↓reduceIte, hrel_eq]
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hlookup :
        annealLiveAllocationLookup mach allocId =
          .ok ⟨localAlloc.allocation.byteSize, localAlloc.allocation.align,
               .liveData, localAlloc.allocation.mutability⟩ := by
      dsimp only [annealLiveAllocationLookup]
      simp only [hfind]
    exact ⟨allocId, relOffset, (), localAlloc.allocation.byteSize, localAlloc.allocation.align,
      localAlloc.allocation.mutability, hres_ptr, hlookup,
      Nat.le_trans (Nat.add_le_add_left hoff_le _) hin⟩

/-- Vendor `Miri.Interpreter.projectionMemoryOffset` in `OffsetMode.inbounds` succeeds on
any `mp` related by `MemPlaceRel mach ty layouts optVal mp` whenever `offset` fits within
`(translateTy ty layouts).layout.size` and `offset.bytes.toNat < 2 ^ 63`. -/
theorem projectionMemoryOffset_inbounds_of_memPlaceRel
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {offset : Miri.ABI.Size}
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach ty layouts optVal mp)
    (hoff_le : offset.bytes.toNat ≤ (translateTy ty layouts).layout.size.bytes.toNat)
    (hoff_i64 : offset.bytes.toNat < 2 ^ 63) :
    Miri.Interpreter.projectionMemoryOffset
      annealPointerArithmetic
      (annealPointerResolver mach)
      (annealLiveAllocationLookup mach)
      mp offset .inbounds .none =
      .ok
        { mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + offset.bytes) }
          metadata := .none } := by
  have hnot_ge63 : ¬ (offset.bytes.toNat ≥ 2 ^ 63) := Nat.not_le.mpr hoff_i64
  have hi64_toU64 : (Int64.ofInt (offset.bytes.toNat : Int)).toUInt64 = offset.bytes := by
    rw [show (Int64.ofInt (offset.bytes.toNat : Int)).toUInt64 =
        UInt64.ofBitVec (BitVec.ofInt 64 (offset.bytes.toNat : Int)) from rfl,
      BitVec.ofInt_natCast]
    exact UInt64.ofNat_toNat
  have hwrap :
      mp.ptr.wrappingSignedOffset (Int64.ofInt (offset.bytes.toNat : Int))
        annealPointerArithmetic =
      .ok { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + offset.bytes) } := by
    dsimp only [Miri.Memory.Pointer.wrappingSignedOffset]
    rw [hi64_toU64]
    have hsz_eq : Miri.ABI.Size.ofBytes offset.bytes = offset := by cases offset; rfl
    rw [hsz_eq, pointer_wrappingOffset_anneal_eq]
  have hcheck := checkPtrAccessSigned_inbounds_of_memPlaceRel hnodup hmp hoff_le hoff_i64
  dsimp only [Miri.Interpreter.projectionMemoryOffset, Miri.Interpreter.MemPlace.offsetWithMeta,
    Miri.Interpreter.ptrOffsetInbounds, GE.ge]
  have hmeta_false : (Miri.Interpreter.MemPlaceMeta.none (Prov := AnnealProv)).hasMeta = false := rfl
  simp only [hmeta_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    hnot_ge63, hcheck, hwrap, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Helper: `Miri.Interpreter.projectIndex` on an array `OpTy` with `WellTypedArrayTy`
and `MemPlaceRel` (under `annealProjectionCx frame layouts mach`):
- succeeds with offset `idx * elemSize` and layout `translateTy elemTy layouts` when `idx < count`,
- fails with `.error (.bounds (UInt64.ofNat count) (UInt64.ofNat idx))` when `count ≤ idx` and `idx < 2 ^ 64`. -/
theorem projectIndex_array_spec
    {mach : AnnealMachine}
    {frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp) :
    let cx := annealProjectionCx frame layouts mach
    let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, translateTy arrTy layouts⟩
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy layouts).layout
    (∀ idx : Nat, idx < count →
      Miri.Interpreter.projectIndex cx base (UInt64.ofNat idx) =
        .ok
          ⟨.indirect
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes + UInt64.ofNat (idx * elemLay.size.bytes.toNat)) }
              metadata := .none },
            translateTy elemTy layouts⟩) ∧
    (∀ idx : Nat, count ≤ idx → idx < 2 ^ 64 →
      Miri.Interpreter.projectIndex cx base (UInt64.ofNat idx) =
        .error (.bounds (UInt64.ofNat count) (UInt64.ofNat idx))) := by
  intro cx base elemTy elemLay
  have hfields : base.layout.layout.fields = .Array elemLay.size (UInt64.ofNat count) :=
    hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]
    rfl
  have hcount_toNat := hwf.uint64_ofNat_count_toNat
  constructor
  · intro idx hlt
    have hidx_lt_2_64 : idx < 2 ^ 64 := by
      have := hwf.count_lt_two_pow_32; omega
    have hidx_toNat : (UInt64.ofNat idx).toNat = idx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hidx_lt_2_64)]
    have hnot_ge : ¬ (UInt64.ofNat idx ≥ UInt64.ofNat count) := by
      simp only [GE.ge, UInt64.le_iff_toNat_le, hidx_toNat, hcount_toNat]
      omega
    have hmul_lt : idx * elemLay.size.bytes.toNat < 2 ^ 32 := by
      have h1 : idx * elemLay.size.bytes.toNat ≤ count * elemLay.size.bytes.toNat :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      have h2 : count * elemLay.size.bytes.toNat < 2 ^ 32 := hwf.total_bytes_bound
      omega
    have hcomp :
        Miri.Interpreter.IntegerOps.computeSizeInBytes
          elemLay.size (UInt64.ofNat idx) cx.maxSizeOfVal =
        some (Miri.ABI.Size.ofBytes (UInt64.ofNat (idx * elemLay.size.bytes.toNat))) := by
      unfold Miri.Interpreter.IntegerOps.computeSizeInBytes
      rw [hidx_toNat, Nat.mul_comm]
      have hc1 : idx * elemLay.size.bytes.toNat < 2 ^ 64 := by omega
      have hc2 : idx * elemLay.size.bytes.toNat ≤ cx.maxSizeOfVal.bytes.toNat := by
        have hmax : cx.maxSizeOfVal.bytes.toNat = 0x7fff_ffff_ffff_ffff := rfl
        rw [hmax]; omega
      simp [hc1, hc2]
    have hfield : cx.field base.layout 0 = .ok (translateTy elemTy layouts) := by
      change (match base.layout.layout.fields with
        | .Array stride _ => Except.ok (arrayElemLayoutOf layouts base.layout stride)
        | _ => _) = _
      rw [hfields]
      dsimp only [base]
      rw [hwf.elem_layout_eq]
    let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (idx * elemLay.size.bytes.toNat))
    have hoff_toNat : elemOff.bytes.toNat = idx * elemLay.size.bytes.toNat := by
      dsimp only [elemOff, Miri.ABI.Size.ofBytes]
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using by omega)]
    have hoff_le : elemOff.bytes.toNat ≤ (translateTy arrTy layouts).layout.size.bytes.toNat := by
      rw [hoff_toNat, hwf.arr_size_toNat]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
    have hoff_i64 : elemOff.bytes.toNat < 2 ^ 63 := by omega
    have hmem_off := projectionMemoryOffset_inbounds_of_memPlaceRel
      (offset := elemOff) hnodup hmp hoff_le hoff_i64
    unfold Miri.Interpreter.projectIndex
    rw [hfields, hlen]
    simp only [bind, Except.bind, hnot_ge, ↓reduceIte, hcomp, hfield]
    unfold Miri.Interpreter.OpTy.offset Miri.Interpreter.OpTy.offsetWithMeta
    rw [hwf.elem_isSized]
    dsimp only [base, cx, annealProjectionCx, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
    rw [hmem_off]
    rfl
  · intro idx hge hlt64
    have hidx_toNat : (UInt64.ofNat idx).toNat = idx := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64)]
    have hge_u64 : UInt64.ofNat idx ≥ UInt64.ofNat count := by
      simp only [GE.ge, UInt64.le_iff_toNat_le, hidx_toNat, hcount_toNat]
      exact hge
    unfold Miri.Interpreter.projectIndex
    rw [hfields, hlen]
    simp [bind, Except.bind, hge_u64, throw, throwThe, MonadExceptOf.throw]

/-- Evaluate `annealLocalIndex topFrame mach idxLocal` for any declared `usize` local `idxLocal`
(whether immediate in `topFrame` or moved into `mach.memory` via `LocalRel.indirect`). -/
theorem annealLocalIndex_usize_spec
    {body : CapturedMir} {af : StackFrame} {mach : AnnealMachine}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af topFrame)
    (hnodup : LiveAllocsNodup mach)
    {idxLocal : Local} {idxDecl : LocalDecl}
    (hidx_decl : get? body.localDecls idxLocal = some idxDecl)
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 }) :
    ((get? af.locals idxLocal = some .dead ∨ get? af.locals idxLocal = some .uninit) →
      ∃ msg,
        annealLocalIndex topFrame mach idxLocal = .error (.machineError (.undefinedBehavior msg))) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? af.locals idxLocal = some (.init (.scalar idxSc)) →
      idxSc.bits < 2 ^ 64 ∧
      annealLocalIndex topFrame mach idxLocal = .ok (UInt64.ofNat idxSc.bits)) := by
  obtain ⟨slot_idx, mls, _, hlt_mf, hslot_idx, _, hmls_eq, hloc_rel⟩ := hfr.lookup_local hidx_decl
  constructor
  · intro hdu
    rcases hdu with hdead | huninit
    · rw [hdead] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
      cases hloc_rel with
      | dead _ _ =>
        have hop : topFrame.getLocalOperand idxLocal = .error (.localExpectedLive idxLocal) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        exact ⟨"index local is dead", by simp [annealLocalIndex, hop]⟩
      | immediate _ _ _ _ himm =>
        rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
      | indirect _ _ _ _ hnot_dead _ =>
        exact absurd rfl hnot_dead
    · rw [huninit] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
      cases hloc_rel with
      | immediate _ imm _ _ himm =>
        rcases himm with ⟨_, rfl⟩ | ⟨_, hv, _⟩
        · have hop : topFrame.getLocalOperand idxLocal = .ok (.immediate .uninit) := by
            unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
              Miri.Interpreter.LocalState.access
            simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
          exact ⟨"index local is uninitialized", by simp [annealLocalIndex, hop]⟩
        · cases hv
      | indirect _ mp_idx _ _ _ hmp_idx =>
        have hop : topFrame.getLocalOperand idxLocal = .ok (.indirect mp_idx) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        cases hmp_idx with
        | mk aid tag baddr roff la hprov _ _ hlive hbase _ hptr _ _ _ huninit_cons _ _ _ =>
          have hfind := array_find?_of_nodup_fst hnodup hlive
          have hrel_sz : Miri.ABI.Size.ofBytes (mp_idx.ptr.offset.bytes - baddr) = roff := by
            have hbytes : mp_idx.ptr.offset.bytes = baddr + roff.bytes := by rw [hptr]; rfl
            rw [hbytes, uint64_add_sub_cancel_left]; cases roff; rfl
          have hsz8 : (translateTy idxDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
            rw [hidx_ty]; rfl
          have hsz_nz : (translateTy idxDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
            rw [hsz8]; decide
          have hnot_init := huninit_cons rfl hsz_nz
          rw [hsz8] at hnot_init
          refine ⟨"index local is uninitialized", ?_⟩
          unfold annealLocalIndex
          rw [hop]
          dsimp only
          rw [hprov]
          simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
  · intro idxSc hidx_slot
    rw [hidx_slot] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
    cases hloc_rel with
    | immediate _ imm _ _ himm =>
      rcases himm with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
      · cases h1
      · injection hv' with hv_eq
        subst hv_eq
        obtain ⟨sc', msc, hsc_eq, rfl, hsc_rel, hsz_eq, _, _⟩ :=
          ImmediateRel.of_primitive_scalar himm'
            (by rw [hidx_ty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
        injection hsc_eq with hsc_eq'
        subst hsc_eq'
        have hop : topFrame.getLocalOperand idxLocal =
            .ok (.immediate (.scalar (.fromScalarInt msc))) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        have hsz8 : translateSizeBytes idxSc.sizeBytes = Miri.ABI.Size.ofBytes 8 := by
          rw [← hsz_eq, hidx_ty]; rfl
        have hsz_bytes : idxSc.sizeBytes = 8 := by
          rcases hsc_rel.validBytes with h | h | h | h | h <;>
            (rw [h] at hsz8; first | exact h | exact absurd hsz8 (by decide))
        have hbits_lt : idxSc.bits < 2 ^ 64 := by
          have hc := hsc_rel.canonical; rw [hsz_bytes] at hc; exact hc
        have htb8 : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 idxSc.bits) := by
          rw [← hsz8]; exact hsc_rel.toBits_eq
        have htoBits :
            (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
                (Miri.ABI.Size.ofBytes 8) =
              .ok (BitVec.ofNat 128 idxSc.bits) := by
          unfold Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
            Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
          dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
          rw [htb8]; rfl
        have hbv_toNat : (BitVec.ofNat 128 idxSc.bits).toNat = idxSc.bits :=
          bitVec_ofNat_128_toNat hsc_rel.validBytes hsc_rel.canonical
        refine ⟨hbits_lt, ?_⟩
        unfold annealLocalIndex
        rw [hop]; dsimp only; rw [htoBits]; dsimp only; rw [hbv_toNat]
    | indirect _ mp_idx _ _ _ hmp_idx =>
      have hop : topFrame.getLocalOperand idxLocal = .ok (.indirect mp_idx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
      cases hmp_idx with
      | mk aid tag baddr roff la hprov _ _ hlive hbase _ hptr _ _ _ _ hval_cons hsc_cons _ =>
        have hfind := array_find?_of_nodup_fst hnodup hlive
        have hrel_sz : Miri.ABI.Size.ofBytes (mp_idx.ptr.offset.bytes - baddr) = roff := by
          have hbytes : mp_idx.ptr.offset.bytes = baddr + roff.bytes := by rw [hptr]; rfl
          rw [hbytes, uint64_add_sub_cancel_left]; cases roff; rfl
        have hlay8 : (translateTy idxDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
          rw [hidx_ty]; rfl
        have hsz_nz : (translateTy idxDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
          rw [hlay8]; decide
        have hinit_ok := hval_cons (.scalar idxSc) rfl hsz_nz
        rw [hlay8] at hinit_ok
        obtain ⟨hsz_eq, _, _, msc, hsc_rel, hread_sc⟩ := hsc_cons idxSc rfl
        rw [hlay8] at hread_sc
        have hsz8 : translateSizeBytes idxSc.sizeBytes = Miri.ABI.Size.ofBytes 8 := by
          rw [← hsz_eq, hlay8]
        have hsz_bytes : idxSc.sizeBytes = 8 := by
          rcases hsc_rel.validBytes with h | h | h | h | h <;>
            (rw [h] at hsz8; first | exact h | exact absurd hsz8 (by decide))
        have hbits_lt : idxSc.bits < 2 ^ 64 := by
          have hc := hsc_rel.canonical; rw [hsz_bytes] at hc; exact hc
        have htb8 : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 idxSc.bits) := by
          rw [← hsz8]; exact hsc_rel.toBits_eq
        have htoBits :
            (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
                (Miri.ABI.Size.ofBytes 8) =
              .ok (BitVec.ofNat 128 idxSc.bits) := by
          unfold Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
            Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
          dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
          rw [htb8]; rfl
        have hbv_toNat : (BitVec.ofNat 128 idxSc.bits).toNat = idxSc.bits :=
          bitVec_ofNat_128_toNat hsc_rel.validBytes hsc_rel.canonical
        refine ⟨hbits_lt, ?_⟩
        unfold annealLocalIndex
        rw [hop]
        dsimp only
        rw [hprov]
        simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
          hinit_ok, hread_sc, htoBits, hbv_toNat]

/-- **`evalProjection_index_simulation`** (`LM-2.1`):
Evaluating `ProjectionElem.index idxLocal` on an array place of type `arrTy`
(`WellTypedArrayTy layouts arrTy elemKind count`) related by `MemPlaceRel`,
supporting both immediate and memory-backed (`indirect`) `usize` index locals:
1. If `idxLocal` is `.dead` or `.uninit`, both Anneal (`readProjectedValue` /
   `writeProjectedValue`) and Miri (`annealProjectList` lifted via `annealLiftProjectionError`)
   raise UB.
2. If `idxLocal` holds `.init (.scalar idxSc)` with `idxSc.bits < count`:
   Anneal's `readProjectedValue` returns `.ok elemVal` where `get? elems idxSc.bits = some elemVal`,
   Miri's `annealProjectList` advances `mp.ptr.offset` by `idxSc.bits * elemSize` (through vendor
   `projectionMemoryOffset`) with layout `translateTy elemTy layouts`, and `annealReadImmediate`
   reads back the `ImmediateRel`-matching scalar.
3. If `idxLocal` holds `.init (.scalar idxSc)` with `count ≤ idxSc.bits`:
   both Anneal (`readProjectedValue` / `writeProjectedValue`) and Miri raise a
   bounds-check UB fault. -/
theorem evalProjection_index_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {idxLocal : Local} {arrTy : Ty} {idxDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hmp : MemPlaceRel m.machine arrTy body.layouts (some (.aggregate 0 elems)) mp)
    (hidx_decl : get? body.localDecls idxLocal = some idxDecl)
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 }) :
    let cx := annealProjectionCx topFrame body.layouts m.machine
    let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, translateTy arrTy body.layouts⟩
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy body.layouts).layout
    ((get? s.frame.locals idxLocal = some .dead ∨ get? s.frame.locals idxLocal = some .uninit) →
      readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] = .ub ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.Index idxLocal]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? s.frame.locals idxLocal = some (.init (.scalar idxSc)) →
      idxSc.bits < count →
      ∃ elemVal sc msc,
        get? elems idxSc.bits = some elemVal ∧
        elemVal = .scalar sc ∧
        readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] =
          ProjReadResult.ok elemVal ∧
        annealProjectList cx base [.Index idxLocal] =
          Except.ok
            ⟨.indirect
              { mp with
                ptr :=
                  { mp.ptr with
                    offset :=
                      Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes +
                          UInt64.ofNat (idxSc.bits * elemLay.size.bytes.toNat)) }
                metadata := .none },
              translateTy elemTy body.layouts⟩ ∧
        ImmediateRel elemTy body.layouts elemVal (.scalar (.fromScalarInt msc)) ∧
        annealReadImmediate
          ⟨.indirect
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idxSc.bits * elemLay.size.bytes.toNat)) }
              metadata := .none },
            translateTy elemTy body.layouts⟩
          m = EStateM.Result.ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩ m) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? s.frame.locals idxLocal = some (.init (.scalar idxSc)) →
      count ≤ idxSc.bits →
      readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] = .ub ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.Index idxLocal]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) := by
  intro cx base elemTy elemLay
  rcases hrel with ⟨tf, hframes', _, _, hfr, _, _, _, _, _, _⟩
  rw [hframes] at hframes'
  injection hframes' with htf_eq
  injection htf_eq with htf_eq'
  subst htf_eq'
  have ⟨hproj_in, hproj_oob⟩ :=
    projectIndex_array_spec (frame := topFrame) hwf hnodup hmp
  have ⟨hidx_err, hidx_ok⟩ :=
    annealLocalIndex_usize_spec hfr hnodup hidx_decl hidx_ty
  have hlen_elems : elems.length = count := by
    cases hmp with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ harr =>
      exact (harr elemKind count elems hwf.arr_kind rfl).2.2.2.elems_len
  refine ⟨?_, ?_, ?_⟩
  · intro hdead_uninit
    obtain ⟨msg, hloc_err⟩ := hidx_err hdead_uninit
    have hcx_err : cx.localIndex idxLocal = .error (.machineError (.undefinedBehavior msg)) :=
      hloc_err
    rcases hdead_uninit with hdead | huninit
    · refine ⟨by simp [readProjectedValue, hdead],
        fun v => by simp [writeProjectedValue, hdead], msg, ?_⟩
      simp [annealProjectList, Miri.Interpreter.project, hcx_err, Except.mapError,
        annealLiftProjectionError, bind, Except.bind]
    · refine ⟨by simp [readProjectedValue, huninit],
        fun v => by simp [writeProjectedValue, huninit], msg, ?_⟩
      simp [annealProjectList, Miri.Interpreter.project, hcx_err, Except.mapError,
        annealLiftProjectionError, bind, Except.bind]
  · intro idxSc hidx_slot hlt
    obtain ⟨_, hlocalIdx⟩ := hidx_ok idxSc hidx_slot
    have hlt_len : idxSc.bits < elems.length := by rw [hlen_elems]; exact hlt
    let elemVal := elems[idxSc.bits]'hlt_len
    have hget_seq : get? elems idxSc.bits = some elemVal := by
      rw [get?_eq_getElem?]
      exact List.getElem?_eq_some_iff.mpr ⟨hlt_len, rfl⟩
    obtain ⟨sc_e, msc_e, hval_eq, himm_e, hread_e⟩ :=
      annealReadImmediate_of_projected_array_elem hwf hnodup hmp hget_seq
    refine ⟨elemVal, sc_e, msc_e, hget_seq, hval_eq, ?_, ?_, himm_e, hread_e⟩
    · simp [readProjectedValue, hidx_slot, hget_seq]
    · have hcx_local : cx.localIndex idxLocal = .ok (UInt64.ofNat idxSc.bits) := hlocalIdx
      simp only [annealProjectList, Miri.Interpreter.project, hcx_local, bind, Except.bind]
      dsimp only [cx, base]
      rw [hproj_in idxSc.bits hlt]
  · intro idxSc hidx_slot hge
    obtain ⟨hbits_lt, hlocalIdx⟩ := hidx_ok idxSc hidx_slot
    have hget_none : get? elems idxSc.bits = none := by
      change elems[idxSc.bits]? = none
      rw [List.getElem?_eq_none_iff, hlen_elems]
      exact hge
    refine ⟨by simp [readProjectedValue, hidx_slot, hget_none],
      fun v => by simp [writeProjectedValue, hidx_slot, hget_none], ?_⟩
    have hcx_local : cx.localIndex idxLocal = .ok (UInt64.ofNat idxSc.bits) := hlocalIdx
    refine ⟨s!"bounds check failed: index {UInt64.ofNat idxSc.bits} >= len {UInt64.ofNat count}", ?_⟩
    simp only [annealProjectList, Miri.Interpreter.project, hcx_local, bind, Except.bind,
      Except.mapError]
    dsimp only [cx, base]
    rw [hproj_oob idxSc.bits hge hbits_lt]
    rfl

/-- **`evalProjection_constantIndex_simulation`** (`LM-2.1`):
Evaluating `ProjectionElem.constantIndex offset minLength fromEnd` on an array place
of type `arrTy` (`WellTypedArrayTy layouts arrTy elemKind count`) related by `MemPlaceRel`,
for both `fromEnd = false` (`idx = offset`) and `fromEnd = true` (`idx = count - offset`):
1. In-bounds (`minLength ≤ count`): Anneal's `readProjectedValue` returns `.ok elemVal`
   where `get? elems idx = some elemVal`, Miri's `annealProjectList` advances
   `mp.ptr.offset` by `idx * elemSize` with layout `translateTy elemTy layouts`, and
   `annealReadImmediate` reads back the `ImmediateRel`-matching scalar.
2. Out-of-bounds (`count < minLength`): both Anneal (`readProjectedValue` /
   `writeProjectedValue`) and Miri (`annealProjectList` lifted via `annealLiftProjectionError`)
   raise a bounds-check UB fault. -/
theorem evalProjection_constantIndex_simulation
    {body : CapturedMir} {locals : List LocalSlot} {m : AnnealStepState}
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hnodup : LiveAllocsNodup m.machine)
    {arrTy : Ty}
    {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hmp : MemPlaceRel m.machine arrTy body.layouts (some (.aggregate 0 elems)) mp)
    (offset minLength : Nat) (fromEnd : Bool)
    (hoff_bound : offset < 2 ^ 64)
    (hmin_bound : minLength < 2 ^ 64)
    (hwf_const :
      (fromEnd = false → offset < minLength) ∧
      (fromEnd = true → 0 < offset ∧ offset ≤ minLength)) :
    let cx := annealProjectionCx topFrame body.layouts m.machine
    let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, translateTy arrTy body.layouts⟩
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy body.layouts).layout
    let idx := if fromEnd then count - offset else offset
    (minLength ≤ count →
      ∃ elemVal sc msc,
        get? elems idx = some elemVal ∧
        elemVal = .scalar sc ∧
        readProjectedValue locals (.aggregate 0 elems)
          [.constantIndex offset minLength fromEnd] = ProjReadResult.ok elemVal ∧
        annealProjectList cx base [.ConstantIndex offset minLength fromEnd] =
          Except.ok
            ⟨.indirect
              { mp with
                ptr :=
                  { mp.ptr with
                    offset :=
                      Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes +
                          UInt64.ofNat (idx * elemLay.size.bytes.toNat)) }
                metadata := .none },
              translateTy elemTy body.layouts⟩ ∧
        ImmediateRel elemTy body.layouts elemVal (.scalar (.fromScalarInt msc)) ∧
        annealReadImmediate
          ⟨.indirect
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idx * elemLay.size.bytes.toNat)) }
              metadata := .none },
            translateTy elemTy body.layouts⟩
          m = EStateM.Result.ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩ m) ∧
    (count < minLength →
      readProjectedValue locals (.aggregate 0 elems)
        [.constantIndex offset minLength fromEnd] = .ub ∧
      (∀ v,
        writeProjectedValue locals (.aggregate 0 elems)
          [.constantIndex offset minLength fromEnd] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.ConstantIndex offset minLength fromEnd]).mapError
          annealLiftProjectionError = .error (.undefinedBehavior msg)) := by
  intro cx base elemTy elemLay idx
  have ⟨hproj_in, _⟩ := projectIndex_array_spec (frame := topFrame) hwf hnodup hmp
  have hlen_elems : elems.length = count := by
    cases hmp with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ harr =>
      exact (harr elemKind count elems hwf.arr_kind rfl).2.2.2.elems_len
  have hlen_seq : Trusted.Sequence.length elems = count := by
    have hseq : ∀ xs : List Value, Trusted.Sequence.length xs = xs.length := by
      intro xs; induction xs with
      | nil => rfl
      | cons _ _ ih => simp [Trusted.Sequence.length]
    rw [hseq, hlen_elems]
  have hfields : base.layout.layout.fields = .Array elemLay.size (UInt64.ofNat count) :=
    hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen_miri : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]
    rfl
  have hcount_toNat := hwf.uint64_ofNat_count_toNat
  have hoff_toNat : (UInt64.ofNat offset).toNat = offset := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hoff_bound)]
  have hmin_toNat : (UInt64.ofNat minLength).toNat = minLength := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hmin_bound)]
  have hnot_ovf : ¬ (offset ≥ 2 ^ 64 || minLength ≥ 2 ^ 64) := by
    simp [Nat.not_le.mpr hoff_bound, Nat.not_le.mpr hmin_bound]
  constructor
  · intro hmin_le
    have hble : Nat.ble minLength count = true := Nat.ble_eq.mpr hmin_le
    have hnot_lt_min : ¬ (UInt64.ofNat count < UInt64.ofNat minLength) := by
      simp only [UInt64.lt_iff_toNat_lt, hcount_toNat, hmin_toNat]
      omega
    have hidx_lt : idx < count := by
      cases fromEnd with
      | false =>
        have := hwf_const.1 rfl
        dsimp [idx]; omega
      | true =>
        have ⟨hpos, hle⟩ := hwf_const.2 rfl
        dsimp [idx]; omega
    have hlt_len : idx < elems.length := by rw [hlen_elems]; exact hidx_lt
    obtain ⟨elemVal, hget_seq⟩ : ∃ elemVal, get? elems idx = some elemVal :=
      ⟨elems[idx]'hlt_len, by rw [get?_eq_getElem?]; exact List.getElem?_eq_some_iff.mpr ⟨hlt_len, rfl⟩⟩
    obtain ⟨sc_e, msc_e, hval_eq, himm_e, hread_e⟩ :=
      annealReadImmediate_of_projected_array_elem hwf hnodup hmp hget_seq
    refine ⟨elemVal, sc_e, msc_e, hget_seq, hval_eq, ?_, ?_, himm_e, hread_e⟩
    · have hget_idx : get? elems (if fromEnd then count - offset else offset) = some elemVal :=
        hget_seq
      cases fromEnd <;>
        (simp only [Bool.false_eq_true, ↓reduceIte] at hget_idx;
         simp (config := { zetaDelta := true }) only [readProjectedValue, hlen_seq, hble,
           Nat.sub_eq, hget_idx])
    · simp only [annealProjectList, Miri.Interpreter.project, hnot_ovf, ↓reduceIte,
        Miri.Interpreter.projectConstantIndex, hlen_miri, bind, Except.bind, hnot_lt_min]
      cases fromEnd with
      | false =>
        have hoff_lt_min : offset < minLength := hwf_const.1 rfl
        have hnot_ge : ¬ (UInt64.ofNat offset ≥ UInt64.ofNat minLength) := by
          simp only [GE.ge, UInt64.le_iff_toNat_le, hoff_toNat, hmin_toNat]
          omega
        simp only [Bool.false_eq_true, ↓reduceIte, hnot_ge, pure, Except.pure, idx]
        dsimp only [cx, base]
        rw [hproj_in offset hidx_lt]
      | true =>
        have ⟨hpos, hle⟩ := hwf_const.2 rfl
        have hne_zero : (UInt64.ofNat offset == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro h0
          have h0_nat : (UInt64.ofNat offset).toNat = (0 : UInt64).toNat :=
            congrArg UInt64.toNat h0
          rw [hoff_toNat] at h0_nat
          change offset = 0 at h0_nat
          omega
        have hnot_gt : ¬ (UInt64.ofNat offset > UInt64.ofNat minLength) := by
          simp only [GT.gt, UInt64.lt_iff_toNat_lt, hoff_toNat, hmin_toNat]
          omega
        have hsub_u64 : UInt64.ofNat count - UInt64.ofNat offset = UInt64.ofNat (count - offset) := by
          apply UInt64.eq_of_toBitVec_eq
          apply BitVec.eq_of_toNat_eq
          have hle_u64 : UInt64.ofNat offset ≤ UInt64.ofNat count := by
            rw [UInt64.le_iff_toNat_le, hoff_toNat, hcount_toNat]; omega
          simp only [UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le _ _ hle_u64,
            hcount_toNat, hoff_toNat, UInt64.toNat_ofNat']
          rw [Nat.mod_eq_of_lt (by have := hwf.count_lt_two_pow_32; simpa [UInt64.size] using by omega)]
        simp only [↓reduceIte, hne_zero, Bool.false_or, decide_eq_true_eq, hnot_gt,
          pure, Except.pure, hsub_u64, idx]
        dsimp only [cx, base]
        rw [hproj_in (count - offset) hidx_lt]
        rfl
  · intro hlt_min
    have hble : Nat.ble minLength count = false := by
      rw [Bool.eq_false_iff]
      intro h
      have := Nat.ble_eq.mp h
      omega
    have hlt_u64 : UInt64.ofNat count < UInt64.ofNat minLength := by
      simp only [UInt64.lt_iff_toNat_lt, hcount_toNat, hmin_toNat]
      exact hlt_min
    refine ⟨?_, ?_, ?_⟩
    · cases fromEnd <;>
        simp (config := { zetaDelta := true }) only [readProjectedValue, hlen_seq, hble]
    · intro v
      cases fromEnd <;>
        simp (config := { zetaDelta := true }) only [writeProjectedValue, hlen_seq, hble]
    · refine ⟨s!"bounds check failed: index {UInt64.ofNat count} >= len {UInt64.ofNat minLength}", ?_⟩
      simp only [annealProjectList, Miri.Interpreter.project, hnot_ovf, Bool.false_eq_true, ↓reduceIte,
        Miri.Interpreter.projectConstantIndex, hlen_miri, bind, Except.bind, hlt_u64,
        throw, throwThe, MonadExceptOf.throw, Except.mapError, annealLiftProjectionError]

/-! ## 3. Array Length Query Simulation (`evalRvalue_len_array_simulation`) & Fail-Closed Whole-Array Reads -/

/-- Ordinary unprojected whole-array immediate reads (`ty ≠ arraySliceMetaTyId`) fail closed
with `StepError.unsupported "whole-array immediate read not supported"`, ensuring only
`Rvalue.len`'s `UnwrapUnsafeBinder arraySliceMetaTyId` projection
(`ty = arraySliceMetaTyId`) extracts `(ptr, len)` metadata. -/
theorem annealReadImmediate_whole_array_unsupported
    {m : AnnealStepState} {layouts : LayoutTable}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup m.machine)
    (hmp : MemPlaceRel m.machine arrTy layouts optVal mp) :
    annealReadImmediate ⟨.indirect mp, translateTy arrTy layouts⟩ m =
      .error (.unsupported "whole-array immediate read not supported") m := by
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase _ _ _ _ _ _ _ _ _ =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    unfold annealReadImmediate
    dsimp only
    rw [hprov, hwf.arr_fields, hwf.ty_ne_arraySliceMetaTyId]
    simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- No Anneal `Ty` ever encodes to `arraySliceMetaTyId` (`60`). -/
theorem encodeTyId_ne_arraySliceMetaTyId (ty : Ty) :
    encodeTyId ty ≠ arraySliceMetaTyId := by
  rcases ty with ⟨kind, layoutIdx⟩
  unfold encodeTyId arraySliceMetaTyId Miri.MIR.TyId
  cases kind with
  | int it => cases it <;> (dsimp only; decide)
  | uint ut => cases ut <;> (dsimp only; decide)
  | float ft => cases ft <;> (dsimp only; decide)
  | tuple elems => cases elems <;> (dsimp only; omega)
  | array elemKind _ =>
    dsimp only
    cases encodeScalarRigidTy elemKind <;> dsimp only <;> omega
  | _ =>
    dsimp only
    omega

/-- No source-MIR `ProjectionElem` (`translateProjectionElem`) can forge the synthetic
`Rvalue.len` projection `.UnwrapUnsafeBinder arraySliceMetaTyId`. -/
theorem translateProjectionElem_ne_unwrapArraySliceMeta (p : ProjectionElem) :
    translateProjectionElem p ≠ .UnwrapUnsafeBinder arraySliceMetaTyId := by
  cases p with
  | unwrapUnsafeBinder ty =>
    simp [translateProjectionElem, encodeTyId_ne_arraySliceMetaTyId ty]
  | _ => nofun

/-- Projecting an initialized array `OpTy` (`MemPlaceRel`) by
`[.UnwrapUnsafeBinder arraySliceMetaTyId]` (`Rvalue.len`) tags its `LocalLayout`
with `arraySliceMetaTyId` while preserving `mp` and `(translateTy arrTy layouts).layout`. -/
theorem projectUnwrapArraySliceMeta_of_array_memPlaceRel
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp) :
    annealProjectList (annealProjectionCx frame layouts mach)
      ⟨.indirect mp, translateTy arrTy layouts⟩ [.UnwrapUnsafeBinder arraySliceMetaTyId] =
      .ok ⟨.indirect mp, { ty := arraySliceMetaTyId, layout := (translateTy arrTy layouts).layout }⟩ := by
  have hfields := hwf.arr_fields
  have hisSized := hwf.arr_isSized
  have hmeta : mp.metadata = .none := by cases hmp; assumption
  have hoff_zero : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + Miri.ABI.Size.ZERO.bytes) = mp.ptr.offset := by
    cases mp.ptr.offset
    simp [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes]
  have hwrap_zero :
      mp.ptr.wrappingOffset Miri.ABI.Size.ZERO annealPointerArithmetic = .ok mp.ptr := by
    rw [pointer_wrappingOffset_anneal_eq, hoff_zero]
  simp only [annealProjectList, beq_self_eq_true, ↓reduceIte, Miri.Interpreter.project]
  rw [hfields]
  dsimp only [bind, Except.bind, Miri.Interpreter.OpTy.transmute]
  rw [hisSized]
  simp only [Bool.not_true, Bool.false_or, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Miri.Interpreter.OpTy.offsetWithMeta, annealProjectionCx,
    Miri.Interpreter.projectionMemoryOffset, Miri.Interpreter.MemPlace.offsetWithMeta,
    Miri.Interpreter.MemPlaceMeta.hasMeta, Bool.false_and, hwrap_zero, Except.mapError,
    pure, Except.pure]
  rw [← hmeta]
  rfl

/-- Every in-bounds array `Subslice` projection (`fromEnd = false` with `fromIdx ≤ toIdx ≤ count`,
or `fromEnd = true` with `fromIdx + toIdx ≤ count` — covering both partial and whole-array
subslices) fails closed with `.error (.obligation "array subslice in annealProjectionCx")`,
which `annealLiftProjectionError` maps to `StepError.unsupported`. -/
theorem projectSubslice_array_unsupported
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (fromIdx toIdx : Nat) (fromEnd : Bool)
    (hin :
      (fromEnd = false ∧ fromIdx ≤ toIdx ∧ toIdx ≤ count) ∨
      (fromEnd = true ∧ fromIdx + toIdx ≤ count)) :
    annealProjectList (annealProjectionCx frame layouts mach)
      ⟨.indirect mp, translateTy arrTy layouts⟩ [.Subslice fromIdx toIdx fromEnd] =
      .error (.obligation "array subslice in annealProjectionCx") := by
  let cx := annealProjectionCx frame layouts mach
  let base : Miri.Interpreter.OpTy AnnealProv := ⟨.indirect mp, translateTy arrTy layouts⟩
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have hfields : base.layout.layout.fields = .Array elemSize (UInt64.ofNat count) := hwf.arr_fields
  have hisSized : base.layout.layout.isSized = true := hwf.arr_isSized
  have hlen : base.len cx = .ok (UInt64.ofNat count) := by
    unfold Miri.Interpreter.OpTy.len
    rw [hisSized, hfields]; rfl
  have hcnt32 := hwf.count_lt_two_pow_32
  have hfrom_le : fromIdx ≤ count := by
    rcases hin with ⟨_, h1, h2⟩ | ⟨_, h1⟩ <;> omega
  have hto_le : toIdx ≤ count := by
    rcases hin with ⟨_, _, h2⟩ | ⟨_, h1⟩ <;> omega
  have hfrom_lt64 : fromIdx < 2 ^ 64 := by omega
  have hto_lt64 : toIdx < 2 ^ 64 := by omega
  have hnot_ge64 : ¬(fromIdx ≥ 2 ^ 64 || toIdx ≥ 2 ^ 64) := by
    simp only [GE.ge, Bool.or_eq_true, decide_eq_true_eq, not_or]
    omega
  have hfrom_toNat : (UInt64.ofNat fromIdx).toNat = fromIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hfrom_lt64)]
  have hto_toNat : (UInt64.ofNat toIdx).toNat = toIdx := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hto_lt64)]
  have hcount_toNat := hwf.uint64_ofNat_count_toNat
  have hmul_lt64 : elemSize.bytes.toNat * (UInt64.ofNat fromIdx).toNat < 2 ^ 64 := by
    rw [hfrom_toNat, Nat.mul_comm]
    have hle : fromIdx * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat :=
      Nat.mul_le_mul_right _ hfrom_le
    have htot := hwf.total_bytes_bound
    dsimp only [elemSize] at hle ⊢
    omega
  have hmul_ok : elemSize.mul (UInt64.ofNat fromIdx) =
      .ok (Miri.ABI.Size.ofBytes (elemSize.bytes * UInt64.ofNat fromIdx)) := by
    unfold Miri.ABI.Size.mul
    dsimp only
    have hcond :
        (UInt64.ofNat fromIdx != 0 &&
          elemSize.bytes * UInt64.ofNat fromIdx / UInt64.ofNat fromIdx != elemSize.bytes) = false := by
      by_cases hz : UInt64.ofNat fromIdx = 0
      · simp [hz]
      · have hpos : 0 < (UInt64.ofNat fromIdx).toNat := by
          exact Nat.pos_of_ne_zero (fun h0 => hz (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h0)))
        have hprod_toNat :
            (elemSize.bytes * UInt64.ofNat fromIdx).toNat =
              elemSize.bytes.toNat * (UInt64.ofNat fromIdx).toNat := by
          rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hmul_lt64)]
        have hdiv : elemSize.bytes * UInt64.ofNat fromIdx / UInt64.ofNat fromIdx = elemSize.bytes := by
          apply UInt64.eq_of_toBitVec_eq
          apply BitVec.eq_of_toNat_eq
          change ((elemSize.bytes * UInt64.ofNat fromIdx) / UInt64.ofNat fromIdx).toNat = elemSize.bytes.toNat
          rw [UInt64.toNat_div, hprod_toNat, Nat.mul_div_left _ hpos]
        simp [hdiv]
    rw [hcond]
    rfl
  have hsublay : ∀ subCount,
      cx.subsliceLayout base.layout subCount =
        .error (.obligation "array subslice in annealProjectionCx") := by
    intro subCount
    change (match base.layout.layout.fields with
      | .Array _ _ => Except.error (Miri.Interpreter.ProjectionError.obligation "array subslice in annealProjectionCx")
      | _ => Except.error (Miri.Interpreter.ProjectionError.invariant "subslice on non-array")) = _
    rw [hfields]
  simp only [annealProjectList, Miri.Interpreter.project, hnot_ge64]
  change (do
    let next ← Miri.Interpreter.projectSubslice cx base (UInt64.ofNat fromIdx) (UInt64.ofNat toIdx) fromEnd
    Except.ok next) = _
  unfold Miri.Interpreter.projectSubslice Miri.Interpreter.prepareSubslice
  rw [hlen, hfields]
  rcases hin with ⟨rfl, hft, _⟩ | ⟨rfl, hsum⟩
  · have hnot_lt : ¬(UInt64.ofNat toIdx < UInt64.ofNat fromIdx) := by
      simp only [UInt64.lt_iff_toNat_lt, hto_toNat, hfrom_toNat]
      omega
    simp only [Bool.false_eq_true, ↓reduceIte, hmul_ok, Except.mapError, hnot_lt,
      bind, Except.bind, pure, Except.pure, hsublay]
  · have hnot_oob : ¬((UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat ≥ 2 ^ 64 ||
        (UInt64.ofNat fromIdx).toNat + (UInt64.ofNat toIdx).toNat > (UInt64.ofNat count).toNat) := by
      rw [hfrom_toNat, hto_toNat, hcount_toNat]
      simp only [GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    have hsub_toNat : (UInt64.ofNat count - UInt64.ofNat toIdx).toNat = count - toIdx := by
      rw [UInt64.toNat_sub_of_le]
      · rw [hcount_toNat, hto_toNat]
      · simp only [UInt64.le_iff_toNat_le, hto_toNat, hcount_toNat, hto_le]
    have hnot_lt : ¬(UInt64.ofNat count - UInt64.ofNat toIdx < UInt64.ofNat fromIdx) := by
      simp only [UInt64.lt_iff_toNat_lt, hsub_toNat, hfrom_toNat]
      omega
    simp only [↓reduceIte, hnot_oob, Bool.false_eq_true, hmul_ok, Except.mapError, hnot_lt,
      bind, Except.bind, pure, Except.pure, hsublay]

/-- Helper: `annealReadImmediate` on an `UnwrapUnsafeBinder arraySliceMetaTyId`-projected array `OpTy`
(`ty = arraySliceMetaTyId`, `MemPlaceRel`) followed by `ScalarOps.unary .PtrMetadata`
succeeds and produces a `usize` scalar `ImmediateRel`-related to `Value.scalar ⟨count, 8⟩`. -/
theorem annealReadImmediate_of_array_memPlaceRel
    {m : AnnealStepState} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup m.machine)
    (hmp : MemPlaceRel m.machine arrTy layouts (some (.aggregate 0 elems)) mp) :
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let sliceOp : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, { ty := arraySliceMetaTyId, layout := (translateTy arrTy layouts).layout }⟩
    ∃ countSc,
      elems.length = count ∧
      Trusted.Sequence.length elems = count ∧
      ScalarRel ⟨count, 8⟩ countSc ∧
      ImmediateRel usizeTy layouts (.scalar ⟨count, 8⟩) (.scalar (.fromScalarInt countSc)) ∧
      ((annealReadImmediate sliceOp >>=
          fun val =>
            Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks localDecls layouts) () .PtrMetadata val) m =
        .ok ⟨.scalar (.fromScalarInt countSc), translateTy usizeTy layouts⟩ m) := by
  intro usizeTy sliceOp
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov _ _ hlive hbase _ hptr _ _ hin _ _ _ harr =>
    obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
    have hlen_elems : elems.length = count := hslice.elems_len
    have hlen_seq : Trusted.Sequence.length elems = count := by
      have hseq : ∀ xs : List Value, Trusted.Sequence.length xs = xs.length := by
        intro xs; induction xs with
        | nil => rfl
        | cons _ _ _ => simp [Trusted.Sequence.length]
      rw [hseq, hlen_elems]
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by
        rw [hptr]; rfl
      rw [hbytes, uint64_add_sub_cancel_left]
      cases relOffset; rfl
    have hinit := initMask_new_true_isRangeInitialized_inbounds hin
    have hcount_can : count < scalarModulus 8 := by
      have := hwf.count_lt_two_pow_32
      change count < 2 ^ 64
      omega
    obtain ⟨countSc, htry_count, hsc_rel⟩ :=
      tryFromUInt_of_valid_canonical (sc := ⟨count, 8⟩)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hcount_can
    have hcount_toNat := hwf.uint64_ofNat_count_toNat
    have htry_eq :
        (Miri.Memory.ScalarInt.tryFromUInt
          (BitVec.ofNat 128 (UInt64.ofNat count).toNat)
          (Miri.ABI.Size.ofBytes 8)).toOption.join = some countSc := by
      rw [hcount_toNat]
      change (Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 count) (translateSizeBytes 8)).toOption.join =
        some countSc
      rw [htry_count]
      rfl
    have himm : ImmediateRel usizeTy layouts (.scalar ⟨count, 8⟩) (.scalar (.fromScalarInt countSc)) :=
      .scalar ⟨count, 8⟩ countSc hsc_rel rfl (fun h => by cases h) (fun h => by cases h)
    refine ⟨countSc, hlen_elems, hlen_seq, hsc_rel, himm, ?_⟩
    have hread :
        annealReadImmediate sliceOp m =
          .ok
            ⟨.scalarPair
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨mp.ptr.offset, .concrete allocId tag⟩)
              (.fromScalarInt countSc),
              translateTy { kind := .ref .not (.slice .bool), layoutIdx := 0 }⟩
            m := by
      unfold annealReadImmediate
      dsimp only [sliceOp]
      rw [hprov, hwf.arr_fields]
      simp only [beq_self_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get, bind,
        EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
        hslice.alloc_mask, hinit, htry_eq, pure, EStateM.pure]
    rw [EStateM.bind_eq_ok hread]
    unfold Miri.Interpreter.ScalarOps.unary annealScalarOpsHooks
    rfl

/-- A `lean-miri` statement that ends by writing an immediate into the
immediate local `dstIdx` (`annealWriteImmediate` on `.local 0 dstIdx none id0`)
either fails or keeps `m.machine`, so it preserves both `LiveAllocsNodup` and
`MemoryHighWater` (`allocBudget = 0`). -/
theorem stepPreservesNodup_and_HighWater_of_write_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity} {dstLay : Miri.Interpreter.LocalLayout}
    {bb : BasicBlockData} {stmt : Statement}
    (hnodup : LiveAllocsNodup m.machine)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hloc₁ : topFrame₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hlt : dstIdx < topFrame₁.locals.size)
    (himm : IsImmediateFrameLocal topFrame₁ dstIdx)
    (heval_m : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate imm ⟨.local 0 dstIdx none id0, dstLay⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hsome : topFrame₁.locals[dstIdx]? = some (topFrame₁.locals[dstIdx]'hlt) :=
    Array.getElem?_eq_getElem hlt
  cases hmls : topFrame₁.locals[dstIdx]'hlt with
  | mk val lay =>
    rw [hmls] at hsome
    have hget := frame_getLocal_of_getElem? topFrame₁ dstIdx _ hsome
    cases val with
    | dead =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          ({ m with stack := ⟨#[topFrame₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [heval_m]
        unfold Miri.Interpreter.runRvalue
        rw [annealWriteImmediate_dead (topFrame := topFrame₁) rfl hget]
      rw [miri_step_at_statement_error _ hframes hbody₀ hloc₀ hbb hstmt hm_err]
      exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
    | live op =>
      cases op with
      | indirect mp => exact absurd rfl (himm _ hsome mp)
      | immediate oldImm =>
        have hw := annealWriteImmediate_live (m := { m with stack := ⟨#[topFrame₁]⟩ })
          (val := imm) (dstLay := dstLay) (id0 := id0) rfl hlt hget
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            ({ m with
                stack :=
                  ⟨#[{ topFrame₁ with
                        locals := topFrame₁.locals.set dstIdx
                          { topFrame₁.locals[dstIdx]'hlt with value := .live (.immediate imm) }
                          hlt }]⟩ },
              .ok ()) := by
          rw [heval_m]
          unfold Miri.Interpreter.runRvalue
          rw [hw]
        rw [miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_ok rfl hloc₁]
        exact ⟨StepPreservesNodup.of_nodup hnodup, StepPreservesHighWater.of_same_memory rfl⟩

theorem stepPreservesNodup_of_write_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity} {dstLay : Miri.Interpreter.LocalLayout}
    {bb : BasicBlockData} {stmt : Statement}
    (hnodup : LiveAllocsNodup m.machine)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hloc₁ : topFrame₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hlt : dstIdx < topFrame₁.locals.size)
    (himm : IsImmediateFrameLocal topFrame₁ dstIdx)
    (heval_m : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate imm ⟨.local 0 dstIdx none id0, dstLay⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  (stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hbody₀ hloc₀ hbb hstmt
    hloc₁ hlt himm heval_m).1

/-- **`evalRvalue_len_array_simulation`** (`LM-2.1`):
Statement-level simulation of `dst = Len(arr)` (`StatementKind.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩)`)
for a fixed-size homogeneous array local `arrIdx` (`WellTypedArrayTy body.layouts arrDecl.ty elemKind count`):
- When `arrIdx` is `.dead` or `.uninit`, both Anneal (`stepMirFn`) and Miri (`Step.step`)
  report an undefined-behavior fault (`StepRel.ub`).
- When `arrIdx` holds `.init (.aggregate 0 elems)` and `dstIdx` is `.dead`, both report UB (`StepRel.ub`).
- When `arrIdx` holds `.init (.aggregate 0 elems)` and `dstIdx` is live, both step to
  `StateRel`-related states with `dstIdx` storing `.scalar ⟨count, 8⟩`
  (`StepRel.step`).
- A normal `lean-miri` step preserves `LiveAllocsNodup` (`StepPreservesNodup`),
  the immediacy of every local (`StepPreservesImmediate`), and `MemoryHighWater`
  with zero `AllocId` consumption (`StepPreservesHighWater m 0`).

The uninitialized case excludes a memory-backed zero-length array (`count = 0`
with `arrIdx` not immediate): it has no bytes whose initialization `lean-miri`
could check, so `lean-miri` returns `0` where Anneal reports UB (see
`translateRvalue`). -/
theorem evalRvalue_len_array_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx arrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩)
    {arrDecl dstDecl : LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_ty : dstDecl.ty = { kind := .uint .usize, layoutIdx := 0 })
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      (get? s.frame.locals arrIdx = some .uninit ∧
        (0 < count ∨ ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame arrIdx)) ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  have hdst_imm_tf := hdst_imm topFrame hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨_, mls_dst0, _, hlt_dst0, _, hmls_opt, hmls_eq0, hloc_dst0⟩ :=
    hframe.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := by
    apply MemoryAllocDisjoint.mono_layout hd_tf
    intro k
    by_cases hk : k = dstIdx
    · subst hk
      exists (translateTy dstDecl.ty body.layouts)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set]
      simp only [↓reduceIte]
      rw [hmls_opt, hmls_eq0]
      rfl
    · exists (topFrame.locals[k]?).bind (fun x => x.layout)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases topFrame.locals[k]? <;> rfl
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_eq0]; exact hloc_dst0.layout_eq
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity,
        translateTy dstDecl.ty body.layouts⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
  have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_dst hlt_dst0
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun _ hj => hj.cache_layout hlt_dst0 _
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperand body.localDecls body.layouts
            (.Copy ⟨arrIdx, #[.UnwrapUnsafeBinder arraySliceMetaTyId]⟩) none >>=
            annealReadImmediate) >>=
          fun val => do
            let result ← Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) () .PtrMetadata val
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            annealWriteImmediate result.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, translateOperand, List.map, List.toArray,
      Array.push, translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    rw [evalRvalueIntoPlace_unaryOp_def]
    unfold annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, Miri.MIR.UnOp.homogeneous,
      Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hevalPlace_dst]
    exact EStateM.bind_assoc_apply _ _ _ m₀
  obtain ⟨slot_arr, mls_arr, hlt_af_arr, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe₀.lookup_local hdecl_arr
  let topFrame₁ :=
    cacheFrameLocalLayout topFrame₀ arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
  have hcache_arr : ∀ l, (topFrame₀.locals[arrIdx]'hlt_arr).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hres_arr : annealResolveAndCacheLocalLayout body.localDecls body.layouts arrIdx none m₀ =
      .ok (topFrame₁, translateTy arrDecl.ty body.layouts) { m₀ with stack := ⟨#[topFrame₁]⟩ } :=
    annealResolveAndCacheLocalLayout_eq (known := none) (rfl : m₀.stack.frames = #[topFrame₀])
      hlt_arr hdecl_arr hcache_arr
  have hlt_arr₁ : arrIdx < topFrame₁.locals.size := by
    unfold topFrame₁ cacheFrameLocalLayout; simp [hlt_arr]
  have hval_arr₁ : (topFrame₁.locals[arrIdx]'hlt_arr₁).value = mls_arr.value := by
    have hget : topFrame₁.locals[arrIdx]? =
        some { topFrame₀.locals[arrIdx]'hlt_arr with layout := some (translateTy arrDecl.ty body.layouts) } := by
      unfold topFrame₁ cacheFrameLocalLayout; rw [Array.getElem?_set]; simp
    rw [Array.getElem?_eq_getElem hlt_arr₁] at hget
    injection hget with hget_eq
    rw [hget_eq, hmls_arr_eq]
  have hnot_empty₀ : m₀.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m₀.stack topFrame₀ rfl]; rfl
  rcases harr_slot with hdead | ⟨huninit, hcount_or_imm⟩ | ⟨elems, hinit_elems⟩
  · -- Case 1: `arrIdx` is `.dead`
    rw [hdead] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | dead _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        simp [evalRvalue, evalOperand, hdead]
      have hgop : topFrame₁.getLocalOperand arrIdx = .error (.localExpectedLive arrIdx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr₁, hval_arr₁, bind, Except.bind, pure, Except.pure, Except.mapError]
      have hop_err : annealEvalOperand body.localDecls body.layouts
          (.Copy ⟨arrIdx, #[.UnwrapUnsafeBinder arraySliceMetaTyId]⟩) none m₀ =
          .error (.undefinedBehavior "read of dead local") { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
        unfold annealEvalOperand
        simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
          hnot_empty₀, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
          ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error (EStateM.bind_eq_error hop_err)]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
        StepPreservesHighWater.of_error⟩
    | immediate _ _ _ _ himm =>
      rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
    | indirect _ _ _ _ hnot_dead _ =>
      exact absurd rfl hnot_dead
  · -- Case 2: `arrIdx` is `.uninit`
    rw [huninit] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      simp [evalRvalue, evalOperand, huninit]
    cases hloc_arr with
    | immediate _ imm _ _ hval =>
      rcases hval with ⟨_, rfl⟩ | ⟨_, hv, _⟩
      · have hgop : topFrame₁.getLocalOperand arrIdx = .ok (.immediate .uninit) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr₁, hval_arr₁, bind, Except.bind, pure, Except.pure, Except.mapError]
        have hop_err : annealEvalOperand body.localDecls body.layouts
            (.Copy ⟨arrIdx, #[.UnwrapUnsafeBinder arraySliceMetaTyId]⟩) none m₀ =
            .error (.undefinedBehavior "projected read of uninitialized local")
              { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
          unfold annealEvalOperand
          simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
            hnot_empty₀, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
            ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
              .error (.undefinedBehavior "projected read of uninitialized local")) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error (EStateM.bind_eq_error hop_err)]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
          StepPreservesHighWater.of_error⟩
      · cases hv
    | indirect _ mp _ _ _ hmp =>
      rcases hcount_or_imm with hpos | himm_arr
      · have hgop : topFrame₁.getLocalOperand arrIdx = .ok (.indirect mp) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr₁, hval_arr₁, bind, Except.bind, pure, Except.pure, Except.mapError]
        cases hmp with
        | mk allocId tag baseAddr relOffset localAlloc
            hprov _ _ hlive hbase _ hptr _ _ _ huninit_cons _ _ _ =>
          have hfind := array_find?_of_nodup_fst hnodup hlive
          have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
            have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by
              rw [hptr]; rfl
            rw [hbytes, uint64_add_sub_cancel_left]
            cases relOffset; rfl
          have hsz_nz : (translateTy arrDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
            intro hzero
            have hbytes0 : (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat = 0 := by
              rw [hzero]; rfl
            rw [hwf.arr_size_toNat] at hbytes0
            have := Nat.mul_pos hpos hwf.elem_size_pos
            omega
          have hnot_init := huninit_cons rfl hsz_nz
          have hchk_err : annealCheckIndirectInitialized m.machine mp
              (translateTy arrDecl.ty body.layouts).layout.size =
              .error (.undefinedBehavior "access to uninitialized indirect place") := by
            unfold annealCheckIndirectInitialized
            dsimp only [m₀] at hbase hfind
            rw [hprov]
            simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
              throw, throwThe, MonadExceptOf.throw]
          have hop_err : annealEvalOperand body.localDecls body.layouts
              (.Copy ⟨arrIdx, #[.UnwrapUnsafeBinder arraySliceMetaTyId]⟩) none m₀ =
              .error (.undefinedBehavior "access to uninitialized indirect place")
                { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
            unfold annealEvalOperand
            simp [m₀, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
              EStateM.pure, hnot_empty₀, hres_arr, hgop, hchk_err, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
              ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
                .error (.undefinedBehavior "access to uninitialized indirect place")) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_error (EStateM.bind_eq_error hop_err)]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
            hstmt hm_err]
          exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
            StepPreservesHighWater.of_error⟩
      · exact absurd rfl (hmono₀ arrIdx (himm_arr topFrame hframes) _ hmls_arr mp)
  · -- Case 3: `arrIdx` holds `.init (.aggregate 0 elems)`
    rw [hinit_elems] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    obtain ⟨mp, cl, rfl, hcl, hmp⟩ := hloc_arr.array_init_is_indirect hwf.arr_kind
    have hgop : topFrame₁.getLocalOperand arrIdx = .ok (.indirect mp) := by
      unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
        Miri.Interpreter.LocalState.access
      simp [hlt_arr₁, hval_arr₁, bind, Except.bind, pure, Except.pure, Except.mapError]
    have hchk_ok : annealCheckIndirectInitialized m.machine mp
        (translateTy arrDecl.ty body.layouts).layout.size = .ok () :=
      annealCheckIndirectInitialized_of_array_memPlaceRel hwf hnodup hmp
    have hsub_ok := projectUnwrapArraySliceMeta_of_array_memPlaceRel
      topFrame₁ hwf hmp
    let sliceOp : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, { ty := arraySliceMetaTyId, layout := (translateTy arrDecl.ty body.layouts).layout }⟩
    have hop_ok : annealEvalOperand body.localDecls body.layouts
        (.Copy ⟨arrIdx, #[.UnwrapUnsafeBinder arraySliceMetaTyId]⟩) none m₀ =
        .ok sliceOp { m with stack := ⟨#[topFrame₁]⟩ } := by
      unfold annealEvalOperand
      simp [m₀, sliceOp, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
        EStateM.pure, hnot_empty₀, hres_arr, hgop, hchk_ok, hsub_ok]
    obtain ⟨countSc, hlen_elems, _, _, himm_count, hread_unary⟩ :=
      annealReadImmediate_of_array_memPlaceRel
        (m := { m with stack := ⟨#[topFrame₁]⟩ })
        (localDecls := body.localDecls) hwf hnodup hmp
    have hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
        Miri.Interpreter.runRvalue (annealWriteImmediate (.scalar (.fromScalarInt countSc)) destPlace)
          { m with stack := ⟨#[topFrame₁]⟩ } := by
      rw [hm_eval]
      apply runRvalue_eq_of_eq
      rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hop_ok]
      have hread_unary' :
          (annealReadImmediate sliceOp >>=
            fun val =>
              Miri.Interpreter.ScalarOps.unary
                (annealScalarOpsHooks body.localDecls body.layouts) () .PtrMetadata val)
            { m with stack := ⟨#[topFrame₁]⟩ } =
          .ok ⟨.scalar (.fromScalarInt countSc), translateTy dstDecl.ty body.layouts⟩
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [hdst_ty]; exact hread_unary
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_ok hread_unary']
      dsimp only
      exact EStateM.bind_eq_ok (assertRvalueLayoutPub_eq_ok _ _ rfl _)
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩
        body.localDecls body.layouts =
        match get? s.frame.locals dstIdx with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? s.frame.locals dstIdx (.init (.scalar ⟨count, 8⟩)) with
          | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only
      have hlen_rval : evalRvalue s.frame.locals (.len ⟨arrIdx, .nil⟩) s.memory
          body.localDecls body.layouts = .ok (.scalar ⟨count, 8⟩) s.frame.locals s.memory := by
        unfold evalRvalue
        dsimp only
        rw [hbor, hcaller]
        simp [evalOperand, readProjectedValue, hinit_elems, hlen_elems]
      rw [hlen_rval]
      dsimp only
      rw [hprot, hbor]
      dsimp only [invalidateConflictingBorrows]
      rw [hmem_same]
      rfl
    have hframe₁ : FrameRel body m.machine s.frame topFrame₁ :=
      hframe₀.cache_local_layout hdecl_arr hlt_arr
    have hdisj₁ : MemoryAllocDisjoint topFrame₁ := by
      apply MemoryAllocDisjoint.mono_layout hdisj₀
      intro k
      by_cases hk : k = arrIdx
      · subst hk
        exists (translateTy arrDecl.ty body.layouts)
        dsimp [topFrame₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set]
        simp only [↓reduceIte]
        rw [hmls_arr, hmls_arr_eq]
        rfl
      · exists (topFrame₀.locals[k]?).bind (fun x => x.layout)
        dsimp [topFrame₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hk)]
        cases topFrame₀.locals[k]? <;> rfl
    have hmono₁ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₁ j :=
      fun j hj => (hmono₀ j hj).cache_layout hlt_arr _
    have himm_dst' : ImmediateRel dstDecl.ty body.layouts (.scalar ⟨count, 8⟩)
        (.scalar (.fromScalarInt countSc)) := by
      rw [hdst_ty]; exact himm_count
    obtain ⟨_, _, _, hlt_dst₁, _, _, _, _⟩ := hframe₁.lookup_local hdecl_dst
    have hext := write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
      hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
      hframes hframe.body_eq hframe.location_eq hmono₁ hbb hstmt hframe₁ hdisj₁
      hdecl_dst (hmono₁ dstIdx hdst_imm_tf) himm_dst' ha_ok hm_write
    obtain ⟨hnd_w, hhw_w⟩ :=
      stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hframe.body_eq
        hframe.location_eq hbb hstmt hframe₁.location_eq hlt_dst₁ (hmono₁ dstIdx hdst_imm_tf)
        hm_write
    refine ⟨hext.1, hnd_w, ?_, hhw_w⟩
    intro hok tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = topFrame := by simpa using htf.symm
    subst htf_eq
    exact hext.2 j hj tf' htf' hok

/-! ## 4. `annealEnsureAllocated` Helpers & `Rvalue.Repeat` Simulation (`evalRvalue_repeat_simulation`) -/

/-- The machine's allocation-ID supply can reserve one fresh `AllocId`. -/
def CanReserveAllocId (mem : AnnealMemory) : Prop :=
  ∃ mem' id, mem.reserveAllocId = (mem', .ok id)

/-- `MemoryHighWater` suffices to reserve a fresh `AllocId` (`CanReserveAllocId`)
via vendor `Miri.Memory.MemoryState.reserve_of_highWater`, with zero assumed-success premises. -/
theorem MemoryHighWater.canReserveAllocId {mem : AnnealMemory}
    (hw : MemoryHighWater mem) : CanReserveAllocId mem := by
  have hnz : mem.nextAllocId ≠ 0 := by
    intro h0
    have : mem.nextAllocId.toNat = 0 := by rw [h0]; rfl
    exact Nat.ne_of_gt hw.nonzero this
  obtain ⟨after, hres⟩ := Miri.Memory.MemoryState.reserve_of_highWater mem
    hw.available hnz
    (fun h => by rw [hw.sourceInactive] at h; cases h)
    (fun h => by rw [hw.sourceInactive] at h; cases h)
    hw.issued_lt hw.live_lt hw.global_lt hw.dead_lt
  exact ⟨after, ⟨mem.nextAllocId, hnz⟩, hres⟩

/-- Reserving a fresh `AllocId` and pushing onto `live` in `stackAllocMachine`
preserves `MemoryHighWater` and advances `nextAllocId` by `1` whenever
`mach.memory.nextAllocId.toNat + 1 < 2 ^ 64`. -/
theorem MemoryHighWater.stackAllocMachine
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hw : MemoryHighWater mach.memory)
    (hbound : mach.memory.nextAllocId.toNat + 1 < 2 ^ 64)
    (hres : mach.memory.reserveAllocId = (mem', .ok id)) :
    MemoryHighWater (Correspondence.stackAllocMachine mach mem' id alloc).memory ∧
    (Correspondence.stackAllocMachine mach mem' id alloc).memory.nextAllocId.toNat ≤
      mach.memory.nextAllocId.toNat + 1 := by
  have hnz : mach.memory.nextAllocId ≠ 0 := by
    intro h0
    have : mach.memory.nextAllocId.toNat = 0 := by rw [h0]; rfl
    exact Nat.ne_of_gt hw.nonzero this
  obtain ⟨after, hres_hw⟩ := Miri.Memory.MemoryState.reserve_of_highWater mach.memory
    hw.available hnz
    (fun h => by rw [hw.sourceInactive] at h; cases h)
    (fun h => by rw [hw.sourceInactive] at h; cases h)
    hw.issued_lt hw.live_lt hw.global_lt hw.dead_lt
  have hid_eq : id = ⟨mach.memory.nextAllocId, hnz⟩ := by
    rw [hres_hw] at hres
    injection hres with _ hok
    injection hok with heq
    exact heq.symm
  unfold Miri.Memory.MemoryState.reserveAllocId at hres
  simp only [hw.available, hw.sourceInactive, Bool.false_and, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, Id.run, pure, Pure.pure] at hres
  cases hof : Miri.Memory.AllocId.ofUInt64 mach.memory.nextAllocId with
  | none => rw [hof] at hres; cases hres
  | some allocId =>
    rw [hof] at hres
    dsimp only at hres
    split at hres
    · cases hres
    · injection hres with hmem_eq hok_eq
      injection hok_eq with halloc_eq
      subst halloc_eq
      subst hmem_eq
      have hnext_toNat : (mach.memory.nextAllocId + 1).toNat = mach.memory.nextAllocId.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one,
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hbound)]
      have hid_val : allocId.value = mach.memory.nextAllocId := by rw [hid_eq]
      dsimp only [Correspondence.stackAllocMachine, MemoryHighWater]
      refine ⟨⟨rfl, by rw [hnext_toNat]; omega, rfl, ?_, ?_, ?_, ?_⟩,
        by rw [hnext_toNat]; exact Nat.le_refl _⟩
      · intro x hx
        change x ∈ (mach.memory.issuedIds.push allocId) at hx
        rcases Array.mem_push.mp hx with hx_old | rfl
        · have hlt := hw.issued_lt x hx_old
          rw [hnext_toNat]; omega
        · rw [hid_val, hnext_toNat]; omega
      · intro row hrow
        rcases Array.mem_push.mp hrow with hrow_old | rfl
        · have hlt := hw.live_lt row hrow_old
          rw [hnext_toNat]; omega
        · dsimp only
          rw [hid_val, hnext_toNat]; omega
      · intro row hrow
        have hlt := hw.global_lt row hrow
        rw [hnext_toNat]; omega
      · intro row hrow
        have hlt := hw.dead_lt row hrow
        rw [hnext_toNat]; omega

/-- Every primitive scalar type translates to a sized `LayoutData`. -/
theorem IsPrimScalarTy.isSized {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty) :
    (translateTy ty layouts).layout.isSized = true := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
    (try cases it) <;> (try cases ut) <;>
    (simp only [translateTy, scalarLayoutData, Miri.ABI.LayoutData.isSized, hk]; rfl)

/-- `WellTypedScalarOperand` is preserved by `cacheFrameLocalLayout`. -/
theorem WellTypedScalarOperand.cache_layout
    {body : CapturedMir}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedScalarOperand body mf op ty)
    {j : Nat} (hlt : j < mf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    WellTypedScalarOperand body (cacheFrameLocalLayout mf j hlt lay) op ty := by
  cases h with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    exact .constScalar c sc hval hprim hsz hcan hlaysz hbool hchar
  | copyLocal idx decl hdecl hsz_nz himm =>
    exact .copyLocal idx decl hdecl hsz_nz (himm.cache_layout hlt lay)

/-- Scalar operand supported in `LM-2.1` array construction (`Repeat`, `Aggregate`)
and element writes (`writeElem`):
either a `WellTypedScalarOperand` (scalar constant or `copy _s` of an immediate local)
or a destructive `move _s` of an immediate primitive-scalar local. -/
inductive WellTypedLM2_1ScalarOperand
    (body : CapturedMir)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    MirAst.Operand → Ty → Prop where
  | ofScalar {op : MirAst.Operand} {ty : Ty} :
      WellTypedScalarOperand body mf op ty →
      WellTypedLM2_1ScalarOperand body mf op ty
  | moveLocal (idx : Local) (decl : LocalDecl) :
      get? body.localDecls idx = some decl →
      IsPrimScalarTy decl.ty →
      IsImmediateFrameLocal mf idx →
      WellTypedLM2_1ScalarOperand body mf (.move ⟨idx, .nil⟩) decl.ty

/-- Extract the moved unprojected local from a `MirAst.Operand`, if any. -/
def movedScalarLocal? : MirAst.Operand → Option Local
  | .move ⟨idx, .nil⟩ => some idx
  | _ => none

theorem WellTypedLM2_1ScalarOperand.mono_immediate
    {body : CapturedMir}
    {mf mf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedLM2_1ScalarOperand body mf op ty)
    (hmono : ∀ j, IsImmediateFrameLocal mf j → IsImmediateFrameLocal mf' j) :
    WellTypedLM2_1ScalarOperand body mf' op ty := by
  cases h with
  | ofScalar hs => exact .ofScalar (hs.mono_immediate hmono)
  | moveLocal idx decl hdecl hprim himm =>
    exact .moveLocal idx decl hdecl hprim (hmono idx himm)

theorem WellTypedLM2_1ScalarOperand.cache_layout
    {body : CapturedMir}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedLM2_1ScalarOperand body mf op ty)
    {j : Nat} (hlt : j < mf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    WellTypedLM2_1ScalarOperand body (cacheFrameLocalLayout mf j hlt lay) op ty :=
  h.mono_immediate fun _ hj => hj.cache_layout hlt lay

/-- Any local declared with a primitive scalar type is distinct from any local
declared with an array type `[elemKind; count]`. -/
theorem primScalarLocal_ne_array_local
    {body : CapturedMir} {dstIdx idx : Local} {dstDecl srcDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hdecl_src : get? body.localDecls idx = some srcDecl)
    (hprim : IsPrimScalarTy srcDecl.ty) :
    idx ≠ dstIdx := by
  intro heq
  subst heq
  rw [hdecl_dst] at hdecl_src
  injection hdecl_src with h_eq
  subst h_eq
  rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
    (rw [hwf.arr_kind] at hk; nomatch hk)

/-- Public mirror of `Miri.Interpreter.aggregateLift` (`private` in `Aggregate.lean`). -/
def aggregateLiftPub {S A : Type} (value : Except Miri.Interpreter.StepError A) :
    Miri.Interpreter.RvalueM S A :=
  match value with
  | .ok value => pure value
  | .error error => throw error

theorem evalRvalueIntoPlace_repeat_def {P S C V : Type}
    (h : Miri.Interpreter.RvalueHooks P S C V) (choice : C)
    (operand : Miri.MIR.Operand) (count : Miri.MIR.TypeConst) (place : Miri.MIR.Place) :
    Miri.Interpreter.evalRvalueIntoPlace h choice (.Repeat operand count) place =
      (do
        let dest ← h.evalPlace choice place true
        h.writeRepeat choice operand dest) := rfl

theorem evalRvalueIntoPlace_aggregate_def {P S C V : Type}
    (h : Miri.Interpreter.RvalueHooks P S C V) (choice : C)
    (kind : Miri.MIR.AggregateKind) (operands : Array Miri.MIR.Operand) (place : Miri.MIR.Place) :
    Miri.Interpreter.evalRvalueIntoPlace h choice (.Aggregate kind operands) place =
      (do
        let dest ← h.evalPlace choice place true
        h.writeAggregate choice kind operands dest) := rfl

theorem writeRepeat_def {P S C V : Type}
    (h : Miri.Interpreter.AggregateHooks P S C V) (choice : C)
    (operand : Miri.MIR.Operand) (dest : V) :
    Miri.Interpreter.writeRepeat h choice operand dest =
      (do
        let source ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.rvalue "operand") operand none
        if !source.layout.layout.isSized then throw (.invalidProgram "repeat source is unsized")
        let dest ← h.forceAllocation choice dest
        let length ← h.length choice dest
        if length == 0 then
          h.getPlaceAllocMut choice dest
        else
          let first ← h.projectIndex choice dest 0
          h.copyOp choice source first
          let elemSize := (h.placeLayout first).layout.size
          let firstPtr ← aggregateLiftPub (h.placePointer first)
          let restPtr ← aggregateLiftPub (h.wrappingOffset firstPtr elemSize)
          h.memCopyRepeatedly choice firstPtr restPtr elemSize (length - 1) true) := rfl

/-- `annealEnsureAllocated` on a `.dead` destination local raises
`StepError.undefinedBehavior "write to dead local"`. -/
theorem annealEnsureAllocated_dead
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity} {lay : Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hdead : (tf.locals[dstIdx]'hlt).value = .dead) :
    annealEnsureAllocated ⟨.local 0 dstIdx none id, lay⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  have hgop : tf.getLocalOperand dstIdx = .error (.localExpectedLive dstIdx) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hdead, bind, Except.bind, pure, Except.pure, Except.mapError]
  unfold annealEnsureAllocated
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, hframes, Array.size, List.length_singleton,
    Nat.sub_self, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hgop]
  rfl

/-- Set local `idx` of frame `tf` to `.live (.indirect mp)`, preserving its cached layout. -/
def setFrameLocalIndirect
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (idx : Nat) (hlt : idx < tf.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { tf with
    locals := tf.locals.set idx
      { tf.locals[idx]'hlt with value := .live (.indirect mp) } hlt }

theorem IsImmediateFrameLocal.setFrameLocalIndirect_ne
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx idx : Nat} (hlt : dstIdx < tf.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (hne : idx ≠ dstIdx)
    (h : IsImmediateFrameLocal tf idx) :
    IsImmediateFrameLocal (setFrameLocalIndirect tf dstIdx hlt mp) idx := by
  intro mls hmls
  dsimp only [setFrameLocalIndirect] at hmls
  rw [Array.getElem?_set_ne _ hne.symm] at hmls
  exact h mls hmls

/-- `annealEnsureAllocated` on an `.immediate` destination local allocates a
fresh zeroed mutable stack allocation satisfying `ArraySliceRel elemKind 0`. -/
theorem annealEnsureAllocated_immediate
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity} {imm : Miri.Interpreter.Immediate AnnealProv}
    {arrTy : Ty} {layouts : LayoutTable} {elemKind : RigidTy}
    {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (himm : (tf.locals[dstIdx]'hlt).value = .live (.immediate imm))
    (hres : m.machine.memory.reserveAllocId = (mem', .ok allocId)) :
    let lay := translateTy arrTy layouts
    ∃ alloc₀ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      annealEnsureAllocated ⟨.local 0 dstIdx none id, lay⟩ m =
        .ok (stackAllocPlace allocId)
          { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt (stackAllocPlace allocId)]⟩,
            machine := stackAllocMachine m.machine mem' allocId alloc₀ } ∧
      alloc₀.byteSize = lay.layout.size ∧
      alloc₀.align = lay.layout.align.abi ∧
      alloc₀.mutability = .Mut ∧
      alloc₀.initializationMask = Miri.Memory.InitMask.new lay.layout.size true ∧
      ArraySliceRel elemKind 0 layouts [] Miri.ABI.Size.ZERO alloc₀ := by
  dsimp only
  let lay := translateTy arrTy layouts
  have hgop : tf.getLocalOperand dstIdx = .ok (.immediate imm) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, himm, bind, Except.bind, pure, Except.pure, Except.mapError]
  obtain ⟨a, hfrom, _, _, _, _, _, _, hwith⟩ :=
    fromBytes_replicate_zero_spec lay.layout.size lay.layout.align.abi
      (translateTy_align_pow2_le_29 arrTy layouts)
  dsimp only [lay] at hfrom
  obtain ⟨hbs, hlen, halign, hmut, hprov, hmask⟩ :=
    hwith (none : Option Miri.TreeBorrows.BorrowTree)
  refine ⟨a.withExtra none, ?_, hbs, halign, hmut, hmask,
    ArraySliceRel.nil elemKind layouts (by simp [Miri.ABI.Size.ZERO])
      (by rw [hbs]; exact hlen) hmut hprov (by rw [hbs]; exact hmask)⟩
  rcases m with ⟨⟨frames⟩, machine⟩
  dsimp only at hframes hres
  subst hframes
  have hsz1 : (#[tf]).size = 1 := rfl
  unfold annealEnsureAllocated setFrameLocalIndirect
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, hsz1, Nat.sub_self,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hgop, hfrom, hres, frame_replaceLocalValue_of_lt tf dstIdx hlt,
    Nat.zero_lt_one, ↓reduceDIte, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]
  rfl

/-- `annealEnsureAllocated` on a memory-backed (`.indirect`) destination local
returns its `MemPlace` without modifying the state, mirroring
`Miri.Interpreter.forceAllocation`. -/
theorem annealEnsureAllocated_indirect
    {st : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity} {lay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hframes : st.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : (tf.locals[dstIdx]'hlt).value = .live (.indirect mp)) :
    annealEnsureAllocated ⟨.local 0 dstIdx none id, lay⟩ st = .ok mp st := by
  have hgop : tf.getLocalOperand dstIdx = .ok (.indirect mp) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hind, bind, Except.bind, pure, Except.pure, Except.mapError]
  unfold annealEnsureAllocated
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton st.stack tf hframes, hframes, Array.size, List.length_singleton,
    Nat.sub_self, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hgop]
  rfl

/-- Once `dstIdx` holds `.live (.indirect (stackAllocPlace allocId))`,
`annealEnsureAllocated` returns `stackAllocPlace allocId` without modifying the state. -/
theorem annealEnsureAllocated_stackAlloc_idempotent
    {mach : AnnealMachine} {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity} {lay : Miri.Interpreter.LocalLayout}
    (hlt : dstIdx < tf.locals.size)
    (hind : (tf.locals[dstIdx]'hlt).value = .live (.indirect (stackAllocPlace allocId))) :
    let st : AnnealStepState :=
      { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc }
    annealEnsureAllocated ⟨.local 0 dstIdx none id, lay⟩ st =
      .ok (stackAllocPlace allocId) st :=
  annealEnsureAllocated_indirect rfl hlt hind

/-- `MemoryAllocDisjoint` is preserved by memoizing a local's layout via `cacheFrameLocalLayout`. -/
theorem MemoryAllocDisjoint.cache_layout
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MemoryAllocDisjoint tf)
    {idx : Nat} (hlt : idx < tf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    MemoryAllocDisjoint (cacheFrameLocalLayout tf idx hlt lay) := by
  apply MemoryAllocDisjoint.mono_layout hdisj
  intro k
  by_cases hk : k = idx
  · subst hk
    exists lay
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    simp only [↓reduceIte, Array.getElem?_eq_getElem hlt]
    rfl
  · exists (tf.locals[k]?).bind (fun x => x.layout)
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ (Ne.symm hk)]
    cases tf.locals[k]? <;> rfl

/-- `Array`-level lookup and in-place update under `LiveAllocsNodup`. -/
theorem array_findIdx?_of_nodup_fst
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {allocId : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hlive : (allocId, localAlloc) ∈ mach.memory.live.toList) :
    ∃ allocIdx : Nat,
      allocIdx < mach.memory.live.size ∧
      mach.memory.live.findIdx? (fun (k, _) => k == allocId) = some allocIdx ∧
      mach.memory.live[allocIdx]? = some (allocId, localAlloc) ∧
      ∀ localAlloc' :
          Miri.Memory.LocalAllocation
            AnnealProv
            (Option Miri.TreeBorrows.BorrowTree)
            Miri.Memory.MiriMemoryKind,
        let live' := mach.memory.live.set! allocIdx (allocId, localAlloc')
        (live'.toList.map Prod.fst).Nodup ∧
        (allocId, localAlloc') ∈ live'.toList ∧
        ∀ id' la', id' ≠ allocId → (id', la') ∈ mach.memory.live.toList →
          (id', la') ∈ live'.toList := by
  obtain ⟨idx, hlt_l, hfind_l, hget_l, hset_l⟩ := list_findIdx?_of_nodup_fst hnodup hlive
  have hlt : idx < mach.memory.live.size := by simpa using hlt_l
  refine ⟨idx, hlt, ?_, ?_, fun localAlloc' => ?_⟩
  · rw [Array.findIdx?_eq_some_iff_getElem]
    obtain ⟨_, hp_idx, hp_lt⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind_l
    exact ⟨hlt, by simpa using hp_idx, fun j hj => by simpa using hp_lt j hj⟩
  · simpa [Array.getElem?_toList] using hget_l
  · dsimp only
    have hset_eq : mach.memory.live.set! idx (allocId, localAlloc') =
        mach.memory.live.set idx (allocId, localAlloc') hlt := by
      rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
      simp [hlt]
    rw [hset_eq, Array.toList_set]
    exact hset_l localAlloc'

theorem WellTypedScalarOperand.ne_array_local
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx idx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedScalarOperand body tf (.copy ⟨idx, .nil⟩) { kind := elemKind, layoutIdx := 0 }) :
    idx ≠ dstIdx := by
  intro heq
  subst heq
  generalize helemTy : ({ kind := elemKind, layoutIdx := 0 } : Ty) = elemTy at hop
  cases hop with
  | copyLocal _ decl hdecl _ _ =>
    rw [hdecl_dst] at hdecl
    injection hdecl with hdecl_eq
    have hkind : dstDecl.ty.kind = elemKind := by
      rw [hdecl_eq, ← helemTy]
    rw [hwf.arr_kind] at hkind
    rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
      (dsimp only at hk; rw [hk] at hkind; nomatch hkind)

theorem WellTypedScalarOperand.evalOperand_locals_eq
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty} {locals locals' : List LocalSlot}
    {globals : List CapturedAllocation} {v : Value}
    (hop : WellTypedScalarOperand body tf op ty)
    (heval : evalOperand locals op .nil globals body.layouts .nil = .ok v locals') :
    locals' = locals := by
  cases hop with
  | constScalar c sc hval _ _ _ _ _ _ =>
    unfold evalOperand at heval; dsimp only at heval; rw [hval] at heval
    injection heval with _ hloc
    exact hloc.symm
  | copyLocal idx decl _ _ _ =>
    unfold evalOperand at heval; dsimp only at heval
    cases hget : get? locals idx with
    | none => simp [hget] at heval
    | some slot =>
      cases slot with
      | dead | uninit => simp [hget] at heval
      | init val =>
        simp [hget, readProjectedValue] at heval
        exact heval.2.symm

/-- Evaluating a `WellTypedScalarOperand` of element type `{ kind := elemKind, layoutIdx := 0 }`
preserves `tf.locals[arrIdx]?` (since `arrIdx` has array type `[elemKind; count]`). -/
theorem evalScalarOperand_preserves_array_local
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdisj : MemoryAllocDisjoint tf)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    let m : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf',
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩
          { stack := ⟨#[tf']⟩, machine := mach } ∧
      tf'.locals[arrIdx]? = tf.locals[arrIdx]? ∧
      FrameRel body mach af tf' ∧
      MemoryAllocDisjoint tf' ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy elemTy body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  intro m elemTy
  have hsim := evalOperand_scalar_simulation (m := m) rfl hframe hop globals known
  generalize heval_a :
    evalOperand af.locals op .nil globals body.layouts .nil = res_a at hsim
  generalize heval_m :
    (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
      annealReadImmediate) m = res_m at hsim
  cases hsim with
  | ub m' msg =>
    exact Or.inl ⟨rfl, m', msg, rfl⟩
  | ok v locals₁ tf' imm hframe' himm hmono' htf'_eq hdisj_imp =>
    have hloc_eq := hop.evalOperand_locals_eq heval_a
    subst hloc_eq
    obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, hchar⟩ := himm.of_primitive_scalar hprim
    have harr_eq : tf'.locals[arrIdx]? = tf.locals[arrIdx]? := by
      generalize helem : ({ kind := elemKind, layoutIdx := 0 } : Ty) = eTy at hop
      cases hop with
      | constScalar c sc_c hval hprim_c hsz_c hcan_c _ _ _ =>
        obtain ⟨msc_c, htry_c, _⟩ := tryFromUInt_of_valid_canonical hsz_c hcan_c
        have heval_c : annealEvalOperand body.localDecls body.layouts
            (translateOperand (.constant c)) known m =
            .ok ⟨.immediate (.scalar (.fromScalarInt msc_c)), translateTy c.ty body.layouts⟩ m := by
          with_unfolding_all
            unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
            dsimp only
            rw [hval]
            simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
              EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
              stack_currentFrame?_singleton m.stack tf rfl, Option.isNone_some,
              Bool.false_eq_true, ↓reduceIte, htry_c, hprim_c.layoutOfEncoded]
        rw [EStateM.bind_eq_ok heval_c] at heval_m
        dsimp only [annealReadImmediate, pure, EStateM.pure] at heval_m
        injection heval_m with _ hm_eq
        have htf : tf' = tf := by simpa [m] using hm_eq.symm
        rw [htf]
      | copyLocal srcIdx decl_s hdecl_s hsz_nz himm_s =>
        have hop_s : WellTypedScalarOperand body tf (.copy ⟨srcIdx, .nil⟩) decl_s.ty :=
          .copyLocal srcIdx decl_s hdecl_s hsz_nz himm_s
        rw [← helem] at hop_s
        have hne : srcIdx ≠ arrIdx := hop_s.ne_array_local hdecl_arr hwf hprim
        obtain ⟨_, mls_s, _, hlt_s, _, hmls_s, hmls_s_eq, hloc_s⟩ := hframe.lookup_local hdecl_s
        dsimp only [translateOperand, translatePlace, List.map, List.toArray] at heval_m
        cases hloc_s with
        | dead cl hcl =>
          have hd_err := annealEvalOperand_copy_dead (m := m) (topFrame := tf) (known := known)
            rfl hlt_s hdecl_s hmls_s_eq hcl
          rw [EStateM.bind_eq_error hd_err] at heval_m
          cases heval_m
        | indirect _ mp_s _ _ _ _ =>
          exact absurd rfl (himm_s _ hmls_s mp_s)
        | immediate _ imm_s cl hcl hval_s =>
          have hlive_s := annealEvalOperand_copy_live (m := m) (topFrame := tf) (known := known)
            rfl hlt_s hdecl_s hmls_s_eq hcl
          rw [EStateM.bind_eq_ok hlive_s] at heval_m
          rcases hval_s with ⟨_, rfl⟩ | ⟨v_s, rfl, himm_vs⟩
          · dsimp only [annealReadImmediate, throw, throwThe, MonadExceptOf.throw,
              EStateM.throw] at heval_m
            cases heval_m
          · obtain ⟨hread_s, _⟩ := annealReadImmediate_of_immediateRel himm_vs hsz_nz
              (translateTy decl_s.ty body.layouts)
              { m with stack := ⟨#[cacheFrameLocalLayout tf srcIdx hlt_s (translateTy decl_s.ty body.layouts)]⟩ }
            rw [hread_s] at heval_m
            injection heval_m with _ hm_eq
            have htf : tf' = cacheFrameLocalLayout tf srcIdx hlt_s (translateTy decl_s.ty body.layouts) := by
              simpa [m] using hm_eq.symm
            rw [htf]
            unfold cacheFrameLocalLayout
            rw [Array.getElem?_set]
            simp [hne]
    exact Or.inr ⟨sc, msc, tf', rfl, rfl, harr_eq, hframe', hdisj_imp hdisj, hmono', htf'_eq,
      hrel, hsz, hbool, hchar⟩

/-- Evaluating a `WellTypedLM2_1ScalarOperand` (constant, `copy`, or destructive `move`)
of element type `{ kind := elemKind, layoutIdx := 0 }` preserves `tf.locals[arrIdx]?`
and `get? af.locals arrIdx` (since `arrIdx` has array type `[elemKind; count]`),
advancing `af.locals` to `locals₁` (deinitializing `srcIdx` on `move _srcIdx`). -/
theorem evalLM2_1ScalarOperand_preserves_array_local
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdisj : MemoryAllocDisjoint tf)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedLM2_1ScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    let m : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc locals₁ tf',
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) locals₁ ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩
          { stack := ⟨#[tf']⟩, machine := mach } ∧
      get? locals₁ arrIdx = get? af.locals arrIdx ∧
      (∀ j, movedScalarLocal? op ≠ some j → get? locals₁ j = get? af.locals j) ∧
      locals₁.length = af.locals.length ∧
      tf'.locals[arrIdx]? = tf.locals[arrIdx]? ∧
      FrameRel body mach { af with locals := locals₁ } tf' ∧
      MemoryAllocDisjoint tf' ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy elemTy body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  intro m elemTy
  have hop' : ∃ eTy, eTy = ({ kind := elemKind, layoutIdx := 0 } : Ty) ∧
      WellTypedLM2_1ScalarOperand body tf op eTy := ⟨_, rfl, hop⟩
  rcases hop' with ⟨eTy, helem, hop_gen⟩
  cases hop_gen with
  | ofScalar hop_s =>
    subst helem
    rcases evalScalarOperand_preserves_array_local hframe hdisj hdecl_arr hwf hprim hop_s
        globals known with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, tf', ha_ok, hm_ok, harr_eq, hframe', hdisj', hmono', htf'_eq,
        hrel, hsz, hbool, hchar⟩
    · exact Or.inl ⟨ha_ub, m', msg, hm_err⟩
    · exact Or.inr ⟨sc, msc, af.locals, tf', ha_ok, hm_ok, rfl, fun _ _ => rfl, rfl,
        harr_eq, hframe', hdisj', hmono', htf'_eq, hrel, hsz, hbool, hchar⟩
  | moveLocal srcIdx srcDecl hdecl_src hprim_src himm_src =>
    have hne : srcIdx ≠ arrIdx := primScalarLocal_ne_array_local hdecl_arr hwf hdecl_src hprim_src
    obtain ⟨slot, mls, hlt_af, hlt_src, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl_src
    cases hloc with
    | dead _ hcache =>
      left
      have hdead := annealEvalOperand_move_dead (m := m) (topFrame := tf) (known := known)
        rfl hlt_src hdecl_src hmls_eq (fun l hl => hcache l hl)
      refine ⟨by simp [evalOperand, hslot],
        { m with stack := ⟨#[cacheFrameLocalLayout tf srcIdx hlt_src (translateTy srcDecl.ty body.layouts)]⟩ },
        "read of dead local", ?_⟩
      dsimp only [translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact absurd rfl (himm_src _ hmls mp')
    | immediate _ imm _ hcache hval =>
      have hlt_src' : srcIdx < (cacheFrameLocalLayout tf srcIdx hlt_src
          (translateTy srcDecl.ty body.layouts)).locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_src
      let tf' := deinitFrameLocal
        (cacheFrameLocalLayout tf srcIdx hlt_src (translateTy srcDecl.ty body.layouts))
        srcIdx hlt_src'
      have hlive := annealEvalOperand_move_live (m := m) (topFrame := tf) (known := known)
        rfl hlt_src hdecl_src hmls_eq (fun l hl => hcache l hl)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot], { m with stack := ⟨#[tf']⟩ },
          "read of uninitialized local", ?_⟩
        dsimp only [translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        have himmRel' : ImmediateRel { kind := elemKind, layoutIdx := 0 } body.layouts v imm :=
          helem ▸ himmRel
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel'.of_primitive_scalar hprim
        obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hprim_src.size_ne_zero
          (translateTy srcDecl.ty body.layouts) { m with stack := ⟨#[tf']⟩ }
        have ha_ok : evalOperand af.locals (.move ⟨srcIdx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) (af.locals.set srcIdx .uninit) := by
          simp [evalOperand, hslot, set?_eq_some_set hlt_af]
        have hm_ok : (annealEvalOperand body.localDecls body.layouts
            (translateOperand (.move ⟨srcIdx, .nil⟩)) known >>= annealReadImmediate) m =
            .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩
              { stack := ⟨#[tf']⟩, machine := mach } := by
          dsimp only [translateOperand, translatePlace, List.map, List.toArray, elemTy]
          rw [EStateM.bind_eq_ok hlive, hread, helem]
        have hget_arr : get? (af.locals.set srcIdx .uninit) arrIdx = get? af.locals arrIdx := by
          simp only [get?_eq_getElem?, List.getElem?_set, hne, ↓reduceIte]
        have hget_other : ∀ j, movedScalarLocal? (.move ⟨srcIdx, .nil⟩) ≠ some j →
            get? (af.locals.set srcIdx .uninit) j = get? af.locals j := by
          intro j hj
          have hne_j : srcIdx ≠ j := fun h => hj (by simp [movedScalarLocal?, h])
          simp only [get?_eq_getElem?, List.getElem?_set, hne_j, ↓reduceIte]
        have harr_tf : tf'.locals[arrIdx]? = tf.locals[arrIdx]? := by
          simp only [tf', deinitFrameLocal, cacheFrameLocalLayout, Array.getElem?_set, hne, ↓reduceIte]
        have hnew : LocalRel mach srcDecl body.layouts .uninit
            { (cacheFrameLocalLayout tf srcIdx hlt_src
                (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src' with
              value := .live (.immediate .uninit) } := by
          have hlay : ((cacheFrameLocalLayout tf srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src').layout =
              some (translateTy srcDecl.ty body.layouts) := by
            simp [cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        have hframe' : FrameRel body mach { af with locals := af.locals.set srcIdx .uninit } tf' :=
          (hframe.cache_local_layout hdecl_src hlt_src).update_local hdecl_src .uninit
            (.live (.immediate .uninit)) hnew
        have hdisj' : MemoryAllocDisjoint tf' := by
          apply MemoryAllocDisjoint.mono_immediate (tf := cacheFrameLocalLayout tf srcIdx hlt_src
            (translateTy srcDecl.ty body.layouts)) (hdisj.cache_layout hlt_src _)
          intro k
          by_cases hk : k = srcIdx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy srcDecl.ty body.layouts), by
              simp [tf', deinitFrameLocal, cacheFrameLocalLayout]⟩
          · left
            simp [tf', deinitFrameLocal, Array.getElem?_set_ne _ (Ne.symm hk)]
        have hmono' : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j :=
          fun j hj => ((hj.cache_layout hlt_src _).set_immediate hlt_src' .uninit)
        exact ⟨sc, msc, af.locals.set srcIdx .uninit, tf', ha_ok, hm_ok,
          hget_arr, hget_other, List.length_set, harr_tf, hframe', hdisj', hmono', rfl,
          hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩

/-- Destination local readiness for array construction (`Repeat` or `Aggregate`):
- `dstIdx` is `.dead` (both Anneal and `lean-miri` raise UB),
- `dstIdx` is immediate (`IsImmediateFrameLocal`) and `CanReserveAllocId` holds
  (`lean-miri` allocates a fresh stack allocation via `annealEnsureAllocated`), or
- `dstIdx` already holds `.init (.aggregate 0 oldElems)` (`lean-miri` reuses the
  existing `.indirect mp` allocation in place without reserving a new `AllocId`).

An uninitialized memory-backed destination is not covered: writing elements
into an allocation whose mask is not the lazy all-initialized mask materializes
the mask, which `ArraySliceRel` does not describe. Abstract multi-allocation
chains discharge `CanReserveAllocId` from `MemoryHighWater.canReserveAllocId`,
propagated across every step via `StepPreservesHighWater`. -/
def ArrayConstructDestReady
    (s : MachineState) (m : AnnealStepState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (dstIdx : Local) : Prop :=
  get? s.frame.locals dstIdx = some .dead ∨
  (IsImmediateFrameLocal topFrame dstIdx ∧ CanReserveAllocId m.machine.memory) ∨
  ∃ oldElems, get? s.frame.locals dstIdx = some (.init (.aggregate 0 oldElems))

/-- Machine state obtained by updating the existing live allocation at `allocIdx`
in `mach.memory.live` to `(allocId, ⟨kind, alloc⟩)` in place. -/
def inplaceMachine (mach : AnnealMachine) (allocIdx : Nat) (allocId : Miri.Memory.AllocId)
    (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealMachine :=
  { mach with
    memory :=
      { mach.memory with
        live := mach.memory.live.set! allocIdx (allocId, ⟨kind, alloc⟩) } }

/-- Updating an existing live allocation in place (`inplaceMachine`) preserves
`MemoryHighWater` without advancing `nextAllocId`. -/
theorem MemoryHighWater.inplaceMachine
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {la₀ : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hw : MemoryHighWater mach.memory)
    (hlive₀ : (allocId, la₀) ∈ mach.memory.live.toList) :
    MemoryHighWater
      (_root_.LeanMiriSpec.Correspondence.inplaceMachine mach allocIdx allocId kind alloc).memory ∧
    (_root_.LeanMiriSpec.Correspondence.inplaceMachine mach allocIdx allocId kind alloc).memory.nextAllocId =
      mach.memory.nextAllocId := by
  have hid_lt : allocId.value.toNat < mach.memory.nextAllocId.toNat :=
    hw.live_lt (allocId, la₀) (Array.mem_def.mpr hlive₀)
  refine ⟨⟨hw.available, hw.nonzero, hw.sourceInactive, hw.issued_lt, ?_, hw.global_lt, hw.dead_lt⟩, rfl⟩
  intro row hmem
  dsimp only [_root_.LeanMiriSpec.Correspondence.inplaceMachine] at hmem
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds] at hmem
  by_cases hlt : allocIdx < mach.memory.live.size
  · simp only [hlt, ↓reduceDIte] at hmem
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hmem
    rw [Array.getElem_set]
    split
    · exact hid_lt
    · exact hw.live_lt _ (Array.getElem_mem _)
  · simp only [hlt, ↓reduceDIte] at hmem
    exact hw.live_lt row hmem

theorem inplaceMachine_self
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc₀ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hget : mach.memory.live[allocIdx]? = some (allocId, ⟨kind, alloc₀⟩)) :
    inplaceMachine mach allocIdx allocId kind alloc₀ = mach := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hget
  rcases mach with ⟨⟨live, dead, nextId, issued, globals⟩, addr, bt⟩
  dsimp only [inplaceMachine] at hlt heq ⊢
  congr 2
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  simp only [hlt, ↓reduceDIte]
  apply Array.ext
  · simp
  · intro i hi₁ hi₂
    rw [Array.getElem_set]
    split
    · rename_i h; subst h; exact heq.symm
    · rfl

theorem array_set!_idem {α : Type} (arr : Array α) (idx : Nat) (x y : α) :
    (arr.set! idx x).set! idx y = arr.set! idx y := by
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  by_cases h : idx < arr.size
  · have h' : idx < (arr.set idx x h).size := by simp [h]
    simp only [h, h', ↓reduceDIte]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_set]
      split <;> rfl
  · simp [h]

theorem inplaceMachine_findIdx?
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hfind : mach.memory.live.findIdx? (fun (k, _) => k == allocId) = some allocIdx) :
    (inplaceMachine mach allocIdx allocId kind alloc).memory.live.findIdx?
      (fun (k, _) => k == allocId) = some allocIdx := by
  obtain ⟨hlt, _, hp_lt⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfind
  dsimp only [inplaceMachine]
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  simp only [hlt, ↓reduceDIte]
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by simp [hlt], by simp, fun j hj => ?_⟩
  rw [Array.getElem_set]
  simp [Nat.ne_of_gt hj, hp_lt j hj]

theorem inplaceMachine_getElem?
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hlt : allocIdx < mach.memory.live.size) :
    (inplaceMachine mach allocIdx allocId kind alloc).memory.live[allocIdx]? =
      some (allocId, ⟨kind, alloc⟩) := by
  dsimp only [inplaceMachine]
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  simp [hlt]

/-- Writing `.scalar (.fromScalarInt msc)` to element `k` of `stackAllocPlace allocId`
in `stackAllocMachine mach mem' allocId alloc` appends `.scalar sc` to `ArraySliceRel`. -/
theorem annealWriteImmediate_stackAlloc_snoc
    {mach : AnnealMachine} {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {elemKind : RigidTy} {k : Nat} {layouts : LayoutTable} {elems : List Value}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {destLay : Miri.Interpreter.LocalLayout}
    (hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false)
    (hslice : ArraySliceRel elemKind k layouts elems Miri.ABI.Size.ZERO alloc)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hin :
      (k + 1) * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat ≤
        alloc.byteSize.bytes.toNat) :
    let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))
    let mp_k : Miri.Interpreter.MemPlace AnnealProv :=
      { (stackAllocPlace allocId) with
        ptr := { (stackAllocPlace allocId).ptr with
          offset := Miri.ABI.Size.ofBytes ((stackAllocPlace allocId).ptr.offset.bytes + elemOff.bytes) } }
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      annealWriteImmediate (.scalar (.fromScalarInt msc)) ⟨.memory mp_k, destLay⟩
        { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc } =
        .ok () { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc' } ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true ∧
      ArraySliceRel elemKind (k + 1) layouts (elems ++ [.scalar sc]) Miri.ABI.Size.ZERO alloc' := by
  dsimp only
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  have hin0 : Miri.ABI.Size.ZERO.bytes.toNat + (k + 1) * elemSize.bytes.toNat ≤
      alloc.byteSize.bytes.toNat := by
    simpa [Miri.ABI.Size.ZERO] using hin
  obtain ⟨alloc', hwrite, hbyteSize, halign, hmask, hslice'⟩ :=
    hslice.writeScalar_snoc hrel hsz hbool hchar hslice.alloc_mask hin0
  have hbase := lookupBaseAddr_stackAllocMachine_self mach mem' allocId alloc
  have hidx := findIdx?_push_fresh mem'.live allocId
    ({ kind := .stack, allocation := alloc } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine mach mem' allocId alloc).memory.live =
      mem'.live.push (allocId, ⟨.stack, alloc⟩) := rfl
  have hoff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId)).bytes +
            (Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))).bytes)).bytes -
        annealStackBaseAddr allocId) =
      Miri.ABI.Size.ofBytes
        (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (k * elemSize.bytes.toNat)) := by
    simp only [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, uint64_add_sub_cancel_left,
      UInt64.zero_add]
  dsimp only [elemSize] at hoff
  have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size := rfl
  refine ⟨alloc', ?_, hbyteSize, halign, hmask, hslice'⟩
  unfold annealWriteImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, stackAllocPlace, Option.bind,
    Miri.Memory.Provenance.getAllocId, hbase, hlive, hidx, Array.getElem?_push_size,
    hoff, hmsc_sz, hwrite, pure, set, MonadStateOf.set, EStateM.set, array_push_set!_size]
  rfl

/-- Writing `.scalar (.fromScalarInt msc)` to element `k` of an existing indirect
array place `mp` in `inplaceMachine mach allocIdx allocId kind alloc` appends
`.scalar sc` to `ArraySliceRel` at arbitrary `relOffset`. -/
theorem annealWriteImmediate_inplace_snoc
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {elemKind : RigidTy} {k : Nat} {layouts : LayoutTable} {elems : List Value}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {destLay : Miri.Interpreter.LocalLayout}
    (hlt_idx : allocIdx < mach.memory.live.size)
    (hfind : mach.memory.live.findIdx? (fun (id, _) => id == allocId) = some allocIdx)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : mach.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
    (hslice : ArraySliceRel elemKind k layouts elems relOffset alloc)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hin :
      relOffset.bytes.toNat +
        (k + 1) * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat ≤
        alloc.byteSize.bytes.toNat) :
    let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))
    let mp_k : Miri.Interpreter.MemPlace AnnealProv :=
      { mp with
        ptr := { mp.ptr with
          offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) } }
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      annealWriteImmediate (.scalar (.fromScalarInt msc)) ⟨.memory mp_k, destLay⟩
        { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc } =
        .ok () { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc' } ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = Miri.Memory.InitMask.new alloc.byteSize true ∧
      ArraySliceRel elemKind (k + 1) layouts (elems ++ [.scalar sc]) relOffset alloc' := by
  dsimp only
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
  obtain ⟨alloc', hwrite, hbyteSize, halign, hmask, hslice'⟩ :=
    hslice.writeScalar_snoc hrel hsz hbool hchar hslice.alloc_mask hin
  have hbase_in : (inplaceMachine mach allocIdx allocId kind alloc).lookupBaseAddr allocId =
      some baseAddr := hbase
  have hfind_in := inplaceMachine_findIdx? (kind := kind) alloc hfind
  have hget_in := inplaceMachine_getElem? (allocId := allocId) (kind := kind) alloc hlt_idx
  have hoff :
      Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes
            (mp.ptr.offset.bytes +
              (Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))).bytes)).bytes -
          baseAddr) =
      Miri.ABI.Size.ofBytes
        (relOffset.bytes + UInt64.ofNat (k * elemSize.bytes.toNat)) := by
    have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
    simp only [Miri.ABI.Size.ofBytes, hbytes, uint64_add_add_sub_cancel_left]
  dsimp only [elemSize] at hoff
  have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size := rfl
  refine ⟨alloc', ?_, hbyteSize, halign, hmask, hslice'⟩
  unfold annealWriteImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, hprov, Option.bind_some,
    Miri.Memory.Provenance.getAllocId, hbase_in, hfind_in, hget_in,
    hoff, hmsc_sz, hwrite, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
  dsimp only [inplaceMachine]
  simp only [array_set!_idem]

private def localStateIndirect?
    (s : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    Option (Miri.Interpreter.MemPlace AnnealProv) :=
  match s.value with
  | .live (.indirect mp) => some mp
  | _ => none

/-- Concluding `StepRel` after an array Rvalue (`Repeat` or `Aggregate`) allocates
`(allocId, alloc_final)` satisfying `ArraySliceRel elemKind count` and updates
`dstIdx` to `.live (.indirect (stackAllocPlace allocId))`. Because `allocId` is
fresh, the step also preserves `LiveAllocsNodup`. -/
theorem write_array_after_rvalue_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals₁ : List LocalSlot}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hframe₁ : FrameRel body m.machine { s.frame with locals := locals₁ } topFrame₁)
    (hdisj₁ : MemoryAllocDisjoint topFrame₁)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hlt_mf : dstIdx < topFrame₁.locals.size)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok allocId))
    (hsize_final : alloc_final.byteSize = (translateTy dstDecl.ty body.layouts).layout.size)
    (hslice_final : ArraySliceRel elemKind count body.layouts elems Miri.ABI.Size.ZERO alloc_final)
    (ha_step : evalStmt s stmt body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init (.aggregate 0 elems))) s.memory))
    (hm_step : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      ({ stack := ⟨#[setFrameLocalIndirect topFrame₁ dstIdx hlt_mf (stackAllocPlace allocId)]⟩,
         machine := stackAllocMachine m.machine mem' allocId alloc_final },
       .ok ()))
    (hnodup : LiveAllocsNodup m.machine)
    (hmono : ∀ j, IsImmediateFrameLocal tf₀ j → IsImmediateFrameLocal topFrame₁ j) :
    StepRel body m
      (evalStmt s stmt body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 1
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let topFrame₂ := setFrameLocalIndirect topFrame₁ dstIdx hlt_mf (stackAllocPlace allocId)
  have hloc₂ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    hframe₁.location_eq
  rw [ha_step, miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_step rfl hloc₂]
  refine ⟨StepRel.step _ _ ?_,
    StepPreservesNodup.of_nodup (LiveAllocsNodup.stackAllocMachine alloc_final hnodup hres),
    ?himm,
    fun _ hw hbound => MemoryHighWater.stackAllocMachine alloc_final hw hbound hres⟩
  case himm =>
    intro _ tf tf' htf htf' j hne hj
    rw [hframes] at htf
    have htf_eq : tf = tf₀ := by simpa using htf.symm
    subst htf_eq
    have htf'_eq : tf' = { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
      simpa using htf'.symm
    subst htf'_eq
    exact IsImmediateFrameLocal.setFrameLocalIndirect_ne hlt_mf (stackAllocPlace allocId) hne
      (hmono j hj)
  obtain ⟨hlive, hfreshne, hbase⟩ :=
    stackAllocMachine_live_base (mach := m.machine) alloc_final hres
  have hfr₁' := hframe₁.of_live_base hlive hbase
  obtain ⟨_, mls_dst₁, _, _, _, _, hmls_dst₁_eq, hloc_dst₁⟩ := hframe₁.lookup_local hdecl_dst
  have hmp_rel : MemPlaceRel (stackAllocMachine m.machine mem' allocId alloc_final)
      dstDecl.ty body.layouts (some (.aggregate 0 elems)) (stackAllocPlace allocId) := by
    refine stackAlloc_memPlaceRel hslice_final.alloc_mut
      (translateTy_align_pow2_le_29 dstDecl.ty body.layouts)
      hsize_final
      (fun h => nomatch h)
      (fun _ _ _ => ?_)
      (fun _ h => nomatch h)
      (fun ek cnt es hk hopt => ?_)
    · rw [hslice_final.alloc_mask, hsize_final]
      exact initMask_new_true_isRangeInitialized_inbounds (by simp [Miri.ABI.Size.ZERO])
    · rw [hwf.arr_kind] at hk
      injection hk with hek hcnt
      subst hek hcnt
      injection hopt with hagg
      injection hagg with _ hes
      subst hes
      exact ⟨hwf.arr_fields, hwf.arr_size, hwf.arr_align, hslice_final⟩
  have hloc_new : LocalRel (stackAllocMachine m.machine mem' allocId alloc_final)
      dstDecl body.layouts (.init (.aggregate 0 elems))
      { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.indirect (stackAllocPlace allocId)) } := by
    refine .indirect (.init (.aggregate 0 elems)) (stackAllocPlace allocId)
      (topFrame₁.locals[dstIdx]'hlt_mf).layout
      (by rw [hmls_dst₁_eq]; exact hloc_dst₁.layout_eq)
      nofun
      hmp_rel
  have hfr₂ := hfr₁'.update_local hdecl_dst (.init (.aggregate 0 elems))
    (.live (.indirect (stackAllocPlace allocId))) hloc_new
  obtain ⟨retLay, hretP⟩ := hretPlace
  refine StateRel.mk
    { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    rfl hretCont ⟨retLay, hretP⟩
    ⟨hfr₂.body_eq, rfl, hfr₂.af_locals_len, hfr₂.mf_locals_size, hfr₂.locals_rel⟩
    hcal hstack hbor hprot hcaller ?_
  intro i j mp_i mp_j lay_i lay_j hij hi hj
  dsimp only [topFrame₂, setFrameLocalIndirect] at hi hj
  rw [Array.getElem?_set] at hi hj
  by_cases hi_idx : dstIdx = i
  · subst hi_idx
    have hj_idx : dstIdx ≠ j := hij
    simp only [hj_idx, ↓reduceIte] at hj
    simp only [↓reduceIte] at hi
    obtain ⟨a, la, ha, hla⟩ := hframe₁.indirect_allocId hj
    have hmp_i : mp_i = stackAllocPlace allocId :=
      (Option.some.inj (congrArg (Option.bind · localStateIndirect?) hi)).symm
    subst hmp_i
    rw [ha]
    simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
      Option.some.injEq]
    exact fun h => hfreshne a la hla h.symm
  · simp only [hi_idx, ↓reduceIte] at hi
    by_cases hj_idx : dstIdx = j
    · subst hj_idx
      simp only [↓reduceIte] at hj
      obtain ⟨a, la, ha, hla⟩ := hframe₁.indirect_allocId hi
      have hmp_j : mp_j = stackAllocPlace allocId :=
        (Option.some.inj (congrArg (Option.bind · localStateIndirect?) hj)).symm
      subst hmp_j
      rw [ha]
      simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact hfreshne a la hla
    · simp only [hj_idx, ↓reduceIte] at hj
      exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj

/-- Concluding `StepRel`, `StepPreservesNodup`, and `StepPreservesImmediate` after
an array Rvalue (`Repeat` or `Aggregate`) overwrites an already-allocated indirect
array local `dstIdx` (`mp`) in place (`inplaceMachine`). -/
theorem write_array_inplace_after_rvalue_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals₁ : List LocalSlot}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat} {oldElems elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {cachedLay : Option Miri.Interpreter.LocalLayout}
    {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc₀ alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {bb : BasicBlockData} {stmt : Statement}
    (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body)
    (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hframe₁ : FrameRel body m.machine { s.frame with locals := locals₁ } topFrame₁)
    (hdisj₁ : MemoryAllocDisjoint topFrame₁)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hmls_dst₁ : topFrame₁.locals[dstIdx]? = some ⟨.live (.indirect mp), cachedLay⟩)
    (hcache_dst : ∀ l ∈ cachedLay, l = translateTy dstDecl.ty body.layouts)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hno_ovf : baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
    (haligned : mp.ptr.offset.isAligned (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok true)
    (hin_arr :
      relOffset.bytes.toNat + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
        alloc₀.byteSize.bytes.toNat)
    (hval_cons :
      ∀ v, some (Value.aggregate 0 oldElems) = some v →
        (translateTy dstDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
        alloc₀.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange relOffset (translateTy dstDecl.ty body.layouts).layout.size) =
            Except.ok (Except.ok ()))
    (hmask₀ : alloc₀.initializationMask = Miri.Memory.InitMask.new alloc₀.byteSize true)
    (hsize_final : alloc_final.byteSize = alloc₀.byteSize)
    (hslice_final : ArraySliceRel elemKind count body.layouts elems relOffset alloc_final)
    (hlive₀ :
      (allocId, ({ kind := kind, allocation := alloc₀ } :
        Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)) ∈
        m.machine.memory.live.toList)
    (hnodup' : LiveAllocsNodup (inplaceMachine m.machine allocIdx allocId kind alloc_final))
    (hlive' :
      (allocId, ({ kind := kind, allocation := alloc_final } :
        Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)) ∈
        (inplaceMachine m.machine allocIdx allocId kind alloc_final).memory.live.toList)
    (hother_live :
      ∀ id' la', id' ≠ allocId → (id', la') ∈ m.machine.memory.live.toList →
        (id', la') ∈ (inplaceMachine m.machine allocIdx allocId kind alloc_final).memory.live.toList)
    (ha_step : evalStmt s stmt body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init (.aggregate 0 elems))) s.memory))
    (hm_step : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      ({ stack := ⟨#[topFrame₁]⟩,
         machine := inplaceMachine m.machine allocIdx allocId kind alloc_final },
       .ok ()))
    (hmono : ∀ j, IsImmediateFrameLocal tf₀ j → IsImmediateFrameLocal topFrame₁ j) :
    StepRel body m
      (evalStmt s stmt body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let mach' := inplaceMachine m.machine allocIdx allocId kind alloc_final
  have hloc₁ : topFrame₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    hframe₁.location_eq
  rw [ha_step, miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_step rfl hloc₁]
  refine ⟨StepRel.step _ _ ?_, StepPreservesNodup.of_nodup hnodup', ?himm, ?hhw⟩
  case hhw =>
    intro _ hw _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.inplaceMachine
      (allocIdx := allocIdx) (kind := kind) (alloc := alloc_final) hw hlive₀
    exact ⟨hw', by dsimp only [mach']; rw [hnext]; omega⟩
  case himm =>
    intro _ tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = tf₀ := by simpa using htf.symm
    subst htf_eq
    have htf'_eq : tf' = { topFrame₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
      simpa using htf'.symm
    subst htf'_eq
    exact hmono j hj
  have hmp' : MemPlaceRel mach' dstDecl.ty body.layouts (some (.aggregate 0 elems)) mp := by
    refine .mk allocId tag baseAddr relOffset ⟨kind, alloc_final⟩
      hprov hmis hmeta hlive' hbase hno_ovf hptr hslice_final.alloc_mut haligned
      (by dsimp only; rw [hsize_final]; exact hin_arr)
      (fun h => nomatch h)
      (fun _ _ hnz => by
        dsimp only
        rw [hslice_final.alloc_mask, hsize_final, ← hmask₀]
        exact hval_cons (Value.aggregate 0 oldElems) rfl hnz)
      (fun _ h => nomatch h)
      (fun ek cnt es hk hopt => ?_)
    rw [hwf.arr_kind] at hk
    injection hk with hek hcnt
    subst hek hcnt
    injection hopt with hagg
    injection hagg with _ hes
    subst hes
    exact ⟨hwf.arr_fields, hwf.arr_size, hwf.arr_align, hslice_final⟩
  have hlt_af : dstIdx < locals₁.length := by
    have ⟨hlt_mf, _⟩ := Array.getElem?_eq_some_iff.mp hmls_dst₁
    rw [hframe₁.af_locals_len, ← hframe₁.mf_locals_size]
    exact hlt_mf
  obtain ⟨retLay, hretP⟩ := hretPlace
  refine StateRel.mk
    { topFrame₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    rfl hretCont ⟨retLay, hretP⟩
    ⟨hframe₁.body_eq, rfl,
      by dsimp only [advanceStmt]; rw [List.length_set, hframe₁.af_locals_len],
      hframe₁.mf_locals_size, ?_⟩
    hcal hstack hbor hprot hcaller
    (fun i j mp_i mp_j lay_i lay_j hij hi hj =>
      hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj)
  intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
  dsimp only [advanceStmt] at hslot_i
  rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
  by_cases heq : dstIdx = i
  · subst heq
    simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i
    subst hslot_i
    rw [hdecl_dst] at hdecl_i; injection hdecl_i with hd_eq; subst hd_eq
    rw [hmls_dst₁] at hmls_i; injection hmls_i with hm_eq; subst hm_eq
    exact .indirect (.init (.aggregate 0 elems)) mp cachedLay hcache_dst nofun hmp'
  · simp only [heq, ↓reduceIte] at hslot_i
    have hloc_i := hframe₁.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    cases hloc_i with
    | dead c hc => exact .dead c hc
    | immediate _ imm_i c hc hv => exact .immediate slot_i imm_i c hc hv
    | indirect _ mp_i c hc hnd hmp_i =>
      refine .indirect slot_i mp_i c hc hnd ?_
      cases hmp_i with
      | mk aid_i tag_i baddr_i roff_i la_i hp_i hm_i hmt_i hlv_i hb_i hno_i hpa_i
          hmu_i hal_i hib_i huc_i hvc_i hsc_i hac_i =>
        have hne_id : aid_i ≠ allocId := by
          have hd := hdisj₁ dstIdx i mp mp_i cachedLay c heq hmls_dst₁ hmls_i
          rw [hprov, hp_i] at hd
          simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq] at hd
          exact Ne.symm hd
        exact .mk aid_i tag_i baddr_i roff_i la_i hp_i hm_i hmt_i
          (hother_live aid_i la_i hne_id hlv_i) hb_i hno_i hpa_i
          hmu_i hal_i hib_i huc_i hvc_i hsc_i hac_i

/-- `ScalarRel` uniquely determines the `Miri.Memory.ScalarInt` for a given `MirAst.ScalarInt`. -/
theorem ScalarRel.unique {sc : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (h₁ : ScalarRel sc msc₁) (h₂ : ScalarRel sc msc₂) : msc₁ = msc₂ := by
  cases msc₁; cases msc₂
  have hd := h₁.data_eq.trans h₂.data_eq.symm
  have hs := h₁.size_eq.trans h₂.size_eq.symm
  subst hd hs
  rfl

/-- Execution of the post-allocation body of `writeRepeat` on `stackAllocPlace allocId`:
populates `count` copies of `.scalar sc` and establishes
`ArraySliceRel elemKind count body.layouts (List.replicate count (.scalar sc))`. -/
theorem writeRepeat_after_forceAlloc_spec
    {body : CapturedMir}
    {mach : AnnealMachine} {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {alloc₀ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {srcLay : Miri.Interpreter.LocalLayout}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hsize₀ : alloc₀.byteSize = (translateTy arrTy body.layouts).layout.size)
    (hslice₀ : ArraySliceRel elemKind 0 body.layouts [] Miri.ABI.Size.ZERO alloc₀) :
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory (stackAllocPlace allocId), translateTy arrTy body.layouts⟩
    let source : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.immediate (.scalar (.fromScalarInt msc)), srcLay⟩
    let st₀ : AnnealStepState :=
      { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc₀ }
    ∃ alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      (do
        let length ← h.length () dest
        if length == 0 then
          h.getPlaceAllocMut () dest
        else
          let first ← h.projectIndex () dest 0
          h.copyOp () source first
          let elemSize := (h.placeLayout first).layout.size
          let firstPtr ← aggregateLiftPub (h.placePointer first)
          let restPtr ← aggregateLiftPub (h.wrappingOffset firstPtr elemSize)
          h.memCopyRepeatedly () firstPtr restPtr elemSize (length - 1) true) st₀ =
        .ok () { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc_final } ∧
      alloc_final.byteSize = (translateTy arrTy body.layouts).layout.size ∧
      ArraySliceRel elemKind count body.layouts (List.replicate count (.scalar sc))
        Miri.ABI.Size.ZERO alloc_final := by
  dsimp only
  let h := annealAggregateHooks body.localDecls body.layouts
  let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.memory (stackAllocPlace allocId), translateTy arrTy body.layouts⟩
  let source : Miri.Interpreter.OpTy AnnealProv :=
    ⟨.immediate (.scalar (.fromScalarInt msc)), srcLay⟩
  let st₀ : AnnealStepState :=
    { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc₀ }
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
  have hlen_ok : h.length () dest st₀ = .ok (UInt64.ofNat count) st₀ := by
    dsimp only [h, dest, annealAggregateHooks]
    rw [hwf.arr_fields]
    rfl
  rw [EStateM.bind_eq_ok hlen_ok]
  cases count with
  | zero =>
    refine ⟨alloc₀, rfl, hsize₀, hslice₀⟩
  | succ k =>
    have hcnt_le := hwf.count_lt_two_pow_32
    have hlt64 : k + 1 < 2 ^ 64 := by omega
    have hne0 : (UInt64.ofNat (k + 1) == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro heq
      have htoNat : (UInt64.ofNat (k + 1)).toNat = 0 := by
        rw [beq_iff_eq] at heq; rw [heq]; rfl
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64)] at htoNat
      omega
    simp only [hne0, Bool.false_eq_true, ↓reduceIte]
    let elemOff₀ := Miri.ABI.Size.ofBytes (UInt64.ofNat (0 * elemSize.bytes.toNat))
    let mp₀ : Miri.Interpreter.MemPlace AnnealProv :=
      { (stackAllocPlace allocId) with
        ptr := { (stackAllocPlace allocId).ptr with
          offset := Miri.ABI.Size.ofBytes ((stackAllocPlace allocId).ptr.offset.bytes + elemOff₀.bytes) } }
    let firstPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory mp₀, translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
    have hproj0 : h.projectIndex () dest 0 st₀ = .ok firstPlace st₀ := by
      dsimp only [h, dest, annealAggregateHooks, firstPlace, mp₀, elemOff₀, elemSize]
      rw [hwf.arr_fields]
      dsimp only
      rw [hwf.elem_layout_eq]
      rfl
    rw [EStateM.bind_eq_ok hproj0]
    have hin₁ :
        (0 + 1) * elemSize.bytes.toNat ≤ alloc₀.byteSize.bytes.toNat := by
      rw [hsize₀, hwf.arr_size_toNat]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨alloc₁, hwrite₁, hbs₁, _, hmask₁, hslice₁⟩ :=
      annealWriteImmediate_stackAlloc_snoc (mach := mach) (tf := tf) (k := 0)
        (destLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts)
        hfresh hslice₀ hrel hsz hbool hchar hin₁
    let st₁ : AnnealStepState :=
      { stack := ⟨#[tf]⟩, machine := stackAllocMachine mach mem' allocId alloc₁ }
    have hcopy0 : h.copyOp () source firstPlace st₀ = .ok () st₁ := by
      dsimp only [h, annealAggregateHooks, source]
      exact hwrite₁
    rw [EStateM.bind_eq_ok hcopy0]
    dsimp only [h, annealAggregateHooks, firstPlace, aggregateLiftPub, pure, EStateM.pure,
      bind, EStateM.bind]
    rw [aggregateWrappingOffset_anneal_eq]
    dsimp only [EStateM.pure]
    have hsub1 : UInt64.ofNat (k + 1) - 1 = UInt64.ofNat k := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hk64 : k < 2 ^ 64 := by omega
      rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le]
      · simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64),
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hk64)]
      · rw [UInt64.le_iff_toNat_le]
        simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64)]
    rw [hsub1]
    cases k with
    | zero =>
      exact ⟨alloc₁, rfl, hbs₁.trans hsize₀, hslice₁⟩
    | succ m =>
      have hm64 : m + 1 < 2 ^ 64 := by omega
      have hne0_m : (UInt64.ofNat (m + 1) == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro heq
        have htoNat : (UInt64.ofNat (m + 1)).toNat = 0 := by
          rw [beq_iff_eq] at heq; rw [heq]; rfl
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hm64)] at htoNat
        omega
      have htoNat_m : (UInt64.ofNat (m + 1)).toNat = m + 1 := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hm64)]
      obtain ⟨sc₀, msc₀, hsc₀_eq, _, _, _, hrel₀, hread₀⟩ :=
        hslice₁.elem_rel 0 (Value.scalar sc) rfl
      injection hsc₀_eq with hsc₀_eq'
      subst hsc₀_eq'
      have hmsc₀_eq : msc₀ = msc := hrel₀.unique hrel
      subst hmsc₀_eq
      have hfirstOff_zero :
          Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (0 * elemSize.bytes.toNat)) =
            Miri.ABI.Size.ZERO := by
        simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
      rw [hfirstOff_zero] at hread₀
      have hin_m :
          Miri.ABI.Size.ZERO.bytes.toNat + (1 + (m + 1)) * elemSize.bytes.toNat ≤
            alloc₁.byteSize.bytes.toNat := by
        rw [hbs₁, hsize₀, hwf.arr_size_toNat]
        have : 1 + (m + 1) = m + 1 + 1 := by omega
        rw [this]
        simp [elemSize, Miri.ABI.Size.ZERO]
      obtain ⟨alloc₂, hrep, hbs₂, _, _, hslice₂⟩ :=
        writeScalarRepeatedly_spec (m + 1) hslice₁ hrel hsz hbool hchar
          (by rw [hbs₁]; exact hmask₁) hin_m
      have hbase₁ := lookupBaseAddr_stackAllocMachine_self mach mem' allocId alloc₁
      have hidx₁ := findIdx?_push_fresh mem'.live allocId
        ({ kind := .stack, allocation := alloc₁ } : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
      have hlive₁ : (stackAllocMachine mach mem' allocId alloc₁).memory.live =
          mem'.live.push (allocId, ⟨.stack, alloc₁⟩) := rfl
      have hprov₀ : mp₀.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId := rfl
      have hoff_first :
          Miri.ABI.Size.ofBytes (mp₀.ptr.offset.bytes - annealStackBaseAddr allocId) =
            Miri.ABI.Size.ZERO := by
        dsimp only [mp₀, elemOff₀, stackAllocPlace]
        simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
      have hoff_rest :
          Miri.ABI.Size.ofBytes
            ((Miri.ABI.Size.ofBytes (mp₀.ptr.offset.bytes + elemSize.bytes)).bytes -
              annealStackBaseAddr allocId) =
          Miri.ABI.Size.ofBytes
            (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (1 * elemSize.bytes.toNat)) := by
        dsimp only [mp₀, elemOff₀, stackAllocPlace]
        have h_u0 : UInt64.ofNat 0 = 0 := rfl
        have h_u64 : UInt64.ofNat (1 * elemSize.bytes.toNat) = elemSize.bytes := by
          rw [Nat.one_mul, UInt64.ofNat_toNat]
        simp only [Nat.zero_mul, h_u0, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO,
          UInt64.add_zero, UInt64.zero_add, h_u64, uint64_add_sub_cancel_left]
      dsimp only [elemSize] at hoff_rest hread₀ hrep
      refine ⟨alloc₂, ?_, hbs₂.trans (hbs₁.trans hsize₀), ?_⟩
      · simp only [hne0_m, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
          EStateM.get, EStateM.bind, hprov₀, st₁, hbase₁, hlive₁, hidx₁,
          Array.getElem?_push_size]
        rw [hoff_first, hoff_rest, htoNat_m, hread₀]
        dsimp only [pure, EStateM.pure, EStateM.bind]
        rw [hrep]
        simp only [EStateM.pure, EStateM.bind, set, MonadStateOf.set, EStateM.set,
          array_push_set!_size]
        rfl
      · have hcnt : 1 + (m + 1) = m + 1 + 1 := by omega
        have hlist : [Value.scalar sc] ++ List.replicate (m + 1) (Value.scalar sc) =
            List.replicate (m + 1 + 1) (Value.scalar sc) := rfl
        rw [← hlist, ← hcnt]
        exact hslice₂

/-- Execution of the post-allocation body of `writeRepeat` on an existing indirect
array place `mp` (`inplaceMachine`): populates `count` copies of `.scalar sc` in place
at arbitrary `relOffset` and establishes `ArraySliceRel elemKind count`. -/
theorem writeRepeat_inplace_spec
    {body : CapturedMir}
    {mach : AnnealMachine} {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc₀ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    {srcLay : Miri.Interpreter.LocalLayout}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hlt_idx : allocIdx < mach.memory.live.size)
    (hfind : mach.memory.live.findIdx? (fun (id, _) => id == allocId) = some allocIdx)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : mach.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hin_arr :
      relOffset.bytes.toNat + (translateTy arrTy body.layouts).layout.size.bytes.toNat ≤
        alloc₀.byteSize.bytes.toNat)
    (hslice₀ : ArraySliceRel elemKind 0 body.layouts [] relOffset alloc₀) :
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory mp, translateTy arrTy body.layouts⟩
    let source : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.immediate (.scalar (.fromScalarInt msc)), srcLay⟩
    let st₀ : AnnealStepState :=
      { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc₀ }
    ∃ alloc_final : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      (do
        let length ← h.length () dest
        if length == 0 then
          h.getPlaceAllocMut () dest
        else
          let first ← h.projectIndex () dest 0
          h.copyOp () source first
          let elemSize := (h.placeLayout first).layout.size
          let firstPtr ← aggregateLiftPub (h.placePointer first)
          let restPtr ← aggregateLiftPub (h.wrappingOffset firstPtr elemSize)
          h.memCopyRepeatedly () firstPtr restPtr elemSize (length - 1) true) st₀ =
        .ok () { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc_final } ∧
      alloc_final.byteSize = alloc₀.byteSize ∧
      ArraySliceRel elemKind count body.layouts (List.replicate count (.scalar sc))
        relOffset alloc_final := by
  dsimp only
  let h := annealAggregateHooks body.localDecls body.layouts
  let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.memory mp, translateTy arrTy body.layouts⟩
  let source : Miri.Interpreter.OpTy AnnealProv :=
    ⟨.immediate (.scalar (.fromScalarInt msc)), srcLay⟩
  let st₀ : AnnealStepState :=
    { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc₀ }
  let elemSize := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
  have hlen_ok : h.length () dest st₀ = .ok (UInt64.ofNat count) st₀ := by
    dsimp only [h, dest, annealAggregateHooks]
    rw [hwf.arr_fields]
    rfl
  rw [EStateM.bind_eq_ok hlen_ok]
  cases count with
  | zero =>
    refine ⟨alloc₀, rfl, rfl, hslice₀⟩
  | succ k =>
    have hcnt_le := hwf.count_lt_two_pow_32
    have hlt64 : k + 1 < 2 ^ 64 := by omega
    have hne0 : (UInt64.ofNat (k + 1) == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro heq
      have htoNat : (UInt64.ofNat (k + 1)).toNat = 0 := by
        rw [beq_iff_eq] at heq; rw [heq]; rfl
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64)] at htoNat
      omega
    simp only [hne0, Bool.false_eq_true, ↓reduceIte]
    let elemOff₀ := Miri.ABI.Size.ofBytes (UInt64.ofNat (0 * elemSize.bytes.toNat))
    let mp₀ : Miri.Interpreter.MemPlace AnnealProv :=
      { mp with
        ptr := { mp.ptr with
          offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff₀.bytes) } }
    let firstPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory mp₀, translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
    have hproj0 : h.projectIndex () dest 0 st₀ = .ok firstPlace st₀ := by
      dsimp only [h, dest, annealAggregateHooks, firstPlace, mp₀, elemOff₀, elemSize]
      rw [hwf.arr_fields]
      dsimp only
      rw [hwf.elem_layout_eq]
      rfl
    rw [EStateM.bind_eq_ok hproj0]
    have hin₁ :
        relOffset.bytes.toNat + (0 + 1) * elemSize.bytes.toNat ≤ alloc₀.byteSize.bytes.toNat := by
      rw [hwf.arr_size_toNat] at hin_arr
      have hle : (0 + 1) * elemSize.bytes.toNat ≤ (k + 1) * elemSize.bytes.toNat :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [elemSize] at hle ⊢
      omega
    obtain ⟨alloc₁, hwrite₁, hbs₁, _, hmask₁, hslice₁⟩ :=
      annealWriteImmediate_inplace_snoc (mach := mach) (allocIdx := allocIdx)
        (allocId := allocId) (kind := kind) (alloc := alloc₀) (mp := mp) (tf := tf) (k := 0)
        (destLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts)
        hlt_idx hfind hprov hbase hptr hslice₀ hrel hsz hbool hchar hin₁
    let st₁ : AnnealStepState :=
      { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc₁ }
    have hcopy0 : h.copyOp () source firstPlace st₀ = .ok () st₁ := by
      dsimp only [h, annealAggregateHooks, source]
      exact hwrite₁
    rw [EStateM.bind_eq_ok hcopy0]
    dsimp only [h, annealAggregateHooks, firstPlace, aggregateLiftPub, pure, EStateM.pure,
      bind, EStateM.bind]
    rw [aggregateWrappingOffset_anneal_eq]
    dsimp only [EStateM.pure]
    have hsub1 : UInt64.ofNat (k + 1) - 1 = UInt64.ofNat k := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hk64 : k < 2 ^ 64 := by omega
      rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le]
      · simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64),
          Nat.mod_eq_of_lt (by simpa [UInt64.size] using hk64)]
      · rw [UInt64.le_iff_toNat_le]
        simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt64)]
    rw [hsub1]
    cases k with
    | zero =>
      exact ⟨alloc₁, rfl, hbs₁, hslice₁⟩
    | succ m =>
      have hm64 : m + 1 < 2 ^ 64 := by omega
      have hne0_m : (UInt64.ofNat (m + 1) == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro heq
        have htoNat : (UInt64.ofNat (m + 1)).toNat = 0 := by
          rw [beq_iff_eq] at heq; rw [heq]; rfl
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hm64)] at htoNat
        omega
      have htoNat_m : (UInt64.ofNat (m + 1)).toNat = m + 1 := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa [UInt64.size] using hm64)]
      obtain ⟨sc₀, msc₀, hsc₀_eq, _, _, _, hrel₀, hread₀⟩ :=
        hslice₁.elem_rel 0 (Value.scalar sc) rfl
      injection hsc₀_eq with hsc₀_eq'
      subst hsc₀_eq'
      have hmsc₀_eq : msc₀ = msc := hrel₀.unique hrel
      subst hmsc₀_eq
      have hfirstOff_rel :
          Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (0 * elemSize.bytes.toNat)) =
            relOffset := by
        have h_u0 : UInt64.ofNat 0 = 0 := rfl
        simp only [Nat.zero_mul, h_u0, UInt64.add_zero]
        cases relOffset; rfl
      rw [hfirstOff_rel] at hread₀
      have hin_m :
          relOffset.bytes.toNat + (1 + (m + 1)) * elemSize.bytes.toNat ≤
            alloc₁.byteSize.bytes.toNat := by
        rw [hbs₁]
        rw [hwf.arr_size_toNat] at hin_arr
        have : 1 + (m + 1) = m + 1 + 1 := by omega
        rw [this]
        exact hin_arr
      obtain ⟨alloc₂, hrep, hbs₂, _, _, hslice₂⟩ :=
        writeScalarRepeatedly_spec (m + 1) hslice₁ hrel hsz hbool hchar
          (by rw [hbs₁]; exact hmask₁) hin_m
      have hbase₁ : (inplaceMachine mach allocIdx allocId kind alloc₁).lookupBaseAddr allocId =
          some baseAddr := hbase
      have hidx₁ := inplaceMachine_findIdx? (kind := kind) alloc₁ hfind
      have hget₁ := inplaceMachine_getElem? (allocId := allocId) (kind := kind) alloc₁ hlt_idx
      have hprov₀ : mp₀.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId := by
        dsimp only [mp₀]
        rw [hprov]
        rfl
      have hbytes_mp : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      have hoff_first :
          Miri.ABI.Size.ofBytes (mp₀.ptr.offset.bytes - baseAddr) = relOffset := by
        dsimp only [mp₀, elemOff₀]
        have h_u0 : UInt64.ofNat 0 = 0 := rfl
        simp only [Nat.zero_mul, h_u0, Miri.ABI.Size.ofBytes, hbytes_mp, UInt64.add_zero,
          uint64_add_sub_cancel_left]
      have hoff_rest :
          Miri.ABI.Size.ofBytes
            ((Miri.ABI.Size.ofBytes (mp₀.ptr.offset.bytes + elemSize.bytes)).bytes - baseAddr) =
          Miri.ABI.Size.ofBytes
            (relOffset.bytes + UInt64.ofNat (1 * elemSize.bytes.toNat)) := by
        dsimp only [mp₀, elemOff₀]
        have h_u0 : UInt64.ofNat 0 = 0 := rfl
        have h_u64 : UInt64.ofNat (1 * elemSize.bytes.toNat) = elemSize.bytes := by
          rw [Nat.one_mul, UInt64.ofNat_toNat]
        simp only [Nat.zero_mul, h_u0, Miri.ABI.Size.ofBytes, hbytes_mp, UInt64.add_zero,
          h_u64, uint64_add_add_sub_cancel_left]
      dsimp only [elemSize] at hoff_rest hread₀ hrep
      refine ⟨alloc₂, ?_, hbs₂.trans hbs₁, ?_⟩
      · simp only [hne0_m, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get,
          EStateM.get, EStateM.bind, hprov₀, st₁, hbase₁, hidx₁, hget₁]
        rw [hoff_first, hoff_rest, htoNat_m, hread₀]
        dsimp only [pure, EStateM.pure, EStateM.bind]
        rw [hrep]
        simp only [EStateM.pure, EStateM.bind, set, MonadStateOf.set, EStateM.set]
        dsimp only [inplaceMachine]
        simp only [array_set!_idem]
      · have hcnt : 1 + (m + 1) = m + 1 + 1 := by omega
        have hlist : [Value.scalar sc] ++ List.replicate (m + 1) (Value.scalar sc) =
            List.replicate (m + 1 + 1) (Value.scalar sc) := rfl
        rw [← hlist, ← hcnt]
        exact hslice₂

theorem replicateValue_eq_replicate (n : Nat) (v : Value) :
    replicateValue n v = List.replicate n v := by
  induction n with
  | zero => rfl
  | succ k ih => simp [replicateValue, List.replicate, ih]

/-- Full single-step correspondence for `_dst = [op; count]` (`Rvalue.repeat`):
handles source operand UB (dead/uninitialized local, including destructive `move`),
destination `.dead` UB, fresh stack allocation when `dstIdx` is immediate
(`CanReserveAllocId`), and in-place overwrite when `dstIdx` already holds
`.init (.aggregate 0 oldElems)` (reusing its existing allocation without reserving a
new `AllocId`), establishing `ArraySliceRel` and preserving `StateRel`
(`MemoryAllocDisjoint`), `StepPreservesNodup`, `StepPreservesImmediate`, and
`StepPreservesHighWater m 1`. -/
theorem evalRvalue_repeat_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat} {op : MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hdst_ready : ∀ topFrame, m.stack.frames = #[topFrame] →
      ArrayConstructDestReady s m topFrame dstIdx)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 }) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 1
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hrel with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hdst_ready_tf := hdst_ready topFrame hframes
  have hop_tf := hop topFrame hframes
  obtain ⟨slot_dst, mls_dst, _, hlt_dst, _, hmls_dst, hmls_dst_eq, hloc_dst⟩ :=
    hframe.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have heval_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst hdecl_dst (by rw [hmls_dst_eq]; exact hloc_dst.layout_eq)
  have hframe₀ : FrameRel body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_dst hlt_dst
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ :=
    hdisj.cache_layout hlt_dst _
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun j hj => hj.cache_layout hlt_dst _
  have hop₀ : WellTypedLM2_1ScalarOperand body topFrame₀ op { kind := elemKind, layoutIdx := 0 } :=
    hop_tf.cache_layout hlt_dst _
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeRepeat (annealAggregateHooks body.localDecls body.layouts) ()
          (translateOperand op) destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
      translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    rw [evalRvalueIntoPlace_repeat_def]
    unfold annealRvalueHooks
    dsimp only
    exact EStateM.bind_eq_ok heval_dst
  have hm₀_eq : m₀ = { stack := ⟨#[topFrame₀]⟩, machine := m.machine } := rfl
  rcases evalLM2_1ScalarOperand_preserves_array_local hframe₀ hdisj₀ hdecl_dst hwf hprim hop₀
      s.memory.globals none with
    ⟨heval_a, m', msg, heval_m⟩ |
    ⟨sc, msc, locals₁, topFrame₁, heval_a, heval_m, hget_dst₁, _, _, _,
      hframe₁, hdisj₁, hmono₁, htf₁_eq, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
  · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue
      dsimp only
      rw [hbor, hcaller, heval_a]
    have heval_agg_err :
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand op) none m₀ =
        .error (.undefinedBehavior msg) m' := by
      dsimp only [annealAggregateHooks]
      rw [hm₀_eq, EStateM.bind_assoc_apply, EStateM.bind_eq_error heval_m]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
        (m', .error (.undefinedBehavior msg)) := by
      rw [hm_eval, writeRepeat_def]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error heval_agg_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
      hstmt hm_err]
    exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
      StepPreservesHighWater.of_error⟩
  · have hisSized :
        (!(translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.isSized) = false := by
      rw [hprim.isSized]; rfl
    have heval_agg_op :
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand op) none m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { m with stack := ⟨#[topFrame₁]⟩ } := by
      dsimp only [annealAggregateHooks]
      rw [hm₀_eq, EStateM.bind_assoc_apply, EStateM.bind_eq_ok heval_m]
      rfl
    obtain ⟨slot_dst₁, mls_dst₁, hlt_af_dst₁, hlt_dst₁, hslot_dst₁, hmls_dst₁, hmls_dst₁_eq, hloc_dst₁⟩ :=
      hframe₁.lookup_local hdecl_dst
    dsimp only at hlt_af_dst₁ hslot_dst₁
    have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
      revert hbor hprot
      generalize s.memory = mem
      intro hbor hprot
      cases mem
      dsimp only at hbor hprot
      subst hbor hprot
      rfl
    dsimp only at hmem_same
    have hretCont₁ : topFrame₁.returnContinuation = .stop false := by
      rw [htf₁_eq]; exact hretCont
    have hretPlace₁ : ∃ retLay, topFrame₁.returnPlace =
        .frameLocal 0 0 none retLay topFrame₁.localsIdentity := by
      rw [htf₁_eq]; exact ⟨retLay, hretPlace⟩
    cases hloc_dst₁ with
    | dead _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller, heval_a]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hslot_dst₁]
      have hdead_val : (topFrame₁.locals[dstIdx]'hlt_dst₁).value = .dead := by
        rw [hmls_dst₁_eq]
      have hens_err := annealEnsureAllocated_dead
        (m := { m with stack := ⟨#[topFrame₁]⟩ }) (tf := topFrame₁)
        (id := topFrame.localsIdentity) (lay := translateTy dstDecl.ty body.layouts)
        rfl hlt_dst₁ hdead_val
      have hforce_err :
          (annealAggregateHooks body.localDecls body.layouts).forceAllocation () destPlace
            { m with stack := ⟨#[topFrame₁]⟩ } =
          .error (.undefinedBehavior "write to dead local")
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        dsimp only [annealAggregateHooks, destPlace]
        exact EStateM.bind_eq_error hens_err
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
          ({ m with stack := ⟨#[topFrame₁]⟩ },
            .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_eval, writeRepeat_def]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok heval_agg_op]
        dsimp only
        rw [hisSized]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [EStateM.bind_eq_error hforce_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
        StepPreservesHighWater.of_error⟩
    | indirect slot_dst₁ mp cachedLay hcache_dst hnot_dead hmp =>
      rcases hdst_ready_tf with hdead_s | ⟨hdst_imm_tf, _⟩ | ⟨oldElems, hold_s⟩
      · rw [← hget_dst₁, hslot_dst₁] at hdead_s; injection hdead_s with heq; exact absurd heq hnot_dead
      · exact False.elim ((hmono₁ dstIdx (hmono₀ dstIdx hdst_imm_tf)) _ hmls_dst₁ mp rfl)
      · have hold_s₁ : get? locals₁ dstIdx = some (.init (.aggregate 0 oldElems)) := by
          rw [hget_dst₁]; exact hold_s
        rw [hold_s₁] at hslot_dst₁; injection hslot_dst₁ with heq; subst heq
        have hset_ok : set? locals₁ dstIdx
            (.init (.aggregate 0 (List.replicate count (.scalar sc)))) =
            some (locals₁.set dstIdx
              (.init (.aggregate 0 (List.replicate count (.scalar sc))))) :=
          set?_eq_some_set hlt_af_dst₁ _
        have ha_step : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
            body.localDecls body.layouts =
            MirStepNode.step (advanceStmt s
              (locals₁.set dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc)))))
              s.memory) := by
          unfold evalStmt evalRvalue
          dsimp only
          rw [hbor, hcaller, heval_a]
          dsimp only
          rw [replicateValue_eq_replicate, hprot, hbor]
          dsimp only [invalidateConflictingBorrows]
          rw [hmem_same, hold_s₁]
          simp [hset_ok]
        cases hmp with
        | mk allocId tag baseAddr relOffset localAlloc
            hprov hmis hmeta hlive hbase hno_ovf hptr hmut haligned hin_arr _ hval_cons _ harr =>
          rcases localAlloc with ⟨kind, alloc₀⟩
          obtain ⟨_, _, _, hslice_old⟩ := harr elemKind count oldElems hwf.arr_kind rfl
          dsimp only at hslice_old hin_arr hval_cons hmut
          obtain ⟨allocIdx, hlt_idx, hfindIdx, hgetIdx, hset_prop⟩ :=
            array_findIdx?_of_nodup_fst hnodup hlive
          have hslice₀ : ArraySliceRel elemKind 0 body.layouts [] relOffset alloc₀ :=
            { elems_len := rfl
              alloc_len := hslice_old.alloc_len
              alloc_mut := hslice_old.alloc_mut
              alloc_prov := hslice_old.alloc_prov
              alloc_mask := hslice_old.alloc_mask
              slice_in_bounds := by have := hslice_old.slice_in_bounds; omega
              elem_rel := fun _ _ h => nomatch h }
          obtain ⟨alloc_final, hbody_ok, hsize_final, hslice_final⟩ :=
            writeRepeat_inplace_spec (body := body) (mach := m.machine)
              (allocIdx := allocIdx) (allocId := allocId) (kind := kind) (alloc₀ := alloc₀)
              (mp := mp) (tf := topFrame₁) (arrTy := dstDecl.ty) (elemKind := elemKind)
              (count := count) (sc := sc) (msc := msc)
              (srcLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts)
              hwf hlt_idx hfindIdx hprov hbase hptr hrel_sc hsz_sc hbool_sc hchar_sc
              hin_arr hslice₀
          have hind_val : (topFrame₁.locals[dstIdx]'hlt_dst₁).value = .live (.indirect mp) := by
            rw [hmls_dst₁_eq]
          have hens_ind := annealEnsureAllocated_indirect
            (st := { m with stack := ⟨#[topFrame₁]⟩ }) (tf := topFrame₁)
            (id := topFrame.localsIdentity) (lay := translateTy dstDecl.ty body.layouts)
            rfl hlt_dst₁ hind_val
          have hm_self : { m with stack := ⟨#[topFrame₁]⟩ } =
              ({ stack := ⟨#[topFrame₁]⟩,
                 machine := inplaceMachine m.machine allocIdx allocId kind alloc₀ } : AnnealStepState) := by
            rw [inplaceMachine_self hgetIdx]
          have hforce_ok :
              (annealAggregateHooks body.localDecls body.layouts).forceAllocation () destPlace
                { m with stack := ⟨#[topFrame₁]⟩ } =
              .ok ⟨.memory mp, translateTy dstDecl.ty body.layouts⟩
                { stack := ⟨#[topFrame₁]⟩,
                  machine := inplaceMachine m.machine allocIdx allocId kind alloc₀ } := by
            dsimp only [annealAggregateHooks, destPlace]
            rw [EStateM.bind_eq_ok hens_ind, ← hm_self]
            rfl
          have hm_step : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
              ({ stack := ⟨#[topFrame₁]⟩,
                 machine := inplaceMachine m.machine allocIdx allocId kind alloc_final },
               .ok ()) := by
            rw [hm_eval, writeRepeat_def]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok heval_agg_op]
            dsimp only
            rw [hisSized]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [EStateM.bind_eq_ok hforce_ok, hbody_ok]
          obtain ⟨hnodup', hlive', hother_live⟩ := hset_prop ⟨kind, alloc_final⟩
          obtain ⟨hs_rel, hs_nd, hs_imm, hs_hw⟩ :=
            write_array_inplace_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := topFrame₁)
              hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller
              hframes hframe.body_eq hframe.location_eq hbb hstmt hframe₁ hdisj₁
              hdecl_dst hwf hmls_dst₁ hcache_dst hprov hmis hmeta hbase hno_ovf hptr haligned
              hin_arr hval_cons hslice_old.alloc_mask hsize_final hslice_final
              hlive hnodup' hlive' hother_live ha_step hm_step
              (fun j hj => hmono₁ j (hmono₀ j hj))
          exact ⟨hs_rel, hs_nd, hs_imm, hs_hw.mono_budget (by decide : 0 ≤ 1)⟩
    | immediate slot_dst₁ imm_dst _ _ hval =>
      have hnot_dead : slot_dst₁ ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
      have hcan_res : CanReserveAllocId m.machine.memory := by
        rcases hdst_ready_tf with hdead_s | ⟨_, hres⟩ | ⟨oldElems, hold_s⟩
        · rw [← hget_dst₁, hslot_dst₁] at hdead_s; injection hdead_s with heq; exact absurd heq hnot_dead
        · exact hres
        · rw [← hget_dst₁, hslot_dst₁] at hold_s; injection hold_s with heq; subst heq
          rcases hval with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
          · cases h1
          · injection hv' with hv_eq; subst hv_eq
            cases himm' with
            | scalarPair _ _ _ _ _ _ hagg _ =>
              rcases hagg with ⟨_, ht⟩ | ⟨_, _, ht⟩ <;> (rw [hwf.arr_kind] at ht; cases ht)
      have hset_ok : set? locals₁ dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc)))) =
          some (locals₁.set dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc))))) :=
        set?_eq_some_set hlt_af_dst₁ _
      have ha_step : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
          body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s
            (locals₁.set dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc)))))
            s.memory) := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller, heval_a]
        dsimp only
        rw [replicateValue_eq_replicate, hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same, hslot_dst₁]
        cases slot_dst₁ with
        | dead => exact absurd rfl hnot_dead
        | uninit => simp [hset_ok]
        | init _ => simp [hset_ok]
      obtain ⟨mem', allocId, hres⟩ := hcan_res
      have himm_val : (topFrame₁.locals[dstIdx]'hlt_dst₁).value = .live (.immediate imm_dst) := by
        rw [hmls_dst₁_eq]
      obtain ⟨alloc₀, hens_ok, hsize₀, _, _, _, hslice₀⟩ :=
        annealEnsureAllocated_immediate
          (m := { m with stack := ⟨#[topFrame₁]⟩ }) (tf := topFrame₁)
          (id := topFrame.localsIdentity) (arrTy := dstDecl.ty)
          (layouts := body.layouts) (elemKind := elemKind)
          rfl hlt_dst₁ himm_val hres
      obtain ⟨hlive_eq, hfresh₀⟩ := reserveAllocId_ok_live hres
      have hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false := by
        rw [hlive_eq]; exact hfresh₀
      obtain ⟨alloc_final, hbody_ok, hsize_final, hslice_final⟩ :=
        writeRepeat_after_forceAlloc_spec (body := body) (mach := m.machine) (mem' := mem')
          (allocId := allocId) (alloc₀ := alloc₀)
          (tf := setFrameLocalIndirect topFrame₁ dstIdx hlt_dst₁ (stackAllocPlace allocId))
          (arrTy := dstDecl.ty) (elemKind := elemKind) (count := count)
          (sc := sc) (msc := msc)
          (srcLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts)
          hwf hfresh hrel_sc hsz_sc hbool_sc hchar_sc hsize₀ hslice₀
      have hforce_ok :
          (annealAggregateHooks body.localDecls body.layouts).forceAllocation () destPlace
            { m with stack := ⟨#[topFrame₁]⟩ } =
          .ok ⟨.memory (stackAllocPlace allocId), translateTy dstDecl.ty body.layouts⟩
            { stack := ⟨#[setFrameLocalIndirect topFrame₁ dstIdx hlt_dst₁ (stackAllocPlace allocId)]⟩,
              machine := stackAllocMachine m.machine mem' allocId alloc₀ } := by
        dsimp only [annealAggregateHooks, destPlace]
        rw [EStateM.bind_eq_ok hens_ok]
        rfl
      have hm_step : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
          ({ stack := ⟨#[setFrameLocalIndirect topFrame₁ dstIdx hlt_dst₁ (stackAllocPlace allocId)]⟩,
             machine := stackAllocMachine m.machine mem' allocId alloc_final },
           .ok ()) := by
        rw [hm_eval, writeRepeat_def]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok heval_agg_op]
        dsimp only
        rw [hisSized]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [EStateM.bind_eq_ok hforce_ok, hbody_ok]
      exact write_array_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := topFrame₁)
        hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt hframe₁ hdisj₁
        hdecl_dst hwf hlt_dst₁ hres hsize_final hslice_final ha_step hm_step hnodup
        (fun j hj => hmono₁ j (hmono₀ j hj))

/-! ## 5. `Rvalue.Aggregate (.array _)` Simulation (`evalRvalue_aggregate_array_simulation`) -/

theorem cacheFrameLocalLayout_setFrameLocalIndirect_comm
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {dstIdx idx : Nat}
    (hlt_dst : dstIdx < tf.locals.size)
    (hlt_idx : idx < tf.locals.size)
    (hne : idx ≠ dstIdx)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    cacheFrameLocalLayout (setFrameLocalIndirect tf dstIdx hlt_dst mp) idx
      (by unfold setFrameLocalIndirect; simp [hlt_idx]) lay =
    setFrameLocalIndirect (cacheFrameLocalLayout tf idx hlt_idx lay) dstIdx
      (by unfold cacheFrameLocalLayout; simp [hlt_dst]) mp := by
  unfold cacheFrameLocalLayout setFrameLocalIndirect
  congr 1
  apply Array.ext
  · simp
  · intro i hi₁ hi₂
    simp only [Array.getElem_set]
    by_cases h1 : idx = i
    · subst h1
      simp only [↓reduceIte, hne.symm]
    · by_cases h2 : dstIdx = i
      · subst h2
        simp only [h1, ↓reduceIte]
      · simp only [h1, h2, ↓reduceIte]

/-- Evaluating a `WellTypedScalarOperand` of element type `{ kind := elemKind, layoutIdx := 0 }`
on a frame where `dstIdx` (of array type `[elemKind; count]`) has already been set to
`.live (.indirect mp)` behaves identically to evaluating it on `tf` and commutes with
`setFrameLocalIndirect`. -/
theorem evalScalarOperand_with_indirect_dst
    {body : CapturedMir} {mach mach' : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (hlt_dst : dstIdx < tf.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (globals : List CapturedAllocation)
    (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState :=
      { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt_dst mp]⟩, machine := mach' }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
          (translateOperand op) known st = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf', ∃ hlt_dst' : dstIdx < tf'.locals.size,
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { stack := ⟨#[setFrameLocalIndirect tf' dstIdx hlt_dst' mp]⟩, machine := mach' } ∧
      FrameRel body mach af tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  dsimp only
  let tf_ind := setFrameLocalIndirect tf dstIdx hlt_dst mp
  let st : AnnealStepState := { stack := ⟨#[tf_ind]⟩, machine := mach' }
  generalize helemTy : ({ kind := elemKind, layoutIdx := 0 } : Ty) = elemTy at hop hprim
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ st := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton st.stack tf_ind rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    have hkind_c : c.ty.kind = elemKind := by rw [← helemTy]
    refine Or.inr ⟨sc, msc, tf, hlt_dst, heval_a, ?_, hframe, id, (fun _ h => h), rfl,
      hrel, hlaysz,
      by intro hb; exact hbool (hkind_c.trans hb),
      by intro hc; exact hchar (hkind_c.trans hc)⟩
    dsimp only [annealAggregateHooks]
    rw [EStateM.bind_eq_ok heval_m]
    rfl
  | copyLocal idx decl hdecl hsz_nz himm =>
    have hop_orig : WellTypedScalarOperand body tf (.copy ⟨idx, .nil⟩) decl.ty :=
      .copyLocal idx decl hdecl hsz_nz himm
    rw [← helemTy] at hop_orig hprim
    have hne : idx ≠ dstIdx := hop_orig.ne_array_local hdecl_dst hwf hprim
    obtain ⟨slot, mls, _, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hlt_ind : idx < tf_ind.locals.size := by
      unfold tf_ind setFrameLocalIndirect; simp [hlt_idx]
    have hmls_ind : tf_ind.locals[idx]'hlt_ind = mls :=
      Option.some.inj (by
        rw [← Array.getElem?_eq_getElem]
        dsimp only [tf_ind, setFrameLocalIndirect]
        rw [Array.getElem?_set_ne _ hne.symm]
        exact hmls)
    have himm' := himm mls hmls
    cases hloc with
    | dead cachedLayout hcache =>
      left
      have hdead := annealEvalOperand_copy_dead (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind hcache
      dsimp only [st] at hdead
      refine ⟨by simp [evalOperand, hslot],
        { stack := ⟨#[cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts)]⟩,
          machine := mach' },
        "read of dead local", ?_⟩
      dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm cachedLayout hcache hval =>
      let tf' := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
      have hlt_dst' : dstIdx < tf'.locals.size := by
        unfold tf' cacheFrameLocalLayout; simp [hlt_dst]
      have hcomm : cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts) =
          setFrameLocalIndirect tf' dstIdx hlt_dst' mp :=
        cacheFrameLocalLayout_setFrameLocalIndirect_comm tf hlt_dst hlt_idx hne mp
          (translateTy decl.ty body.layouts)
      have hlive := annealEvalOperand_copy_live (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind hcache
      dsimp only [st] at hlive
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot],
          { stack := ⟨#[cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts)]⟩,
            machine := mach' },
          "read of uninitialized local", ?_⟩
        dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        rw [← helemTy] at himmRel
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel.of_primitive_scalar hprim
        have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        refine ⟨sc, msc, tf', hlt_dst', ha, ?_,
          hframe.cache_local_layout hdecl hlt_idx,
          ?_, (fun _ hj => hj.cache_layout hlt_idx _), rfl,
          hrel_sc, by rw [← helemTy]; exact hsz_sc, hbool_sc, hchar_sc⟩
        · dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
          rw [EStateM.bind_eq_ok hlive]
          dsimp only [annealReadImmediate, pure, EStateM.pure, bind, EStateM.bind]
          rw [hcomm]
        · intro hdisj
          apply MemoryAllocDisjoint.mono_layout hdisj
          intro k
          by_cases hk : k = idx
          · subst hk
            exists (translateTy decl.ty body.layouts)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set]
            simp only [↓reduceIte]
            simp [hmls, hmls_eq]
          · exists (tf.locals[k]?).bind (fun x => x.layout)
            dsimp [tf', cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
            cases tf.locals[k]? <;> rfl

/-- Evaluating a `WellTypedScalarOperand` of element type `{ kind := elemKind, layoutIdx := 0 }`
under arbitrary `mach'` preserves `tf.locals[dstIdx]?` (since `dstIdx` has array type
`[elemKind; count]`). -/
theorem evalScalarOperand_for_agg_inplace
    {body : CapturedMir} {mach mach' : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (globals : List CapturedAllocation)
    (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach' }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
          (translateOperand op) known st = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf',
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) af.locals ∧
      (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { stack := ⟨#[tf']⟩, machine := mach' } ∧
      tf'.locals[dstIdx]? = tf.locals[dstIdx]? ∧
      FrameRel body mach af tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  dsimp only
  let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach' }
  generalize helemTy : ({ kind := elemKind, layoutIdx := 0 } : Ty) = elemTy at hop hprim
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ st := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton st.stack tf rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    have hkind_c : c.ty.kind = elemKind := by rw [← helemTy]
    refine Or.inr ⟨sc, msc, tf, heval_a, ?_, rfl, hframe, id, (fun _ h => h), rfl,
      hrel, hlaysz,
      by intro hb; exact hbool (hkind_c.trans hb),
      by intro hc; exact hchar (hkind_c.trans hc)⟩
    dsimp only [annealAggregateHooks]
    rw [EStateM.bind_eq_ok heval_m]
    rfl
  | copyLocal idx decl hdecl hsz_nz himm =>
    have hop_orig : WellTypedScalarOperand body tf (.copy ⟨idx, .nil⟩) decl.ty :=
      .copyLocal idx decl hdecl hsz_nz himm
    rw [← helemTy] at hop_orig hprim
    have hne : idx ≠ dstIdx := hop_orig.ne_array_local hdecl_dst hwf hprim
    obtain ⟨slot, mls, _, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have himm' := himm mls hmls
    cases hloc with
    | dead cachedLayout hcache =>
      left
      have hdead := annealEvalOperand_copy_dead (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq hcache
      dsimp only [st] at hdead
      refine ⟨by simp [evalOperand, hslot],
        { stack := ⟨#[cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)]⟩,
          machine := mach' },
        "read of dead local", ?_⟩
      dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm cachedLayout hcache hval =>
      let tf' := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
      have hlive := annealEvalOperand_copy_live (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq hcache
      dsimp only [st] at hlive
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot],
          { stack := ⟨#[tf']⟩, machine := mach' },
          "read of uninitialized local", ?_⟩
        dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        rw [← helemTy] at himmRel
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel.of_primitive_scalar hprim
        have ha : evalOperand af.locals (.copy ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) af.locals := by
          simp [evalOperand, readProjectedValue, hslot]
        have hdst_pres : tf'.locals[dstIdx]? = tf.locals[dstIdx]? := by
          dsimp only [tf', cacheFrameLocalLayout]
          exact Array.getElem?_set_ne _ hne
        refine ⟨sc, msc, tf', ha, ?_, hdst_pres,
          hframe.cache_local_layout hdecl hlt_idx,
          fun hdisj => hdisj.cache_layout hlt_idx _,
          (fun _ hj => hj.cache_layout hlt_idx _), rfl,
          hrel_sc, by rw [← helemTy]; exact hsz_sc, hbool_sc, hchar_sc⟩
        dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl

theorem evalOperands_scalar_dichotomy
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ops : List MirAst.Operand} {ty : Ty}
    (hframe : FrameRel body mach af tf)
    (hops : ∀ op ∈ ops, WellTypedScalarOperand body tf op ty)
    (globals : List CapturedAllocation) :
    evalOperands af.locals ops .nil globals body.layouts .nil = .ub ∨
      ∃ vals, evalOperands af.locals ops .nil globals body.layouts .nil = .ok vals af.locals := by
  induction ops generalizing tf with
  | nil =>
    exact Or.inr ⟨[], rfl⟩
  | cons op rest ih =>
    have hop : WellTypedScalarOperand body tf op ty := hops op List.mem_cons_self
    have hsim := evalOperand_scalar_simulation (m := { stack := ⟨#[tf]⟩, machine := mach })
      rfl hframe hop globals none
    generalize heval_a : evalOperand af.locals op .nil globals body.layouts .nil = res_a at hsim
    generalize heval_m :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) none >>=
        annealReadImmediate) { stack := ⟨#[tf]⟩, machine := mach } = res_m at hsim
    cases hsim with
    | ub _ _ =>
      exact Or.inl (by simp [evalOperands, heval_a])
    | ok v locals' tf' imm hframe' _ hmono' _ _ =>
      have hloc_eq := hop.evalOperand_locals_eq heval_a
      subst hloc_eq
      have hrest : ∀ op' ∈ rest, WellTypedScalarOperand body tf' op' ty :=
        fun op' hmem => (hops op' (List.mem_cons_of_mem _ hmem)).mono_immediate hmono'
      rcases ih hframe' hrest with hub | ⟨vs, hvs⟩
      · exact Or.inl (by simp [evalOperands, heval_a, hub])
      · exact Or.inr ⟨v :: vs, by simp [evalOperands, heval_a, hvs]⟩

theorem deinitFrameLocal_setFrameLocalIndirect_comm
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {dstIdx idx : Nat}
    (hlt_dst : dstIdx < tf.locals.size)
    (hlt_idx : idx < tf.locals.size)
    (hne : idx ≠ dstIdx)
    (mp : Miri.Interpreter.MemPlace AnnealProv) :
    deinitFrameLocal (setFrameLocalIndirect tf dstIdx hlt_dst mp) idx
      (by unfold setFrameLocalIndirect; simp [hlt_idx]) =
    setFrameLocalIndirect (deinitFrameLocal tf idx hlt_idx) dstIdx
      (by unfold deinitFrameLocal; simp [hlt_dst]) mp := by
  unfold deinitFrameLocal setFrameLocalIndirect
  congr 1
  apply Array.ext
  · simp
  · intro i hi₁ hi₂
    simp only [Array.getElem_set]
    by_cases h1 : idx = i
    · subst h1
      simp only [↓reduceIte, hne.symm]
    · by_cases h2 : dstIdx = i
      · subst h2
        simp only [h1, ↓reduceIte]
      · simp only [h1, h2, ↓reduceIte]

/-- Evaluating a `WellTypedLM2_1ScalarOperand` (constant, `copy`, or destructive `move`)
of element type `{ kind := elemKind, layoutIdx := 0 }` on a frame where `dstIdx`
(of array type `[elemKind; count]`) has already been set to `.live (.indirect mp)`
behaves identically to evaluating it on `tf` and commutes with `setFrameLocalIndirect`. -/
theorem evalLM2_1ScalarOperand_with_indirect_dst
    {body : CapturedMir} {mach mach' : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedLM2_1ScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (hlt_dst : dstIdx < tf.locals.size)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (globals : List CapturedAllocation)
    (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState :=
      { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt_dst mp]⟩, machine := mach' }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
          (translateOperand op) known st = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc locals₁ tf', ∃ hlt_dst' : dstIdx < tf'.locals.size,
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) locals₁ ∧
      (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { stack := ⟨#[setFrameLocalIndirect tf' dstIdx hlt_dst' mp]⟩, machine := mach' } ∧
      get? locals₁ dstIdx = get? af.locals dstIdx ∧
      FrameRel body mach { af with locals := locals₁ } tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  dsimp only
  have hop' : ∃ eTy, eTy = ({ kind := elemKind, layoutIdx := 0 } : Ty) ∧
      WellTypedLM2_1ScalarOperand body tf op eTy := ⟨_, rfl, hop⟩
  rcases hop' with ⟨eTy, helem, hop_gen⟩
  cases hop_gen with
  | ofScalar hop_s =>
    subst helem
    rcases evalScalarOperand_with_indirect_dst (mach' := mach') hframe hdecl_dst hwf hprim
        hop_s hlt_dst mp globals path known with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, tf', hlt_dst', ha_ok, hm_ok, hframe', hdisj_imp, hmono', htf'_eq,
        hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
    · exact Or.inl ⟨ha_ub, m', msg, hm_err⟩
    · exact Or.inr ⟨sc, msc, af.locals, tf', hlt_dst', ha_ok, hm_ok, rfl, hframe',
        hdisj_imp, hmono', htf'_eq, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
  | moveLocal idx decl hdecl hprim_src himm =>
    let tf_ind := setFrameLocalIndirect tf dstIdx hlt_dst mp
    let st : AnnealStepState := { stack := ⟨#[tf_ind]⟩, machine := mach' }
    have hne : idx ≠ dstIdx := primScalarLocal_ne_array_local hdecl_dst hwf hdecl hprim_src
    obtain ⟨slot, mls, hlt_af, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have hlt_ind : idx < tf_ind.locals.size := by
      unfold tf_ind setFrameLocalIndirect; simp [hlt_idx]
    have hmls_ind : tf_ind.locals[idx]'hlt_ind = mls :=
      Option.some.inj (by
        rw [← Array.getElem?_eq_getElem]
        dsimp only [tf_ind, setFrameLocalIndirect]
        rw [Array.getElem?_set_ne _ hne.symm]
        exact hmls)
    have himm' := himm mls hmls
    cases hloc with
    | dead _ hcache =>
      left
      have hdead := annealEvalOperand_move_dead (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind (fun l hl => hcache l hl)
      dsimp only [st] at hdead
      refine ⟨by simp [evalOperand, hslot],
        { stack := ⟨#[cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts)]⟩,
          machine := mach' },
        "read of dead local", ?_⟩
      dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm _ hcache hval =>
      let tf_c := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
      have hlt_idx_c : idx < tf_c.locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_idx
      let tf' := deinitFrameLocal tf_c idx hlt_idx_c
      have hlt_dst_c : dstIdx < tf_c.locals.size := by
        unfold tf_c cacheFrameLocalLayout; simp [hlt_dst]
      have hlt_dst' : dstIdx < tf'.locals.size := by
        unfold tf' deinitFrameLocal; simp [hlt_dst_c]
      have hcomm_c : cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts) =
          setFrameLocalIndirect tf_c dstIdx hlt_dst_c mp :=
        cacheFrameLocalLayout_setFrameLocalIndirect_comm tf hlt_dst hlt_idx hne mp
          (translateTy decl.ty body.layouts)
      have hlt_ind_c : idx < (cacheFrameLocalLayout tf_ind idx hlt_ind
          (translateTy decl.ty body.layouts)).locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_ind
      have hcomm :
          deinitFrameLocal
            (cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts))
            idx hlt_ind_c =
          setFrameLocalIndirect tf' dstIdx hlt_dst' mp := by
        have hdeinit_congr :
            ∀ (f₁ f₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
              (h_eq : f₁ = f₂) (h₁ : idx < f₁.locals.size),
              deinitFrameLocal f₁ idx h₁ = deinitFrameLocal f₂ idx (h_eq ▸ h₁) := by
          intro f₁ f₂ h_eq h₁; subst h_eq; rfl
        rw [hdeinit_congr _ _ hcomm_c hlt_ind_c]
        exact deinitFrameLocal_setFrameLocalIndirect_comm tf_c hlt_dst_c hlt_idx_c hne mp
      have hlive := annealEvalOperand_move_live (m := st) (topFrame := tf_ind) (known := known)
        rfl hlt_ind hdecl hmls_ind (fun l hl => hcache l hl)
      dsimp only [st] at hlive
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot],
          { stack := ⟨#[deinitFrameLocal
              (cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts))
              idx hlt_ind_c]⟩,
            machine := mach' },
          "read of uninitialized local", ?_⟩
        dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        have himmRel' : ImmediateRel { kind := elemKind, layoutIdx := 0 } body.layouts v imm :=
          helem ▸ himmRel
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel'.of_primitive_scalar hprim
        obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hprim_src.size_ne_zero
          (translateTy decl.ty body.layouts)
          { stack := ⟨#[deinitFrameLocal
              (cacheFrameLocalLayout tf_ind idx hlt_ind (translateTy decl.ty body.layouts))
              idx hlt_ind_c]⟩,
            machine := mach' }
        have ha : evalOperand af.locals (.move ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) (af.locals.set idx .uninit) := by
          simp [evalOperand, hslot, set?_eq_some_set hlt_af]
        have hget_dst : get? (af.locals.set idx .uninit) dstIdx = get? af.locals dstIdx := by
          simp only [get?_eq_getElem?, List.getElem?_set, hne, ↓reduceIte]
        have hnew : LocalRel mach decl body.layouts .uninit
            { tf_c.locals[idx]'hlt_idx_c with value := .live (.immediate .uninit) } := by
          have hlay : (tf_c.locals[idx]'hlt_idx_c).layout =
              some (translateTy decl.ty body.layouts) := by
            simp [tf_c, cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        have hframe' : FrameRel body mach { af with locals := af.locals.set idx .uninit } tf' :=
          (hframe.cache_local_layout hdecl hlt_idx).update_local hdecl .uninit
            (.live (.immediate .uninit)) hnew
        refine ⟨sc, msc, af.locals.set idx .uninit, tf', hlt_dst', ha, ?_, hget_dst,
          hframe', ?_,
          (fun _ hj => (hj.cache_layout hlt_idx _).set_immediate hlt_idx_c .uninit),
          rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
        · dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
          rw [EStateM.bind_eq_ok hlive, EStateM.bind_eq_ok hread, hcomm, helem]
          rfl
        · intro hdisj
          apply MemoryAllocDisjoint.mono_immediate (tf := tf_c) (hdisj.cache_layout hlt_idx _)
          intro k
          by_cases hk : k = idx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy decl.ty body.layouts), by
              simp [tf', tf_c, deinitFrameLocal, cacheFrameLocalLayout]⟩
          · left
            simp [tf', deinitFrameLocal, Array.getElem?_set_ne _ (Ne.symm hk)]

/-- Evaluating a `WellTypedLM2_1ScalarOperand` (constant, `copy`, or destructive `move`)
of element type `{ kind := elemKind, layoutIdx := 0 }` under arbitrary `mach'`
preserves `tf.locals[dstIdx]?` and `get? af.locals dstIdx`. -/
theorem evalLM2_1ScalarOperand_for_agg_inplace
    {body : CapturedMir} {mach mach' : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {op : MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hop : WellTypedLM2_1ScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (globals : List CapturedAllocation)
    (path : Miri.Interpreter.OperandPath)
    (known : Option Miri.Interpreter.LocalLayout) :
    let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach' }
    (evalOperand af.locals op .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
          (translateOperand op) known st = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc locals₁ tf',
      evalOperand af.locals op .nil globals body.layouts .nil = .ok (.scalar sc) locals₁ ∧
      (annealAggregateHooks body.localDecls body.layouts).evalOperandAt () path
        (translateOperand op) known st =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { stack := ⟨#[tf']⟩, machine := mach' } ∧
      get? locals₁ dstIdx = get? af.locals dstIdx ∧
      tf'.locals[dstIdx]? = tf.locals[dstIdx]? ∧
      FrameRel body mach { af with locals := locals₁ } tf' ∧
      (MemoryAllocDisjoint tf → MemoryAllocDisjoint tf') ∧
      (∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      tf' = { tf with locals := tf'.locals } ∧
      ScalarRel sc msc ∧
      (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes ∧
      (elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)) := by
  dsimp only
  have hop' : ∃ eTy, eTy = ({ kind := elemKind, layoutIdx := 0 } : Ty) ∧
      WellTypedLM2_1ScalarOperand body tf op eTy := ⟨_, rfl, hop⟩
  rcases hop' with ⟨eTy, helem, hop_gen⟩
  cases hop_gen with
  | ofScalar hop_s =>
    subst helem
    rcases evalScalarOperand_for_agg_inplace (mach' := mach') hframe hdecl_dst hwf hprim
        hop_s globals path known with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, tf', ha_ok, hm_ok, hdst_pres, hframe', hdisj_imp, hmono', htf'_eq,
        hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
    · exact Or.inl ⟨ha_ub, m', msg, hm_err⟩
    · exact Or.inr ⟨sc, msc, af.locals, tf', ha_ok, hm_ok, rfl, hdst_pres, hframe',
        hdisj_imp, hmono', htf'_eq, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
  | moveLocal idx decl hdecl hprim_src himm =>
    let st : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach' }
    have hne : idx ≠ dstIdx := primScalarLocal_ne_array_local hdecl_dst hwf hdecl hprim_src
    obtain ⟨slot, mls, hlt_af, hlt_idx, hslot, hmls, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
    have himm' := himm mls hmls
    cases hloc with
    | dead _ hcache =>
      left
      have hdead := annealEvalOperand_move_dead (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq (fun l hl => hcache l hl)
      dsimp only [st] at hdead
      refine ⟨by simp [evalOperand, hslot],
        { stack := ⟨#[cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)]⟩,
          machine := mach' },
        "read of dead local", ?_⟩
      dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
      exact EStateM.bind_eq_error hdead
    | indirect _ mp' _ _ _ _ =>
      exact False.elim (himm' mp' rfl)
    | immediate _ imm _ hcache hval =>
      let tf_c := cacheFrameLocalLayout tf idx hlt_idx (translateTy decl.ty body.layouts)
      have hlt_idx_c : idx < tf_c.locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_idx
      let tf' := deinitFrameLocal tf_c idx hlt_idx_c
      have hlive := annealEvalOperand_move_live (m := st) (topFrame := tf) (known := known)
        rfl hlt_idx hdecl hmls_eq (fun l hl => hcache l hl)
      dsimp only [st] at hlive
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · left
        refine ⟨by simp [evalOperand, hslot], { stack := ⟨#[tf']⟩, machine := mach' },
          "read of uninitialized local", ?_⟩
        dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
        rw [EStateM.bind_eq_ok hlive]
        rfl
      · right
        have himmRel' : ImmediateRel { kind := elemKind, layoutIdx := 0 } body.layouts v imm :=
          helem ▸ himmRel
        obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
          himmRel'.of_primitive_scalar hprim
        obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hprim_src.size_ne_zero
          (translateTy decl.ty body.layouts) { stack := ⟨#[tf']⟩, machine := mach' }
        have ha : evalOperand af.locals (.move ⟨idx, .nil⟩) .nil globals body.layouts .nil =
            .ok (.scalar sc) (af.locals.set idx .uninit) := by
          simp [evalOperand, hslot, set?_eq_some_set hlt_af]
        have hget_dst : get? (af.locals.set idx .uninit) dstIdx = get? af.locals dstIdx := by
          simp only [get?_eq_getElem?, List.getElem?_set, hne, ↓reduceIte]
        have hdst_pres : tf'.locals[dstIdx]? = tf.locals[dstIdx]? := by
          simp only [tf', tf_c, deinitFrameLocal, cacheFrameLocalLayout, Array.getElem?_set, hne, ↓reduceIte]
        have hnew : LocalRel mach decl body.layouts .uninit
            { tf_c.locals[idx]'hlt_idx_c with value := .live (.immediate .uninit) } := by
          have hlay : (tf_c.locals[idx]'hlt_idx_c).layout =
              some (translateTy decl.ty body.layouts) := by
            simp [tf_c, cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        have hframe' : FrameRel body mach { af with locals := af.locals.set idx .uninit } tf' :=
          (hframe.cache_local_layout hdecl hlt_idx).update_local hdecl .uninit
            (.live (.immediate .uninit)) hnew
        refine ⟨sc, msc, af.locals.set idx .uninit, tf', ha, ?_, hget_dst, hdst_pres,
          hframe', ?_,
          (fun _ hj => (hj.cache_layout hlt_idx _).set_immediate hlt_idx_c .uninit),
          rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
        · dsimp only [annealAggregateHooks, translateOperand, translatePlace, List.map, List.toArray]
          rw [EStateM.bind_eq_ok hlive, EStateM.bind_eq_ok hread, helem]
          rfl
        · intro hdisj
          apply MemoryAllocDisjoint.mono_immediate (tf := tf_c) (hdisj.cache_layout hlt_idx _)
          intro k
          by_cases hk : k = idx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy decl.ty body.layouts), by
              simp [tf', tf_c, deinitFrameLocal, cacheFrameLocalLayout]⟩
          · left
            simp [tf', deinitFrameLocal, Array.getElem?_set_ne _ (Ne.symm hk)]

theorem evalOperands_lm2_1_dichotomy
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {ops : List MirAst.Operand}
    (hframe : FrameRel body mach af tf)
    (hdisj : MemoryAllocDisjoint tf)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hops : ∀ op ∈ ops, WellTypedLM2_1ScalarOperand body tf op { kind := elemKind, layoutIdx := 0 })
    (globals : List CapturedAllocation) :
    evalOperands af.locals ops .nil globals body.layouts .nil = .ub ∨
      ∃ vals locals_final,
        evalOperands af.locals ops .nil globals body.layouts .nil = .ok vals locals_final ∧
        get? locals_final arrIdx = get? af.locals arrIdx := by
  induction ops generalizing af tf with
  | nil =>
    exact Or.inr ⟨[], af.locals, rfl, rfl⟩
  | cons op rest ih =>
    have hop : WellTypedLM2_1ScalarOperand body tf op { kind := elemKind, layoutIdx := 0 } :=
      hops op List.mem_cons_self
    rcases evalLM2_1ScalarOperand_preserves_array_local hframe hdisj hdecl_arr hwf hprim hop
        globals none with
      ⟨heval_a, _⟩ |
      ⟨sc, _, locals₁, tf', heval_a, _, hget_arr₁, _, _, _, hframe', hdisj', hmono', _⟩
    · exact Or.inl (by simp [evalOperands, heval_a])
    · have hrest : ∀ op' ∈ rest,
          WellTypedLM2_1ScalarOperand body tf' op' { kind := elemKind, layoutIdx := 0 } :=
        fun op' hmem => (hops op' (List.mem_cons_of_mem _ hmem)).mono_immediate hmono'
      rcases ih hframe' hdisj' hrest with hub | ⟨vs, locals_final, hvs, hget_arr_f⟩
      · exact Or.inl (by simp [evalOperands, heval_a, hub])
      · exact Or.inr ⟨.scalar sc :: vs, locals_final, by simp [evalOperands, heval_a, hvs],
          hget_arr_f.trans hget_arr₁⟩

/-- Loop body of `Miri.Interpreter.writeAggregate` for `AggregateKind.Array`. -/
def aggLoopBody {P S C V : Type}
    (h : Miri.Interpreter.AggregateHooks P S C V) (choice : C)
    (operands : Array Miri.MIR.Operand) (dest : V)
    (index : Nat) (_ : PUnit) : Miri.Interpreter.RvalueM S (ForInStep PUnit) :=
  match operands[index]? with
  | some operand => do
    let field ← h.projectField choice dest index
    let operand ← h.evalOperandAt choice (Miri.Interpreter.OperandPath.aggregate index)
      operand (some (h.placeLayout field))
    h.copyOpNoValidate choice operand field false
    pure (ForInStep.yield PUnit.unit)
  | none => do
    throw (.invalidProgram "aggregate operand index")
    pure (ForInStep.yield PUnit.unit)

theorem writeAggregate_array_def {P S C V : Type}
    (h : Miri.Interpreter.AggregateHooks P S C V) (choice : C)
    (elemTy : Miri.MIR.TyId) (operands : Array Miri.MIR.Operand) (dest : V) :
    Miri.Interpreter.writeAggregate h choice (.Array elemTy) operands dest =
      (do
        forIn [:operands.size] PUnit.unit (aggLoopBody h choice operands dest)
        h.writeDiscriminant choice 0 dest
        if ← h.enforceValidity choice (h.placeLayout dest) then
          h.validate choice dest) := by
  unfold Miri.Interpreter.writeAggregate aggLoopBody
  simp only [pure_bind, Option.isSome, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Option.getD_none]
  congr 2
  ext index u
  cases operands[index]? <;> rfl

private theorem EStateM.bind_congr_apply {ε σ α β : Type}
    {m₁ m₂ : EStateM ε σ α} {f : α → EStateM ε σ β} {s₁ s₂ : σ}
    (h : m₁ s₁ = m₂ s₂) :
    (m₁ >>= f) s₁ = (m₂ >>= f) s₂ := by
  change (match m₁ s₁ with | .ok a s => f a s | .error e s => .error e s) =
         (match m₂ s₂ with | .ok a s => f a s | .error e s => .error e s)
  rw [h]

/-- When `dstIdx` is `.dead`, `writeAggregate` on an array destination fails with
`StepError.undefinedBehavior "write to dead local"` (either at `projectField 0`
when `operands.size > 0`, or at `writeDiscriminant` when `operands.size = 0`). -/
theorem writeAggregate_dead_err
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hdead : (tf.locals[dstIdx]'hlt).value = .dead)
    (elemTyId : Miri.MIR.TyId) (operands : Array Miri.MIR.Operand) :
    Miri.Interpreter.writeAggregate (annealAggregateHooks body.localDecls body.layouts) ()
      (.Array elemTyId) operands ⟨.local 0 dstIdx none id, translateTy arrTy body.layouts⟩ m =
      .error (.undefinedBehavior "write to dead local") m := by
  let h := annealAggregateHooks body.localDecls body.layouts
  let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none id, translateTy arrTy body.layouts⟩
  have hens_err := annealEnsureAllocated_dead (lay := translateTy arrTy body.layouts)
    (id := id) hframes hlt hdead
  rw [writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  cases hsz : operands.size with
  | zero =>
    simp only [List.range', List.forIn_nil, pure_bind]
    dsimp only [annealAggregateHooks]
    rw [← EStateM.bind_assoc_apply]
    exact EStateM.bind_eq_error hens_err
  | succ n =>
    have hlt0 : 0 < operands.size := by omega
    have hget0 : operands[0]? = some (operands[0]'hlt0) := Array.getElem?_eq_getElem hlt0
    rw [List.range'_succ]
    simp only [List.forIn_cons]
    have hstep0 :
        aggLoopBody h () operands dest 0 PUnit.unit m =
        .error (.undefinedBehavior "write to dead local") m := by
      unfold aggLoopBody
      rw [hget0]
      have hproj_err : h.projectField () dest 0 m =
          .error (.undefinedBehavior "write to dead local") m := by
        dsimp only [h, annealAggregateHooks, dest]
        rw [hwf.arr_fields]
        dsimp only
        exact EStateM.bind_eq_error hens_err
      exact EStateM.bind_eq_error hproj_err
    rw [← EStateM.bind_assoc_apply]
    exact EStateM.bind_eq_error hstep0

/-- When `dstIdx` holds `.live (.immediate imm_dst)` in `tf`, `writeAggregate` on `st_pre`
produces the exact same result as `writeAggregate` starting from `st_alloc₀` where
`annealEnsureAllocated` has already allocated `(allocId, alloc₀)` at `dstIdx`. -/
theorem writeAggregate_pre_eq_alloc0
    {body : CapturedMir} {mach : AnnealMachine}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {alloc₀ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hlt : dstIdx < tf.locals.size)
    (hens_pre :
      annealEnsureAllocated ⟨.local 0 dstIdx none id, translateTy arrTy body.layouts⟩
        { stack := ⟨#[tf]⟩, machine := mach } =
      .ok (stackAllocPlace allocId)
        { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt (stackAllocPlace allocId)]⟩,
          machine := stackAllocMachine mach mem' allocId alloc₀ })
    (elemTyId : Miri.MIR.TyId) (operands : Array Miri.MIR.Operand) :
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none id, translateTy arrTy body.layouts⟩
    let st_pre : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
    let st_alloc₀ : AnnealStepState :=
      { stack := ⟨#[setFrameLocalIndirect tf dstIdx hlt (stackAllocPlace allocId)]⟩,
        machine := stackAllocMachine mach mem' allocId alloc₀ }
    Miri.Interpreter.writeAggregate (annealAggregateHooks body.localDecls body.layouts) ()
      (.Array elemTyId) operands dest st_pre =
    Miri.Interpreter.writeAggregate (annealAggregateHooks body.localDecls body.layouts) ()
      (.Array elemTyId) operands dest st_alloc₀ := by
  dsimp only
  let h := annealAggregateHooks body.localDecls body.layouts
  let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none id, translateTy arrTy body.layouts⟩
  let tf_ind := setFrameLocalIndirect tf dstIdx hlt (stackAllocPlace allocId)
  let st_pre : AnnealStepState := { stack := ⟨#[tf]⟩, machine := mach }
  let st_alloc₀ : AnnealStepState :=
    { stack := ⟨#[tf_ind]⟩, machine := stackAllocMachine mach mem' allocId alloc₀ }
  have hlt_ind : dstIdx < tf_ind.locals.size := by
    unfold tf_ind setFrameLocalIndirect; simp [hlt]
  have hind_val : (tf_ind.locals[dstIdx]'hlt_ind).value =
      .live (.indirect (stackAllocPlace allocId)) := by
    have hget : tf_ind.locals[dstIdx]? =
        some { tf.locals[dstIdx]'hlt with value := .live (.indirect (stackAllocPlace allocId)) } := by
      unfold tf_ind setFrameLocalIndirect
      rw [Array.getElem?_set]
      simp
    rw [Array.getElem?_eq_getElem hlt_ind] at hget
    injection hget with hget_eq
    rw [hget_eq]
  have hens_id := annealEnsureAllocated_stackAlloc_idempotent
    (mach := mach) (mem' := mem') (allocId := allocId) (alloc := alloc₀)
    (tf := tf_ind) (id := id) (lay := translateTy arrTy body.layouts)
    hlt_ind hind_val
  dsimp only at hens_id
  rw [writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  cases hsz : operands.size with
  | zero =>
    simp only [List.range', List.forIn_nil, pure_bind]
    dsimp only [annealAggregateHooks]
    rw [← EStateM.bind_assoc_apply, ← EStateM.bind_assoc_apply,
      EStateM.bind_eq_ok hens_pre, EStateM.bind_eq_ok hens_id]
  | succ n =>
    have hlt0 : 0 < operands.size := by omega
    have hget0 : operands[0]? = some (operands[0]'hlt0) := Array.getElem?_eq_getElem hlt0
    rw [List.range'_succ]
    simp only [List.forIn_cons]
    have hproj_eq : h.projectField () dest 0 st_pre = h.projectField () dest 0 st_alloc₀ := by
      dsimp only [h, annealAggregateHooks, dest]
      rw [hwf.arr_fields]
      dsimp only
      rw [EStateM.bind_eq_ok hens_pre, EStateM.bind_eq_ok hens_id]
    have hstep0_eq :
        aggLoopBody h () operands dest 0 PUnit.unit st_pre =
        aggLoopBody h () operands dest 0 PUnit.unit st_alloc₀ := by
      unfold aggLoopBody
      rw [hget0]
      exact EStateM.bind_congr_apply hproj_eq
    rw [← EStateM.bind_assoc_apply, ← EStateM.bind_assoc_apply]
    exact EStateM.bind_congr_apply hstep0_eq

/-- Parametric induction over any suffix `remOps` of array aggregate operands starting
at element index `k`: either `evalOperands` hits UB and `lean-miri` raises
`StepError.undefinedBehavior`, or all remaining elements are written sequentially
establishing `ArraySliceRel elemKind count body.layouts (elems_k ++ vals)`. -/
theorem writeAggregate_loop_spec
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {dstIdx : Local} {dstDecl : LocalDecl} {id : Miri.Interpreter.LocalsIdentity}
    {elemKind : RigidTy} {count : Nat}
    {mem' : AnnealMemory} {allocId : Miri.Memory.AllocId}
    {operands : Array Miri.MIR.Operand}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false)
    (globals : List CapturedAllocation)
    (remOps : List MirAst.Operand)
    (k : Nat)
    (tf_k : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hlt_k : dstIdx < tf_k.locals.size)
    (elems_k : List Value)
    (alloc_k : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hk_len : k + remOps.length = count)
    (hops_arr : ∀ i (hi : i < remOps.length),
      operands[k + i]? = some (translateOperand (remOps[i]'hi)))
    (hframe_k : FrameRel body mach af tf_k)
    (hdisj_k : MemoryAllocDisjoint tf_k)
    (hops_k : ∀ op ∈ remOps, WellTypedLM2_1ScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 })
    (hsize_k : alloc_k.byteSize = (translateTy dstDecl.ty body.layouts).layout.size)
    (hslice_k : ArraySliceRel elemKind k body.layouts elems_k Miri.ABI.Size.ZERO alloc_k) :
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none id, translateTy dstDecl.ty body.layouts⟩
    let st_k : AnnealStepState :=
      { stack := ⟨#[setFrameLocalIndirect tf_k dstIdx hlt_k (stackAllocPlace allocId)]⟩,
        machine := stackAllocMachine mach mem' allocId alloc_k }
    let prog : Miri.Interpreter.RvalueM AnnealStepState Unit := do
      forIn (List.range' k remOps.length) PUnit.unit (aggLoopBody h () operands dest)
      h.writeDiscriminant () 0 dest
      if ← h.enforceValidity () (h.placeLayout dest) then
        h.validate () dest
    (evalOperands af.locals remOps .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg, prog st_k = .error (.undefinedBehavior msg) m') ∨
    (∃ vals locals_final tf_final, ∃ hlt_final : dstIdx < tf_final.locals.size, ∃ alloc_final,
      evalOperands af.locals remOps .nil globals body.layouts .nil = .ok vals locals_final ∧
      prog st_k =
        .ok () { stack := ⟨#[setFrameLocalIndirect tf_final dstIdx hlt_final (stackAllocPlace allocId)]⟩,
                 machine := stackAllocMachine mach mem' allocId alloc_final } ∧
      get? locals_final dstIdx = get? af.locals dstIdx ∧
      FrameRel body mach { af with locals := locals_final } tf_final ∧
      MemoryAllocDisjoint tf_final ∧
      (∀ j, IsImmediateFrameLocal tf_k j → IsImmediateFrameLocal tf_final j) ∧
      tf_final = { tf_k with locals := tf_final.locals } ∧
      alloc_final.byteSize = (translateTy dstDecl.ty body.layouts).layout.size ∧
      ArraySliceRel elemKind count body.layouts (elems_k ++ vals) Miri.ABI.Size.ZERO alloc_final) := by
  induction remOps generalizing af k tf_k elems_k alloc_k with
  | nil =>
    dsimp only [List.length_nil] at hk_len ⊢
    subst hk_len
    right
    let tf_ind := setFrameLocalIndirect tf_k dstIdx hlt_k (stackAllocPlace allocId)
    have hlt_ind : dstIdx < tf_ind.locals.size := by
      unfold tf_ind setFrameLocalIndirect; simp [hlt_k]
    have hind_val : (tf_ind.locals[dstIdx]'hlt_ind).value =
        .live (.indirect (stackAllocPlace allocId)) := by
      have hget : tf_ind.locals[dstIdx]? =
          some { tf_k.locals[dstIdx]'hlt_k with value := .live (.indirect (stackAllocPlace allocId)) } := by
        unfold tf_ind setFrameLocalIndirect; rw [Array.getElem?_set]; simp
      rw [Array.getElem?_eq_getElem hlt_ind] at hget
      injection hget with hget_eq; rw [hget_eq]
    have hens_id := annealEnsureAllocated_stackAlloc_idempotent
      (mach := mach) (mem' := mem') (allocId := allocId) (alloc := alloc_k)
      (tf := tf_ind) (id := id) (lay := translateTy dstDecl.ty body.layouts)
      hlt_ind hind_val
    dsimp only at hens_id
    refine ⟨[], af.locals, tf_k, hlt_k, alloc_k, rfl, ?_, rfl, hframe_k, hdisj_k,
      fun _ hj => hj, rfl, hsize_k, by simpa using hslice_k⟩
    simp only [List.range', List.forIn_nil, pure_bind]
    dsimp only [annealAggregateHooks]
    rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hens_id]
    rfl
  | cons op rest ih =>
    dsimp only [List.length_cons] at hk_len ⊢
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none id, translateTy dstDecl.ty body.layouts⟩
    let tf_ind := setFrameLocalIndirect tf_k dstIdx hlt_k (stackAllocPlace allocId)
    let st_k : AnnealStepState :=
      { stack := ⟨#[tf_ind]⟩, machine := stackAllocMachine mach mem' allocId alloc_k }
    have hget_k : operands[k]? = some (translateOperand op) := by
      simpa using hops_arr 0 (Nat.zero_lt_succ _)
    have hlt_ind : dstIdx < tf_ind.locals.size := by
      unfold tf_ind setFrameLocalIndirect; simp [hlt_k]
    have hind_val : (tf_ind.locals[dstIdx]'hlt_ind).value =
        .live (.indirect (stackAllocPlace allocId)) := by
      have hget : tf_ind.locals[dstIdx]? =
          some { tf_k.locals[dstIdx]'hlt_k with value := .live (.indirect (stackAllocPlace allocId)) } := by
        unfold tf_ind setFrameLocalIndirect; rw [Array.getElem?_set]; simp
      rw [Array.getElem?_eq_getElem hlt_ind] at hget
      injection hget with hget_eq; rw [hget_eq]
    have hens_id := annealEnsureAllocated_stackAlloc_idempotent
      (mach := mach) (mem' := mem') (allocId := allocId) (alloc := alloc_k)
      (tf := tf_ind) (id := id) (lay := translateTy dstDecl.ty body.layouts)
      hlt_ind hind_val
    dsimp only at hens_id
    let elemLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts
    let elemSize := elemLay.layout.size
    let elemOff_k := Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))
    let mp_k : Miri.Interpreter.MemPlace AnnealProv :=
      { (stackAllocPlace allocId) with
        ptr := { (stackAllocPlace allocId).ptr with
          offset := Miri.ABI.Size.ofBytes ((stackAllocPlace allocId).ptr.offset.bytes + elemOff_k.bytes) } }
    let fieldPlace : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.memory mp_k, elemLay⟩
    have hlay_fp : h.placeLayout fieldPlace = elemLay := rfl
    have hproj_k : h.projectField () dest k st_k = .ok fieldPlace st_k := by
      dsimp only [h, dest, annealAggregateHooks, fieldPlace, mp_k, elemOff_k, elemSize, elemLay]
      rw [hwf.arr_fields]
      dsimp only
      rw [EStateM.bind_eq_ok hens_id, hwf.elem_layout_eq]
      rfl
    have hop_head : WellTypedLM2_1ScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 } :=
      hops_k op List.mem_cons_self
    rcases evalLM2_1ScalarOperand_with_indirect_dst
        (mach' := stackAllocMachine mach mem' allocId alloc_k)
        hframe_k hdecl_dst hwf hprim hop_head hlt_k (stackAllocPlace allocId)
        globals (Miri.Interpreter.OperandPath.aggregate k) (some elemLay) with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, locals_k1, tf_k1, hlt_k1, ha_ok, hm_ok, hget_dst1, hframe_k1, hdisj_imp1,
        hmono_1, htf_eq1, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
    · left
      refine ⟨by simp [evalOperands, ha_ub], m', msg, ?_⟩
      rw [List.range'_succ]
      simp only [List.forIn_cons]
      have hstep_err :
          aggLoopBody h () operands dest k PUnit.unit st_k =
          .error (.undefinedBehavior msg) m' := by
        unfold aggLoopBody
        rw [hget_k]
        dsimp only
        rw [EStateM.bind_eq_ok hproj_k, hlay_fp, EStateM.bind_eq_error hm_err]
      rw [← EStateM.bind_assoc_apply]
      exact EStateM.bind_eq_error hstep_err
    · have hin_k : (k + 1) * elemSize.bytes.toNat ≤ alloc_k.byteSize.bytes.toNat := by
        rw [hsize_k, hwf.arr_size_toNat]
        exact Nat.mul_le_mul_right _ (by omega)
      obtain ⟨alloc_k1, hwrite_k1, hbs_k1, _, _, hslice_k1⟩ :=
        annealWriteImmediate_stackAlloc_snoc (mach := mach) (mem' := mem') (allocId := allocId)
          (alloc := alloc_k)
          (tf := setFrameLocalIndirect tf_k1 dstIdx hlt_k1 (stackAllocPlace allocId))
          (k := k) (destLay := elemLay)
          hfresh hslice_k hrel_sc hsz_sc hbool_sc hchar_sc hin_k
      let st_k1 : AnnealStepState :=
        { stack := ⟨#[setFrameLocalIndirect tf_k1 dstIdx hlt_k1 (stackAllocPlace allocId)]⟩,
          machine := stackAllocMachine mach mem' allocId alloc_k1 }
      have hcopy_ok :
          h.copyOpNoValidate ()
            ⟨.immediate (.scalar (.fromScalarInt msc)), elemLay⟩ fieldPlace false
            { stack := ⟨#[setFrameLocalIndirect tf_k1 dstIdx hlt_k1 (stackAllocPlace allocId)]⟩,
              machine := stackAllocMachine mach mem' allocId alloc_k } =
          .ok () st_k1 := by
        dsimp only [h, annealAggregateHooks, annealReadImmediate, pure, EStateM.pure, bind,
          EStateM.bind]
        exact hwrite_k1
      have hstep_ok :
          aggLoopBody h () operands dest k PUnit.unit st_k =
          .ok (ForInStep.yield PUnit.unit) st_k1 := by
        unfold aggLoopBody
        rw [hget_k]
        dsimp only
        rw [EStateM.bind_eq_ok hproj_k, hlay_fp, EStateM.bind_eq_ok hm_ok,
          EStateM.bind_eq_ok hcopy_ok]
        rfl
      have hk_len1 : (k + 1) + rest.length = count := by omega
      have hops_arr1 : ∀ i (hi : i < rest.length),
          operands[(k + 1) + i]? = some (translateOperand (rest[i]'hi)) := by
        intro i hi
        have hidx : (k + 1) + i = k + (i + 1) := by omega
        rw [hidx]
        simpa using hops_arr (i + 1) (Nat.succ_lt_succ hi)
      have hops_k1 : ∀ op' ∈ rest,
          WellTypedLM2_1ScalarOperand body tf_k1 op' { kind := elemKind, layoutIdx := 0 } :=
        fun op' hmem => (hops_k op' (List.mem_cons_of_mem _ hmem)).mono_immediate hmono_1
      have hsize_k1 : alloc_k1.byteSize = (translateTy dstDecl.ty body.layouts).layout.size :=
        hbs_k1.trans hsize_k
      rcases ih (af := { af with locals := locals_k1 }) (k + 1) tf_k1 hlt_k1
          (elems_k ++ [.scalar sc]) alloc_k1 hk_len1 hops_arr1 hframe_k1
          (hdisj_imp1 hdisj_k) hops_k1 hsize_k1 hslice_k1 with
        ⟨ha_rest_ub, m', msg, hm_rest_err⟩ |
        ⟨vs, locals_final, tf_final, hlt_final, alloc_final, ha_rest_ok, hm_rest_ok,
          hget_dst_f, hframe_final, hdisj_final, hmono_final, htf_eq_final,
          hsize_final, hslice_final⟩
      · left
        dsimp only at ha_rest_ub
        refine ⟨by simp [evalOperands, ha_ok, ha_rest_ub], m', msg, ?_⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_err
      · right
        dsimp only at ha_rest_ok hget_dst_f hframe_final
        have htf_eq_tot : tf_final = { tf_k with locals := tf_final.locals } := by
          rw [htf_eq_final, htf_eq1]
        have hslice_tot :
            ArraySliceRel elemKind count body.layouts (elems_k ++ (.scalar sc :: vs))
              Miri.ABI.Size.ZERO alloc_final := by
          simpa [List.append_assoc] using hslice_final
        refine ⟨.scalar sc :: vs, locals_final, tf_final, hlt_final, alloc_final,
          by simp [evalOperands, ha_ok, ha_rest_ok], ?_, hget_dst_f.trans hget_dst1,
          hframe_final, hdisj_final, fun j hj => hmono_final j (hmono_1 j hj), htf_eq_tot,
          hsize_final, hslice_tot⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_ok

/-- Parametric induction over any suffix `remOps` of array aggregate operands starting
at element index `k` when `dstIdx` is already `.live (.indirect mp)` (`inplaceMachine`):
either `evalOperands` hits UB and `lean-miri` raises `StepError.undefinedBehavior`,
or all remaining elements are written sequentially in place at `relOffset`, establishing
`ArraySliceRel elemKind count body.layouts (elems_k ++ vals)`. -/
theorem writeAggregate_inplace_loop_spec
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {dstIdx : Local} {dstDecl : LocalDecl} {id : Miri.Interpreter.LocalsIdentity}
    {elemKind : RigidTy} {count : Nat}
    {allocIdx : Nat} {allocId : Miri.Memory.AllocId}
    {tag : Miri.Memory.BorTag} {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {cachedLay : Option Miri.Interpreter.LocalLayout}
    {operands : Array Miri.MIR.Operand}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hlt_idx : allocIdx < mach.memory.live.size)
    (hfind : mach.memory.live.findIdx? (fun (aid, _) => aid == allocId) = some allocIdx)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : mach.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
    (globals : List CapturedAllocation)
    (remOps : List MirAst.Operand)
    (k : Nat)
    (tf_k : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hmls_k : tf_k.locals[dstIdx]? = some ⟨.live (.indirect mp), cachedLay⟩)
    (elems_k : List Value)
    (alloc_k : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hk_len : k + remOps.length = count)
    (hops_arr : ∀ i (hi : i < remOps.length),
      operands[k + i]? = some (translateOperand (remOps[i]'hi)))
    (hframe_k : FrameRel body mach af tf_k)
    (hdisj_k : MemoryAllocDisjoint tf_k)
    (hops_k : ∀ op ∈ remOps, WellTypedLM2_1ScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 })
    (hin_k :
      relOffset.bytes.toNat + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
        alloc_k.byteSize.bytes.toNat)
    (hslice_k : ArraySliceRel elemKind k body.layouts elems_k relOffset alloc_k) :
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none id, translateTy dstDecl.ty body.layouts⟩
    let st_k : AnnealStepState :=
      { stack := ⟨#[tf_k]⟩,
        machine := inplaceMachine mach allocIdx allocId kind alloc_k }
    let prog : Miri.Interpreter.RvalueM AnnealStepState Unit := do
      forIn (List.range' k remOps.length) PUnit.unit (aggLoopBody h () operands dest)
      h.writeDiscriminant () 0 dest
      if ← h.enforceValidity () (h.placeLayout dest) then
        h.validate () dest
    (evalOperands af.locals remOps .nil globals body.layouts .nil = .ub ∧
      ∃ m' msg, prog st_k = .error (.undefinedBehavior msg) m') ∨
    (∃ vals locals_final tf_final alloc_final,
      evalOperands af.locals remOps .nil globals body.layouts .nil = .ok vals locals_final ∧
      prog st_k =
        .ok () { stack := ⟨#[tf_final]⟩,
                 machine := inplaceMachine mach allocIdx allocId kind alloc_final } ∧
      get? locals_final dstIdx = get? af.locals dstIdx ∧
      tf_final.locals[dstIdx]? = some ⟨.live (.indirect mp), cachedLay⟩ ∧
      FrameRel body mach { af with locals := locals_final } tf_final ∧
      MemoryAllocDisjoint tf_final ∧
      (∀ j, IsImmediateFrameLocal tf_k j → IsImmediateFrameLocal tf_final j) ∧
      tf_final = { tf_k with locals := tf_final.locals } ∧
      alloc_final.byteSize = alloc_k.byteSize ∧
      ArraySliceRel elemKind count body.layouts (elems_k ++ vals) relOffset alloc_final) := by
  induction remOps generalizing af k tf_k elems_k alloc_k with
  | nil =>
    dsimp only [List.length_nil] at hk_len ⊢
    subst hk_len
    right
    obtain ⟨hlt_k, hget_eq⟩ := Array.getElem?_eq_some_iff.mp hmls_k
    have hind_val : (tf_k.locals[dstIdx]'hlt_k).value = .live (.indirect mp) := by
      rw [hget_eq]
    have hens_id := annealEnsureAllocated_indirect
      (st := { stack := ⟨#[tf_k]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc_k })
      (tf := tf_k) (id := id) (lay := translateTy dstDecl.ty body.layouts)
      rfl hlt_k hind_val
    refine ⟨[], af.locals, tf_k, alloc_k, rfl, ?_, rfl, hmls_k, hframe_k, hdisj_k,
      fun _ hj => hj, rfl, rfl, by simpa using hslice_k⟩
    simp only [List.range', List.forIn_nil, pure_bind]
    dsimp only [annealAggregateHooks]
    rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hens_id]
    rfl
  | cons op rest ih =>
    dsimp only [List.length_cons] at hk_len ⊢
    let h := annealAggregateHooks body.localDecls body.layouts
    let dest : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none id, translateTy dstDecl.ty body.layouts⟩
    let st_k : AnnealStepState :=
      { stack := ⟨#[tf_k]⟩, machine := inplaceMachine mach allocIdx allocId kind alloc_k }
    have hget_k : operands[k]? = some (translateOperand op) := by
      simpa using hops_arr 0 (Nat.zero_lt_succ _)
    obtain ⟨hlt_k, hget_eq⟩ := Array.getElem?_eq_some_iff.mp hmls_k
    have hind_val : (tf_k.locals[dstIdx]'hlt_k).value = .live (.indirect mp) := by
      rw [hget_eq]
    have hens_id := annealEnsureAllocated_indirect
      (st := st_k) (tf := tf_k) (id := id) (lay := translateTy dstDecl.ty body.layouts)
      rfl hlt_k hind_val
    let elemLay := translateTy { kind := elemKind, layoutIdx := 0 } body.layouts
    let elemSize := elemLay.layout.size
    let elemOff_k := Miri.ABI.Size.ofBytes (UInt64.ofNat (k * elemSize.bytes.toNat))
    let mp_k : Miri.Interpreter.MemPlace AnnealProv :=
      { mp with
        ptr := { mp.ptr with
          offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff_k.bytes) } }
    let fieldPlace : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.memory mp_k, elemLay⟩
    have hlay_fp : h.placeLayout fieldPlace = elemLay := rfl
    have hproj_k : h.projectField () dest k st_k = .ok fieldPlace st_k := by
      dsimp only [h, dest, annealAggregateHooks, fieldPlace, mp_k, elemOff_k, elemSize, elemLay]
      rw [hwf.arr_fields]
      dsimp only
      rw [EStateM.bind_eq_ok hens_id, hwf.elem_layout_eq]
      rfl
    have hop_head : WellTypedLM2_1ScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 } :=
      hops_k op List.mem_cons_self
    rcases evalLM2_1ScalarOperand_for_agg_inplace
        (mach' := inplaceMachine mach allocIdx allocId kind alloc_k)
        hframe_k hdecl_dst hwf hprim hop_head
        globals (Miri.Interpreter.OperandPath.aggregate k) (some elemLay) with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, locals_k1, tf_k1, ha_ok, hm_ok, hget_dst1, hdst_pres1, hframe_k1,
        hdisj_imp1, hmono_1, htf_eq1, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
    · left
      refine ⟨by simp [evalOperands, ha_ub], m', msg, ?_⟩
      rw [List.range'_succ]
      simp only [List.forIn_cons]
      have hstep_err :
          aggLoopBody h () operands dest k PUnit.unit st_k =
          .error (.undefinedBehavior msg) m' := by
        unfold aggLoopBody
        rw [hget_k]
        dsimp only
        rw [EStateM.bind_eq_ok hproj_k, hlay_fp, EStateM.bind_eq_error hm_err]
      rw [← EStateM.bind_assoc_apply]
      exact EStateM.bind_eq_error hstep_err
    · have hin_elem_k :
          relOffset.bytes.toNat + (k + 1) * elemSize.bytes.toNat ≤
            alloc_k.byteSize.bytes.toNat := by
        have hin_arr := hin_k
        rw [hwf.arr_size_toNat] at hin_arr
        have hle : (k + 1) * elemSize.bytes.toNat ≤ count * elemSize.bytes.toNat :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [elemSize, elemLay] at hle ⊢
        omega
      obtain ⟨alloc_k1, hwrite_k1, hbs_k1, _, _, hslice_k1⟩ :=
        annealWriteImmediate_inplace_snoc (mach := mach) (allocIdx := allocIdx)
          (allocId := allocId) (kind := kind) (alloc := alloc_k) (mp := mp)
          (tf := tf_k1) (k := k) (destLay := elemLay)
          hlt_idx hfind hprov hbase hptr hslice_k hrel_sc hsz_sc hbool_sc hchar_sc hin_elem_k
      let st_k1 : AnnealStepState :=
        { stack := ⟨#[tf_k1]⟩,
          machine := inplaceMachine mach allocIdx allocId kind alloc_k1 }
      have hcopy_ok :
          h.copyOpNoValidate ()
            ⟨.immediate (.scalar (.fromScalarInt msc)), elemLay⟩ fieldPlace false
            { stack := ⟨#[tf_k1]⟩,
              machine := inplaceMachine mach allocIdx allocId kind alloc_k } =
          .ok () st_k1 := by
        dsimp only [h, annealAggregateHooks, annealReadImmediate, pure, EStateM.pure, bind,
          EStateM.bind]
        exact hwrite_k1
      have hstep_ok :
          aggLoopBody h () operands dest k PUnit.unit st_k =
          .ok (ForInStep.yield PUnit.unit) st_k1 := by
        unfold aggLoopBody
        rw [hget_k]
        dsimp only
        rw [EStateM.bind_eq_ok hproj_k, hlay_fp, EStateM.bind_eq_ok hm_ok,
          EStateM.bind_eq_ok hcopy_ok]
        rfl
      have hmls_k1 : tf_k1.locals[dstIdx]? = some ⟨.live (.indirect mp), cachedLay⟩ := by
        rw [hdst_pres1]; exact hmls_k
      have hk_len1 : (k + 1) + rest.length = count := by omega
      have hops_arr1 : ∀ i (hi : i < rest.length),
          operands[(k + 1) + i]? = some (translateOperand (rest[i]'hi)) := by
        intro i hi
        have hidx : (k + 1) + i = k + (i + 1) := by omega
        rw [hidx]
        simpa using hops_arr (i + 1) (Nat.succ_lt_succ hi)
      have hops_k1 : ∀ op' ∈ rest,
          WellTypedLM2_1ScalarOperand body tf_k1 op' { kind := elemKind, layoutIdx := 0 } :=
        fun op' hmem => (hops_k op' (List.mem_cons_of_mem _ hmem)).mono_immediate hmono_1
      have hin_k1 :
          relOffset.bytes.toNat + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
            alloc_k1.byteSize.bytes.toNat := by
        rw [hbs_k1]; exact hin_k
      rcases ih (af := { af with locals := locals_k1 }) (k + 1) tf_k1 hmls_k1
          (elems_k ++ [.scalar sc]) alloc_k1 hk_len1 hops_arr1 hframe_k1
          (hdisj_imp1 hdisj_k) hops_k1 hin_k1 hslice_k1 with
        ⟨ha_rest_ub, m', msg, hm_rest_err⟩ |
        ⟨vs, locals_final, tf_final, alloc_final, ha_rest_ok, hm_rest_ok,
          hget_dst_f, hmls_final, hframe_final, hdisj_final, hmono_final,
          htf_eq_final, hsize_final, hslice_final⟩
      · left
        dsimp only at ha_rest_ub
        refine ⟨by simp [evalOperands, ha_ok, ha_rest_ub], m', msg, ?_⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_err
      · right
        dsimp only at ha_rest_ok hget_dst_f hframe_final
        have htf_eq_tot : tf_final = { tf_k with locals := tf_final.locals } := by
          rw [htf_eq_final, htf_eq1]
        have hslice_tot :
            ArraySliceRel elemKind count body.layouts (elems_k ++ (.scalar sc :: vs))
              relOffset alloc_final := by
          simpa [List.append_assoc] using hslice_final
        refine ⟨.scalar sc :: vs, locals_final, tf_final, alloc_final,
          by simp [evalOperands, ha_ok, ha_rest_ok], ?_, hget_dst_f.trans hget_dst1,
          hmls_final, hframe_final, hdisj_final,
          fun j hj => hmono_final j (hmono_1 j hj), htf_eq_tot,
          hsize_final.trans hbs_k1, hslice_tot⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_ok

/-- Full single-step correspondence for `_dst = [op_0, ..., op_{count-1}]`
(`Rvalue.aggregate (.array elemTy) ops`):
handles destination `.dead` UB, source operand UB (dead/uninitialized local at any
position in `ops`, including destructive `move`s such as `[move _x, copy _x]`),
fresh stack allocation when `dstIdx` is immediate (`CanReserveAllocId`), and
in-place overwrite when `dstIdx` already holds `.init (.aggregate 0 oldElems)`
(reusing its existing allocation without reserving a new `AllocId`), establishing
`ArraySliceRel` and preserving `StateRel` (`MemoryAllocDisjoint`), `StepPreservesNodup`,
`StepPreservesImmediate`, and `StepPreservesHighWater m 1`. -/
theorem evalRvalue_aggregate_array_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl}
    {elemTy : Ty} {elemKind : RigidTy} {count : Nat}
    {ops : List MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hlen_ops : ops.length = count)
    (hdst_ready : ∀ topFrame, m.stack.frames = #[topFrame] →
      ArrayConstructDestReady s m topFrame dstIdx)
    (hops : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ op ∈ ops, WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 }) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 1
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hrel with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hdst_ready_tf := hdst_ready topFrame hframes
  have hops_tf := hops topFrame hframes
  obtain ⟨slot_dst, mls_dst, _, hlt_dst, _, hmls_dst, hmls_dst_eq, hloc_dst⟩ :=
    hframe.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst (translateTy dstDecl.ty body.layouts)
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have heval_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst hdecl_dst (by rw [hmls_dst_eq]; exact hloc_dst.layout_eq)
  have hframe₀ : FrameRel body m.machine s.frame topFrame₀ :=
    hframe.cache_local_layout hdecl_dst hlt_dst
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ :=
    hdisj.cache_layout hlt_dst _
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun j hj => hj.cache_layout hlt_dst _
  have hops₀ : ∀ op ∈ ops,
      WellTypedLM2_1ScalarOperand body topFrame₀ op { kind := elemKind, layoutIdx := 0 } :=
    fun op hmem => (hops_tf op hmem).cache_layout hlt_dst _
  let operands : Array Miri.MIR.Operand := (ops.map translateOperand).toArray
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.writeAggregate (annealAggregateHooks body.localDecls body.layouts) ()
          (.Array (encodeTyId elemTy)) operands destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, translateRvalue, translateAggregateKind,
      annealStepHooks]
    apply runRvalue_eq_of_eq
    rw [evalRvalueIntoPlace_aggregate_def]
    unfold annealRvalueHooks
    dsimp only
    exact EStateM.bind_eq_ok heval_dst
  obtain ⟨slot_dst₀, mls_dst₀, _, hlt_dst₀, hslot_dst₀, hmls_dst₀, hmls_dst₀_eq, hloc_dst₀⟩ :=
    hframe₀.lookup_local hdecl_dst
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  have hops_arr : ∀ i (hi : i < ops.length),
      operands[0 + i]? = some (translateOperand (ops[i]'hi)) := by
    intro i hi
    simp [operands, hi]
  have hsz_ops : operands.size = ops.length := by simp [operands]
  cases hloc_dst₀ with
  | dead _ _ =>
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue
      dsimp only
      rw [hbor, hcaller]
      rcases evalOperands_lm2_1_dichotomy hframe₀ hdisj₀ hdecl_dst hwf hprim hops₀ s.memory.globals with
        hub | ⟨vals, locals_final, hok, hdst_eq⟩
      · rw [hub]
      · rw [hok]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hdst_eq, hslot_dst₀]
    have hdead_val : (topFrame₀.locals[dstIdx]'hlt_dst₀).value = .dead := by
      rw [hmls_dst₀_eq]
    have hw_err := writeAggregate_dead_err (body := body) (m := m₀) (tf := topFrame₀)
      (id := topFrame.localsIdentity) hwf rfl hlt_dst₀ hdead_val (encodeTyId elemTy) operands
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
        (m₀, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_eval]
      unfold Miri.Interpreter.runRvalue
      rw [hw_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
      hstmt hm_err]
    exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
      StepPreservesHighWater.of_error⟩
  | indirect slot_dst₀ mp cachedLay hcache_dst hnot_dead hmp =>
    rcases hdst_ready_tf with hdead_s | ⟨hdst_imm_tf, _⟩ | ⟨oldElems, hold_s⟩
    · rw [hdead_s] at hslot_dst₀; injection hslot_dst₀ with heq; exact absurd heq.symm hnot_dead
    · exact False.elim ((hmono₀ dstIdx hdst_imm_tf) _ hmls_dst₀ mp rfl)
    · rw [hold_s] at hslot_dst₀; injection hslot_dst₀ with heq; subst heq
      cases hmp with
      | mk allocId tag baseAddr relOffset localAlloc
          hprov hmis hmeta hlive hbase hno_ovf hptr hmut haligned hin_arr _ hval_cons _ harr =>
        rcases localAlloc with ⟨kind, alloc₀⟩
        obtain ⟨_, _, _, hslice_old⟩ := harr elemKind count oldElems hwf.arr_kind rfl
        dsimp only at hslice_old hin_arr hval_cons hmut
        obtain ⟨allocIdx, hlt_idx, hfindIdx, hgetIdx, hset_prop⟩ :=
          array_findIdx?_of_nodup_fst hnodup hlive
        have hslice₀ : ArraySliceRel elemKind 0 body.layouts [] relOffset alloc₀ :=
          { elems_len := rfl
            alloc_len := hslice_old.alloc_len
            alloc_mut := hslice_old.alloc_mut
            alloc_prov := hslice_old.alloc_prov
            alloc_mask := hslice_old.alloc_mask
            slice_in_bounds := by have := hslice_old.slice_in_bounds; omega
            elem_rel := fun _ _ h => nomatch h }
        have hm₀_self : m₀ =
            ({ stack := ⟨#[topFrame₀]⟩,
               machine := inplaceMachine m.machine allocIdx allocId kind alloc₀ } : AnnealStepState) := by
          rw [inplaceMachine_self hgetIdx]
        rcases writeAggregate_inplace_loop_spec (body := body) (mach := m.machine) (af := s.frame)
            (dstIdx := dstIdx) (dstDecl := dstDecl) (id := topFrame.localsIdentity)
            (elemKind := elemKind) (count := count) (allocIdx := allocIdx) (allocId := allocId)
            (kind := kind) (mp := mp) (cachedLay := cachedLay) (operands := operands)
            hdecl_dst hwf hprim hlt_idx hfindIdx hprov hbase hptr s.memory.globals
            ops 0 topFrame₀ hmls_dst₀ [] alloc₀ (by simpa using hlen_ops) hops_arr
            hframe₀ hdisj₀ hops₀ hin_arr hslice₀ with
          ⟨ha_ub_ops, m', msg, hm_loop_err⟩ |
          ⟨vals, locals_final, tf_final, alloc_final, ha_ok_ops, hm_loop_ok, hget_dst_f,
            hmls_final, hframe_final, hdisj_final, hmono_final, htf_eq_final,
            hsize_final, hslice_final⟩
        · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
              body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt evalRvalue
            dsimp only
            rw [hbor, hcaller, ha_ub_ops]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
              (m', .error (.undefinedBehavior msg)) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [hm₀_self, writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
            simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hsz_ops]
            rw [hm_loop_err]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
            hstmt hm_err]
          exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
            StepPreservesHighWater.of_error⟩
        · obtain ⟨_, _, hlt_af_dst_f, _, _, _, _, _⟩ := hframe_final.lookup_local hdecl_dst
          dsimp only at hlt_af_dst_f
          have hold_f : get? locals_final dstIdx = some (.init (.aggregate 0 oldElems)) := by
            rw [hget_dst_f]; exact hold_s
          have hset_ok : set? locals_final dstIdx (.init (.aggregate 0 vals)) =
              some (locals_final.set dstIdx (.init (.aggregate 0 vals))) :=
            set?_eq_some_set hlt_af_dst_f _
          have ha_step : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
              body.localDecls body.layouts =
              MirStepNode.step (advanceStmt s
                (locals_final.set dstIdx (.init (.aggregate 0 vals))) s.memory) := by
            unfold evalStmt evalRvalue
            dsimp only
            rw [hbor, hcaller, ha_ok_ops]
            dsimp only
            rw [hprot, hbor]
            dsimp only [invalidateConflictingBorrows]
            rw [hmem_same, hold_f]
            simp [hset_ok]
          have hm_step : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
              ({ stack := ⟨#[tf_final]⟩,
                 machine := inplaceMachine m.machine allocIdx allocId kind alloc_final },
               .ok ()) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [hm₀_self, writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
            simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hsz_ops]
            rw [hm_loop_ok]
          have hretCont_f : tf_final.returnContinuation = .stop false := by
            rw [htf_eq_final]; exact hretCont
          have hretPlace_f : ∃ retLay, tf_final.returnPlace =
              .frameLocal 0 0 none retLay tf_final.localsIdentity := by
            rw [htf_eq_final]; exact ⟨retLay, hretPlace⟩
          obtain ⟨hnodup', hlive', hother_live⟩ := hset_prop ⟨kind, alloc_final⟩
          obtain ⟨hs_rel, hs_nd, hs_imm, hs_hw⟩ :=
            write_array_inplace_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := tf_final)
              hretCont_f hretPlace_f hcal hstack hbor hprot hcaller
              hframes hframe.body_eq hframe.location_eq hbb hstmt hframe_final hdisj_final
              hdecl_dst hwf hmls_final hcache_dst hprov hmis hmeta hbase hno_ovf hptr haligned
              hin_arr hval_cons hslice_old.alloc_mask hsize_final (by simpa using hslice_final)
              hlive hnodup' hlive' hother_live ha_step hm_step
              (fun j hj => hmono_final j (hmono₀ j hj))
          exact ⟨hs_rel, hs_nd, hs_imm, hs_hw.mono_budget (by decide : 0 ≤ 1)⟩
  | immediate slot_dst₀ imm_dst _ _ hval =>
    have hnot_dead : slot_dst₀ ≠ .dead := by
      rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
    have hcan_res : CanReserveAllocId m.machine.memory := by
      rcases hdst_ready_tf with hdead_s | ⟨_, hres⟩ | ⟨oldElems, hold_s⟩
      · rw [hdead_s] at hslot_dst₀; injection hslot_dst₀ with heq; exact absurd heq.symm hnot_dead
      · exact hres
      · rw [hold_s] at hslot_dst₀; injection hslot_dst₀ with heq; subst heq
        rcases hval with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
        · cases h1
        · injection hv' with hv_eq; subst hv_eq
          cases himm' with
          | scalarPair _ _ _ _ _ _ hagg _ =>
            rcases hagg with ⟨_, ht⟩ | ⟨_, _, ht⟩ <;> (rw [hwf.arr_kind] at ht; cases ht)
    obtain ⟨mem', allocId, hres⟩ := hcan_res
    have himm_val : (topFrame₀.locals[dstIdx]'hlt_dst₀).value = .live (.immediate imm_dst) := by
      rw [hmls_dst₀_eq]
    obtain ⟨alloc₀, hens_ok, hsize₀, _, _, _, hslice₀⟩ :=
      annealEnsureAllocated_immediate
        (m := { stack := ⟨#[topFrame₀]⟩, machine := m.machine }) (tf := topFrame₀)
        (id := topFrame.localsIdentity) (arrTy := dstDecl.ty)
        (layouts := body.layouts) (elemKind := elemKind)
        rfl hlt_dst₀ himm_val hres
    obtain ⟨hlive_eq, hfresh₀⟩ := reserveAllocId_ok_live hres
    have hfresh : mem'.live.any (fun entry => entry.1 == allocId) = false := by
      rw [hlive_eq]; exact hfresh₀
    have hm₀_eq : m₀ = { stack := ⟨#[topFrame₀]⟩, machine := m.machine } := rfl
    have hpre_eq := writeAggregate_pre_eq_alloc0 (body := body) (mach := m.machine)
      (tf := topFrame₀) (id := topFrame.localsIdentity)
      (arrTy := dstDecl.ty) (elemKind := elemKind) (count := count)
      (mem' := mem') (allocId := allocId) (alloc₀ := alloc₀)
      hwf hlt_dst₀ hens_ok (encodeTyId elemTy) operands
    rcases writeAggregate_loop_spec (body := body) (mach := m.machine) (af := s.frame)
        (dstIdx := dstIdx) (dstDecl := dstDecl) (id := topFrame.localsIdentity)
        (elemKind := elemKind) (count := count) (mem' := mem') (allocId := allocId)
        (operands := operands)
        hdecl_dst hwf hprim hfresh s.memory.globals ops 0 topFrame₀ hlt_dst₀ [] alloc₀
        (by simpa using hlen_ops) hops_arr hframe₀ hdisj₀ hops₀ hsize₀ hslice₀ with
      ⟨ha_ub_ops, m', msg, hm_loop_err⟩ |
      ⟨vals, locals_final, tf_final, hlt_final, alloc_final, ha_ok_ops, hm_loop_ok,
        hget_dst_f, hframe_final, hdisj_final, hmono_final, htf_eq_final,
        hsize_final, hslice_final⟩
    · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller, ha_ub_ops]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [hm₀_eq, hpre_eq, writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
        simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hsz_ops]
        rw [hm_loop_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
        StepPreservesHighWater.of_error⟩
    · obtain ⟨_, _, hlt_af_dst_f, _, _, _, _, _⟩ := hframe_final.lookup_local hdecl_dst
      dsimp only at hlt_af_dst_f
      have hslot_dst_f : get? locals_final dstIdx = some slot_dst₀ := by
        rw [hget_dst_f]; exact hslot_dst₀
      have hset_ok : set? locals_final dstIdx (.init (.aggregate 0 vals)) =
          some (locals_final.set dstIdx (.init (.aggregate 0 vals))) :=
        set?_eq_some_set hlt_af_dst_f _
      have ha_step : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
          body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s
            (locals_final.set dstIdx (.init (.aggregate 0 vals))) s.memory) := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller, ha_ok_ops]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same, hslot_dst_f]
        cases slot_dst₀ with
        | dead => exact absurd rfl hnot_dead
        | uninit => simp [hset_ok]
        | init _ => simp [hset_ok]
      have hm_step : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩) m =
          ({ stack := ⟨#[setFrameLocalIndirect tf_final dstIdx hlt_final (stackAllocPlace allocId)]⟩,
             machine := stackAllocMachine m.machine mem' allocId alloc_final },
           .ok ()) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [hm₀_eq, hpre_eq, writeAggregate_array_def, Std.Legacy.Range.forIn_eq_forIn_range']
        simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hsz_ops]
        rw [hm_loop_ok]
      have hretCont_f : tf_final.returnContinuation = .stop false := by
        rw [htf_eq_final]; exact hretCont
      have hretPlace_f : ∃ retLay, tf_final.returnPlace =
          .frameLocal 0 0 none retLay tf_final.localsIdentity := by
        rw [htf_eq_final]; exact ⟨retLay, hretPlace⟩
      exact write_array_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := tf_final)
        hretCont_f hretPlace_f hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt hframe_final hdisj_final
        hdecl_dst hwf hlt_final hres hsize_final (by simpa using hslice_final) ha_step hm_step
        hnodup (fun j hj => hmono_final j (hmono₀ j hj))

/-! ## 6. Array Element Read/Write (`step_assign_array_element_simulation`) & Master `LM-2.1` Simulation (`step_stmt_lm2_1_simulation`) -/

/-- Well-typed single array-element projection (`ProjectionElem.index idxLocal` or
`ProjectionElem.constantIndex offset minLength fromEnd`), supporting both immediate
and stack-allocated (`.indirect`) `usize` index locals. -/
inductive WellTypedArrayElemProj
    (body : CapturedMir)
    (s : MachineState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    ProjectionElem → Prop where
  | index (idxLocal : Local) (idxDecl : LocalDecl) :
      get? body.localDecls idxLocal = some idxDecl →
      idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 } →
      (IsImmediateFrameLocal topFrame idxLocal ∨
        get? s.frame.locals idxLocal = some .dead ∨
        get? s.frame.locals idxLocal = some .uninit ∨
        ∃ idxSc, get? s.frame.locals idxLocal = some (.init (.scalar idxSc))) →
      WellTypedArrayElemProj body s topFrame (.index idxLocal)
  | constantIndex (offset minLength : Nat) (fromEnd : Bool) :
      offset < 2 ^ 64 →
      minLength < 2 ^ 64 →
      ((fromEnd = false → offset < minLength) ∧
        (fromEnd = true → 0 < offset ∧ offset ≤ minLength)) →
      WellTypedArrayElemProj body s topFrame (.constantIndex offset minLength fromEnd)

/-- `WellTypedArrayElemProj` is preserved by `cacheFrameLocalLayout`. -/
theorem WellTypedArrayElemProj.cache_layout
    {body : CapturedMir} {s : MachineState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {proj : ProjectionElem}
    (h : WellTypedArrayElemProj body s tf proj)
    {j : Nat} (hlt : j < tf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    WellTypedArrayElemProj body s (cacheFrameLocalLayout tf j hlt lay) proj := by
  cases h with
  | index idxLocal idxDecl hdecl hty hslot_or_imm =>
    refine .index idxLocal idxDecl hdecl hty ?_
    rcases hslot_or_imm with himm | hrest
    · exact Or.inl (himm.cache_layout hlt lay)
    · exact Or.inr hrest
  | constantIndex offset minLength fromEnd hoff hmin hwf =>
    exact .constantIndex offset minLength fromEnd hoff hmin hwf

/-- Under `FrameRel`, a `usize` local that is either immediate in `tf` or explicitly
known to be `.dead`, `.uninit`, or `.init (.scalar _)` in `af.locals` satisfies
the 3-way `af.locals` trichotomy required by `evalProjection_index_simulation`. -/
private theorem usize_local_slot_trichotomy
    {body : CapturedMir} {mach : AnnealMachine} {af : StackFrame}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframe : FrameRel body mach af tf)
    {idxLocal : Local} {idxDecl : LocalDecl}
    (hdecl : get? body.localDecls idxLocal = some idxDecl)
    (hty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 })
    (hslot_or_imm :
      IsImmediateFrameLocal tf idxLocal ∨
      get? af.locals idxLocal = some .dead ∨
      get? af.locals idxLocal = some .uninit ∨
      ∃ idxSc, get? af.locals idxLocal = some (.init (.scalar idxSc))) :
    get? af.locals idxLocal = some .dead ∨
    get? af.locals idxLocal = some .uninit ∨
    ∃ idxSc, get? af.locals idxLocal = some (.init (.scalar idxSc)) := by
  rcases hslot_or_imm with himm | hrest
  · obtain ⟨_, mls_i, _, _, hslot_i, hmls_i, _, hloc_i⟩ := hframe.lookup_local hdecl
    cases hloc_i with
    | dead _ _ => exact Or.inl hslot_i
    | indirect _ mp_i _ _ _ _ => exact absurd rfl (himm _ hmls_i mp_i)
    | immediate _ _ _ _ himm_i =>
      rcases himm_i with ⟨rfl, _⟩ | ⟨_, rfl, himmRel_i⟩
      · exact Or.inr (Or.inl hslot_i)
      · obtain ⟨idxSc, _, rfl, _, _, _, _, _⟩ :=
          himmRel_i.of_primitive_scalar (by rw [hty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
        exact Or.inr (Or.inr ⟨idxSc, hslot_i⟩)
  · exact hrest

/-- Construct a projected array-element read `MirAst.Operand` (`copy` when `isMove = false`,
`move` when `isMove = true`). -/
def arrayElemReadOperand (isMove : Bool) (arrIdx : Local) (proj : ProjectionElem) :
    MirAst.Operand :=
  if isMove then .move ⟨arrIdx, [proj]⟩ else .copy ⟨arrIdx, [proj]⟩

/-- Evaluating a projected array-element read operand (`copy _arr[proj]` or `move _arr[proj]`)
for `WellTypedArrayElemProj` (`Index` or `ConstantIndex`):
either both Anneal (`evalOperand`) and Miri (`annealEvalOperand >>= annealReadImmediate`)
raise UB (dead/uninitialized array, dead/uninitialized index local, or out-of-bounds index),
or both succeed returning `ImmediateRel`-related scalars without mutating `s.frame.locals`
or `m.machine`. -/
theorem annealEvalOperand_projected_array_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {proj : ProjectionElem} (isMove : Bool)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hproj : WellTypedArrayElemProj body s topFrame proj)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      (get? s.frame.locals arrIdx = some .uninit ∧
        (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    let op := arrayElemReadOperand isMove arrIdx proj
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    (evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc topFrame',
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
        .ok (.scalar sc) s.frame.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      StateRel body s { m with stack := ⟨#[topFrame']⟩ } ∧
      FrameRel body m.machine s.frame topFrame' ∧
      MemoryAllocDisjoint topFrame' ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      ImmediateRel elemTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) := by
  dsimp only
  rcases hstate with
    ⟨tf_s, hframes_s, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have htf_eq : tf_s = topFrame := by
    rw [hframes] at hframes_s
    simpa using hframes_s.symm
  rw [htf_eq] at hretCont hretPlace hframe hdisj
  clear hframes_s htf_eq tf_s
  obtain ⟨slot_arr, mls_arr, _, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  let topFrame' :=
    cacheFrameLocalLayout topFrame arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
  let m' : AnnealStepState := { m with stack := ⟨#[topFrame']⟩ }
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hres_arr : annealResolveAndCacheLocalLayout body.localDecls body.layouts arrIdx known m =
      .ok (topFrame', translateTy arrDecl.ty body.layouts) m' :=
    annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt_arr hdecl_arr hcache_arr
  have hframe' : FrameRel body m.machine s.frame topFrame' :=
    hframe.cache_local_layout hdecl_arr hlt_arr
  have hdisj' : MemoryAllocDisjoint topFrame' :=
    hdisj.cache_layout hlt_arr _
  have hmono' : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j :=
    fun j hj => hj.cache_layout hlt_arr _
  have hstate' : StateRel body s m' :=
    StateRel.mk topFrame' rfl hretCont ⟨retLay, hretPlace⟩ hframe' hcal hstack hbor hprot hcaller hdisj'
  have hproj' : WellTypedArrayElemProj body s topFrame' proj :=
    hproj.cache_layout hlt_arr _
  have hlt_arr' : arrIdx < topFrame'.locals.size := by
    unfold topFrame' cacheFrameLocalLayout; simp [hlt_arr]
  have hval_arr' : (topFrame'.locals[arrIdx]'hlt_arr').value = mls_arr.value := by
    have hget : topFrame'.locals[arrIdx]? =
        some { topFrame.locals[arrIdx]'hlt_arr with layout := some (translateTy arrDecl.ty body.layouts) } := by
      unfold topFrame' cacheFrameLocalLayout; rw [Array.getElem?_set]; simp
    rw [Array.getElem?_eq_getElem hlt_arr'] at hget
    injection hget with hget_eq
    rw [hget_eq, hmls_arr_eq]
  have hnot_empty : m.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
  rcases harr_slot with hdead | ⟨huninit, hcount_or_imm⟩ | ⟨elems, hinit_elems⟩
  · left
    rw [hdead] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | dead _ _ =>
      have hgop : topFrame'.getLocalOperand arrIdx = .error (.localExpectedLive arrIdx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
      have ha_ub : evalOperand s.frame.locals (arrayElemReadOperand isMove arrIdx proj) .nil
          s.memory.globals body.layouts .nil = .ub := by
        cases isMove <;> cases hproj <;> simp [arrayElemReadOperand, evalOperand, hdead]
      have hm_err : annealEvalOperand body.localDecls body.layouts
          (translateOperand (arrayElemReadOperand isMove arrIdx proj)) known m =
          .error (.undefinedBehavior "read of dead local") m' := by
        cases isMove <;>
          (dsimp only [arrayElemReadOperand, translateOperand, translatePlace, List.map];
           unfold annealEvalOperand;
           simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
             hnot_empty, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw])
      exact ⟨ha_ub, m', "read of dead local", EStateM.bind_eq_error hm_err⟩
    | immediate _ _ _ _ himm =>
      rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
    | indirect _ _ _ _ hnot_dead _ =>
      exact absurd rfl hnot_dead
  · left
    rw [huninit] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    have ha_ub : evalOperand s.frame.locals (arrayElemReadOperand isMove arrIdx proj) .nil
        s.memory.globals body.layouts .nil = .ub := by
      cases isMove <;> cases hproj <;> simp [arrayElemReadOperand, evalOperand, huninit]
    cases hloc_arr with
    | immediate _ imm _ _ hval =>
      rcases hval with ⟨_, rfl⟩ | ⟨_, hv, _⟩
      · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.immediate .uninit) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
        have hm_err : annealEvalOperand body.localDecls body.layouts
            (translateOperand (arrayElemReadOperand isMove arrIdx proj)) known m =
            .error (.undefinedBehavior "projected read of uninitialized local") m' := by
          cases isMove <;> cases hproj <;>
            (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
             unfold annealEvalOperand;
             simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
               EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, throw, throwThe,
               MonadExceptOf.throw, EStateM.throw])
        exact ⟨ha_ub, m', "projected read of uninitialized local", EStateM.bind_eq_error hm_err⟩
      · cases hv
    | indirect _ mp _ _ _ hmp =>
      rcases hcount_or_imm with hpos | himm_arr
      · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
        cases hmp with
        | mk allocId tag baseAddr relOffset localAlloc
            hprov _ _ hlive hbase _ hptr _ _ _ huninit_cons _ _ _ =>
          have hfind := array_find?_of_nodup_fst hnodup hlive
          have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
            have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
            rw [hbytes, uint64_add_sub_cancel_left]; cases relOffset; rfl
          have hsz_nz : (translateTy arrDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
            intro hzero
            have hbytes0 : (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat = 0 := by
              rw [hzero]; rfl
            rw [hwf.arr_size_toNat] at hbytes0
            have := Nat.mul_pos hpos hwf.elem_size_pos
            omega
          have hnot_init := huninit_cons rfl hsz_nz
          have hchk_err : annealCheckIndirectInitialized m'.machine mp
              (translateTy arrDecl.ty body.layouts).layout.size =
              .error (.undefinedBehavior "access to uninitialized indirect place") := by
            unfold annealCheckIndirectInitialized
            dsimp only [m']
            rw [hprov]
            simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
            rfl
          have hm_err : annealEvalOperand body.localDecls body.layouts
              (translateOperand (arrayElemReadOperand isMove arrIdx proj)) known m =
              .error (.undefinedBehavior "access to uninitialized indirect place") m' := by
            cases isMove <;> cases hproj <;>
              (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
               unfold annealEvalOperand;
               simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                 EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, hchk_err, throw,
                 throwThe, MonadExceptOf.throw, EStateM.throw])
          exact ⟨ha_ub, m', "access to uninitialized indirect place", EStateM.bind_eq_error hm_err⟩
      · exact absurd rfl (himm_arr _ hmls_arr mp)
  · rw [hinit_elems] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    obtain ⟨mp, _, rfl, _, hmp⟩ := hloc_arr.array_init_is_indirect hwf.arr_kind
    have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
      unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
        Miri.Interpreter.LocalState.access
      simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
    have hchk_ok : annealCheckIndirectInitialized m'.machine mp
        (translateTy arrDecl.ty body.layouts).layout.size = .ok () :=
      annealCheckIndirectInitialized_of_array_memPlaceRel hwf hnodup hmp
    cases hproj' with
    | index idxLocal idxDecl hidx_decl hidx_ty hidx_slot_or_imm =>
      have ⟨hdead_idx, hin_idx, hoob_idx⟩ :=
        evalProjection_index_simulation (m := m') hstate' rfl hnodup hwf hmp
          hidx_decl hidx_ty
      rcases usize_local_slot_trichotomy hframe' hidx_decl hidx_ty hidx_slot_or_imm with
        hdead_i | huninit_i | ⟨idxSc, hslot_idx⟩
      · left
        obtain ⟨hr_ub, _, msg, hpl_err⟩ := hdead_idx (Or.inl hdead_i)
        have ha_ub : evalOperand s.frame.locals
            (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
            s.memory.globals body.layouts .nil = .ub := by
          cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
        have hm_err : annealEvalOperand body.localDecls body.layouts
            (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
            .error (.undefinedBehavior msg) m' := by
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            cases isMove <;>
              (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
               unfold annealEvalOperand;
               simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                 EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, hchk_ok, hpl,
                 hpl_err, throw, throwThe, MonadExceptOf.throw, EStateM.throw])
        exact ⟨ha_ub, m', msg, EStateM.bind_eq_error hm_err⟩
      · left
        obtain ⟨hr_ub, _, msg, hpl_err⟩ := hdead_idx (Or.inr huninit_i)
        have ha_ub : evalOperand s.frame.locals
            (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
            s.memory.globals body.layouts .nil = .ub := by
          cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
        have hm_err : annealEvalOperand body.localDecls body.layouts
            (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
            .error (.undefinedBehavior msg) m' := by
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            cases isMove <;>
              (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
               unfold annealEvalOperand;
               simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                 EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, hchk_ok, hpl,
                 hpl_err, throw, throwThe, MonadExceptOf.throw, EStateM.throw])
        exact ⟨ha_ub, m', msg, EStateM.bind_eq_error hm_err⟩
      · by_cases hlt_c : idxSc.bits < count
        · right
          obtain ⟨elemVal, sc_e, msc_e, _, rfl, hr_ok, hpl_ok, himm_e, hread_e⟩ :=
            hin_idx idxSc hslot_idx hlt_c
          have ha_ok : evalOperand s.frame.locals
              (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
              s.memory.globals body.layouts .nil =
              .ok (.scalar sc_e) s.frame.locals := by
            cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ok]
          obtain ⟨projOp, hm_op, hread_proj⟩ :
              ∃ projOp,
                annealEvalOperand body.localDecls body.layouts
                  (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
                  .ok projOp m' ∧
                annealReadImmediate projOp m' =
                  .ok ⟨.scalar (.fromScalarInt msc_e),
                    translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩ m' := by
            refine ⟨_, ?_, hread_e⟩
            cases isMove <;>
              (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
               unfold annealEvalOperand;
               simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                 EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl_ok, pure, EStateM.pure])
          refine ⟨sc_e, msc_e, topFrame', ha_ok, ?_, hstate', hframe', hdisj', hmono', rfl, himm_e⟩
          rw [EStateM.bind_eq_ok hm_op]
          exact hread_proj
        · left
          obtain ⟨hr_ub, _, msg, hpl_err⟩ := hoob_idx idxSc hslot_idx (Nat.le_of_not_lt hlt_c)
          have ha_ub : evalOperand s.frame.locals
              (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
              s.memory.globals body.layouts .nil = .ub := by
            cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
          have hm_err : annealEvalOperand body.localDecls body.layouts
              (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
              .error (.undefinedBehavior msg) m' := by
            cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
                ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
            | ok _ => simp [hpl, Except.mapError] at hpl_err
            | error pe =>
              simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
              cases isMove <;>
                (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
                 unfold annealEvalOperand;
                 simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                   EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, hchk_ok, hpl,
                   hpl_err, throw, throwThe, MonadExceptOf.throw, EStateM.throw])
          exact ⟨ha_ub, m', msg, EStateM.bind_eq_error hm_err⟩
    | constantIndex offset minLength fromEnd hoff hmin hwf_c =>
      have ⟨hin_c, hoob_c⟩ :=
        evalProjection_constantIndex_simulation (m := m') (locals := s.frame.locals) topFrame'
          hnodup hwf hmp offset minLength fromEnd hoff hmin hwf_c
      by_cases hle_min : minLength ≤ count
      · right
        obtain ⟨elemVal, sc_e, msc_e, _, rfl, hr_ok, hpl_ok, himm_e, hread_e⟩ := hin_c hle_min
        have ha_ok : evalOperand s.frame.locals
            (arrayElemReadOperand isMove arrIdx (.constantIndex offset minLength fromEnd)) .nil
            s.memory.globals body.layouts .nil =
            .ok (.scalar sc_e) s.frame.locals := by
          cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ok]
        obtain ⟨projOp, hm_op, hread_proj⟩ :
            ∃ projOp,
              annealEvalOperand body.localDecls body.layouts
                (translateOperand (arrayElemReadOperand isMove arrIdx
                  (.constantIndex offset minLength fromEnd))) known m =
                .ok projOp m' ∧
              annealReadImmediate projOp m' =
                .ok ⟨.scalar (.fromScalarInt msc_e),
                  translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩ m' := by
          refine ⟨_, ?_, hread_e⟩
          cases isMove <;>
            (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
             unfold annealEvalOperand;
             simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
               EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl_ok, pure, EStateM.pure])
        refine ⟨sc_e, msc_e, topFrame', ha_ok, ?_, hstate', hframe', hdisj', hmono', rfl, himm_e⟩
        rw [EStateM.bind_eq_ok hm_op]
        exact hread_proj
      · left
        obtain ⟨hr_ub, _, msg, hpl_err⟩ := hoob_c (Nat.lt_of_not_le hle_min)
        have ha_ub : evalOperand s.frame.locals
            (arrayElemReadOperand isMove arrIdx (.constantIndex offset minLength fromEnd)) .nil
            s.memory.globals body.layouts .nil = .ub := by
          cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
        have hm_err : annealEvalOperand body.localDecls body.layouts
            (translateOperand (arrayElemReadOperand isMove arrIdx
              (.constantIndex offset minLength fromEnd))) known m =
            .error (.undefinedBehavior msg) m' := by
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
              [.ConstantIndex offset minLength fromEnd] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            cases isMove <;>
              (dsimp only [arrayElemReadOperand, translateOperand, translatePlace];
               unfold annealEvalOperand;
               simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
                 EStateM.bind, pure, EStateM.pure, hnot_empty, hres_arr, hgop, hchk_ok, hpl,
                 hpl_err, throw, throwThe, MonadExceptOf.throw, EStateM.throw])
        exact ⟨ha_ub, m', msg, EStateM.bind_eq_error hm_err⟩

/-- Evaluating a projected array-element destination place `⟨arrIdx, [proj]⟩` via
`annealEvalPlace` for `WellTypedArrayElemProj` (`Index` or `ConstantIndex`):
- If `arrIdx` is `.dead` or `.uninit`, or if `proj` is UB (dead/uninitialized `idxLocal`
  or out-of-bounds index), `annealEvalPlace` raises `StepError.undefinedBehavior` and
  Anneal fails with `.ub`.
- If `arrIdx` holds `.init (.aggregate 0 elems)` and `proj` resolves to in-bounds
  index `idx < count`, `annealEvalPlace` returns `.memory elemMp` at byte offset
  `mp.ptr.offset + idx * elemSize`, and `writeProjectedValue` updates `elems.set idx v`. -/
theorem annealEvalPlace_projected_array_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat}
    {proj : ProjectionElem}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hproj : WellTypedArrayElemProj body s topFrame proj)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      (get? s.frame.locals arrIdx = some .uninit ∧
        (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := translateTy elemTy body.layouts
    ((get? s.frame.locals arrIdx = some .dead ∨
        get? s.frame.locals arrIdx = some .uninit ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
          ∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [proj] v = .ub) ∧
      ∃ m' msg,
        annealEvalPlace body.localDecls body.layouts (translatePlace ⟨arrIdx, [proj]⟩) m =
          .error (.undefinedBehavior msg) m') ∨
    (∃ elems mp idx topFrame',
      idx < count ∧
      get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [proj] v =
        .ok (.aggregate 0 (elems.set idx v))) ∧
      annealEvalPlace body.localDecls body.layouts (translatePlace ⟨arrIdx, [proj]⟩) m =
        .ok
          ⟨.memory
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idx * elemLay.layout.size.bytes.toNat)) }
              metadata := .none },
            elemLay⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      topFrame'.locals[arrIdx]? =
        some ⟨.live (.indirect mp), some (translateTy arrDecl.ty body.layouts)⟩ ∧
      MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp ∧
      FrameRel body m.machine s.frame topFrame' ∧
      MemoryAllocDisjoint topFrame' ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      topFrame' = { topFrame with locals := topFrame'.locals }) := by
  intro elemTy elemLay
  rcases hstate with
    ⟨tf_s, hframes_s, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have htf_eq : tf_s = topFrame := by
    rw [hframes] at hframes_s
    simpa using hframes_s.symm
  rw [htf_eq] at hretCont hretPlace hframe hdisj
  clear hframes_s htf_eq tf_s
  obtain ⟨slot_arr, mls_arr, _, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe.lookup_local hdecl_arr
  let topFrame' :=
    cacheFrameLocalLayout topFrame arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
  let m' : AnnealStepState := { m with stack := ⟨#[topFrame']⟩ }
  have hcache_arr : ∀ l, (topFrame.locals[arrIdx]'hlt_arr).layout = some l →
      l = translateTy arrDecl.ty body.layouts := by
    rw [hmls_arr_eq]; exact hloc_arr.layout_eq
  have hres_arr : annealResolveAndCacheLocalLayout body.localDecls body.layouts arrIdx none m =
      .ok (topFrame', translateTy arrDecl.ty body.layouts) m' :=
    annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt_arr hdecl_arr hcache_arr
  have hframe' : FrameRel body m.machine s.frame topFrame' :=
    hframe.cache_local_layout hdecl_arr hlt_arr
  have hdisj' : MemoryAllocDisjoint topFrame' :=
    hdisj.cache_layout hlt_arr _
  have hmono' : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j :=
    fun j hj => hj.cache_layout hlt_arr _
  have hstate' : StateRel body s m' :=
    StateRel.mk topFrame' rfl hretCont ⟨retLay, hretPlace⟩ hframe' hcal hstack hbor hprot hcaller hdisj'
  have hproj' : WellTypedArrayElemProj body s topFrame' proj :=
    hproj.cache_layout hlt_arr _
  have hlt_arr' : arrIdx < topFrame'.locals.size := by
    unfold topFrame' cacheFrameLocalLayout; simp [hlt_arr]
  have hmls_arr' : topFrame'.locals[arrIdx]? =
      some { mls_arr with layout := some (translateTy arrDecl.ty body.layouts) } := by
    unfold topFrame' cacheFrameLocalLayout
    rw [Array.getElem?_set]
    simp [hmls_arr_eq]
  have hval_arr' : (topFrame'.locals[arrIdx]'hlt_arr').value = mls_arr.value := by
    have hget := hmls_arr'
    rw [Array.getElem?_eq_getElem hlt_arr'] at hget
    injection hget with hget_eq
    rw [hget_eq]
  have hnot_empty : m.stack.currentFrame?.isNone = false := by
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
  rcases harr_slot with hdead | ⟨huninit, hcount_or_imm⟩ | ⟨elems, hinit_elems⟩
  · left
    rw [hdead] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | dead _ _ =>
      have hgop : topFrame'.getLocalOperand arrIdx = .error (.localExpectedLive arrIdx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
      refine ⟨Or.inl hdead, m', "projected write to dead local", ?_⟩
      dsimp only [translatePlace, List.map]
      unfold annealEvalPlace
      simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
        hnot_empty, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | immediate _ _ _ _ himm =>
      rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
    | indirect _ _ _ _ hnot_dead _ =>
      exact absurd rfl hnot_dead
  · left
    rw [huninit] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | immediate _ imm _ _ hval =>
      rcases hval with ⟨_, rfl⟩ | ⟨_, hv, _⟩
      · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.immediate .uninit) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
        refine ⟨Or.inr (Or.inl huninit), m', "projected write to uninitialized local", ?_⟩
        dsimp only [translatePlace, List.map]
        unfold annealEvalPlace
        simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
          hnot_empty, hres_arr, hgop, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      · cases hv
    | indirect _ mp _ _ _ hmp =>
      rcases hcount_or_imm with hpos | himm_arr
      · have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
        cases hmp with
        | mk allocId tag baseAddr relOffset localAlloc
            hprov _ _ hlive hbase _ hptr _ _ _ huninit_cons _ _ _ =>
          have hfind := array_find?_of_nodup_fst hnodup hlive
          have hrel_sz : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = relOffset := by
            have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
            rw [hbytes, uint64_add_sub_cancel_left]; cases relOffset; rfl
          have hsz_nz : (translateTy arrDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
            intro hzero
            have hbytes0 : (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat = 0 := by
              rw [hzero]; rfl
            rw [hwf.arr_size_toNat] at hbytes0
            have := Nat.mul_pos hpos hwf.elem_size_pos
            omega
          have hnot_init := huninit_cons rfl hsz_nz
          have hchk_err : annealCheckIndirectInitialized m'.machine mp
              (translateTy arrDecl.ty body.layouts).layout.size =
              .error (.undefinedBehavior "access to uninitialized indirect place") := by
            unfold annealCheckIndirectInitialized
            dsimp only [m']
            rw [hprov]
            simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
            rfl
          refine ⟨Or.inr (Or.inl huninit), m', "access to uninitialized indirect place", ?_⟩
          dsimp only [translatePlace, List.map]
          unfold annealEvalPlace
          simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
            hnot_empty, hres_arr, hgop, hchk_err, throw, throwThe, MonadExceptOf.throw,
            EStateM.throw]
      · exact absurd rfl (himm_arr _ hmls_arr mp)
  · rw [hinit_elems] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    obtain ⟨mp, _, rfl, _, hmp⟩ := hloc_arr.array_init_is_indirect hwf.arr_kind
    have hlen_elems : elems.length = count := by
      cases hmp with
      | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ harr =>
        exact (harr elemKind count elems hwf.arr_kind rfl).2.2.2.elems_len
    have hgop : topFrame'.getLocalOperand arrIdx = .ok (.indirect mp) := by
      unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
        Miri.Interpreter.LocalState.access
      simp [hlt_arr', hval_arr', bind, Except.bind, pure, Except.pure, Except.mapError]
    have hchk_ok : annealCheckIndirectInitialized m'.machine mp
        (translateTy arrDecl.ty body.layouts).layout.size = .ok () :=
      annealCheckIndirectInitialized_of_array_memPlaceRel hwf hnodup hmp
    cases hproj' with
    | index idxLocal idxDecl hidx_decl hidx_ty hidx_slot_or_imm =>
      have ⟨hdead_idx, hin_idx, hoob_idx⟩ :=
        evalProjection_index_simulation (m := m') hstate' rfl hnodup hwf hmp
          hidx_decl hidx_ty
      rcases usize_local_slot_trichotomy hframe' hidx_decl hidx_ty hidx_slot_or_imm with
        hdead_i | huninit_i | ⟨idxSc, hslot_idx⟩
      · left
        obtain ⟨_, hw_ub, msg, hpl_err⟩ := hdead_idx (Or.inl hdead_i)
        refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
        cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
            ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
        | ok _ => simp [hpl, Except.mapError] at hpl_err
        | error pe =>
          simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
          dsimp only [translatePlace]
          unfold annealEvalPlace
          simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
            EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw]
      · left
        obtain ⟨_, hw_ub, msg, hpl_err⟩ := hdead_idx (Or.inr huninit_i)
        refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
        cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
            ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
        | ok _ => simp [hpl, Except.mapError] at hpl_err
        | error pe =>
          simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
          dsimp only [translatePlace]
          unfold annealEvalPlace
          simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
            EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw]
      · by_cases hlt_c : idxSc.bits < count
        · right
          obtain ⟨elemVal, _, _, hget_e, _, _, hpl_ok, _, _⟩ := hin_idx idxSc hslot_idx hlt_c
          have hlt_len : idxSc.bits < elems.length := by rw [hlen_elems]; exact hlt_c
          refine ⟨elems, mp, idxSc.bits, topFrame', hlt_c, hinit_elems, ?_, ?_,
            hmls_arr', hmp, hframe', hdisj', hmono', rfl⟩
          · intro v
            simp [writeProjectedValue, hslot_idx, hget_e, set?_eq_some_set hlt_len v]
          · dsimp only [translatePlace, elemLay, elemTy]
            unfold annealEvalPlace
            simp [m', translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
              EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl_ok, pure, EStateM.pure]
        · left
          obtain ⟨_, hw_ub, msg, hpl_err⟩ := hoob_idx idxSc hslot_idx (Nat.le_of_not_lt hlt_c)
          refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            dsimp only [translatePlace]
            unfold annealEvalPlace
            simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
              EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw]
    | constantIndex offset minLength fromEnd hoff hmin hwf_c =>
      have ⟨hin_c, hoob_c⟩ :=
        evalProjection_constantIndex_simulation (m := m') (locals := s.frame.locals) topFrame'
          hnodup hwf hmp offset minLength fromEnd hoff hmin hwf_c
      have hlen_seq : Trusted.Sequence.length elems = count := by
        have hseq : ∀ xs : List Value, Trusted.Sequence.length xs = xs.length := by
          intro xs; induction xs with
          | nil => rfl
          | cons _ _ ih => simp [Trusted.Sequence.length]
        rw [hseq, hlen_elems]
      by_cases hle_min : minLength ≤ count
      · right
        let idx := if fromEnd then count - offset else offset
        have hidx_lt : idx < count := by
          cases fromEnd with
          | false => have := hwf_c.1 rfl; dsimp [idx]; omega
          | true => have := hwf_c.2 rfl; dsimp [idx]; omega
        have hlt_len : idx < elems.length := by rw [hlen_elems]; exact hidx_lt
        have hble : Nat.ble minLength count = true := Nat.ble_eq.mpr hle_min
        obtain ⟨elemVal, _, _, hget_e, _, _, hpl_ok, _, _⟩ := hin_c hle_min
        refine ⟨elems, mp, idx, topFrame', hidx_lt, hinit_elems, ?_, ?_,
          hmls_arr', hmp, hframe', hdisj', hmono', rfl⟩
        · intro v
          have hset_e := set?_eq_some_set hlt_len v
          have hget_idx : get? elems (if fromEnd then count - offset else offset) = some elemVal :=
            hget_e
          have hset_idx : set? elems (if fromEnd then count - offset else offset) v =
              some (elems.set (if fromEnd then count - offset else offset) v) := hset_e
          dsimp only [idx]
          cases fromEnd <;>
            (simp only [Bool.false_eq_true, ↓reduceIte] at hget_idx hset_idx ⊢;
             simp (config := { zetaDelta := true }) only [writeProjectedValue, hlen_seq, hble,
               Nat.sub_eq, hget_idx, hset_idx])
        · dsimp only [translatePlace, elemLay, elemTy, idx]
          unfold annealEvalPlace
          simp [m', translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
            EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl_ok, pure, EStateM.pure]
      · left
        obtain ⟨_, hw_ub, msg, hpl_err⟩ := hoob_c (Nat.lt_of_not_le hle_min)
        refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
        cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts m'.machine)
            ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
            [.ConstantIndex offset minLength fromEnd] with
        | ok _ => simp [hpl, Except.mapError] at hpl_err
        | error pe =>
          simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
          dsimp only [translatePlace]
          unfold annealEvalPlace
          simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
            EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw]

/-- Writing a `ScalarRel`-related scalar into projected element `idx < count` of an
array local `arrIdx` via `annealWriteImmediate`:
updates the backing `Allocation` in `mach.memory.live` via `ArraySliceRel.writeScalar_set`,
preserves `LiveAllocsNodup` and `MemoryHighWater` (with unchanged `nextAllocId`),
updates `MemPlaceRel` of `arrIdx` to `elems.set idx (.scalar sc)` (preserving all
`j ≠ idx` elements), and preserves `FrameRel` across all other locals via
`MemoryAllocDisjoint`. -/
theorem annealWriteImmediate_array_elem_set
    {body : CapturedMir} {af : StackFrame} {mach : AnnealMachine}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframe : FrameRel body mach af tf)
    (hdisj : MemoryAllocDisjoint tf)
    (hnodup : LiveAllocsNodup mach)
    {arrIdx : Local} {arrDecl : LocalDecl}
    {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hmls_arr : tf.locals[arrIdx]? =
      some ⟨.live (.indirect mp), some (translateTy arrDecl.ty body.layouts)⟩)
    (hmp : MemPlaceRel mach arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp)
    {idx : Nat} (hlt_idx : idx < count)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := translateTy elemTy body.layouts
    let elemMp : Miri.Interpreter.MemPlace AnnealProv :=
      { mp with
        ptr :=
          { mp.ptr with
            offset :=
              Miri.ABI.Size.ofBytes
                (mp.ptr.offset.bytes +
                  UInt64.ofNat (idx * elemLay.layout.size.bytes.toNat)) }
        metadata := .none }
    ∃ mach' : AnnealMachine,
      annealWriteImmediate (.scalar (.fromScalarInt msc)) ⟨.memory elemMp, elemLay⟩
        { stack := ⟨#[tf]⟩, machine := mach } =
        .ok () { stack := ⟨#[tf]⟩, machine := mach' } ∧
      LiveAllocsNodup mach' ∧
      MemPlaceRel mach' arrDecl.ty body.layouts
        (some (.aggregate 0 (elems.set idx (.scalar sc)))) mp ∧
      FrameRel body mach'
        { af with locals := af.locals.set arrIdx (.init (.aggregate 0 (elems.set idx (.scalar sc)))) }
        tf ∧
      (MemoryHighWater mach.memory → MemoryHighWater mach'.memory) ∧
      mach'.memory.nextAllocId = mach.memory.nextAllocId := by
  intro elemTy elemLay elemMp
  cases hmp with
  | mk allocId tag baseAddr relOffset localAlloc
      hprov hmis hmeta hlive hbase hno_ovf hptr hmut haligned hin _ hval_cons _ harr =>
    obtain ⟨_, _, _, hslice⟩ := harr elemKind count elems hwf.arr_kind rfl
    obtain ⟨alloc', hwrite, hbyteSize, _, hmask, hslice'⟩ :=
      hslice.writeScalar_set hlt_idx hrel hsz hbool hchar
    obtain ⟨allocIdx, _, hfindIdx, hgetIdx, hset_prop⟩ :=
      array_findIdx?_of_nodup_fst hnodup hlive
    rcases localAlloc with ⟨kind, alloc⟩
    dsimp only at hslice hwrite hbyteSize hmask hslice'
    obtain ⟨hnodup', hlive', hother_live⟩ := hset_prop ⟨kind, alloc'⟩
    let mach' : AnnealMachine := inplaceMachine mach allocIdx allocId kind alloc'
    have hoff_eq :
        Miri.ABI.Size.ofBytes (elemMp.ptr.offset.bytes - baseAddr) =
        Miri.ABI.Size.ofBytes
          (relOffset.bytes + UInt64.ofNat (idx * elemLay.layout.size.bytes.toNat)) := by
      have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by rw [hptr]; rfl
      dsimp only [elemMp]
      simp only [Miri.ABI.Size.ofBytes, hbytes, uint64_add_add_sub_cancel_left]
    dsimp only [elemLay, elemTy] at hoff_eq
    have hmsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size := rfl
    have hprov_e : elemMp.ptr.provenance = some (.concrete allocId tag) := hprov
    have hw_ok : annealWriteImmediate (.scalar (.fromScalarInt msc)) ⟨.memory elemMp, elemLay⟩
        { stack := ⟨#[tf]⟩, machine := mach } =
        .ok () { stack := ⟨#[tf]⟩, machine := mach' } := by
      unfold annealWriteImmediate
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
        stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl, hprov_e, Option.bind_some,
        Miri.Memory.Provenance.getAllocId, hbase, hfindIdx, hgetIdx, hoff_eq,
        hmsc_sz, hwrite, pure, set, MonadStateOf.set, EStateM.set]
      rfl
    have hmp' : MemPlaceRel mach' arrDecl.ty body.layouts
        (some (.aggregate 0 (elems.set idx (.scalar sc)))) mp := by
      refine .mk allocId tag baseAddr relOffset ⟨kind, alloc'⟩
        hprov hmis hmeta hlive' hbase hno_ovf hptr hslice'.alloc_mut haligned
        (by dsimp only; rw [hbyteSize]; exact hin)
        (fun h => nomatch h)
        (fun _ _ hnz => by dsimp only; rw [hmask]; exact hval_cons (.aggregate 0 elems) rfl hnz)
        (fun _ h => nomatch h)
        (fun ek cnt es hk hopt => ?_)
      rw [hwf.arr_kind] at hk
      injection hk with hek hcnt
      subst hek hcnt
      injection hopt with hagg
      injection hagg with _ hes
      subst hes
      exact ⟨hwf.arr_fields, hwf.arr_size, hwf.arr_align, hslice'⟩
    refine ⟨mach', hw_ok, hnodup', hmp', ?_,
      fun hw => (MemoryHighWater.inplaceMachine (allocIdx := allocIdx) (kind := kind)
        (alloc := alloc') hw hlive).1,
      rfl⟩
    have hlt_af : arrIdx < af.locals.length := by
      have ⟨hlt_mf, _⟩ := Array.getElem?_eq_some_iff.mp hmls_arr
      rw [hframe.af_locals_len, ← hframe.mf_locals_size]
      exact hlt_mf
    refine ⟨hframe.body_eq, hframe.location_eq,
      by rw [List.length_set, hframe.af_locals_len],
      hframe.mf_locals_size, ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    by_cases heq : arrIdx = i
    · subst heq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i
      subst hslot_i
      rw [hdecl_arr] at hdecl_i; injection hdecl_i with hd_eq; subst hd_eq
      rw [hmls_arr] at hmls_i; injection hmls_i with hm_eq; subst hm_eq
      exact .indirect (.init (.aggregate 0 (elems.set idx (.scalar sc)))) mp _
        (fun l hl => Option.some.inj hl.symm) nofun hmp'
    · simp only [heq, ↓reduceIte] at hslot_i
      have hloc_i := hframe.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
      cases hloc_i with
      | dead c hc => exact .dead c hc
      | immediate _ imm_i c hc hv => exact .immediate slot_i imm_i c hc hv
      | indirect _ mp_i c hc hnd hmp_i =>
        refine .indirect slot_i mp_i c hc hnd ?_
        cases hmp_i with
        | mk aid_i tag_i baddr_i roff_i la_i hp_i hm_i hmt_i hlv_i hb_i hno_i hpa_i
            hmu_i hal_i hib_i huc_i hvc_i hsc_i hac_i =>
          have hne_id : aid_i ≠ allocId := by
            have hd := hdisj arrIdx i mp mp_i _ c heq hmls_arr hmls_i
            rw [hprov, hp_i] at hd
            simp only [Option.bind_some, Miri.Memory.Provenance.getAllocId, ne_eq,
              Option.some.injEq] at hd
            exact Ne.symm hd
          exact .mk aid_i tag_i baddr_i roff_i la_i hp_i hm_i hmt_i
            (hother_live aid_i la_i hne_id hlv_i) hb_i hno_i hpa_i
            hmu_i hal_i hib_i huc_i hvc_i hsc_i hac_i

/-- Well-typed array element read or write `Statement` (`_dst = copy/move _arr[proj]`
or `_arr[proj] = srcOp`, where `proj` is `.index idxLocal` or
`.constantIndex offset minLength fromEnd`). -/
inductive WellTypedArrayElemAssign
    (body : CapturedMir)
    (s : MachineState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Statement → Prop where
  /-- Element read: `_dst = copy _arr[proj]` or `_dst = move _arr[proj]`. -/
  | readElem
      (dstIdx arrIdx : Local) (dstDecl arrDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat)
      (proj : ProjectionElem) (isMove : Bool) (span : String) :
      get? body.localDecls arrIdx = some arrDecl →
      WellTypedArrayTy body.layouts arrDecl.ty elemKind count →
      get? body.localDecls dstIdx = some dstDecl →
      dstDecl.ty = { kind := elemKind, layoutIdx := 0 } →
      IsImmediateFrameLocal topFrame dstIdx →
      WellTypedArrayElemProj body s topFrame proj →
      (get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) →
      WellTypedArrayElemAssign body s topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (arrayElemReadOperand isMove arrIdx proj)), span⟩
  /-- Element write: `_arr[proj] = .use srcOp` (constant, `copy`, or destructive `move`,
  excluding self-indexing `_arr[_i] = move _i` where `evalStmt` deinitializes `_i` before
  evaluating `proj` while `lean-miri` evaluates `proj` before `srcOp`). -/
  | writeElem
      (arrIdx : Local) (arrDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat)
      (proj : ProjectionElem) (srcOp : MirAst.Operand) (span : String) :
      get? body.localDecls arrIdx = some arrDecl →
      WellTypedArrayTy body.layouts arrDecl.ty elemKind count →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      WellTypedArrayElemProj body s topFrame proj →
      WellTypedLM2_1ScalarOperand body topFrame srcOp { kind := elemKind, layoutIdx := 0 } →
      (∀ idxLocal, movedScalarLocal? srcOp = some idxLocal → proj ≠ .index idxLocal) →
      (get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) →
      WellTypedArrayElemAssign body s topFrame
        ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩

private theorem evalRvalue_use_scalar_eq
    {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {s : MachineState} {srcOp : MirAst.Operand} {ty : Ty}
    (hop : WellTypedLM2_1ScalarOperand body tf srcOp ty)
    (hbor : s.memory.borrows = .nil)
    (hcaller : s.memory.callerLocals = .nil) :
    evalRvalue s.frame.locals (.use srcOp) s.memory body.localDecls body.layouts =
      match evalOperand s.frame.locals srcOp .nil s.memory.globals body.layouts .nil with
      | .ok val locals' => .ok val locals' s.memory
      | .ub => .ub
      | .unsupported => .unsupported := by
  cases hop with
  | ofScalar hop_s =>
    cases hop_s with
    | constScalar c _ _ _ _ _ _ _ _ =>
      unfold evalRvalue; dsimp only; rw [hbor, hcaller]
      cases evalOperand s.frame.locals (.constant c) .nil s.memory.globals body.layouts .nil <;> rfl
    | copyLocal idx _ _ _ _ =>
      unfold evalRvalue; dsimp only; rw [hbor, hcaller]
      cases evalOperand s.frame.locals (.copy ⟨idx, .nil⟩) .nil s.memory.globals body.layouts .nil <;> rfl
  | moveLocal idx _ _ _ _ =>
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    cases evalOperand s.frame.locals (.move ⟨idx, .nil⟩) .nil s.memory.globals body.layouts .nil <;> rfl

private theorem writeProjectedValue_elem_congr
    {body : CapturedMir} {s : MachineState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals₁ : List LocalSlot} {proj : ProjectionElem} {srcOp : MirAst.Operand}
    (hproj : WellTypedArrayElemProj body s tf proj)
    (hno_self : ∀ idxLocal, movedScalarLocal? srcOp = some idxLocal → proj ≠ .index idxLocal)
    (hget_other : ∀ j, movedScalarLocal? srcOp ≠ some j → get? locals₁ j = get? s.frame.locals j)
    (base newVal : Value) :
    writeProjectedValue locals₁ base [proj] newVal =
      writeProjectedValue s.frame.locals base [proj] newVal := by
  cases hproj with
  | index idxLocal _ _ _ _ =>
    have hne_mv : movedScalarLocal? srcOp ≠ some idxLocal :=
      fun hm => hno_self idxLocal hm rfl
    have hget_idx := hget_other idxLocal hne_mv
    cases base with
    | aggregate v fields =>
      cases v with
      | zero => simp only [writeProjectedValue, hget_idx]
      | succ _ => rfl
    | _ => rfl
  | constantIndex offset minLen fromEnd _ _ _ =>
    cases base with
    | aggregate v fields =>
      cases v with
      | zero => rw [Nat.zero_eq]; rfl
      | succ _ => rfl
    | _ => rfl

/-- **`step_assign_array_element_simulation`** (`LM-2.1`):
Statement-level lockstep simulation for array element reads (`_dst = copy/move _arr[proj]`)
and array element writes (`_arr[proj] = srcOp`, including constant, `copy`, and destructive
`move` source operands) across both `ProjectionElem.index` (with immediate or stack-allocated
`usize` index locals) and `ProjectionElem.constantIndex` (`fromEnd = false` and
`fromEnd = true`), covering:
- dead/uninitialized array local UB,
- dead/uninitialized index local UB,
- out-of-bounds index / invalid `minLength` UB,
- dead/uninitialized source operand or dead destination local UB,
- in-bounds scalar element read, and
- in-bounds scalar element overwrite (`elems.set idx (.scalar sc)` vs byte-slice overwrite
  preserving all `j ≠ idx` elements, `MemoryAllocDisjoint`, and deinitializing moved scalar
  source locals).

A normal `lean-miri` step also preserves `LiveAllocsNodup` (`StepPreservesNodup`),
the immediacy of every local (`StepPreservesImmediate`), and `MemoryHighWater` with
zero `AllocId` consumption (`StepPreservesHighWater m 0`). -/
theorem step_assign_array_element_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedArrayElemAssign body s topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hstate_copy := hstate
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  cases hwt topFrame hframes with
  | readElem dstIdx arrIdx dstDecl arrDecl elemKind count proj isMove span
      hdecl_arr hwf hdecl_dst hdst_ty hdst_imm hproj harr_slot =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, _, hmls_dst_eq, hloc_dst0⟩ :=
      hframe.lookup_local hdecl_dst
    let topFrame₀ :=
      cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok destPlace m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst
        (by rw [hmls_dst_eq]; exact hloc_dst0.layout_eq)
    have hframe₀ : FrameRel body m.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hdisj₀ : MemoryAllocDisjoint topFrame₀ :=
      hdisj.cache_layout hlt_dst0 _
    have hstate₀ : StateRel body s m₀ :=
      StateRel.mk topFrame₀ rfl hretCont ⟨retLay, hretPlace⟩ hframe₀
        hcal hstack hbor hprot hcaller hdisj₀
    have hproj₀ : WellTypedArrayElemProj body s topFrame₀ proj :=
      hproj.cache_layout hlt_dst0 _
    have harr_slot₀ :
        get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame₀ arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) := by
      rcases harr_slot with hd | ⟨hu, hpos | himm_a⟩ | he
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨hu, Or.inl hpos⟩)
      · exact Or.inr (Or.inl ⟨hu, Or.inr (himm_a.cache_layout hlt_dst0 _)⟩)
      · exact Or.inr (Or.inr he)
    let readOp := arrayElemReadOperand isMove arrIdx proj
    have huse_read : evalRvalue s.frame.locals (.use readOp) s.memory body.localDecls body.layouts =
        match evalOperand s.frame.locals readOp .nil s.memory.globals body.layouts .nil with
        | .ok val locals' => .ok val locals' s.memory
        | .ub => .ub
        | .unsupported => .unsupported := by
      dsimp only [readOp]
      cases isMove <;> cases hproj <;>
        (unfold evalRvalue; dsimp only [arrayElemReadOperand]; rw [hbor, hcaller];
         cases evalOperand _ _ _ _ _ _ <;> rfl)
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use readOp), span⟩) m =
        Miri.Interpreter.runRvalue
          ((annealEvalOperand body.localDecls body.layouts (translateOperand readOp)
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
            fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
        translateRvalue, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst]
      exact EStateM.bind_assoc_apply _ _ _ m₀
    rcases annealEvalOperand_projected_array_simulation hstate₀ rfl hnodup isMove
        (some (translateTy dstDecl.ty body.layouts)) hdecl_arr hwf hproj₀ harr_slot₀ with
      ⟨ha_ub_op, m', msg, hm_err_op⟩ |
      ⟨sc_e, msc_e, topFrame₁, ha_ok_op, hm_ok_op, _, hframe₁, hdisj₁, hmono₁, htf₁_eq, himm_e⟩
    · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use readOp), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        rw [huse_read, ha_ub_op]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use readOp), span⟩) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_err_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
        StepPreservesHighWater.of_error⟩
    · have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use readOp), span⟩
          body.localDecls body.layouts =
          match get? s.frame.locals dstIdx with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? s.frame.locals dstIdx (.init (.scalar sc_e)) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        rw [huse_read, ha_ok_op]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same]
        rfl
      have hm_write : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use readOp), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_e)) destPlace)
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [hm_eval]
        apply runRvalue_eq_of_eq
        exact EStateM.bind_eq_ok hm_ok_op
      have hmono_tot : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₁ j :=
        fun j hj => hmono₁ j (hj.cache_layout hlt_dst0 _)
      have himm_dst : ImmediateRel dstDecl.ty body.layouts (.scalar sc_e)
          (.scalar (.fromScalarInt msc_e)) := by
        rw [hdst_ty]; exact himm_e
      have hretCont₁ : topFrame₁.returnContinuation = .stop false := by
        rw [htf₁_eq]; exact hretCont
      have hretPlace₁ : ∃ retLay, topFrame₁.returnPlace =
          .frameLocal 0 0 none retLay topFrame₁.localsIdentity := by
        rw [htf₁_eq]; exact ⟨retLay, hretPlace⟩
      obtain ⟨_, _, _, hlt_dst₁, _, _, _, _⟩ := hframe₁.lookup_local hdecl_dst
      have hext := write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
        hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hmono_tot hbb hstmt hframe₁ hdisj₁
        hdecl_dst (hmono_tot dstIdx hdst_imm) himm_dst ha_ok hm_write
      obtain ⟨hnd_w, hhw_w⟩ :=
        stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hframe.body_eq
          hframe.location_eq hbb hstmt hframe₁.location_eq hlt_dst₁
          (hmono_tot dstIdx hdst_imm) hm_write
      refine ⟨hext.1, hnd_w, ?_, hhw_w⟩
      intro hok tf tf' htf htf' j _ hj
      rw [hframes] at htf
      have htf_eq : tf = topFrame := by simpa using htf.symm
      subst htf_eq
      exact hext.2 j hj tf' htf' hok
  | writeElem arrIdx arrDecl elemKind count proj srcOp span
      hdecl_arr hwf hprim hproj hop hno_self harr_slot =>
    have huse_src := evalRvalue_use_scalar_eq hop hbor hcaller
    rcases annealEvalPlace_projected_array_simulation hstate_copy hframes hnodup
        hdecl_arr hwf hproj harr_slot with
      ⟨ha_dst_ub, m', msg, hevalPlace_err⟩ |
      ⟨elems, mp, idx, topFrame₀, hlt_idx, hinit_elems, hwrite_proj, hevalPlace_ok,
        hmls_arr₀, hmp, hframe₀, hdisj₀, hmono₀, htf₀_eq⟩
    · -- Destination array place or index is UB: both Anneal and Miri report UB.
      rcases evalLM2_1ScalarOperand_preserves_array_local hframe hdisj hdecl_arr hwf hprim hop
          s.memory.globals none with
        ⟨ha_src_ub, _⟩ |
        ⟨sc, _, locals₁, _, ha_src_ok, _, hget_arr₁, hget_other₁, _⟩
      · have ha_ub : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only
          rw [huse_src, ha_src_ub]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩) m =
            (m', .error (.undefinedBehavior msg)) := by
          unfold Miri.Interpreter.Step.evalStatement translateStmt
          dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
          unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          dsimp only
          rw [EStateM.bind_eq_error hevalPlace_err]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
          StepPreservesHighWater.of_error⟩
      · have ha_ub : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only
          rw [huse_src, ha_src_ok]
          cases hproj_c : proj with
          | index idxLocal =>
            dsimp only
            rw [hget_arr₁]
            rcases ha_dst_ub with hd | hu | ⟨es, hes, hw_ub⟩
            · simp [hd]
            · simp [hu]
            · have hw_c := writeProjectedValue_elem_congr hproj hno_self hget_other₁
                (.aggregate 0 es) (.scalar sc)
              rw [hproj_c] at hw_c hw_ub
              simp [hes, hw_c, hw_ub (.scalar sc)]
          | constantIndex offset minLen fromEnd =>
            dsimp only
            rw [hget_arr₁]
            rcases ha_dst_ub with hd | hu | ⟨es, hes, hw_ub⟩
            · simp [hd]
            · simp [hu]
            · have hw_c := writeProjectedValue_elem_congr hproj hno_self hget_other₁
                (.aggregate 0 es) (.scalar sc)
              rw [hproj_c] at hw_c hw_ub
              simp [hes, hw_c, hw_ub (.scalar sc)]
          | _ =>
            cases hproj_c ▸ hproj
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩) m =
            (m', .error (.undefinedBehavior msg)) := by
          unfold Miri.Interpreter.Step.evalStatement translateStmt
          dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
          unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          dsimp only
          rw [EStateM.bind_eq_error hevalPlace_err]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
          StepPreservesHighWater.of_error⟩
    · -- Destination array place is in-bounds at `idx < count`; now evaluate `srcOp`.
      let elemTy : Ty := { kind := elemKind, layoutIdx := 0 }
      let elemLay := translateTy elemTy body.layouts
      let elemMp : Miri.Interpreter.MemPlace AnnealProv :=
        { mp with
          ptr :=
            { mp.ptr with
              offset :=
                Miri.ABI.Size.ofBytes
                  (mp.ptr.offset.bytes +
                    UInt64.ofNat (idx * elemLay.layout.size.bytes.toNat)) }
          metadata := .none }
      have hm₀_eq : { m with stack := ⟨#[topFrame₀]⟩ } =
          ({ stack := ⟨#[topFrame₀]⟩, machine := m.machine } : AnnealStepState) := by
        cases m; rfl
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand srcOp)
                (some elemLay) >>= annealReadImmediate) >>=
              fun imm => annealWriteImmediate imm.imm ⟨.memory elemMp, elemLay⟩)
            { stack := ⟨#[topFrame₀]⟩, machine := m.machine } := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
        rw [← hm₀_eq]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_ok]
        exact EStateM.bind_assoc_apply _ _ _ _
      have hop₀ : WellTypedLM2_1ScalarOperand body topFrame₀ srcOp elemTy :=
        hop.mono_immediate hmono₀
      rcases evalLM2_1ScalarOperand_preserves_array_local hframe₀ hdisj₀ hdecl_arr hwf hprim hop₀
          s.memory.globals (some elemLay) with
        ⟨ha_src_ub, m', msg, hm_src_err⟩ |
        ⟨sc, msc, locals₁, topFrame₁, ha_src_ok, hm_src_ok, hget_arr₁, hget_other₁,
          hlen_loc₁, harr_eq₁, hframe₁, hdisj₁, hmono₁, htf₁_eq, hrel_sc, hsz_sc,
          hbool_sc, hchar_sc⟩
      · have ha_ub : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only
          rw [huse_src, ha_src_ub]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_src_err]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
          StepPreservesHighWater.of_error⟩
      · have hmls_arr₁ : topFrame₁.locals[arrIdx]? =
            some ⟨.live (.indirect mp), some (translateTy arrDecl.ty body.layouts)⟩ := by
          rw [harr_eq₁]; exact hmls_arr₀
        obtain ⟨mach', hw_ok, hnodup', _, hframe', hhw_imp, hnext_eq⟩ :=
          annealWriteImmediate_array_elem_set hframe₁ hdisj₁ hnodup hdecl_arr hwf hmls_arr₁
            hmp hlt_idx hrel_sc hsz_sc hbool_sc hchar_sc
        obtain ⟨_, _, hlt_af_arr, _, _, _, _, _⟩ := hframe.lookup_local hdecl_arr
        have hlt_af_arr₁ : arrIdx < locals₁.length := by rw [hlen_loc₁]; exact hlt_af_arr
        have hset_arr : set? locals₁ arrIdx
            (.init (.aggregate 0 (elems.set idx (.scalar sc)))) =
            some (locals₁.set arrIdx (.init (.aggregate 0 (elems.set idx (.scalar sc))))) :=
          set?_eq_some_set hlt_af_arr₁ _
        have hinit_elems₁ : get? locals₁ arrIdx = some (.init (.aggregate 0 elems)) := by
          rw [hget_arr₁]; exact hinit_elems
        have hw_congr := writeProjectedValue_elem_congr hproj hno_self hget_other₁
          (.aggregate 0 elems) (.scalar sc)
        have ha_step : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
            body.localDecls body.layouts =
            MirStepNode.step (advanceStmt s
              (locals₁.set arrIdx (.init (.aggregate 0 (elems.set idx (.scalar sc)))))
              s.memory) := by
          unfold evalStmt
          dsimp only
          rw [huse_src, ha_src_ok]
          cases hproj_c : proj with
          | index _ =>
            dsimp only
            rw [hinit_elems₁]
            dsimp only
            rw [hproj_c] at hw_congr hwrite_proj
            rw [hw_congr, hwrite_proj (.scalar sc)]
            dsimp only
            rw [hset_arr, hprot, hbor]
            dsimp only [invalidateConflictingBorrowsAtProj]
            rw [hmem_same]
          | constantIndex _ _ _ =>
            dsimp only
            rw [hinit_elems₁]
            dsimp only
            rw [hproj_c] at hw_congr hwrite_proj
            rw [hw_congr, hwrite_proj (.scalar sc)]
            dsimp only
            rw [hset_arr, hprot, hbor]
            dsimp only [invalidateConflictingBorrowsAtProj]
            rw [hmem_same]
          | _ =>
            cases hproj_c ▸ hproj
        have hm_step : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩) m =
            ({ stack := ⟨#[topFrame₁]⟩, machine := mach' }, .ok ()) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_src_ok, hw_ok]
        have hloc₁ : topFrame₁.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
          hframe₁.location_eq
        rw [ha_step, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
          hbb hstmt hm_step rfl hloc₁]
        refine ⟨StepRel.step _ _ ?_, StepPreservesNodup.of_nodup hnodup', ?himm,
          fun _ hw _ => ⟨hhw_imp hw, by dsimp only; rw [hnext_eq]; omega⟩⟩
        case himm =>
          intro _ tf tf' htf htf' j _ hj
          rw [hframes] at htf
          have htf_eq : tf = topFrame := by simpa using htf.symm
          subst htf_eq
          have htf'_eq : tf' =
              { topFrame₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
            simpa using htf'.symm
          subst htf'_eq
          exact hmono₁ j (hmono₀ j hj)
        have hretCont₁ : topFrame₁.returnContinuation = .stop false := by
          rw [htf₁_eq, htf₀_eq]; exact hretCont
        have hretPlace₁ : topFrame₁.returnPlace =
            .frameLocal 0 0 none retLay topFrame₁.localsIdentity := by
          rw [htf₁_eq, htf₀_eq]; exact hretPlace
        refine StateRel.mk
          { topFrame₁ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
          rfl hretCont₁ ⟨retLay, hretPlace₁⟩
          ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size,
            hframe'.locals_rel⟩
          hcal hstack hbor hprot hcaller
          (fun i j mp_i mp_j lay_i lay_j hij hi hj =>
            hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj)

/-- Well-typed `LM-2.1` array statement covered by
`step_stmt_lm2_1_array_simulation`:
1. Homogeneous array literal construction or in-place overwrite
   (`Rvalue.aggregate (.array elemTy) ops`),
2. Homogeneous array repeat construction or in-place overwrite
   (`Rvalue.repeat op count`),
3. Array length query (`Rvalue.len ⟨arrIdx, .nil⟩`), and
4. Bounds-checked array element reads and writes (`ProjectionElem.index` and
   `ProjectionElem.constantIndex` with `fromEnd = false` and `fromEnd = true`). -/
inductive WellTypedLM2_1ArrayStmt
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Statement → Prop where
  | aggregateArray
      (dstIdx : Local) (dstDecl : LocalDecl)
      (elemTy : Ty) (elemKind : RigidTy) (count : Nat)
      (ops : List MirAst.Operand) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      WellTypedArrayTy body.layouts dstDecl.ty elemKind count →
      ops.length = count →
      ArrayConstructDestReady s m topFrame dstIdx →
      (∀ op ∈ ops, WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 }) →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      WellTypedLM2_1ArrayStmt body s m topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
  | repeatArray
      (dstIdx : Local) (dstDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat)
      (op : MirAst.Operand) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      WellTypedArrayTy body.layouts dstDecl.ty elemKind count →
      ArrayConstructDestReady s m topFrame dstIdx →
      WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 } →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      WellTypedLM2_1ArrayStmt body s m topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
  | lenArray
      (dstIdx arrIdx : Local) (dstDecl arrDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat) (span : String) :
      get? body.localDecls arrIdx = some arrDecl →
      WellTypedArrayTy body.layouts arrDecl.ty elemKind count →
      get? body.localDecls dstIdx = some dstDecl →
      dstDecl.ty = { kind := .uint .usize, layoutIdx := 0 } →
      IsImmediateFrameLocal topFrame dstIdx →
      (get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) →
      WellTypedLM2_1ArrayStmt body s m topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩
  | elemAssign {stmt : Statement} :
      WellTypedArrayElemAssign body s topFrame stmt →
      WellTypedLM2_1ArrayStmt body s m topFrame stmt

/-- **`step_stmt_lm2_1_array_simulation`** (`LM-2.1` array statement simulation):
From any `StateRel`-related pair of states `(s, m)` with `LiveAllocsNodup m.machine`,
executing any `WellTypedLM2_1ArrayStmt` (array `Aggregate`, `Repeat`, `Len`, and
`Index`/`ConstantIndex` element reads and writes, including destructive `move` source
operands, in-place whole-array reassignment, and stack-allocated `usize` index locals)
steps Anneal (`stepMirFn`) and `lean-miri` (`Step.step`) in exact lockstep (`StepRel`).
Normal steps preserve `StateRel` (including `ArraySliceRel` and `MemoryAllocDisjoint`),
`LiveAllocsNodup` (`StepPreservesNodup`), the immediacy of every local except the
destination of an array construction (`StepPreservesImmediate`), and `MemoryHighWater`
(`StepPreservesHighWater`, consuming at most `1` `AllocId` on array construction and `0`
on all other array statements); both machines report UB when an array, index, operand,
or destination local is dead or uninitialized or an index is out of bounds. -/
theorem step_stmt_lm2_1_array_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1ArrayStmt body s m topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => arrayConstructDest? stmt ≠ some j)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m (if (arrayConstructDest? stmt).isSome then 1 else 0)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hstate_copy := hstate
  rcases hstate with ⟨topFrame, hframes, _, _, _, hcal, _, _, _, _, _⟩
  have htf_eq : ∀ tf, m.stack.frames = #[tf] → tf = topFrame := by
    intro tf h
    rw [hframes] at h
    simpa using h.symm
  cases hwt topFrame hframes with
  | aggregateArray dstIdx dstDecl elemTy elemKind count ops span
      hdecl_dst hwf hlen_ops hdst_ready hops hprim =>
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨hrel', hnd', him', hhw'⟩ := evalRvalue_aggregate_array_simulation hstate_copy hnodup hbb
      hstmt hdecl_dst hwf hlen_ops
      (fun tf htf => htf_eq tf htf ▸ hdst_ready)
      (fun tf htf => htf_eq tf htf ▸ hops)
      hprim
    refine ⟨hrel', hnd', him'.mono fun j hj => ?_, hhw'⟩
    intro hjd
    apply hj
    show some dstIdx = some j
    rw [hjd]
  | repeatArray dstIdx dstDecl elemKind count op span
      hdecl_dst hwf hdst_ready hop hprim =>
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨hrel', hnd', him', hhw'⟩ := evalRvalue_repeat_simulation hstate_copy hnodup hbb hstmt
      hdecl_dst hwf
      (fun tf htf => htf_eq tf htf ▸ hdst_ready)
      (fun tf htf => htf_eq tf htf ▸ hop)
      hprim
    refine ⟨hrel', hnd', him'.mono fun j hj => ?_, hhw'⟩
    intro hjd
    apply hj
    show some dstIdx = some j
    rw [hjd]
  | lenArray dstIdx arrIdx dstDecl arrDecl elemKind count span
      hdecl_arr hwf hdecl_dst hdst_ty hdst_imm harr_slot =>
    have harr_slot' :
        get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨
            ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) := by
      rcases harr_slot with hd | ⟨hu, hpos | himm_a⟩ | he
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨hu, Or.inl hpos⟩)
      · exact Or.inr (Or.inl ⟨hu, Or.inr (fun tf htf => htf_eq tf htf ▸ himm_a)⟩)
      · exact Or.inr (Or.inr he)
    obtain ⟨hrel', hnd', him', hhw'⟩ := evalRvalue_len_array_simulation hstate_copy hnodup hphase hbb
      hstmt hdecl_arr hwf hdecl_dst hdst_ty (fun tf htf => htf_eq tf htf ▸ hdst_imm) harr_slot'
    exact ⟨hrel', hnd', him'.mono fun _ _ => trivial, hhw'.mono_budget (Nat.zero_le _)⟩
  | elemAssign helem =>
    obtain ⟨hrel', hnd', him', hhw'⟩ := step_assign_array_element_simulation hstate_copy hnodup hphase
      hbb hstmt (fun tf htf => htf_eq tf htf ▸ helem)
    exact ⟨hrel', hnd', him'.mono fun _ _ => trivial, hhw'.mono_budget (Nat.zero_le _)⟩

/-- Deallocating a local's stack allocation (filtering `memory.live`) preserves
`LiveAllocsNodup`. -/
theorem LiveAllocsNodup.deallocLocalMemory
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    (v : Miri.Interpreter.LocalValue AnnealProv) :
    LiveAllocsNodup { mach with memory := _root_.LeanMiriSpec.Correspondence.deallocLocalMemory mach.memory v } := by
  unfold LiveAllocsNodup _root_.LeanMiriSpec.Correspondence.deallocLocalMemory
  cases v with
  | dead => exact hnodup
  | live op =>
    cases op with
    | immediate _ => exact hnodup
    | indirect mp =>
      dsimp only
      cases mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => exact hnodup
      | some id =>
        dsimp only
        rw [Array.toList_filter]
        exact hnodup.sublist (List.filter_sublist.map Prod.fst)

/-- Executing `StorageLive(loc)` on any declared local establishes
`IsImmediateFrameLocal tf' loc` in the resulting `lean-miri` frame (even if `loc`
previously held a memory-backed allocation). The step always succeeds, so the
lemma needs no hypothesis about its outcome. -/
theorem step_storageLive_establishes_immediate
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    {tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (htf' : (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[tf']) :
    IsImmediateFrameLocal tf' loc := by
  rcases hstate with ⟨topFrame, hframes, _, _, hfr, _, _, _, _, _, _⟩
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := Correspondence.deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at htf'
  dsimp only at htf'
  injection htf' with h_arr
  injection h_arr with h_eq _
  subst h_eq
  intro mls' hmls' mp hval
  simp only [Array.getElem?_set, ↓reduceIte, Option.some.injEq] at hmls'
  subst hmls'
  cases hval

/-- Every `LM-1.1` scalar statement (`WellTypedScalarStmt`) preserves `LiveAllocsNodup`
and `MemoryHighWater` (`allocBudget = 0`). -/
theorem step_scalar_preserves_nodup
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedScalarStmt body topFrame stmt) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _, _⟩
  cases hwt topFrame hframes with
  | nop hkind =>
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        (m, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]; rfl
    rw [miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm hframes hframe.location_eq]
    exact ⟨StepPreservesNodup.of_nodup hnodup, StepPreservesHighWater.of_same_memory rfl⟩
  | storageLive loc decl hkind hdecl himm_loc =>
    obtain ⟨_, mls, _, hlt_mf, _, hmls, hmls_eq, _⟩ := hframe.lookup_local hdecl
    let topFrame' :=
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }
    have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
      rw [hframe.body_eq, translateBody_locals_getElem?, hdecl]
      exact ⟨_, rfl⟩
    have hnotInd : ∀ mp, (topFrame.locals[loc]'hlt_mf).value ≠ .live (.indirect mp) := by
      rw [hmls_eq]; exact himm_loc mls hmls
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      exact annealStepHooks_storageLive_eq hframes hlt_mf hty hnotInd
    rw [miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm rfl hframe.location_eq]
    exact ⟨StepPreservesNodup.of_nodup hnodup, StepPreservesHighWater.of_same_memory rfl⟩
  | storageDead loc decl hkind hdecl hne himm_loc =>
    obtain ⟨_, mls, _, hlt_mf, _, hmls, hmls_eq, _⟩ := hframe.lookup_local hdecl
    let topFrame' :=
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }
    have hnotInd : ∀ mp, (topFrame.locals[loc]'hlt_mf).value ≠ .live (.indirect mp) := by
      rw [hmls_eq]; exact himm_loc mls hmls
    have hm : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok ()) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      exact annealStepHooks_storageDead_eq hframes hlt_mf hne hnotInd
    rw [miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
      hm rfl hframe.location_eq]
    exact ⟨StepPreservesNodup.of_nodup hnodup, StepPreservesHighWater.of_same_memory rfl⟩
  | assign dstIdx dstDecl rv hkind hdecl_dst himm_dst hrv =>
    obtain ⟨_, _, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl_dst
    let topFrame₀ :=
      cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok destPlace m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst
        (by rw [hmls_eq0]; exact hloc_dst0.layout_eq)
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    cases hrv.mono_immediate hmono₀ with
    | use op _ hop =>
      have hop_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hop
        s.memory.globals (some (translateTy dstDecl.ty body.layouts))
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand op)
                (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
              fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst]
        exact EStateM.bind_assoc_apply _ _ _ m₀
      generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = aOp at hop_sim
      generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ = mOp at hop_sim
      cases hop_sim with
      | ub m' msg =>
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_op]
        rw [miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
      | ok _ _ topFrame₁ imm hframe₁ _ hmono _ _ =>
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate imm destPlace)
              { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          exact EStateM.bind_eq_ok hm_op
        obtain ⟨_, _, _, hlt_dst₁, _, _, _, _⟩ := hframe₁.lookup_local hdecl_dst
        exact stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hframe.body_eq
          hframe.location_eq hbb hstmt hframe₁.location_eq hlt_dst₁
          (hmono dstIdx (hmono₀ dstIdx himm_dst)) hm_write
    | unaryOp uop op srcTy _ hop huop =>
      let knownU := if (translateUnOp uop).homogeneous then some (translateTy dstDecl.ty body.layouts) else none
      have hop_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hop s.memory.globals knownU
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand op) knownU >>=
                annealReadImmediate) >>=
              fun val => do
                let result ← Miri.Interpreter.ScalarOps.unary
                  (annealScalarOpsHooks body.localDecls body.layouts) ()
                  (translateUnOp uop) val
                assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                annealWriteImmediate result.imm destPlace) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        rw [evalRvalueIntoPlace_unaryOp_def]
        unfold annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst]
        exact EStateM.bind_assoc_apply _ _ _ m₀
      generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = aOp at hop_sim
      generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand op) knownU >>=
        annealReadImmediate) m₀ = mOp at hop_sim
      cases hop_sim with
      | ub m' msg =>
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_op]
        rw [miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
      | ok _ locals₁ topFrame₁ imm hframe₁ himmRel hmono _ _ =>
        let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
        obtain ⟨_, _, imm', _, _, hm_uop, _⟩ :=
          scalarOps_unary_simulation (locals₁ := locals₁) (mem := s.memory) (m₁ := m₁)
            hop.operandTy_eq huop himmRel
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            Miri.Interpreter.runRvalue
              (annealWriteImmediate imm' destPlace)
              m₁ := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          rw [EStateM.bind_eq_ok hm_op]
          change ((do
            let result ← Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateUnOp uop) ⟨imm, translateTy srcTy body.layouts⟩
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            annealWriteImmediate result.imm destPlace) m₁) = _
          rw [estate_bind_pure_assoc
            (Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateUnOp uop) ⟨imm, translateTy srcTy body.layouts⟩)
            (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
            (fun result => result.imm)
            (fun i => annealWriteImmediate i destPlace)
            m₁]
          exact EStateM.bind_eq_ok hm_uop
        obtain ⟨_, _, _, hlt_dst₁, _, _, _, _⟩ := hframe₁.lookup_local hdecl_dst
        exact stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hframe.body_eq
          hframe.location_eq hbb hstmt hframe₁.location_eq hlt_dst₁
          (hmono dstIdx (hmono₀ dstIdx himm_dst)) hm_write
    | binaryOp bop lhsOp rhsOp lhsTy rhsTy _ hlhsOp hrhsOp hbop =>
      let knownL := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none
      have hlhs_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hlhsOp s.memory.globals knownL
      have hm_eval : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            ((annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
                annealReadImmediate) >>=
              fun left =>
                ((annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                    (if (translateBinOp bop).rightHomogeneous then some left.layout else none) >>=
                    annealReadImmediate) >>=
                  fun right => do
                    let result ← Miri.Interpreter.ScalarOps.binary
                      (annealScalarOpsHooks body.localDecls body.layouts) ()
                      (translateBinOp bop) left right
                    assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                    annealWriteImmediate result.imm destPlace)) m₀ := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        rw [hkind]
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
          translateRvalue, annealStepHooks]
        apply runRvalue_eq_of_eq
        rw [evalRvalueIntoPlace_binaryOp_def]
        unfold annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
        rw [EStateM.bind_eq_ok hevalPlace_dst, EStateM.bind_assoc_apply]
        dsimp only [knownL, destPlace]
        with_unfolding_all
          simp only [Bind.bind, EStateM.bind]
          cases annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp)
            (if (translateBinOp bop).leftHomogeneous = true then some (translateTy dstDecl.ty body.layouts) else none) m₀ with
          | error _ _ => rfl
          | ok opL st₁ =>
            dsimp only
            cases annealReadImmediate opL st₁ with
            | error _ _ => rfl
            | ok left st₂ =>
              dsimp only
              cases annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                (if (translateBinOp bop).rightHomogeneous = true then some left.layout else none) st₂ <;> rfl
      generalize ha_lhs : evalOperand s.frame.locals lhsOp .nil s.memory.globals body.layouts .nil = aLhs at hlhs_sim
      generalize hm_lhs : (annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
        annealReadImmediate) m₀ = mLhs at hlhs_sim
      cases hlhs_sim with
      | ub m' msg =>
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hm_lhs]
        rw [miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
      | ok _ locals₁ topFrame₁ imm₁ hframe₁ himm₁ hmono₁ _ _ =>
        let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
        let knownR := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsTy body.layouts) else none
        have hrhs_sim := evalOperand_scalar_simulation (m := m₁) rfl hframe₁
          (hrhsOp.mono_immediate hmono₁) s.memory.globals knownR
        dsimp only at hrhs_sim
        generalize ha_rhs : evalOperand locals₁ rhsOp .nil s.memory.globals body.layouts .nil = aRhs at hrhs_sim
        generalize hm_rhs : (annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp) knownR >>=
          annealReadImmediate) m₁ = mRhs at hrhs_sim
        cases hrhs_sim with
        | ub m'' msg =>
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              (m'', .error (.undefinedBehavior msg)) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_error hm_rhs]
          rw [miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
          exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
        | ok _ locals₂ topFrame₂ imm₂ hframe₂ himm₂ hmono₂ _ _ =>
          let m₂ : AnnealStepState := { m with stack := ⟨#[topFrame₂]⟩ }
          obtain ⟨sc₁, sc₂, rfl, rfl, hbin_sim⟩ :=
            scalarOps_binary_simulation (locals₂ := locals₂) (mem := s.memory) (m₂ := m₂)
              hlhsOp.operandTy_eq hbop himm₁ himm₂
          have hbind₂ := estate_bind_pure_assoc
            (Miri.Interpreter.ScalarOps.binary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
              ⟨imm₂, translateTy rhsTy body.layouts⟩)
            (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
            (fun result => result.imm)
            (fun i => annealWriteImmediate i destPlace)
            m₂
          generalize ha_bin : evalScalarBinOp bop sc₁ sc₂ locals₂ s.memory
            (operandIsSigned body.localDecls lhsOp body.layouts) = aBin at hbin_sim
          generalize hm_bin : (do
            let result ← Miri.Interpreter.ScalarOps.binary
              (annealScalarOpsHooks body.localDecls body.layouts) ()
              (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
              ⟨imm₂, translateTy rhsTy body.layouts⟩
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            pure result.imm) m₂ = mBin at hbin_sim
          cases hbin_sim with
          | ub msg =>
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
                (m₂, .error (.undefinedBehavior msg)) := by
              rw [hm_eval]
              unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hm_lhs]
              dsimp only
              rw [EStateM.bind_eq_ok hm_rhs]
              rw [hbind₂, EStateM.bind_eq_error hm_bin]
            rw [miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
            exact ⟨StepPreservesNodup.of_error, StepPreservesHighWater.of_error⟩
          | ok _ imm' _ =>
            have hm_write : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
                Miri.Interpreter.runRvalue
                  (annealWriteImmediate imm' destPlace)
                  m₂ := by
              rw [hm_eval]
              apply runRvalue_eq_of_eq
              rw [EStateM.bind_eq_ok hm_lhs]
              dsimp only
              rw [EStateM.bind_eq_ok hm_rhs]
              rw [hbind₂, EStateM.bind_eq_ok hm_bin]
            obtain ⟨_, _, _, hlt_dst₂, _, _, _, _⟩ := hframe₂.lookup_local hdecl_dst
            exact stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hframe.body_eq
              hframe.location_eq hbb hstmt hframe₂.location_eq hlt_dst₂
              (hmono₂ dstIdx (hmono₁ dstIdx (hmono₀ dstIdx himm_dst))) hm_write

/-- Every `LM-1.4` storage/move statement (`WellTypedLM1_4Stmt`) preserves
`LiveAllocsNodup`, `IsImmediateFrameLocal` across all locals, and `MemoryHighWater`
(`allocBudget = 0`). -/
theorem step_lm1_4_preserves_nodup_and_immediate
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM1_4Stmt body topFrame stmt) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  cases hwt topFrame hframes with
  | storageLive loc decl span hdecl =>
    obtain ⟨_, _, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
      rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
      exact ⟨_, rfl⟩
    have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
      rw [hmls_eq]; exact hloc.allocLive
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.storageLive loc, span⟩) m =
        ({ stack := ⟨#[{ topFrame with
              locals := topFrame.locals.set loc
                { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
           machine := { m.machine with
              memory := Correspondence.deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
          .ok ()) := by
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
      hfr.location_eq]
    refine ⟨StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_,
      fun _ hw _ => by
        obtain ⟨hw', hnext⟩ := hw.deallocLocalMemory (topFrame.locals[loc]'hlt_mf).value
        exact ⟨hw', by dsimp only; rw [hnext]; omega⟩⟩
    intro _ tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = topFrame := by simpa using htf.symm
    subst htf_eq
    dsimp only at htf'
    injection htf' with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact hj.set_immediate hlt_mf .uninit
  | storageDead loc decl span hdecl hne =>
    obtain ⟨_, _, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
      rw [hmls_eq]; exact hloc.allocLive
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.storageDead loc, span⟩) m =
        ({ stack := ⟨#[{ topFrame with
              locals := topFrame.locals.set loc
                { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
           machine := { m.machine with
              memory := Correspondence.deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
          .ok ()) := by
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne hlive
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
      hfr.location_eq]
    refine ⟨StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_,
      fun _ hw _ => by
        obtain ⟨hw', hnext⟩ := hw.deallocLocalMemory (topFrame.locals[loc]'hlt_mf).value
        exact ⟨hw', by dsimp only; rw [hnext]; omega⟩⟩
    intro _ tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = topFrame := by simpa using htf.symm
    subst htf_eq
    dsimp only at htf'
    injection htf' with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact hj.set_dead hlt_mf
  | placeMention loc decl span hdecl _ =>
    obtain ⟨_, _, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hcache : ∀ l, (topFrame.locals[loc]'hlt_mf).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq]; exact hloc.layout_eq
    have hm := evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl hcache
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
      hfr.location_eq]
    refine ⟨StepPreservesNodup.of_nodup hnodup, ?_, StepPreservesHighWater.of_same_memory rfl⟩
    intro _ tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = topFrame := by simpa using htf.symm
    subst htf_eq
    dsimp only at htf'
    injection htf' with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact hj.cache_layout hlt_mf _
  | assignMove dstIdx srcIdx dstDecl srcDecl span hdecl_dst hdecl_src hty hsz himm_src himm_dst =>
    obtain ⟨_, _, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hfr.lookup_local hdecl_dst
    let topFrame₀ :=
      cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    have hdisj₀ : MemoryAllocDisjoint topFrame₀ := hdisj.cache_layout hlt_dst0 _
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity,
          translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hfr.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
      revert hbor hprot
      generalize s.memory = mem
      intro hbor hprot
      cases mem
      dsimp only at hbor hprot
      subst hbor hprot
      rfl
    dsimp only at hmem_same
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue
          ((annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
            fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, translateOperand, List.map, List.toArray,
        translateRvalue, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst]
      exact EStateM.bind_assoc_apply _ _ _ m₀
    obtain ⟨_, mls_src, hlt_af_src, hlt_src, hslot_src, hmls_src, hmls_src_eq, hloc_src⟩ :=
      hframe₀.lookup_local hdecl_src
    cases hloc_src with
    | dead cl hcl =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error (EStateM.bind_eq_error
          (annealEvalOperand_move_dead rfl hlt_src hdecl_src hmls_src_eq (fun l hl => hcl l hl)))]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact ⟨StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
        StepPreservesHighWater.of_error⟩
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (hmono₀ srcIdx himm_src _ hmls_src mp)
    | immediate _ imm _ hcl hval =>
      have hlt_src' : srcIdx < (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
          (translateTy srcDecl.ty body.layouts)).locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_src
      let topFrame₁ := deinitFrameLocal
        (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src (translateTy srcDecl.ty body.layouts))
        srcIdx hlt_src'
      have hop := annealEvalOperand_move_live
        (known := some (translateTy dstDecl.ty body.layouts))
        (rfl : m₀.stack.frames = #[topFrame₀]) hlt_src hdecl_src hmls_src_eq
        (fun l hl => hcl l hl)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
            ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          have hAR : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
              .error (.undefinedBehavior "read of uninitialized local")
                { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
            rw [EStateM.bind_eq_ok hop]
            rfl
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hAR]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact ⟨StepPreservesNodup.of_error, StepPreservesImmediate.of_error,
          StepPreservesHighWater.of_error⟩
      · obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hsz
          (translateTy srcDecl.ty body.layouts) { m₀ with stack := ⟨#[topFrame₁]⟩ }
        have hm_op : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
            .ok ⟨imm, translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [EStateM.bind_eq_ok hop, hread]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
            Miri.Interpreter.runRvalue (annealWriteImmediate imm destPlace)
              { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          exact EStateM.bind_eq_ok hm_op
        have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
            body.localDecls body.layouts =
            match get? (s.frame.locals.set srcIdx .uninit) dstIdx with
            | .some .dead => MirStepNode.fail .ub
            | .some _ =>
              match set? (s.frame.locals.set srcIdx .uninit) dstIdx (.init v) with
              | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
              | .none => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only
          have huse : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
              body.localDecls body.layouts = .ok v (s.frame.locals.set srcIdx .uninit) s.memory := by
            unfold evalRvalue
            dsimp only
            rw [hbor, hcaller]
            simp [evalOperand, hslot_src, set?_eq_some_set hlt_af_src]
          rw [huse]
          dsimp only
          rw [hprot, hbor]
          dsimp only [invalidateConflictingBorrows]
          rw [hmem_same]
          rfl
        have hnew : LocalRel m.machine srcDecl body.layouts .uninit
            { (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
                (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src' with
              value := .live (.immediate .uninit) } := by
          have hlay : ((cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src').layout =
              some (translateTy srcDecl.ty body.layouts) := by
            simp [cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        have hframe₁ : FrameRel body m.machine
            { s.frame with locals := s.frame.locals.set srcIdx .uninit } topFrame₁ :=
          (hframe₀.cache_local_layout hdecl_src hlt_src).update_local hdecl_src .uninit
            (.live (.immediate .uninit)) hnew
        have hdisj₁ : MemoryAllocDisjoint topFrame₁ := by
          apply MemoryAllocDisjoint.mono_immediate (tf := topFrame₀) hdisj₀
          intro k
          by_cases hk : k = srcIdx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy srcDecl.ty body.layouts), by
              simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout]⟩
          · left
            simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout,
              Array.getElem?_set_ne _ (Ne.symm hk)]
        have hmono₁ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₁ j :=
          fun j hj => ((hmono₀ j hj).cache_layout hlt_src _).set_immediate hlt_src' .uninit
        have himmRel' : ImmediateRel dstDecl.ty body.layouts v imm := hty ▸ himmRel
        obtain ⟨_, _, _, hlt_dst₁, _, _, _, _⟩ := hframe₁.lookup_local hdecl_dst
        have hext := write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
          hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
          hframes hfr.body_eq hfr.location_eq hmono₁ hbb hstmt hframe₁ hdisj₁
          hdecl_dst (hmono₁ dstIdx himm_dst) himmRel' ha_ok hm_write
        obtain ⟨hnd_w, hhw_w⟩ :=
          stepPreservesNodup_and_HighWater_of_write_local hnodup hframes hfr.body_eq
            hfr.location_eq hbb hstmt hframe₁.location_eq hlt_dst₁
            (hmono₁ dstIdx himm_dst) hm_write
        refine ⟨hnd_w, ?_, hhw_w⟩
        intro hok tf tf' htf htf' j _ hj
        rw [hframes] at htf
        have htf_eq : tf = topFrame := by simpa using htf.symm
        subst htf_eq
        exact hext.2 j hj tf' htf' hok

/-- Well-typed statement covered by the composed `LM-2.1` statement simulation
(`step_stmt_lm2_1_simulation`), uniting:
1. `LM-2.1` array statements (`WellTypedLM2_1ArrayStmt`),
2. `LM-1.1` scalar statements (`WellTypedScalarStmt`), and
3. `LM-1.4` storage/move statements (`WellTypedLM1_4Stmt`). -/
inductive WellTypedLM2_1Stmt
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Statement → Prop where
  | arrayStmt {stmt : Statement} :
      WellTypedLM2_1ArrayStmt body s m topFrame stmt →
      WellTypedLM2_1Stmt body s m topFrame stmt
  | scalarStmt {stmt : Statement} :
      WellTypedScalarStmt body topFrame stmt →
      WellTypedLM2_1Stmt body s m topFrame stmt
  | lm14Stmt {stmt : Statement} :
      WellTypedLM1_4Stmt body topFrame stmt →
      WellTypedLM2_1Stmt body s m topFrame stmt

/-- **`step_stmt_lm2_1_simulation`** (`LM-2.1` master statement simulation):
From any `StateRel`-related pair of states `(s, m)` with `LiveAllocsNodup m.machine`,
executing any `WellTypedLM2_1Stmt` (array `Aggregate`, `Repeat`, `Len`, `Index` and
`ConstantIndex` element reads/writes, `LM-1.1` scalar statements, and `LM-1.4`
storage/move statements) steps Anneal (`stepMirFn`) and `lean-miri` (`Step.step`) in
exact lockstep (`StepRel`), preserving `StateRel` (including `ArraySliceRel` and
`MemoryAllocDisjoint`), `LiveAllocsNodup` (`StepPreservesNodup`),
`IsImmediateFrameLocal` across every local except an array-construction destination
(`StepPreservesImmediate`), and `MemoryHighWater` (`StepPreservesHighWater`, advancing
`nextAllocId` by at most `1` on array-constructing statements and `0` on all others),
so `step_stmt_lm2_1_simulation` composes across multi-allocation chains of array,
scalar, and storage/move statements via `MemoryHighWater.canReserveAllocId`, as long
as `nextAllocId` plus the number of remaining array constructions stays below
`2 ^ 64`.
Both machines agree on UB when array/index/operand/destination locals are dead or
uninitialized or indices are out of bounds. -/
theorem step_stmt_lm2_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1Stmt body s m topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => arrayConstructDest? stmt ≠ some j)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m (if (arrayConstructDest? stmt).isSome then 1 else 0)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hstate_copy := hstate
  rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _, _⟩
  have htf_eq : ∀ tf, m.stack.frames = #[tf] → tf = topFrame := by
    intro tf h
    rw [hframes] at h
    simpa using h.symm
  cases hwt topFrame hframes with
  | arrayStmt harr =>
    exact step_stmt_lm2_1_array_simulation hstate_copy hnodup hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ harr)
  | scalarStmt hsc =>
    have hext := step_assign_scalar_simulation_ext hstate_copy hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hsc)
    obtain ⟨hnd, hhw⟩ := step_scalar_preserves_nodup hstate_copy hnodup hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hsc)
    refine ⟨hext.1, hnd, ?_, hhw.mono_budget (Nat.zero_le _)⟩
    intro hok tf tf' htf htf' j _ hj
    exact hext.2 tf htf j hj tf' htf' hok
  | lm14Stmt hlm14 =>
    have hrel' := step_stmt_lm1_4_simulation hstate_copy hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hlm14)
    obtain ⟨hnd, himm, hhw⟩ := step_lm1_4_preserves_nodup_and_immediate hstate_copy hnodup hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hlm14)
    exact ⟨hrel', hnd, himm.mono fun _ _ => trivial, hhw.mono_budget (Nat.zero_le _)⟩

end LeanMiriSpec.Correspondence
