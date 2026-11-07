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
   offset calculation (`idx < count`), element read correspondence, and out-of-bounds
   (`idx ≥ count`) / uninitialized / dead `idxLocal` UB equivalence.
3. `evalProjection_constantIndex_simulation`: `ProjectionElem.constantIndex offset minLength fromEnd`
   for both `fromEnd = false` (`idx = offset`) and `fromEnd = true` (`idx = count - offset`),
   covering both in-bounds offset calculation (`minLength ≤ count`) and out-of-bounds
   (`count < minLength`) UB equivalence.
4. `evalRvalue_len_array_simulation`: `Rvalue.len place` on `[T; N]` vs `UnaryOp.PtrMetadata`,
   including dead/uninitialized array UB equivalence.
5. `evalRvalue_repeat_simulation`: `Rvalue.repeat op count` vs `Miri.Interpreter.writeRepeat`,
   parametric over `count` (`0` and `> 0`) and `op`, including dead/uninitialized UB equivalence.
6. `evalRvalue_aggregate_array_simulation`: `Rvalue.aggregate (.array elemTy) ops` vs
   `Miri.Interpreter.writeAggregate`, proved by parametric induction over `ops`, including
   dead/uninitialized UB equivalence.
7. `step_assign_array_element_simulation`: indexed array element read (`dst = arr[i]`) and
   indexed array element write (`arr[i] = op`) for both `.index` and `.constantIndex`,
   preserving all `j ≠ idx` elements and `MemoryAllocDisjoint`, plus OOB/uninit/dead UB.
8. `step_stmt_lm2_1_array_simulation`: statement-level lockstep simulation for the
   `LM-2.1` array statements that also re-establishes the invariants outside
   `StateRel` that the next array statement needs (`StepPreservesNodup`,
   `StepPreservesImmediate`), so that the theorem chains across statements.
9. `step_stmt_lm2_1_simulation`: master statement-level lockstep simulation theorem for
   the `LM-2.1` array statements together with the `LM-1.1` scalar and `LM-1.4`
   storage/move statements.
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

/-! ## 2. `Index` and `ConstantIndex` Projection Simulation (`evalProjection_index_simulation`, `evalProjection_constantIndex_simulation`) -/

/-- Helper: `Miri.Interpreter.projectIndex` on an array `OpTy` with `WellTypedArrayTy`:
- succeeds with offset `idx * elemSize` and layout `translateTy elemTy layouts` when `idx < count`,
- fails with `.error (.bounds (UInt64.ofNat count) (UInt64.ofNat idx))` when `count ≤ idx` and `idx < 2 ^ 64`. -/
theorem projectIndex_array_spec
    {frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count) :
    let cx := annealProjectionCx frame layouts
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
    unfold Miri.Interpreter.projectIndex
    rw [hfields, hlen]
    simp only [bind, Except.bind, hnot_ge, ↓reduceIte, hcomp, hfield]
    unfold Miri.Interpreter.OpTy.offset Miri.Interpreter.OpTy.offsetWithMeta
    rw [hwf.elem_isSized]
    simp [base, cx, annealProjectionCx, annealMemoryOffset,
      Miri.Interpreter.MemPlaceMeta.hasMeta, bind, Except.bind, pure, Except.pure]
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

/-- **`evalProjection_index_simulation`** (`LM-2.1`):
Evaluating `ProjectionElem.index idxLocal` on an array place of type `arrTy`
(`WellTypedArrayTy layouts arrTy elemKind count`) related by `MemPlaceRel`:
1. If `idxLocal` is `.dead` or `.uninit`, both Anneal (`readProjectedValue` /
   `writeProjectedValue`) and Miri (`annealProjectList` lifted via `annealLiftProjectionError`)
   raise UB.
2. If `idxLocal` holds `.init (.scalar idxSc)` with `idxSc.bits < count`:
   Anneal's `readProjectedValue` returns `.ok elemVal` where `get? elems idxSc.bits = some elemVal`,
   Miri's `annealProjectList` advances `mp.ptr.offset` by `idxSc.bits * elemSize` with
   layout `translateTy elemTy layouts`, and `annealReadImmediate` reads back the
   `ImmediateRel`-matching scalar.
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
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 })
    (hidx_imm : IsImmediateFrameLocal topFrame idxLocal) :
    let cx := annealProjectionCx topFrame body.layouts
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
  have ⟨hproj_in, hproj_oob⟩ := projectIndex_array_spec (frame := topFrame) (mp := mp) hwf
  have hlen_elems : elems.length = count := by
    cases hmp with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ harr =>
      exact (harr elemKind count elems hwf.arr_kind rfl).2.2.2.elems_len
  refine ⟨?_, ?_, ?_⟩
  · intro hdead_uninit
    obtain ⟨slot_idx, mls, _, hlt_mf, hslot_idx, hmls, hmls_eq, hloc_rel⟩ := hfr.lookup_local hidx_decl
    rcases hdead_uninit with hdead | huninit
    · rw [hdead] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
      cases hloc_rel with
      | dead cachedLayout _ =>
        have hop : topFrame.getLocalOperand idxLocal = .error (.localExpectedLive idxLocal) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        refine ⟨by simp [readProjectedValue, hdead], fun v => by simp [writeProjectedValue, hdead],
          "index local is dead", ?_⟩
        simp [annealProjectList, Miri.Interpreter.project, cx, annealProjectionCx,
          annealLocalIndex, hop, Except.mapError, annealLiftProjectionError, bind, Except.bind]
      | immediate _ _ _ _ himm =>
        rcases himm with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
      | indirect _ _ _ _ hnot_dead _ =>
        exact absurd rfl hnot_dead
    · rw [huninit] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
      cases hloc_rel with
      | immediate _ imm cachedLayout _ himm =>
        rcases himm with ⟨_, rfl⟩ | ⟨_, hv, _⟩
        · have hop : topFrame.getLocalOperand idxLocal = .ok (.immediate .uninit) := by
            unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
              Miri.Interpreter.LocalState.access
            simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
          refine ⟨by simp [readProjectedValue, huninit], fun v => by simp [writeProjectedValue, huninit],
            "index local is uninitialized", ?_⟩
          simp [annealProjectList, Miri.Interpreter.project, cx, annealProjectionCx,
            annealLocalIndex, hop, Except.mapError, annealLiftProjectionError, bind, Except.bind]
        · cases hv
      | indirect _ mp_idx _ _ _ _ =>
        exact absurd rfl (hidx_imm _ hmls mp_idx)
  · intro idxSc hidx_slot hlt
    obtain ⟨slot_idx, mls, _, hlt_mf, hslot_idx, hmls, hmls_eq, hloc_rel⟩ := hfr.lookup_local hidx_decl
    rw [hidx_slot] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
    cases hloc_rel with
    | indirect _ mp_idx _ _ _ _ =>
      exact absurd rfl (hidx_imm _ hmls mp_idx)
    | immediate _ imm cachedLayout _ himm =>
      rcases himm with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
      · cases h1
      · injection hv' with hv_eq
        subst hv_eq
        obtain ⟨sc', msc, hsc_eq, rfl, hsc_rel, hsz_eq, _, _⟩ :=
          ImmediateRel.of_primitive_scalar himm' (by rw [hidx_ty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
        injection hsc_eq with hsc_eq'
        subst hsc_eq'
        have hop : topFrame.getLocalOperand idxLocal = .ok (.immediate (.scalar (.fromScalarInt msc))) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        have hsz8 : translateSizeBytes idxSc.sizeBytes = Miri.ABI.Size.ofBytes 8 := by
          rw [← hsz_eq, hidx_ty]
          rfl
        have htb8 : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 idxSc.bits) := by
          rw [← hsz8]
          exact hsc_rel.toBits_eq
        have htoBits :
            (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits (Miri.ABI.Size.ofBytes 8) =
              .ok (BitVec.ofNat 128 idxSc.bits) := by
          unfold Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
            Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
          dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
          rw [htb8]
          rfl
        have hbv_toNat : (BitVec.ofNat 128 idxSc.bits).toNat = idxSc.bits :=
          bitVec_ofNat_128_toNat hsc_rel.validBytes hsc_rel.canonical
        have hlocalIdx : annealLocalIndex topFrame idxLocal = .ok (UInt64.ofNat idxSc.bits) := by
          unfold annealLocalIndex
          rw [hop]
          dsimp only
          rw [htoBits]
          dsimp only
          rw [hbv_toNat]
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
    obtain ⟨slot_idx, mls, _, hlt_mf, hslot_idx, hmls, hmls_eq, hloc_rel⟩ := hfr.lookup_local hidx_decl
    rw [hidx_slot] at hslot_idx; injection hslot_idx with hslot_eq; subst hslot_eq
    cases hloc_rel with
    | indirect _ mp_idx _ _ _ _ =>
      exact absurd rfl (hidx_imm _ hmls mp_idx)
    | immediate _ imm cachedLayout _ himm =>
      rcases himm with ⟨h1, _⟩ | ⟨v', hv', himm'⟩
      · cases h1
      · injection hv' with hv_eq
        subst hv_eq
        obtain ⟨sc', msc, hsc_eq, rfl, hsc_rel, hsz_eq, _, _⟩ :=
          ImmediateRel.of_primitive_scalar himm' (by rw [hidx_ty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
        injection hsc_eq with hsc_eq'
        subst hsc_eq'
        have hop : topFrame.getLocalOperand idxLocal = .ok (.immediate (.scalar (.fromScalarInt msc))) := by
          unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
            Miri.Interpreter.LocalState.access
          simp [hlt_mf, hmls_eq, bind, Except.bind, pure, Except.pure, Except.mapError]
        have hsz8 : translateSizeBytes idxSc.sizeBytes = Miri.ABI.Size.ofBytes 8 := by
          rw [← hsz_eq, hidx_ty]
          rfl
        have hsz_bytes : idxSc.sizeBytes = 8 := by
          rcases hsc_rel.validBytes with h | h | h | h | h <;>
            (rw [h] at hsz8; first | exact h | exact absurd hsz8 (by decide))
        have hbits_lt : idxSc.bits < 2 ^ 64 := by
          have hc := hsc_rel.canonical
          rw [hsz_bytes] at hc
          exact hc
        have htb8 : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 idxSc.bits) := by
          rw [← hsz8]
          exact hsc_rel.toBits_eq
        have htoBits :
            (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits (Miri.ABI.Size.ofBytes 8) =
              .ok (BitVec.ofNat 128 idxSc.bits) := by
          unfold Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
            Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
          dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
          rw [htb8]
          rfl
        have hbv_toNat : (BitVec.ofNat 128 idxSc.bits).toNat = idxSc.bits :=
          bitVec_ofNat_128_toNat hsc_rel.validBytes hsc_rel.canonical
        have hlocalIdx : annealLocalIndex topFrame idxLocal = .ok (UInt64.ofNat idxSc.bits) := by
          unfold annealLocalIndex
          rw [hop]
          dsimp only
          rw [htoBits]
          dsimp only
          rw [hbv_toNat]
        have hget_none : get? elems idxSc.bits = none := by
          change elems[idxSc.bits]? = none
          rw [List.getElem?_eq_none_iff, hlen_elems]
          exact hge
        refine ⟨by simp [readProjectedValue, hidx_slot, hget_none],
          fun v => by simp [writeProjectedValue, hidx_slot, hget_none],
          ?_⟩
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
    let cx := annealProjectionCx topFrame body.layouts
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
  have ⟨hproj_in, _⟩ := projectIndex_array_spec (frame := topFrame) (mp := mp) hwf
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

/-! ## 3. Array Length Query Simulation (`evalRvalue_len_array_simulation`) -/

/-- Helper: `annealReadImmediate` on an initialized array `OpTy` (`MemPlaceRel`)
followed by `ScalarOps.unary .PtrMetadata` succeeds and produces a `usize` scalar
`ImmediateRel`-related to `Value.scalar ⟨count, 8⟩`. -/
theorem annealReadImmediate_of_array_memPlaceRel
    {m : AnnealStepState} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {arrTy : Ty} {elemKind : RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup m.machine)
    (hmp : MemPlaceRel m.machine arrTy layouts (some (.aggregate 0 elems)) mp) :
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    ∃ countSc,
      elems.length = count ∧
      Trusted.Sequence.length elems = count ∧
      ScalarRel ⟨count, 8⟩ countSc ∧
      ImmediateRel usizeTy layouts (.scalar ⟨count, 8⟩) (.scalar (.fromScalarInt countSc)) ∧
      ((annealReadImmediate ⟨.indirect mp, translateTy arrTy layouts⟩ >>=
          fun val =>
            Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks localDecls layouts) () .PtrMetadata val) m =
        .ok ⟨.scalar (.fromScalarInt countSc), translateTy usizeTy layouts⟩ m) := by
  intro usizeTy
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
        annealReadImmediate ⟨.indirect mp, translateTy arrTy layouts⟩ m =
          .ok
            ⟨.scalarPair
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨mp.ptr.offset, .concrete allocId tag⟩)
              (.fromScalarInt countSc),
              translateTy { kind := .ref .not (.slice .bool), layoutIdx := 0 }⟩
            m := by
      unfold annealReadImmediate
      dsimp only
      rw [hprov, hwf.arr_fields]
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
        Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz,
        hslice.alloc_mask, hinit, htry_eq, pure, EStateM.pure]
    rw [EStateM.bind_eq_ok hread]
    unfold Miri.Interpreter.ScalarOps.unary annealScalarOpsHooks
    rfl

/-- A `lean-miri` statement that ends by writing an immediate into the
immediate local `dstIdx` (`annealWriteImmediate` on `.local 0 dstIdx none id0`)
either fails or keeps `m.machine`, so it preserves `LiveAllocsNodup`. -/
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
      exact StepPreservesNodup.of_error
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
        exact StepPreservesNodup.of_nodup hnodup

/-- **`evalRvalue_len_array_simulation`** (`LM-2.1`):
Statement-level simulation of `dst = Len(arr)` (`StatementKind.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩)`)
for a fixed-size homogeneous array local `arrIdx` (`WellTypedArrayTy body.layouts arrDecl.ty elemKind count`):
- When `arrIdx` is `.dead` or `.uninit`, both Anneal (`stepMirFn`) and Miri (`Step.step`)
  report an undefined-behavior fault (`StepRel.ub`).
- When `arrIdx` holds `.init (.aggregate 0 elems)` and `dstIdx` is `.dead`, both report UB (`StepRel.ub`).
- When `arrIdx` holds `.init (.aggregate 0 elems)` and `dstIdx` is live, both step to
  `StateRel`-related states with `dstIdx` storing `.scalar ⟨count, 8⟩`
  (`StepRel.step`).
- A normal `lean-miri` step preserves `LiveAllocsNodup` (`StepPreservesNodup`)
  and the immediacy of every local (`StepPreservesImmediate`).

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
        ((annealEvalOperand body.localDecls body.layouts (.Copy ⟨arrIdx, #[]⟩) none >>=
            annealReadImmediate) >>=
          fun val => do
            let result ← Miri.Interpreter.ScalarOps.unary
              (annealScalarOpsHooks body.localDecls body.layouts) () .PtrMetadata val
            assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
            annealWriteImmediate result.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, translateOperand, List.map, List.toArray,
      translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    rw [evalRvalueIntoPlace_unaryOp_def]
    unfold annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, Miri.MIR.UnOp.homogeneous,
      Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hevalPlace_dst]
    exact EStateM.bind_assoc_apply _ _ _ m₀
  obtain ⟨slot_arr, mls_arr, hlt_af_arr, hlt_arr, hslot_arr, hmls_arr, hmls_arr_eq, hloc_arr⟩ :=
    hframe₀.lookup_local hdecl_arr
  rcases harr_slot with hdead | ⟨huninit, hcount_or_imm⟩ | ⟨elems, hinit_elems⟩
  · -- Case 1: `arrIdx` is `.dead`
    rw [hdead] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    cases hloc_arr with
    | dead cl hcl =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        simp [evalRvalue, evalOperand, hdead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
          ({ m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ arrIdx hlt_arr
              (translateTy arrDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error (EStateM.bind_eq_error
          (annealEvalOperand_copy_dead rfl hlt_arr hdecl_arr hmls_arr_eq (fun l hl => hcl l hl)))]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
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
    let topFrame₁ :=
      cacheFrameLocalLayout topFrame₀ arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
    cases hloc_arr with
    | immediate _ imm cl hcl hval =>
      rcases hval with ⟨_, rfl⟩ | ⟨_, hv, _⟩
      · have hop := annealEvalOperand_copy_live (known := none)
          (rfl : m₀.stack.frames = #[topFrame₀]) hlt_arr hdecl_arr hmls_arr_eq
          (fun l hl => hcl l hl)
        have hAR : (annealEvalOperand body.localDecls body.layouts (.Copy ⟨arrIdx, #[]⟩) none >>=
            annealReadImmediate) m₀ =
            .error (.undefinedBehavior "read of uninitialized local")
              { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
          rw [EStateM.bind_eq_ok hop]
          rfl
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
            ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hAR]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
      · cases hv
    | indirect _ mp cl hcl _ hmp =>
      rcases hcount_or_imm with hpos | himm_arr
      · have hop := annealEvalOperand_copy_live (known := none)
          (rfl : m₀.stack.frames = #[topFrame₀]) hlt_arr hdecl_arr hmls_arr_eq
          (fun l hl => hcl l hl)
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
            have hpos_elem := hwf.elem_size_pos
            have : 0 < count * (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat :=
              Nat.mul_pos hpos hpos_elem
            omega
          have hnot_init := huninit_cons rfl hsz_nz
          have hread_err :
              annealReadImmediate ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
                { m₀ with stack := ⟨#[topFrame₁]⟩ } =
              .error (.undefinedBehavior "len of uninitialized array")
                { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
            unfold annealReadImmediate
            dsimp only [m₀] at hbase ⊢
            rw [hprov, hwf.arr_fields]
            simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
              Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind, hrel_sz]
            cases his : localAlloc.allocation.initializationMask.isRangeInitialized
                (Miri.Memory.allocRange relOffset (translateTy arrDecl.ty body.layouts).layout.size) with
            | error e => rfl
            | ok inner =>
              cases inner with
              | error e => rfl
              | ok u =>
                cases u
                exact absurd his hnot_init
          have hAR : (annealEvalOperand body.localDecls body.layouts (.Copy ⟨arrIdx, #[]⟩) none >>=
              annealReadImmediate) m₀ =
              .error (.undefinedBehavior "len of uninitialized array")
                { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
            rw [EStateM.bind_eq_ok hop, hread_err]
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩) m =
              ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
                .error (.undefinedBehavior "len of uninitialized array")) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_error hAR]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
            hstmt hm_err]
          exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
      · exact absurd rfl (hmono₀ arrIdx (himm_arr topFrame hframes) _ hmls_arr mp)
  · -- Case 3: `arrIdx` holds `.init (.aggregate 0 elems)`
    rw [hinit_elems] at hslot_arr; injection hslot_arr with hslot_eq; subst hslot_eq
    obtain ⟨mp, cl, rfl, hcl, hmp⟩ := hloc_arr.array_init_is_indirect hwf.arr_kind
    let topFrame₁ :=
      cacheFrameLocalLayout topFrame₀ arrIdx hlt_arr (translateTy arrDecl.ty body.layouts)
    have hop := annealEvalOperand_copy_live (known := none)
      (rfl : m₀.stack.frames = #[topFrame₀]) hlt_arr hdecl_arr hmls_arr_eq
      (fun l hl => hcl l hl)
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
      rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hop]
      have hread_unary' :
          (annealReadImmediate ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ >>=
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
    refine ⟨hext.1,
      stepPreservesNodup_of_write_local hnodup hframes hframe.body_eq hframe.location_eq hbb hstmt
        hframe₁.location_eq hlt_dst₁ (hmono₁ dstIdx hdst_imm_tf) hm_write, ?_⟩
    intro hok tf tf' htf htf' j _ hj
    rw [hframes] at htf
    have htf_eq : tf = topFrame := by simpa using htf.symm
    subst htf_eq
    exact hext.2 j hj tf' htf' hok

/-! ## 4. `annealEnsureAllocated` Helpers & `Rvalue.Repeat` Simulation (`evalRvalue_repeat_simulation`) -/

/-- The machine's allocation-ID supply can reserve one fresh `AllocId`. -/
def CanReserveAllocId (mem : AnnealMemory) : Prop :=
  ∃ mem' id, mem.reserveAllocId = (mem', .ok id)

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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  let topFrame₂ := setFrameLocalIndirect topFrame₁ dstIdx hlt_mf (stackAllocPlace allocId)
  have hloc₂ : topFrame₂.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
    hframe₁.location_eq
  rw [ha_step, miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_step rfl hloc₂]
  refine ⟨StepRel.step _ _ ?_,
    StepPreservesNodup.of_nodup (LiveAllocsNodup.stackAllocMachine alloc_final hnodup hres),
    ?himm⟩
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

theorem replicateValue_eq_replicate (n : Nat) (v : Value) :
    replicateValue n v = List.replicate n v := by
  induction n with
  | zero => rfl
  | succ k ih => simp [replicateValue, List.replicate, ih]

/-- Full single-step correspondence for `_dst = [op; count]` (`Rvalue.repeat`):
handles source operand UB (dead/uninitialized local), destination `.dead` UB,
and in-bounds array allocation + element population establishing `ArraySliceRel`
and preserving `StateRel` (including `MemoryAllocDisjoint`). A normal
`lean-miri` step also preserves `LiveAllocsNodup` (`StepPreservesNodup`) and the
immediacy of every local other than `dstIdx` (`StepPreservesImmediate`). -/
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
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hcan_res : CanReserveAllocId m.machine.memory) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hrel with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hdst_imm_tf := hdst_imm topFrame hframes
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
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := by
    apply MemoryAllocDisjoint.mono_layout hdisj
    intro k
    by_cases hk : k = dstIdx
    · subst hk
      exists (translateTy dstDecl.ty body.layouts)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set]
      simp only [↓reduceIte]
      rw [hmls_dst, hmls_dst_eq]
      rfl
    · exists (topFrame.locals[k]?).bind (fun x => x.layout)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases topFrame.locals[k]? <;> rfl
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun j hj => hj.cache_layout hlt_dst _
  have hop₀ : WellTypedScalarOperand body topFrame₀ op { kind := elemKind, layoutIdx := 0 } :=
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
  have hsim_op := evalOperand_scalar_simulation (m := m₀) (rfl : m₀.stack.frames = #[topFrame₀])
    hframe₀ hop₀ s.memory.globals none
  generalize heval_a :
    evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = res_a at hsim_op
  generalize heval_m :
    (annealEvalOperand body.localDecls body.layouts (translateOperand op) none >>=
      annealReadImmediate) m₀ = res_m at hsim_op
  cases hsim_op with
  | ub m' msg =>
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue
      dsimp only
      rw [hbor, hcaller, heval_a]
    have heval_agg_err :
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand op) none m₀ =
        .error (.undefinedBehavior msg) m' := by
      dsimp only [annealAggregateHooks]
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_error heval_m]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩) m =
        (m', .error (.undefinedBehavior msg)) := by
      rw [hm_eval, writeRepeat_def]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error heval_agg_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
      hstmt hm_err]
    exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
  | ok v locals₁ topFrame₁ imm hframe₁ himm hmono₁ htf₁_eq hdisj_imp =>
    have hdisj₁ : MemoryAllocDisjoint topFrame₁ := hdisj_imp hdisj₀
    obtain ⟨sc, msc, rfl, rfl, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩ :=
      himm.of_primitive_scalar hprim
    have hisSized :
        (!(translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.isSized) = false := by
      rw [hprim.isSized]; rfl
    have heval_agg_op :
        (annealAggregateHooks body.localDecls body.layouts).evalOperandAt ()
          (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand op) none m₀ =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
             translateTy { kind := elemKind, layoutIdx := 0 } body.layouts⟩
          { m with stack := ⟨#[topFrame₁]⟩ } := by
      dsimp only [annealAggregateHooks]
      rw [EStateM.bind_assoc_apply, EStateM.bind_eq_ok heval_m]
      rfl
    obtain ⟨slot_dst₁, mls_dst₁, hlt_af_dst₁, hlt_dst₁, hslot_dst₁, hmls_dst₁, hmls_dst₁_eq, hloc_dst₁⟩ :=
      hframe₁.lookup_local hdecl_dst
    have himm_dst₁ : IsImmediateFrameLocal topFrame₁ dstIdx :=
      hmono₁ dstIdx (hmono₀ dstIdx hdst_imm_tf)
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
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm_dst₁ _ hmls_dst₁ mp rfl)
    | immediate slot_dst₁ imm_dst _ _ hval =>
      have hnot_dead : slot_dst₁ ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
      have hset_ok : set? locals₁ dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc)))) =
          some (locals₁.set dstIdx (.init (.aggregate 0 (List.replicate count (.scalar sc))))) :=
        set?_eq_some_set hlt_af_dst₁ _
      have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
        revert hbor hprot
        generalize s.memory = mem
        intro hbor hprot
        cases mem
        dsimp only at hbor hprot
        subst hbor hprot
        rfl
      dsimp only at hmem_same
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
      have hretCont₁ : topFrame₁.returnContinuation = .stop false := by
        rw [htf₁_eq]; exact hretCont
      have hretPlace₁ : ∃ retLay, topFrame₁.returnPlace =
          .frameLocal 0 0 none retLay topFrame₁.localsIdentity := by
        rw [htf₁_eq]; exact ⟨retLay, hretPlace⟩
      exact write_array_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := topFrame₁)
        hretCont₁ hretPlace₁ hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt hframe₁ hdisj₁
        hdecl_dst hwf hlt_dst₁ hres hsize_final hslice_final ha_step hm_step hnodup
        (fun j hj => hmono₁ j (hmono₀ j hj))

/-! ## 5. `Rvalue.Aggregate (.array _)` Simulation (`evalRvalue_aggregate_array_simulation`) -/

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
    (hops_k : ∀ op ∈ remOps, WellTypedScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 })
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
    (∃ vals tf_final, ∃ hlt_final : dstIdx < tf_final.locals.size, ∃ alloc_final,
      evalOperands af.locals remOps .nil globals body.layouts .nil = .ok vals af.locals ∧
      prog st_k =
        .ok () { stack := ⟨#[setFrameLocalIndirect tf_final dstIdx hlt_final (stackAllocPlace allocId)]⟩,
                 machine := stackAllocMachine mach mem' allocId alloc_final } ∧
      FrameRel body mach af tf_final ∧
      MemoryAllocDisjoint tf_final ∧
      (∀ j, IsImmediateFrameLocal tf_k j → IsImmediateFrameLocal tf_final j) ∧
      tf_final = { tf_k with locals := tf_final.locals } ∧
      alloc_final.byteSize = (translateTy dstDecl.ty body.layouts).layout.size ∧
      ArraySliceRel elemKind count body.layouts (elems_k ++ vals) Miri.ABI.Size.ZERO alloc_final) := by
  induction remOps generalizing k tf_k elems_k alloc_k with
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
    refine ⟨[], tf_k, hlt_k, alloc_k, rfl, ?_, hframe_k, hdisj_k, fun _ hj => hj, rfl, hsize_k,
      by simpa using hslice_k⟩
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
    have hop_head : WellTypedScalarOperand body tf_k op { kind := elemKind, layoutIdx := 0 } :=
      hops_k op List.mem_cons_self
    rcases evalScalarOperand_with_indirect_dst
        (mach' := stackAllocMachine mach mem' allocId alloc_k)
        hframe_k hdecl_dst hwf hprim hop_head hlt_k (stackAllocPlace allocId)
        globals (Miri.Interpreter.OperandPath.aggregate k) (some elemLay) with
      ⟨ha_ub, m', msg, hm_err⟩ |
      ⟨sc, msc, tf_k1, hlt_k1, ha_ok, hm_ok, hframe_k1, hdisj_imp1, hmono_1, htf_eq1,
        hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
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
          WellTypedScalarOperand body tf_k1 op' { kind := elemKind, layoutIdx := 0 } :=
        fun op' hmem => (hops_k op' (List.mem_cons_of_mem _ hmem)).mono_immediate hmono_1
      have hsize_k1 : alloc_k1.byteSize = (translateTy dstDecl.ty body.layouts).layout.size :=
        hbs_k1.trans hsize_k
      rcases ih (k + 1) tf_k1 hlt_k1 (elems_k ++ [.scalar sc]) alloc_k1
          hk_len1 hops_arr1 hframe_k1 (hdisj_imp1 hdisj_k) hops_k1 hsize_k1 hslice_k1 with
        ⟨ha_rest_ub, m', msg, hm_rest_err⟩ |
        ⟨vs, tf_final, hlt_final, alloc_final, ha_rest_ok, hm_rest_ok,
          hframe_final, hdisj_final, hmono_final, htf_eq_final, hsize_final, hslice_final⟩
      · left
        refine ⟨by simp [evalOperands, ha_ok, ha_rest_ub], m', msg, ?_⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_err
      · right
        have htf_eq_tot : tf_final = { tf_k with locals := tf_final.locals } := by
          rw [htf_eq_final, htf_eq1]
        have hslice_tot :
            ArraySliceRel elemKind count body.layouts (elems_k ++ (.scalar sc :: vs))
              Miri.ABI.Size.ZERO alloc_final := by
          simpa [List.append_assoc] using hslice_final
        refine ⟨.scalar sc :: vs, tf_final, hlt_final, alloc_final,
          by simp [evalOperands, ha_ok, ha_rest_ok], ?_,
          hframe_final, hdisj_final, fun j hj => hmono_final j (hmono_1 j hj), htf_eq_tot,
          hsize_final, hslice_tot⟩
        rw [List.range'_succ]
        simp only [List.forIn_cons]
        rw [← EStateM.bind_assoc_apply, EStateM.bind_eq_ok hstep_ok]
        exact hm_rest_ok

/-- Full single-step correspondence for `_dst = [op_0, ..., op_{count-1}]`
(`Rvalue.aggregate (.array elemTy) ops`):
handles destination `.dead` UB, source operand UB (dead/uninitialized local at any
position in `ops`), and in-bounds stack allocation + element-by-element writes
establishing `ArraySliceRel` and preserving `StateRel` (including `MemoryAllocDisjoint`).
A normal `lean-miri` step also preserves `LiveAllocsNodup` (`StepPreservesNodup`)
and the immediacy of every local other than `dstIdx` (`StepPreservesImmediate`). -/
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
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hops : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ op ∈ ops, WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hcan_res : CanReserveAllocId m.machine.memory) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hrel with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  have hdst_imm_tf := hdst_imm topFrame hframes
  have hops_tf := hops topFrame hframes
  obtain ⟨slot_dst, mls_dst, hlt_af_dst, hlt_dst, hslot_dst, hmls_dst, hmls_dst_eq, hloc_dst⟩ :=
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
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := by
    apply MemoryAllocDisjoint.mono_layout hdisj
    intro k
    by_cases hk : k = dstIdx
    · subst hk
      exists (translateTy dstDecl.ty body.layouts)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set]
      simp only [↓reduceIte]
      rw [hmls_dst, hmls_dst_eq]
      rfl
    · exists (topFrame.locals[k]?).bind (fun x => x.layout)
      dsimp [topFrame₀, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases topFrame.locals[k]? <;> rfl
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun j hj => hj.cache_layout hlt_dst _
  have hops₀ : ∀ op ∈ ops,
      WellTypedScalarOperand body topFrame₀ op { kind := elemKind, layoutIdx := 0 } :=
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
  have himm_dst₀ : IsImmediateFrameLocal topFrame₀ dstIdx := hmono₀ dstIdx hdst_imm_tf
  cases hloc_dst₀ with
  | dead _ _ =>
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue
      dsimp only
      rw [hbor, hcaller]
      rcases evalOperands_scalar_dichotomy hframe₀ hops₀ s.memory.globals with hub | ⟨vals, hok⟩
      · rw [hub]
      · rw [hok]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hslot_dst₀]
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
    exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
  | indirect _ mp _ _ _ _ =>
    exact False.elim (himm_dst₀ _ hmls_dst₀ mp rfl)
  | immediate slot_dst₀ imm_dst _ _ hval =>
    have hnot_dead : slot_dst₀ ≠ .dead := by
      rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
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
    have hops_arr : ∀ i (hi : i < ops.length),
        operands[0 + i]? = some (translateOperand (ops[i]'hi)) := by
      intro i hi
      simp [operands, hi]
    have hsz_ops : operands.size = ops.length := by simp [operands]
    rcases writeAggregate_loop_spec (body := body) (mach := m.machine) (af := s.frame)
        (dstIdx := dstIdx) (dstDecl := dstDecl) (id := topFrame.localsIdentity)
        (elemKind := elemKind) (count := count) (mem' := mem') (allocId := allocId)
        (operands := operands)
        hdecl_dst hwf hprim hfresh s.memory.globals ops 0 topFrame₀ hlt_dst₀ [] alloc₀
        (by simpa using hlen_ops) hops_arr hframe₀ hdisj₀ hops₀ hsize₀ hslice₀ with
      ⟨ha_ub_ops, m', msg, hm_loop_err⟩ |
      ⟨vals, tf_final, hlt_final, alloc_final, ha_ok_ops, hm_loop_ok,
        hframe_final, hdisj_final, hmono_final, htf_eq_final, hsize_final, hslice_final⟩
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
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
    · have hset_ok : set? s.frame.locals dstIdx (.init (.aggregate 0 vals)) =
          some (s.frame.locals.set dstIdx (.init (.aggregate 0 vals))) :=
        set?_eq_some_set hlt_af_dst _
      have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
        revert hbor hprot
        generalize s.memory = mem
        intro hbor hprot
        cases mem
        dsimp only at hbor hprot
        subst hbor hprot
        rfl
      dsimp only at hmem_same
      have ha_step : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
          body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s
            (s.frame.locals.set dstIdx (.init (.aggregate 0 vals))) s.memory) := by
        unfold evalStmt evalRvalue
        dsimp only
        rw [hbor, hcaller, ha_ok_ops]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same, hslot_dst₀]
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
      have hframe_final' : FrameRel body m.machine { s.frame with locals := s.frame.locals } tf_final :=
        hframe_final
      exact write_array_after_rvalue_simulation (tf₀ := topFrame) (topFrame₁ := tf_final)
        hretCont_f hretPlace_f hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq hbb hstmt hframe_final' hdisj_final
        hdecl_dst hwf hlt_final hres hsize_final (by simpa using hslice_final) ha_step hm_step
        hnodup (fun j hj => hmono_final j (hmono₀ j hj))

/-! ## 6. Array Element Read/Write (`step_assign_array_element_simulation`) & Master `LM-2.1` Simulation (`step_stmt_lm2_1_simulation`) -/

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

/-- Well-typed single array-element projection (`ProjectionElem.index idxLocal` or
`ProjectionElem.constantIndex offset minLength fromEnd`). -/
inductive WellTypedArrayElemProj
    (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    ProjectionElem → Prop where
  | index (idxLocal : Local) (idxDecl : LocalDecl) :
      get? body.localDecls idxLocal = some idxDecl →
      idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 } →
      IsImmediateFrameLocal topFrame idxLocal →
      WellTypedArrayElemProj body topFrame (.index idxLocal)
  | constantIndex (offset minLength : Nat) (fromEnd : Bool) :
      offset < 2 ^ 64 →
      minLength < 2 ^ 64 →
      ((fromEnd = false → offset < minLength) ∧
        (fromEnd = true → 0 < offset ∧ offset ≤ minLength)) →
      WellTypedArrayElemProj body topFrame (.constantIndex offset minLength fromEnd)

/-- `WellTypedArrayElemProj` is preserved by `cacheFrameLocalLayout`. -/
theorem WellTypedArrayElemProj.cache_layout
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {proj : ProjectionElem}
    (h : WellTypedArrayElemProj body tf proj)
    {j : Nat} (hlt : j < tf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    WellTypedArrayElemProj body (cacheFrameLocalLayout tf j hlt lay) proj := by
  cases h with
  | index idxLocal idxDecl hdecl hty himm =>
    exact .index idxLocal idxDecl hdecl hty (himm.cache_layout hlt lay)
  | constantIndex offset minLength fromEnd hoff hmin hwf =>
    exact .constantIndex offset minLength fromEnd hoff hmin hwf

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
    (hproj : WellTypedArrayElemProj body topFrame proj)
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
  have hproj' : WellTypedArrayElemProj body topFrame' proj :=
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
            cases his : localAlloc.allocation.initializationMask.isRangeInitialized
                (Miri.Memory.allocRange relOffset (translateTy arrDecl.ty body.layouts).layout.size) with
            | error _ => rfl
            | ok inner =>
              cases inner with
              | error _ => rfl
              | ok u => cases u; exact absurd his hnot_init
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
    | index idxLocal idxDecl hidx_decl hidx_ty hidx_imm =>
      have ⟨hdead_idx, hin_idx, hoob_idx⟩ :=
        evalProjection_index_simulation (m := m') hstate' rfl hnodup hwf hmp
          hidx_decl hidx_ty hidx_imm
      obtain ⟨slot_idx, mls_idx, _, _, hslot_idx, hmls_idx, _, hloc_idx⟩ :=
        hframe'.lookup_local hidx_decl
      cases hloc_idx with
      | dead _ _ =>
        left
        obtain ⟨hr_ub, _, msg, hpl_err⟩ := hdead_idx (Or.inl hslot_idx)
        have ha_ub : evalOperand s.frame.locals
            (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
            s.memory.globals body.layouts .nil = .ub := by
          cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
        have hm_err : annealEvalOperand body.localDecls body.layouts
            (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
            .error (.undefinedBehavior msg) m' := by
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
      | indirect _ mp_i _ _ _ _ =>
        exact absurd rfl (hidx_imm _ hmls_idx mp_i)
      | immediate _ imm_i _ _ himm_i =>
        rcases himm_i with ⟨rfl, _⟩ | ⟨v_i, rfl, himmRel_i⟩
        · left
          obtain ⟨hr_ub, _, msg, hpl_err⟩ := hdead_idx (Or.inr hslot_idx)
          have ha_ub : evalOperand s.frame.locals
              (arrayElemReadOperand isMove arrIdx (.index idxLocal)) .nil
              s.memory.globals body.layouts .nil = .ub := by
            cases isMove <;> simp [arrayElemReadOperand, evalOperand, hinit_elems, hr_ub]
          have hm_err : annealEvalOperand body.localDecls body.layouts
              (translateOperand (arrayElemReadOperand isMove arrIdx (.index idxLocal))) known m =
              .error (.undefinedBehavior msg) m' := by
            cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
        · obtain ⟨idxSc, _, rfl, _, _, _, _, _⟩ :=
            himmRel_i.of_primitive_scalar (by rw [hidx_ty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
          by_cases hlt_c : idxSc.bits < count
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
              cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
    (hproj : WellTypedArrayElemProj body topFrame proj)
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
  have hproj' : WellTypedArrayElemProj body topFrame' proj :=
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
            cases his : localAlloc.allocation.initializationMask.isRangeInitialized
                (Miri.Memory.allocRange relOffset (translateTy arrDecl.ty body.layouts).layout.size) with
            | error _ => rfl
            | ok inner =>
              cases inner with
              | error _ => rfl
              | ok u => cases u; exact absurd his hnot_init
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
    | index idxLocal idxDecl hidx_decl hidx_ty hidx_imm =>
      have ⟨hdead_idx, hin_idx, hoob_idx⟩ :=
        evalProjection_index_simulation (m := m') hstate' rfl hnodup hwf hmp
          hidx_decl hidx_ty hidx_imm
      obtain ⟨slot_idx, mls_idx, _, _, hslot_idx, hmls_idx, _, hloc_idx⟩ :=
        hframe'.lookup_local hidx_decl
      cases hloc_idx with
      | dead _ _ =>
        left
        obtain ⟨_, hw_ub, msg, hpl_err⟩ := hdead_idx (Or.inl hslot_idx)
        refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
        cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
            ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
        | ok _ => simp [hpl, Except.mapError] at hpl_err
        | error pe =>
          simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
          dsimp only [translatePlace]
          unfold annealEvalPlace
          simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
            EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw]
      | indirect _ mp_i _ _ _ _ =>
        exact absurd rfl (hidx_imm _ hmls_idx mp_i)
      | immediate _ imm_i _ _ himm_i =>
        rcases himm_i with ⟨rfl, _⟩ | ⟨v_i, rfl, himmRel_i⟩
        · left
          obtain ⟨_, hw_ub, msg, hpl_err⟩ := hdead_idx (Or.inr hslot_idx)
          refine ⟨Or.inr (Or.inr ⟨elems, hinit_elems, hw_ub⟩), m', msg, ?_⟩
          cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
              ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩ [.Index idxLocal] with
          | ok _ => simp [hpl, Except.mapError] at hpl_err
          | error pe =>
            simp only [hpl, Except.mapError, Except.error.injEq] at hpl_err
            dsimp only [translatePlace]
            unfold annealEvalPlace
            simp [translateProjectionElem, get, getThe, MonadStateOf.get, EStateM.get, bind,
              EStateM.bind, hnot_empty, hres_arr, hgop, hchk_ok, hpl, hpl_err, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw]
        · obtain ⟨idxSc, _, rfl, _, _, _, _, _⟩ :=
            himmRel_i.of_primitive_scalar (by rw [hidx_ty]; exact Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
          by_cases hlt_c : idxSc.bits < count
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
            cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
        cases hpl : annealProjectList (annealProjectionCx topFrame' body.layouts)
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
preserves `LiveAllocsNodup`, updates `MemPlaceRel` of `arrIdx` to
`elems.set idx (.scalar sc)` (preserving all `j ≠ idx` elements), and preserves
`FrameRel` across all other locals via `MemoryAllocDisjoint`. -/
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
        tf := by
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
    let mach' : AnnealMachine :=
      { mach with
        memory :=
          { mach.memory with
            live := mach.memory.live.set! allocIdx (allocId, ⟨kind, alloc'⟩) } }
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
    refine ⟨mach', hw_ok, hnodup', hmp', ?_⟩
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
      WellTypedArrayElemProj body topFrame proj →
      (get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) →
      WellTypedArrayElemAssign body s topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (arrayElemReadOperand isMove arrIdx proj)), span⟩
  /-- Element write: `_arr[proj] = .use srcOp`. -/
  | writeElem
      (arrIdx : Local) (arrDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat)
      (proj : ProjectionElem) (srcOp : MirAst.Operand) (span : String) :
      get? body.localDecls arrIdx = some arrDecl →
      WellTypedArrayTy body.layouts arrDecl.ty elemKind count →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      WellTypedArrayElemProj body topFrame proj →
      WellTypedScalarOperand body topFrame srcOp { kind := elemKind, layoutIdx := 0 } →
      (get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx)) ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) →
      WellTypedArrayElemAssign body s topFrame
        ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩

private theorem evalRvalue_use_scalar_eq
    {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {s : MachineState} {srcOp : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf srcOp ty)
    (hbor : s.memory.borrows = .nil)
    (hcaller : s.memory.callerLocals = .nil) :
    evalRvalue s.frame.locals (.use srcOp) s.memory body.localDecls body.layouts =
      match evalOperand s.frame.locals srcOp .nil s.memory.globals body.layouts .nil with
      | .ok val locals' => .ok val locals' s.memory
      | .ub => .ub
      | .unsupported => .unsupported := by
  cases hop with
  | constScalar c _ _ _ _ _ _ _ _ =>
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    cases evalOperand s.frame.locals (.constant c) .nil s.memory.globals body.layouts .nil <;> rfl
  | copyLocal idx _ _ _ _ =>
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    cases evalOperand s.frame.locals (.copy ⟨idx, .nil⟩) .nil s.memory.globals body.layouts .nil <;> rfl

/-- **`step_assign_array_element_simulation`** (`LM-2.1`):
Statement-level lockstep simulation for array element reads (`_dst = copy/move _arr[proj]`)
and array element writes (`_arr[proj] = srcOp`) across both `ProjectionElem.index` and
`ProjectionElem.constantIndex` (`fromEnd = false` and `fromEnd = true`), covering:
- dead/uninitialized array local UB,
- dead/uninitialized index local UB,
- out-of-bounds index / invalid `minLength` UB,
- dead/uninitialized source operand or dead destination local UB,
- in-bounds scalar element read, and
- in-bounds scalar element overwrite (`elems.set idx (.scalar sc)` vs byte-slice overwrite
  preserving all `j ≠ idx` elements and `MemoryAllocDisjoint`).

A normal `lean-miri` step also preserves `LiveAllocsNodup` (`StepPreservesNodup`)
and the immediacy of every local (`StepPreservesImmediate`). -/
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
    have hproj₀ : WellTypedArrayElemProj body topFrame₀ proj :=
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
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
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
      refine ⟨hext.1,
        stepPreservesNodup_of_write_local hnodup hframes hframe.body_eq hframe.location_eq hbb
          hstmt hframe₁.location_eq hlt_dst₁ (hmono_tot dstIdx hdst_imm) hm_write, ?_⟩
      intro hok tf tf' htf htf' j _ hj
      rw [hframes] at htf
      have htf_eq : tf = topFrame := by simpa using htf.symm
      subst htf_eq
      exact hext.2 j hj tf' htf' hok
  | writeElem arrIdx arrDecl elemKind count proj srcOp span
      hdecl_arr hwf hprim hproj hop harr_slot =>
    have huse_src := evalRvalue_use_scalar_eq hop hbor hcaller
    rcases annealEvalPlace_projected_array_simulation hstate_copy hframes hnodup
        hdecl_arr hwf hproj harr_slot with
      ⟨ha_dst_ub, m', msg, hevalPlace_err⟩ |
      ⟨elems, mp, idx, topFrame₀, hlt_idx, hinit_elems, hwrite_proj, hevalPlace_ok,
        hmls_arr₀, hmp, hframe₀, hdisj₀, hmono₀, htf₀_eq⟩
    · -- Destination array place or index is UB: both Anneal and Miri report UB.
      have hop_dich := evalOperands_scalar_dichotomy hframe
        (ops := [srcOp]) (fun o ho => by simp at ho; subst ho; exact hop) s.memory.globals
      have ha_ub : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        rw [huse_src]
        cases heval_src : evalOperand s.frame.locals srcOp .nil s.memory.globals body.layouts .nil with
        | ub => rfl
        | unsupported =>
          simp [evalOperands, heval_src] at hop_dich
        | ok val locals₁ =>
          have hloc₁ : locals₁ = s.frame.locals := hop.evalOperand_locals_eq heval_src
          subst hloc₁
          cases hproj <;>
            (dsimp only;
             rcases ha_dst_ub with hd | hu | ⟨es, hes, hw_ub⟩
             · simp [hd]
             · simp [hu]
             · simp [hes, hw_ub val])
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
      exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
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
      have hop₀ : WellTypedScalarOperand body topFrame₀ srcOp elemTy :=
        hop.mono_immediate hmono₀
      rcases evalScalarOperand_preserves_array_local hframe₀ hdisj₀ hdecl_arr hwf hprim hop₀
          s.memory.globals (some elemLay) with
        ⟨ha_src_ub, m', msg, hm_src_err⟩ |
        ⟨sc, msc, topFrame₁, ha_src_ok, hm_src_ok, harr_eq₁, hframe₁, hdisj₁, hmono₁,
          htf₁_eq, hrel_sc, hsz_sc, hbool_sc, hchar_sc⟩
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
        exact ⟨.ub _ _, StepPreservesNodup.of_error, StepPreservesImmediate.of_error⟩
      · have hmls_arr₁ : topFrame₁.locals[arrIdx]? =
            some ⟨.live (.indirect mp), some (translateTy arrDecl.ty body.layouts)⟩ := by
          rw [harr_eq₁]; exact hmls_arr₀
        obtain ⟨mach', hw_ok, hnodup', _, hframe'⟩ :=
          annealWriteImmediate_array_elem_set hframe₁ hdisj₁ hnodup hdecl_arr hwf hmls_arr₁
            hmp hlt_idx hrel_sc hsz_sc hbool_sc hchar_sc
        obtain ⟨_, _, hlt_af_arr, _, _, _, _, _⟩ := hframe.lookup_local hdecl_arr
        have hset_arr : set? s.frame.locals arrIdx
            (.init (.aggregate 0 (elems.set idx (.scalar sc)))) =
            some (s.frame.locals.set arrIdx (.init (.aggregate 0 (elems.set idx (.scalar sc))))) :=
          set?_eq_some_set hlt_af_arr _
        have ha_step : evalStmt s ⟨.assign ⟨arrIdx, [proj]⟩ (.use srcOp), span⟩
            body.localDecls body.layouts =
            MirStepNode.step (advanceStmt s
              (s.frame.locals.set arrIdx (.init (.aggregate 0 (elems.set idx (.scalar sc)))))
              s.memory) := by
          unfold evalStmt
          dsimp only
          rw [huse_src, ha_src_ok]
          cases hproj <;>
            (dsimp only;
             rw [hinit_elems];
             dsimp only;
             rw [hwrite_proj (.scalar sc)];
             dsimp only;
             rw [hset_arr, hprot, hbor];
             dsimp only [invalidateConflictingBorrowsAtProj];
             rw [hmem_same])
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
        refine ⟨StepRel.step _ _ ?_, StepPreservesNodup.of_nodup hnodup', ?himm⟩
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
1. Homogeneous array literal construction (`Rvalue.aggregate (.array elemTy) ops`),
2. Homogeneous array repeat construction (`Rvalue.repeat op count`),
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
      IsImmediateFrameLocal topFrame dstIdx →
      (∀ op ∈ ops, WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 }) →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      CanReserveAllocId m.machine.memory →
      WellTypedLM2_1ArrayStmt body s m topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
  | repeatArray
      (dstIdx : Local) (dstDecl : LocalDecl)
      (elemKind : RigidTy) (count : Nat)
      (op : MirAst.Operand) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      WellTypedArrayTy body.layouts dstDecl.ty elemKind count →
      IsImmediateFrameLocal topFrame dstIdx →
      WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 } →
      IsPrimScalarTy { kind := elemKind, layoutIdx := 0 } →
      CanReserveAllocId m.machine.memory →
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
`Index`/`ConstantIndex` element reads and writes) steps Anneal (`stepMirFn`) and
`lean-miri` (`Step.step`) in exact lockstep (`StepRel`). Normal steps preserve
`StateRel` (including `ArraySliceRel` and `MemoryAllocDisjoint`),
`LiveAllocsNodup` (`StepPreservesNodup`), and the immediacy of every local except
the destination of an array construction (`StepPreservesImmediate`), so the
theorem applies again to the next array statement; both machines report UB when
an array, index, operand, or destination local is dead or uninitialized or an
index is out of bounds. -/
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hstate_copy := hstate
  rcases hstate with ⟨topFrame, hframes, _, _, _, hcal, _, _, _, _, _⟩
  have htf_eq : ∀ tf, m.stack.frames = #[tf] → tf = topFrame := by
    intro tf h
    rw [hframes] at h
    simpa using h.symm
  cases hwt topFrame hframes with
  | aggregateArray dstIdx dstDecl elemTy elemKind count ops span
      hdecl_dst hwf hlen_ops hdst_imm hops hprim hcan_res =>
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨hrel', hnd', him'⟩ := evalRvalue_aggregate_array_simulation hstate_copy hnodup hbb
      hstmt hdecl_dst hwf hlen_ops
      (fun tf htf => htf_eq tf htf ▸ hdst_imm)
      (fun tf htf => htf_eq tf htf ▸ hops)
      hprim hcan_res
    refine ⟨hrel', hnd', him'.mono fun j hj => ?_⟩
    intro hjd
    apply hj
    show some dstIdx = some j
    rw [hjd]
  | repeatArray dstIdx dstDecl elemKind count op span
      hdecl_dst hwf hdst_imm hop hprim hcan_res =>
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨hrel', hnd', him'⟩ := evalRvalue_repeat_simulation hstate_copy hnodup hbb hstmt
      hdecl_dst hwf
      (fun tf htf => htf_eq tf htf ▸ hdst_imm)
      (fun tf htf => htf_eq tf htf ▸ hop)
      hprim hcan_res
    refine ⟨hrel', hnd', him'.mono fun j hj => ?_⟩
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
    obtain ⟨hrel', hnd', him'⟩ := evalRvalue_len_array_simulation hstate_copy hnodup hphase hbb
      hstmt hdecl_arr hwf hdecl_dst hdst_ty (fun tf htf => htf_eq tf htf ▸ hdst_imm) harr_slot'
    exact ⟨hrel', hnd', him'.mono fun _ _ => trivial⟩
  | elemAssign helem =>
    obtain ⟨hrel', hnd', him'⟩ := step_assign_array_element_simulation hstate_copy hnodup hphase
      hbb hstmt (fun tf htf => htf_eq tf htf ▸ helem)
    exact ⟨hrel', hnd', him'.mono fun _ _ => trivial⟩

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
`MemoryAllocDisjoint`) on normal steps and agreeing on UB when array/index/operand/dest
locals are dead or uninitialized or indices are out of bounds.

For array statements, `step_stmt_lm2_1_array_simulation` additionally shows that
a normal step preserves `LiveAllocsNodup`; the `LM-1.1` and `LM-1.4` theorems do
not expose their `lean-miri` post-states, so this theorem does not claim it. -/
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hstate_copy := hstate
  rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _, _⟩
  have htf_eq : ∀ tf, m.stack.frames = #[tf] → tf = topFrame := by
    intro tf h
    rw [hframes] at h
    simpa using h.symm
  cases hwt topFrame hframes with
  | arrayStmt harr =>
    exact (step_stmt_lm2_1_array_simulation hstate_copy hnodup hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ harr)).1
  | scalarStmt hsc =>
    exact step_assign_scalar_simulation hstate_copy hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hsc)
  | lm14Stmt hlm14 =>
    exact step_stmt_lm1_4_simulation hstate_copy hphase hbb hstmt
      (fun tf htf => htf_eq tf htf ▸ hlm14)

end LeanMiriSpec.Correspondence
