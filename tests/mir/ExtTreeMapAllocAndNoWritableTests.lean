/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal
import Anneal.ExtTreeMapAllocAndNoWritable
import Lean.Elab.Command

/-!
# Closed Canaries, Axiom Pins, and Meta-Level Audit for `Anneal.ExtTreeMapAllocAndNoWritable`

Kernel-checked, closed test witnesses (`canary_*`, zero undischarged hypotheses),
`#guard_msgs in #print axioms` pins, and a meta-level `run_cmd` audit with rolled-back
self-tests covering Parts 1, 2A, 2B, 3A, 3B, and 3C of
`Anneal.ExtTreeMapAllocAndNoWritable`.
-/

namespace Anneal.ExtTreeMapAllocAndNoWritableTests

open Anneal.ExtTreeMapAllocAndNoWritable
open Anneal.Memory
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout

/-! ## Shared Closed Test Fixtures -/

private def id1 : MiriAllocId := ⟨1, by decide⟩
private def id2 : MiriAllocId := ⟨2, by decide⟩
private def id3 : MiriAllocId := ⟨3, by decide⟩
private def id10 : MiriAllocId := ⟨10, by decide⟩
private def idMaxM1 : MiriAllocId := ⟨UInt64.ofNat (2^64 - 2), by decide⟩
private def idMax : MiriAllocId := ⟨UInt64.ofNat (2^64 - 1), by decide⟩

private def entryU32 : LiveAllocEntry :=
  ⟨4, 2, .stack, .mut, [.init 1 none, .init 0 none, .init 0 none, .init 0 none]⟩

private def entryU64 : LiveAllocEntry :=
  ⟨8, 3, .heap, .mut, encodeLeUInt64Bytes 42⟩

private def entryZst : LiveAllocEntry :=
  ⟨0, 0, .stack, .mut, []⟩

private def lwPermAsc : LinearAllocWorld :=
  (LinearAllocWorld.empty.insertLive id1 entryU32).insertLive id2 entryU64

private def lwPermDesc : LinearAllocWorld :=
  (LinearAllocWorld.empty.insertLive id2 entryU64).insertLive id1 entryU32

private def kwPermAsc : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive id1 entryU32).insertLive id2 entryU64

private def kwPermDesc : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive id2 entryU64).insertLive id1 entryU32

private def sampleMapOps : List (ExtTreeMap0.MapTraceOp MiriAllocId Nat) :=
  [ .insert id2 20,
    .insert idMax 99,
    .insert id1 10,
    .insert idMaxM1 98,
    .insert id2 25,
    .erase id1,
    .insert id3 30 ]

private def multiLevelBorrowWorld : FnEntryBorrowWorld where
  nodes := [
    { tag := 0, parentTag := none, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none },
    { tag := 1, parentTag := some 0, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none },
    { tag := 2, parentTag := some 1, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none },
    { tag := 3, parentTag := some 1, perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none }
  ]
  activeProtectors := []
  nextTag := 10
  nextProtector := 100
  pointeeInitialized := true

private theorem multiLevelBorrowWorld_wf : BorrowTreeTagsWF multiLevelBorrowWorld := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · intro n hn
    simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  · intro n hn
    simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  · intro n hn
    simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide

private theorem multiLevelBorrowWorld_ancWritable :
    AncestorsWritableIn multiLevelBorrowWorld 2 0 4 := by
  intro n hn hanc
  simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exfalso
    have hfalse : (ancestorPathTags multiLevelBorrowWorld.nodes 2).contains 3 = false := rfl
    rw [hfalse] at hanc; cases hanc

/-! ## Section 1: Part 1 Closed Canaries (`lean-miri#73`) -/

theorem canary_part1_miriAllocId_fullWidth :
    MiriAllocId.ofUInt64 0 = none ∧
    MiriAllocId.ofUInt64 (UInt64.ofNat (2^64 - 2)) = some idMaxM1 ∧
    MiriAllocId.ofUInt64 (UInt64.ofNat (2^64 - 1)) = some idMax ∧
    0 < idMax.toTrustedAllocId ∧
    idMaxM1.toTrustedAllocId ≠ idMax.toTrustedAllocId ∧
    Function.Injective MiriAllocId.value := by
  have hzero := MiriAllocId.ofUInt64_zero
  have hsome1 : MiriAllocId.ofUInt64 (UInt64.ofNat (2^64 - 2)) = some idMaxM1 :=
    MiriAllocId.ofUInt64_eq_some_iff.2 rfl
  have hsome2 : MiriAllocId.ofUInt64 (UInt64.ofNat (2^64 - 1)) = some idMax :=
    MiriAllocId.ofUInt64_eq_some_iff.2 rfl
  have hpos := MiriAllocId.toTrustedAllocId_pos idMax
  have hne : idMaxM1.toTrustedAllocId ≠ idMax.toTrustedAllocId := fun heq => by
    have hEq := MiriAllocId.toTrustedAllocId_injective heq
    have hv : idMaxM1.value = idMax.value := congrArg MiriAllocId.value hEq
    exact (by decide : idMaxM1.value ≠ idMax.value) hv
  have hext : Function.Injective MiriAllocId.value := fun _ _ h => MiriAllocId.ext h
  exact ⟨hzero, hsome1, hsome2, hpos, hne, hext⟩

theorem canary_part1_rawAATree_and_extTreeMap0_laws :
    let mAsc : ExtTreeMap0 MiriAllocId Nat compare :=
      ((ExtTreeMap0.empty.insert id1 10).insert id2 20).insert idMax 99
    let mDesc : ExtTreeMap0 MiriAllocId Nat compare :=
      ((ExtTreeMap0.empty.insert idMax 99).insert id2 20).insert id1 10
    (ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare) = ∅ ∧
    (ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).size = 0 ∧
    mAsc = mDesc ∧
    mAsc.toList = mDesc.toList ∧
    mAsc.size = 3 ∧
    mAsc[id2]? = some 20 ∧
    mAsc.contains idMax = true ∧
    ((mAsc.insert id2 200).insert id2 20) = mAsc ∧
    ((mAsc.insert id3 30).erase id3) = mAsc ∧
    (mAsc.erase id1).get? id1 = none ∧
    (mAsc.erase id1).get? id2 = some 20 ∧
    ((mAsc.toList.find? (fun p => compare id2 p.1 == .eq)).map Prod.snd = some 20) ∧
    ExtTreeMap0.AgreesWithStdRaw
      (ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare)
      (Std.TreeMap.Raw.empty : Std.TreeMap.Raw MiriAllocId Nat compare) ∧
    (ExtTreeMap0.execMapTraceExt0 (cmp := compare) sampleMapOps).get? id2 =
      (ExtTreeMap0.execMapTraceStdRaw (cmp := compare) sampleMapOps).get? id2 ∧
    (ExtTreeMap0.execMapTraceExt0 (cmp := compare) sampleMapOps).get? id1 =
      (ExtTreeMap0.execMapTraceStdRaw (cmp := compare) sampleMapOps).get? id1 ∧
    (ExtTreeMap0.execMapTraceExt0 (cmp := compare) (sampleMapOps ++ [.insert id10 77])).get? id10 = some 77 := by
  dsimp only
  have hmEq : (((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99 =
      (((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert idMax 99).insert id2 20).insert id1 10 := by
    apply ExtTreeMap0.ext_getElem?
    intro k
    rw [ExtTreeMap0.getElem?_eq_get?, ExtTreeMap0.getElem?_eq_get?]
    rw [ExtTreeMap0.get?_insert, ExtTreeMap0.get?_insert, ExtTreeMap0.get?_insert,
        ExtTreeMap0.get?_insert, ExtTreeMap0.get?_insert, ExtTreeMap0.get?_insert,
        ExtTreeMap0.get?_empty]
    by_cases h1 : k = id1
    · subst h1; rfl
    · by_cases h2 : k = id2
      · subst h2; rfl
      · by_cases hm : k = idMax
        · subst hm; rfl
        · have hc1 : (compare k id1 == .eq) = false := beq_false_of_ne (fun hc => h1 (Std.LawfulEqCmp.eq_of_compare hc))
          have hc2 : (compare k id2 == .eq) = false := beq_false_of_ne (fun hc => h2 (Std.LawfulEqCmp.eq_of_compare hc))
          have hcm : (compare k idMax == .eq) = false := beq_false_of_ne (fun hc => hm (Std.LawfulEqCmp.eq_of_compare hc))
          simp [hc1, hc2, hcm]
  have htoList : ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).toList =
      ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert idMax 99).insert id2 20).insert id1 10).toList := by
    rw [hmEq]
  have htoListInj : ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99) =
      ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert idMax 99).insert id2 20).insert id1 10) :=
    ExtTreeMap0.toList_inj htoList
  have hsz : ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).size = 3 := by
    rw [ExtTreeMap0.size_eq_length_toList]
    rw [ExtTreeMap0.toList_insert, ExtTreeMap0.toList_insert, ExtTreeMap0.toList_insert]
    rfl
  have hget2 : ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99)[id2]? = some 20 := by
    rw [ExtTreeMap0.getElem?_eq_get?, ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self]
  have hcont : ((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).contains idMax = true := by
    rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]; rfl
  have hinsSame : (((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).insert id2 200).insert id2 20 =
      (((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99 := by
    rw [ExtTreeMap0.insert_insert_same]
    apply ExtTreeMap0.ext_get?
    intro k
    rw [ExtTreeMap0.get?_insert]
    by_cases h2 : k = id2
    · subst h2
      have hself : compare id2 id2 = .eq := Std.ReflCmp.compare_self
      rw [hself, ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self]; rfl
    · have hc2 : (compare k id2 == .eq) = false := beq_false_of_ne (fun hc => h2 (Std.LawfulEqCmp.eq_of_compare hc))
      simp [hc2]
  have heraseIns : (((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).insert id3 30).erase id3 =
      (((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99 := by
    apply ExtTreeMap0.erase_insert_self_of_none
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_ne _ _ (by decide),
        ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_empty]
  have herSelf : (((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).erase id1).get? id1 = none :=
    ExtTreeMap0.get?_erase_self _ _
  have herNe : (((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).erase id1).get? id2 = some 20 := by
    rw [ExtTreeMap0.get?_erase_ne _ (by decide), ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self]
  have hlinFind : (((((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat compare).insert id1 10).insert id2 20).insert idMax 99).toList.find?
      (fun p => compare id2 p.1 == .eq)).map Prod.snd = some 20 := by
    rw [ExtTreeMap0.linearFind?_toList, ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self]
  have hsnoc : (ExtTreeMap0.execMapTraceExt0 (cmp := compare) (sampleMapOps ++ [.insert id10 77])).get? id10 = some 77 := by
    rw [ExtTreeMap0.execMapTraceExt0_snoc_insert]
    have hself : compare id10 id10 = .eq := Std.ReflCmp.compare_self
    simp only [hself, beq_self_eq_true, ↓reduceIte]
  refine ⟨ExtTreeMap0.empty_eq_emptyc, ExtTreeMap0.size_empty, htoListInj, htoList, hsz, hget2,
    hcont, hinsSame, heraseIns, herSelf, herNe, hlinFind, ExtTreeMap0.agreesWithStdRaw_empty,
    rfl, rfl, hsnoc⟩

theorem canary_part1_permutation_burden_vs_keyed_ext :
    lwPermAsc ≠ lwPermDesc ∧
    kwPermAsc = kwPermDesc ∧
    KeyedAllocWorld.ofLinear lwPermAsc = kwPermAsc ∧
    KeyedAllocWorld.ofLinear lwPermDesc = kwPermAsc := by
  have hlinNe : lwPermAsc ≠ lwPermDesc := by
    intro h
    have hlive : lwPermAsc.live = lwPermDesc.live := congrArg LinearAllocWorld.live h
    have hhead : lwPermAsc.live.head? = lwPermDesc.live.head? := congrArg List.head? hlive
    simp [lwPermAsc, lwPermDesc, LinearAllocWorld.insertLive, LinearAllocWorld.empty, id1, id2] at hhead
  have hkwEq : kwPermAsc = kwPermDesc := by
    refine KeyedAllocWorld.ext rfl rfl (fun _ => rfl) (fun _ => rfl) ?_ (fun _ => rfl) (fun _ => rfl)
    intro k
    simp only [kwPermAsc, kwPermDesc, KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty]
    by_cases h1 : k = id1
    · subst h1
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self, ExtTreeMap0.get?_insert_self]
    · by_cases h2 : k = id2
      · subst h2
        rw [ExtTreeMap0.get?_insert_self, ExtTreeMap0.get?_insert_ne _ _ (by decide), ExtTreeMap0.get?_insert_self]
      · rw [ExtTreeMap0.get?_insert_ne _ _ h2, ExtTreeMap0.get?_insert_ne _ _ h1,
            ExtTreeMap0.get?_insert_ne _ _ h1, ExtTreeMap0.get?_insert_ne _ _ h2]
  have hrelAsc : AllocWorldRel lwPermAsc kwPermAsc :=
    allocWorldRel_insertLive (allocWorldRel_insertLive allocWorldRel_empty id1 entryU32) id2 entryU64
  have hrelDesc : AllocWorldRel lwPermDesc kwPermDesc :=
    allocWorldRel_insertLive (allocWorldRel_insertLive allocWorldRel_empty id2 entryU64) id1 entryU32
  have hofAsc : KeyedAllocWorld.ofLinear lwPermAsc = kwPermAsc :=
    ((allocWorldRel_iff_eq_ofLinear lwPermAsc kwPermAsc).1 hrelAsc).symm
  have hofDesc : KeyedAllocWorld.ofLinear lwPermDesc = kwPermAsc :=
    (((allocWorldRel_iff_eq_ofLinear lwPermDesc kwPermDesc).1 hrelDesc).symm).trans hkwEq.symm
  exact ⟨hlinNe, hkwEq, hofAsc, hofDesc⟩

theorem canary_part1_allocWorldRel_totality_and_simulation :
    let lw0 := LinearAllocWorld.empty
    let kw0 := KeyedAllocWorld.empty
    let lw1 := (lw0.registerGlobal id10 ⟨.static, 4, 2, .not, []⟩).insertLive id1 entryU32
    let kw1 := (kw0.registerGlobal id10 ⟨.static, 4, 2, .not, []⟩).insertLive id1 entryU32
    let clk : RaceClockEntry := ⟨1, 2, 0, 0, []⟩
    let lw2 := (lw1.setRace id1 clk).updateLiveBytes id1 [.init 9 none]
    let kw2 := (kw1.setRace id1 clk).updateLiveBytes id1 [.init 9 none]
    let lw3 := ((lw2.removeRace id1).removeLive id1).1.insertDead id1 ⟨4, 2⟩
    let kw3 := ((kw2.removeRace id1).removeLive id1).1.insertDead id1 ⟨4, 2⟩
    lw1.containsId id1 = kw1.containsId id1 ∧
    lw1.isAllocLive id1 = kw1.isAllocLive id1 ∧
    lw1.getAllocInfo id10 = kw1.getAllocInfo id10 ∧
    lw1.getLiveAllocSizeAndAlign id1 = kw1.getLiveAllocSizeAndAlign id1 ∧
    AllocWorldRel lw3 kw3 ∧
    (kw0.reserveAllocId).2 = (lw0.reserveAllocId).2 ∧
    (kw0.allocate entryU32).2 = (lw0.allocate entryU32).2 ∧
    (kw0.allocateMachine entryU32 (.configured true) 1 5).2 =
      (lw0.allocateMachine entryU32 (.configured true) 1 5).2 ∧
    (kw1.deallocate (.provenanced id1 0) (some (4, 2)) .stack .ok).outcome =
      (lw1.deallocate (.provenanced id1 0) (some (4, 2)) .stack .ok).outcome ∧
    (kw2.deallocateMachine (.provenanced id1 0) (some (4, 2)) .stack (.configured true) ⟨1, 5, []⟩ .ok).outcome =
      (lw2.deallocateMachine (.provenanced id1 0) (some (4, 2)) .stack (.configured true) ⟨1, 5, []⟩ .ok).outcome ∧
    KeyedAllocWorld.ofLinear (LinearAllocWorld.ofKeyed kw3) = kw3 ∧
    AllocWorldRel lw3 (KeyedAllocWorld.ofLinear lw3) := by
  dsimp only
  have hrel0 : AllocWorldRel LinearAllocWorld.empty KeyedAllocWorld.empty := allocWorldRel_empty
  have hrelG := allocWorldRel_registerGlobal hrel0 id10 ⟨.static, 4, 2, .not, []⟩
  have hrel1 := allocWorldRel_insertLive hrelG id1 entryU32
  have hrelR := allocWorldRel_setRace hrel1 id1 ⟨1, 2, 0, 0, []⟩
  have hrel2 := allocWorldRel_updateLiveBytes hrelR id1 [.init 9 none]
  have hrelRR := allocWorldRel_removeRace hrel2 id1
  have hrelRL := (allocWorldRel_removeLive hrelRR id1).1
  have hrel3 := allocWorldRel_insertDead hrelRL id1 ⟨4, 2⟩
  have hres := (allocWorldRel_reserveAllocId hrel0).2
  have halloc := (allocWorldRel_allocate hrel0 entryU32).2
  have hallocM := (allocWorldRel_allocateMachine hrel0 entryU32 (.configured true) 1 5).2
  have hdealloc := (allocWorldRel_deallocate hrel1 (.provenanced id1 0) (some (4, 2)) .stack .ok).2.2
  have hdeallocM := (allocWorldRel_deallocateMachine hrel2 (.provenanced id1 0) (some (4, 2)) .stack (.configured true) ⟨1, 5, []⟩ .ok).2.2
  have hroundTrip : KeyedAllocWorld.ofLinear (LinearAllocWorld.ofKeyed (((((KeyedAllocWorld.empty.registerGlobal id10 ⟨.static, 4, 2, .not, []⟩).insertLive id1 entryU32).setRace id1 ⟨1, 2, 0, 0, []⟩).updateLiveBytes id1 [.init 9 none]).removeRace id1 |>.removeLive id1 |>.1 |>.insertDead id1 ⟨4, 2⟩)) =
      (((((KeyedAllocWorld.empty.registerGlobal id10 ⟨.static, 4, 2, .not, []⟩).insertLive id1 entryU32).setRace id1 ⟨1, 2, 0, 0, []⟩).updateLiveBytes id1 [.init 9 none]).removeRace id1 |>.removeLive id1 |>.1 |>.insertDead id1 ⟨4, 2⟩) := by
    have hofK := allocWorldRel_ofKeyed (((((KeyedAllocWorld.empty.registerGlobal id10 ⟨.static, 4, 2, .not, []⟩).insertLive id1 entryU32).setRace id1 ⟨1, 2, 0, 0, []⟩).updateLiveBytes id1 [.init 9 none]).removeRace id1 |>.removeLive id1 |>.1 |>.insertDead id1 ⟨4, 2⟩)
    exact (allocWorldRel_keyed_unique hofK (allocWorldRel_ofLinear _)).symm
  exact ⟨allocWorldRel_containsId hrel1 id1,
    allocWorldRel_isAllocLive hrel1 id1,
    allocWorldRel_getAllocInfo hrel1 id10,
    allocWorldRel_getLiveAllocSizeAndAlign hrel1 id1,
    hrel3,
    hres.symm, halloc.symm, hallocM.symm, hdealloc.symm, hdeallocM.symm,
    hroundTrip, allocWorldRel_ofLinear _⟩

theorem canary_part1_findAllocBytes?_precedence_and_allocWorldRel :
    let staticBytes : List MemByte := [.init 0x2A none]
    let liveBytes : List MemByte := [.init 0x7F none]
    let lw := ((LinearAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, staticBytes⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, liveBytes⟩
    let kw := ((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, staticBytes⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, liveBytes⟩
    kw.findAllocBytes? id3 = some liveBytes ∧
    kw.findAllocBytes? id1 = some staticBytes ∧
    kw.findAllocBytes? id2 = none ∧
    lw.findAllocBytes? id1 = kw.findAllocBytes? id1 ∧
    lw.findAllocBytes? id3 = kw.findAllocBytes? id3 := by
  dsimp only
  have hrel : AllocWorldRel
      (((LinearAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
        |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
        |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩)
      (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
        |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
        |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩) :=
    allocWorldRel_insertLive
      (allocWorldRel_registerGlobal
        (allocWorldRel_registerGlobal allocWorldRel_empty id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
        id2 ⟨.function, 0, 0, .not, []⟩)
      id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩
  have hlive3 : (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩).findLive? id3 =
      some ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩ := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]
  have hnl1 : (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩).findLive? id1 = none := by
    simp only [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id3), ExtTreeMap0.get?_empty]
  have hg1 : (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩).findGlobal? id1 =
      some ⟨.static, 1, 0, .not, [.init 0x2A none]⟩ := by
    simp only [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id2), ExtTreeMap0.get?_insert_self]
  have hnl2 : (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩).findLive? id2 = none := by
    simp only [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id3), ExtTreeMap0.get?_empty]
  have hg2 : (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 1, 0, .not, [.init 0x2A none]⟩)
      |>.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩)
      |>.insertLive id3 ⟨1, 0, .stack, .mut, [.init 0x7F none]⟩).findGlobal? id2 =
      some ⟨.function, 0, 0, .not, []⟩ := by
    simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal,
      ExtTreeMap0.get?_insert_self]
  have hp3 := (keyedFindAllocBytes?_precedence _ id3).1 _ hlive3
  have hp1 := ((keyedFindAllocBytes?_precedence _ id1).2 hnl1 _ hg1).1 (Or.inl rfl)
  have hp2 := ((keyedFindAllocBytes?_precedence _ id2).2 hnl2 _ hg2).2 (Or.inl rfl)
  exact ⟨hp3, hp1, hp2, allocWorldRel_findAllocBytes? hrel id1, allocWorldRel_findAllocBytes? hrel id3⟩

theorem canary_part1_highWater_and_wrapAround_exhaustion :
    let wHi : KeyedAllocWorld := { KeyedAllocWorld.empty with nextAllocId := MiriAllocId.maxValue.value }
    let wCol : KeyedAllocWorld := KeyedAllocWorld.empty.insertLive id1 entryU32
    (wHi.reserveAllocId).2 = .ok MiriAllocId.maxValue ∧
    (wHi.reserveAllocId).1.nextAllocId = 0 ∧
    (wHi.reserveAllocId).1.idSupplyExhausted = false ∧
    ((wHi.reserveAllocId).1.reserveAllocId).2 = .error .exhausted ∧
    ((wHi.reserveAllocId).1.reserveAllocId).1.nextAllocId = 1 ∧
    ((wHi.reserveAllocId).1.reserveAllocId).1.idSupplyExhausted = true ∧
    (((wHi.reserveAllocId).1.reserveAllocId).1.reserveAllocId).2 = .error .exhausted ∧
    (wCol.reserveAllocId).2 = .error (.alreadyIssued id1) ∧
    (wCol.reserveAllocId).1.nextAllocId = 2 ∧
    (wCol.reserveAllocId).1.findLive? id1 = some entryU32 ∧
    ((wCol.reserveAllocId).1.reserveAllocId).2 = .ok id2 := by
  dsimp only
  have hfresh : ({ KeyedAllocWorld.empty with nextAllocId := MiriAllocId.maxValue.value } : KeyedAllocWorld).hasIssued MiriAllocId.maxValue = false := by
    simp [KeyedAllocWorld.hasIssued, KeyedAllocWorld.empty, ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty]
  have hnotIn : ({ KeyedAllocWorld.empty with nextAllocId := MiriAllocId.maxValue.value } : KeyedAllocWorld).containsId MiriAllocId.maxValue = false := by
    simp [KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
      KeyedAllocWorld.findGlobal?, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have h1 := keyedReserveAllocId_of_highWater { KeyedAllocWorld.empty with nextAllocId := MiriAllocId.maxValue.value }
    MiriAllocId.maxValue rfl (MiriAllocId.ofUInt64_eq_some_iff.2 rfl) hfresh hnotIn
  have h2 := keyedReserveAllocId_wrapAround_latches_exhausted { KeyedAllocWorld.empty with nextAllocId := MiriAllocId.maxValue.value }
    rfl rfl hfresh hnotIn
  have hcolLive : (KeyedAllocWorld.empty.insertLive id1 entryU32).findLive? id1 = some entryU32 := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]
  have hcol := keyedReserveAllocId_alreadyIssued_advances_cursor (KeyedAllocWorld.empty.insertLive id1 entryU32)
    id1 rfl (MiriAllocId.ofUInt64_eq_some_iff.2 rfl)
    (by simp [KeyedAllocWorld.containsId, hcolLive])
  have hretry : (({ KeyedAllocWorld.empty.insertLive id1 entryU32 with
      nextAllocId := (KeyedAllocWorld.empty.insertLive id1 entryU32).nextAllocId + 1 } : KeyedAllocWorld).reserveAllocId).2 =
      .ok id2 := by
    have hfresh2 : ({ KeyedAllocWorld.empty.insertLive id1 entryU32 with
        nextAllocId := (KeyedAllocWorld.empty.insertLive id1 entryU32).nextAllocId + 1 } : KeyedAllocWorld).hasIssued id2 = false := by
      simp [KeyedAllocWorld.hasIssued, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty,
        ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty]
    have hnotIn2 : ({ KeyedAllocWorld.empty.insertLive id1 entryU32 with
        nextAllocId := (KeyedAllocWorld.empty.insertLive id1 entryU32).nextAllocId + 1 } : KeyedAllocWorld).containsId id2 = false := by
      simp only [KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
        KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id1), ExtTreeMap0.get?_empty,
        ExtTreeMap0.get?_empty, ExtTreeMap0.get?_empty]
      rfl
    exact (keyedReserveAllocId_of_highWater _ id2 rfl (MiriAllocId.ofUInt64_eq_some_iff.2 rfl) hfresh2 hnotIn2).1
  refine ⟨h1.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hcol]
  · rw [hcol]; rfl
  · rw [hcol]; exact hcolLive
  · rw [hcol]; exact hretry

theorem canary_part1_registerReservedGlobal_validation :
    let g : GlobalAllocEntry := ⟨.vtable, 24, 3, .not, []⟩
    let w1 : KeyedAllocWorld :=
      { KeyedAllocWorld.empty with
        nextAllocId := KeyedAllocWorld.empty.nextAllocId + 1
        issued := KeyedAllocWorld.empty.issued.insert id1 () }
    KeyedAllocWorld.empty.reserveAllocId = (w1, .ok id1) ∧
    (KeyedAllocWorld.empty.registerReservedGlobal id1 g).2 = .error (.globalIdAlreadyPresent id1) ∧
    w1.registerReservedGlobal id1 g = (w1.registerGlobal id1 g, .ok ()) ∧
    ((w1.registerGlobal id1 g).registerReservedGlobal id1 g).2 = .error (.duplicateRuntimeId id1) ∧
    ((w1.insertLive id1 entryU32).registerReservedGlobal id1 g).2 = .error (.globalIdAlreadyPresent id1) ∧
    ((w1.insertDead id1 ⟨4, 2⟩).registerReservedGlobal id1 g).2 = .error (.globalIdAlreadyPresent id1) ∧
    (LinearAllocWorld.empty.registerReservedGlobal id1 g).2 =
      (KeyedAllocWorld.empty.registerReservedGlobal id1 g).2 := by
  dsimp only
  have hres0 : KeyedAllocWorld.empty.reserveAllocId = ((KeyedAllocWorld.empty.reserveAllocId).1, .ok id1) := by
    simp [KeyedAllocWorld.reserveAllocId, KeyedAllocWorld.empty, KeyedAllocWorld.hasIssued,
      KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
      KeyedAllocWorld.findGlobal?, ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty,
      MiriAllocId.ofUInt64, id1]
  have hw1 := (keyedReserveAllocId_ok_inv hres0).2.2.2.2
  have hres : KeyedAllocWorld.empty.reserveAllocId =
      ({ KeyedAllocWorld.empty with
          nextAllocId := KeyedAllocWorld.empty.nextAllocId + 1
          issued := KeyedAllocWorld.empty.issued.insert id1 () }, .ok id1) := by
    rw [← hw1]; exact hres0
  have hgNone : (KeyedAllocWorld.empty.findGlobal? id1).isSome = false := by
    simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have hunissued : KeyedAllocWorld.empty.hasIssued id1 = false := by
    simp [KeyedAllocWorld.hasIssued, KeyedAllocWorld.empty, ExtTreeMap0.contains_eq_isSome_get?,
      ExtTreeMap0.get?_empty]
  have hrej0 := (keyedRegisterReservedGlobal_rejections KeyedAllocWorld.empty id1 ⟨.vtable, 24, 3, .not, []⟩).2
    hgNone (Or.inr (Or.inr hunissued))
  have hok := keyedRegisterReservedGlobal_after_reserve ⟨.vtable, 24, 3, .not, []⟩ hres
  have hdup := (keyedRegisterReservedGlobal_rejections
    (({ KeyedAllocWorld.empty with
        nextAllocId := KeyedAllocWorld.empty.nextAllocId + 1
        issued := KeyedAllocWorld.empty.issued.insert id1 () } : KeyedAllocWorld).registerGlobal id1
      ⟨.vtable, 24, 3, .not, []⟩) id1 ⟨.vtable, 24, 3, .not, []⟩).1
    (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.registerGlobal, ExtTreeMap0.get?_insert_self])
  have hlive := (keyedRegisterReservedGlobal_rejections
    (({ KeyedAllocWorld.empty with
        nextAllocId := KeyedAllocWorld.empty.nextAllocId + 1
        issued := KeyedAllocWorld.empty.issued.insert id1 () } : KeyedAllocWorld).insertLive id1 entryU32)
    id1 ⟨.vtable, 24, 3, .not, []⟩).2
    (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty,
      ExtTreeMap0.get?_empty])
    (Or.inl (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]))
  have hdead := (keyedRegisterReservedGlobal_rejections
    (({ KeyedAllocWorld.empty with
        nextAllocId := KeyedAllocWorld.empty.nextAllocId + 1
        issued := KeyedAllocWorld.empty.issued.insert id1 () } : KeyedAllocWorld).insertDead id1 ⟨4, 2⟩)
    id1 ⟨.vtable, 24, 3, .not, []⟩).2
    (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.empty,
      ExtTreeMap0.get?_empty])
    (Or.inr (Or.inl (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead,
      ExtTreeMap0.get?_insert_self])))
  have hlin := (allocWorldRel_registerReservedGlobal allocWorldRel_empty id1 ⟨.vtable, 24, 3, .not, []⟩).2
  exact ⟨hres, congrArg Prod.snd hrej0, hok, congrArg Prod.snd hdup, congrArg Prod.snd hlive,
    congrArg Prod.snd hdead, hlin⟩

theorem canary_part1_deallocate_failure_ordering_and_state_retention :
    let wLive := KeyedAllocWorld.empty.insertLive id1 entryU32
    let wDead := KeyedAllocWorld.empty.insertDead id1 ⟨4, 2⟩
    let wGlob := KeyedAllocWorld.empty.registerGlobal id2 ⟨.vtable, 24, 3, .not, []⟩
    let wDup := (KeyedAllocWorld.empty.insertLive id1 entryU32).insertDead id1 ⟨99, 0⟩
    (wLive.deallocate (.provenanced id1 1) (some (4, 2)) .stack .ok).outcome = .error (.nonzeroOffset id1 1) ∧
    (wLive.deallocate (.provenanced id1 1) (some (4, 2)) .stack .ok).world.findLive? id1 = some entryU32 ∧
    (KeyedAllocWorld.empty.deallocate (.provenanced id1 0) (some (4, 2)) .stack .ok).outcome = .error (.useAfterFree id1) ∧
    (wDead.deallocate (.provenanced id1 0) (some (999, 7)) .heap .ok).outcome = .error (.useAfterFree id1) ∧
    (wGlob.deallocate (.provenanced id2 0) (some (24, 3)) .stack .ok).outcome = .error (.globalErr id2 .vtable) ∧
    (wLive.deallocate (.provenanced id1 0) (some (4, 2)) .heap .ok).outcome = .error (.memoryKindMismatch id1) ∧
    (wLive.deallocate (.provenanced id1 0) (some (4, 2)) .heap .ok).world.findLive? id1 = none ∧
    (wLive.deallocate (.provenanced id1 0) (some (4, 2)) .heap .ok).detached = some (id1, entryU32) ∧
    (wDup.deallocate (.provenanced id1 0) none .stack .ok).outcome = .error (.duplicateDeadAllocation id1) ∧
    (wDup.deallocate (.provenanced id1 0) none .stack .ok).world.findDead? id1 = some ⟨4, 2⟩ ∧
    (wLive.deallocate (.provenanced id1 0) none .stack .protectedDealloc).outcome =
      .error (.hookFailure "TreeBorrowsProtectedDealloc") ∧
    (wLive.deallocate (.provenanced id1 0) none .stack .protectedDealloc).detached = some (id1, entryU32) ∧
    (wLive.deallocate (.provenanced id1 0) none .stack .protectedDealloc).world.findLive? id1 = none ∧
    (wLive.deallocate (.provenanced id1 0) none .stack .protectedDealloc).world.findDead? id1 = none := by
  dsimp only
  have h1 := keyedDeallocate_nonzeroOffset_preserves_live (KeyedAllocWorld.empty.insertLive id1 entryU32)
    id1 1 (by decide) (some (4, 2)) .stack .ok
  have h1Out : ((KeyedAllocWorld.empty.insertLive id1 entryU32).deallocate (.provenanced id1 1) (some (4, 2)) .stack .ok).outcome = .error (.nonzeroOffset id1 1) := by
    rw [h1]
  have h1Live : ((KeyedAllocWorld.empty.insertLive id1 entryU32).deallocate (.provenanced id1 1) (some (4, 2)) .stack .ok).world.findLive? id1 = some entryU32 := by
    rw [h1]; simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.findLive?, ExtTreeMap0.get?_insert_self]
  have h2 : (KeyedAllocWorld.empty.deallocate (.provenanced id1 0) (some (4, 2)) .stack .ok).outcome = .error (.useAfterFree id1) := by
    rw [keyedDeallocate_absent_reports_useAfterFree KeyedAllocWorld.empty id1
      (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
      (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
      (some (4, 2)) .stack .ok]
  have h3 : ((KeyedAllocWorld.empty.insertDead id1 ⟨4, 2⟩).deallocate (.provenanced id1 0) (some (999, 7)) .heap .ok).outcome = .error (.useAfterFree id1) := by
    rw [keyedDeallocate_doubleFree_precedes_layout_and_kind (KeyedAllocWorld.empty.insertDead id1 ⟨4, 2⟩) id1 ⟨4, 2⟩
      (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
      (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
      (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead, ExtTreeMap0.get?_insert_self])
      (some (999, 7)) .heap .ok]
  have h4 : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.vtable, 24, 3, .not, []⟩).deallocate (.provenanced id2 0) (some (24, 3)) .stack .ok).outcome = .error (.globalErr id2 .vtable) := by
    rw [keyedDeallocate_global_reports_globalErr (KeyedAllocWorld.empty.registerGlobal id2 ⟨.vtable, 24, 3, .not, []⟩)
      id2 ⟨.vtable, 24, 3, .not, []⟩
      (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
      (by simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.registerGlobal, ExtTreeMap0.get?_insert_self])
      (some (24, 3)) .stack .ok]
  have h5 := keyedDeallocate_postRemovalFailure_retains_detached_state (KeyedAllocWorld.empty.insertLive id1 entryU32)
    id1 entryU32 (some (4, 2)) .heap .ok
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl (by decide)
  have h6 := keyedDeallocate_duplicateDead_replaces_before_error
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).insertDead id1 ⟨99, 0⟩)
    id1 entryU32 ⟨99, 0⟩
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead, ExtTreeMap0.get?_insert_self])
    rfl
  have h7 := keyedDeallocate_hookFailure_retains_detached_state_without_tombstone
    (KeyedAllocWorld.empty.insertLive id1 entryU32) id1 entryU32 .protectedDealloc "TreeBorrowsProtectedDealloc"
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl rfl
  have h7Dead : (KeyedAllocWorld.empty.insertLive id1 entryU32).findDead? id1 = none := by
    simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  exact ⟨h1Out, h1Live, h2, h3, h4, h5.1, h5.2.2.1, h5.2.1, h6.1, h6.2.2.2,
    h7.1, h7.2.1, h7.2.2.1, h7.2.2.2.trans h7Dead⟩

theorem canary_part1_raceDetectorMode_and_deallocateMachine :
    let wLive := KeyedAllocWorld.empty.insertLive id1 entryU32
    let wWithRace := wLive.setRace id1 ⟨2, 5, 0, 0, []⟩
    let wSameWriter := wLive.setRace id1 ⟨1, 2, 2, 7, []⟩
    let wMultiReader := wLive.setRace id1 ⟨1, 2, 2, 3, [(3, 6)]⟩
    let wZst := (KeyedAllocWorld.empty.insertLive id1 entryZst).setRace id1 ⟨2, 5, 0, 0, []⟩
    wLive.deallocateMachine (.provenanced id1 0) (some (4, 2)) .stack .unconfigured ⟨1, 0, []⟩ .ok =
      wLive.deallocate (.provenanced id1 0) (some (4, 2)) .stack .ok ∧
    (wLive.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 0, []⟩ .ok).outcome =
      .error (.hookFailure "MissingVectorClockExtra") ∧
    wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured false) ⟨1, 0, []⟩ .ok =
      KeyedAllocWorld.detachRaceClock (wWithRace.deallocate (.provenanced id1 0) none .stack .ok) ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured false) ⟨1, 0, []⟩ .ok).outcome =
      (wWithRace.deallocate (.provenanced id1 0) none .stack .ok).outcome ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).outcome =
      .error (.hookFailure "DataRace") ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).world.findLive? id1 =
      none ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).world.findRace? id1 =
      none ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).world.findDead? id1 =
      none ∧
    ((wWithRace.removeRace id1).deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).outcome =
      .error (.hookFailure "MissingVectorClockExtra") ∧
    (wWithRace.deallocateMachine (.provenanced id1 0) none .stack .unconfigured ⟨1, 0, []⟩ .ok).world.findRace? id1 =
      none ∧
    (wWithRace.deallocate (.provenanced id1 0) none .stack .ok).world.findRace? id1 =
      some ⟨2, 5, 0, 0, []⟩ ∧
    (wSameWriter.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok).outcome =
      .error (.hookFailure "DataRace") ∧
    (wMultiReader.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 10, [(2, 10), (3, 2)]⟩ .ok).outcome =
      .error (.hookFailure "DataRace") ∧
    (wZst.deallocateMachine (.provenanced id1 0) none .stack (.configured true) ⟨1, 0, []⟩ .ok).outcome = .ok () ∧
    ((KeyedAllocWorld.empty.allocateMachine entryU32 (.configured true) 1 5).1.deallocateMachine
      (.provenanced id1 0) (some (4, 2)) .stack (.configured true) (DeallocActor.ofVClock 1 [(1, 5)]) .ok).outcome = .ok () ∧
    ((KeyedAllocWorld.empty.allocateMachine entryU32 (.configured true) 1 5).1.deallocateMachine
      (.provenanced id1 0) (some (4, 2)) .stack (.configured true) (DeallocActor.ofVClock 1 [(1, 5)]) .ok).world.findRace? id1 =
      none := by
  dsimp only
  have hLiveRaceNone : (KeyedAllocWorld.empty.insertLive id1 entryU32).findRace? id1 = none := by
    simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have hUnconf := keyedDeallocateMachine_unconfigured_eq_deallocate
    (KeyedAllocWorld.empty.insertLive id1 entryU32) (.provenanced id1 0) (some (4, 2)) .stack ⟨1, 0, []⟩ .ok
    (fun id off h => by
      cases h
      exact hLiveRaceNone)
  have hMiss := keyedDeallocateMachine_missingClock_invalid
    (KeyedAllocWorld.empty.insertLive id1 entryU32) id1 entryU32 true ⟨1, 0, []⟩ .ok
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl hLiveRaceNone
  have hWithRaceLive : ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩).findLive? id1 =
      some entryU32 := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]
  have hWithRaceClk : ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩).findRace? id1 =
      some ⟨2, 5, 0, 0, []⟩ := by
    simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.setRace, ExtTreeMap0.get?_insert_self]
  have hWithRaceDead : ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩).findDead? id1 =
      none := by
    simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty,
      ExtTreeMap0.get?_empty]
  have hNotDet := keyedDeallocateMachine_notDetecting_eq_deallocate
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩)
    id1 0 ⟨2, 5, 0, 0, []⟩ none .stack ⟨1, 0, []⟩ .ok hWithRaceClk
  have hNotDetOut := (keyedDetachRaceClock_preserves_outcome_detached_and_tables
    (((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩).deallocate
      (.provenanced id1 0) none .stack .ok) id1).1
  have hRace := keyedDeallocateMachine_race_checked_before_cleanup
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩)
    id1 entryU32 ⟨2, 5, 0, 0, []⟩ ⟨1, 3, []⟩
    hWithRaceLive rfl (by decide) hWithRaceClk (by decide)
  have hDrop := keyedDeallocateMachine_detached_drops_raceClock
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩)
    (.provenanced id1 0) none .stack (.configured true) ⟨1, 3, []⟩ .ok id1 entryU32 hRace.2.1
  have hUnconfStale := (keyedDeallocateMachine_live_always_detaches_entry_and_clock
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩)
    id1 entryU32 none .stack .unconfigured ⟨1, 0, []⟩ .ok hWithRaceLive).2.2
  have hCoreKeeps := keyedDeallocateWith_preserves_raceClocks
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨2, 5, 0, 0, []⟩)
    (.provenanced id1 0) none .stack (fun _ _ _ => DeallocHookSpec.ok.run) id1
  have hSameW := keyedDeallocateMachine_sameWriter_foreignRead_races
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨1, 2, 2, 7, []⟩)
    id1 entryU32 ⟨1, 2, 2, 7, []⟩ ⟨1, 3, []⟩
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl (by decide)
    (by simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.setRace, ExtTreeMap0.get?_insert_self])
    rfl (by decide) (by decide) (by decide)
  have hMulti := keyedDeallocateMachine_perThreadClock_catches_unsynced_reader
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨1, 2, 2, 3, [(3, 6)]⟩)
    id1 entryU32 ⟨1, 2, 2, 3, [(3, 6)]⟩ ⟨1, 10, [(2, 10), (3, 2)]⟩ 3 6
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl (by decide)
    (by simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.setRace, ExtTreeMap0.get?_insert_self])
    (List.mem_cons_self ..) (by decide) (by decide) (by decide)
  have hZst := keyedDeallocateMachine_zst_skips_race_check
    ((KeyedAllocWorld.empty.insertLive id1 entryZst).setRace id1 ⟨2, 5, 0, 0, []⟩)
    id1 entryZst ⟨2, 5, 0, 0, []⟩ ⟨1, 0, []⟩
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl rfl
    (by simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.setRace, ExtTreeMap0.get?_insert_self])
    (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
  have hAllocEq : KeyedAllocWorld.empty.allocateMachine entryU32 (.configured true) 1 5 =
      ((KeyedAllocWorld.empty.allocateMachine entryU32 (.configured true) 1 5).1, .ok id1) := by
    simp [KeyedAllocWorld.allocateMachine, KeyedAllocWorld.allocate, KeyedAllocWorld.reserveAllocId,
      KeyedAllocWorld.empty, KeyedAllocWorld.hasIssued, KeyedAllocWorld.containsId,
      KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?, KeyedAllocWorld.findGlobal?,
      ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty, MiriAllocId.ofUInt64, id1]
  have hAllocDealloc := keyedAllocateMachine_deallocateMachine_sameThread_ok
    KeyedAllocWorld.empty _ entryU32 (.configured true) 1 5 id1 rfl
    (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
    hAllocEq
  exact ⟨hUnconf, hMiss.1, hNotDet, (congrArg DeallocResult.outcome hNotDet).trans hNotDetOut,
    hRace.1, hRace.2.2.1, hDrop.1, hRace.2.2.2.2.1.trans hWithRaceDead, hRace.2.2.2.2.2,
    hUnconfStale, hCoreKeeps.trans hWithRaceClk, hSameW, hMulti, hZst,
    hAllocDealloc.1, hAllocDealloc.2.1⟩

theorem canary_part1_ofVClock_unlisted_zero_vs_nonzeroFallback :
    (DeallocActor.ofVClock 1 [(2, 10)]).viewFor 3 = 0 ∧
    let w := (KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨1, 2, 1, 0, [(3, 5)]⟩
    (w.deallocateMachine (.provenanced id1 0) none .stack (.configured true)
      (DeallocActor.ofVClock 1 [(2, 10)]) .ok).outcome = .error (.hookFailure "DataRace") ∧
    (w.deallocateMachine (.provenanced id1 0) none .stack (.configured true)
      ⟨1, 10, [(2, 10)]⟩ .ok).outcome = .ok () := by
  dsimp only
  have hv := DeallocActor.ofVClock_viewFor_unlisted_eq_zero 1 3 [(2, 10)] rfl
  have hsep := deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback
    ((KeyedAllocWorld.empty.insertLive id1 entryU32).setRace id1 ⟨1, 2, 1, 0, [(3, 5)]⟩)
    id1 entryU32
    (by simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self])
    rfl (by decide)
    (by simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.setRace, KeyedAllocWorld.insertLive, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty])
    (by simp [KeyedAllocWorld.findRace?, KeyedAllocWorld.setRace, ExtTreeMap0.get?_insert_self])
  exact ⟨hv, hsep.1, hsep.2⟩

/-! ## Section 2: Part 2A & 2B Closed Canaries (`charon#1619/#1620`, `minirust#295`) -/

theorem canary_part2A_policy_and_upstream_create_mirror :
    selectFnEntryPolicy ⟨false, false, false⟩ .mutable ⟨true, false⟩ = .skipRetag ∧
    selectFnEntryPolicy ⟨false, false, false⟩ .box ⟨true, false⟩ = .skipRetag ∧
    selectFnEntryPolicy ⟨true, true, false⟩ .mutable ⟨true, true⟩ = .rustcNoWritable ∧
    ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 1 = .rustcNoWritable ∧
    ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 2 = .skipRetag ∧
    ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 3 = .writableChildWrite ∧
    MiriRetagPolicyMirror.classifyFnEntry
      (MiriRetagPolicyMirror.create ⟨true, true, false⟩ .mutable .fnEntry ⟨true, true⟩) = .rustcNoWritable ∧
    fnEntryRetagPerm .mut (.uint .u32) = .reservedFrz false ∧
    retagPerm .fnEntry .mut (.uint .u32) = .reservedFrz false ∧
    TreeTagNode.isProtected
      { tag := 1, parentTag := none, perm := .reservedFrz false, rangeOffset := 0, rangeLen := 4, protector := some 7 } [7] =
      (TreeTagNode.toByteRangePerm 42
        { tag := 1, parentTag := none, perm := .reservedFrz false, rangeOffset := 0, rangeLen := 4, protector := some 7 }).isProtected ⟨[7]⟩ := by
  have hpin := pinned_mutable_or_box_fnEntry_skips_retag ⟨false, false, false⟩ ⟨true, false⟩ rfl
  have hnowr := selectFnEntryPolicy_rustcNoWritable_mut ⟨true, true, false⟩ true rfl
  have hmap1 : ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 1 = .rustcNoWritable := by
    rw [FnParamRetagMap.policyFor_set_ne _ _ (by decide), FnParamRetagMap.policyFor_set_self]
  have hmap2 : ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 2 = .skipRetag :=
    FnParamRetagMap.policyFor_set_self _ _ _
  have hmap3 : ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .skipRetag).policyFor 3 = .writableChildWrite := by
    rw [FnParamRetagMap.policyFor_set _ 2 3, FnParamRetagMap.policyFor_set _ 1 3]; rfl
  have hup := (selectFnEntryPolicy_eq_upstream_create ⟨true, true, false⟩ .mutable ⟨true, true⟩).trans hnowr
  have hperm1 := fnEntryRetagPerm_mut_eq_reservedFrz (.uint .u32)
  have hperm2 := (retagPerm_fnEntry_eq_fnEntryRetagPerm .mut (.uint .u32)).trans hperm1
  have hprot := TreeTagNode.isProtected_eq_toByteRangePerm 42
    { tag := 1, parentTag := none, perm := .reservedFrz false, rangeOffset := 0, rangeLen := 4, protector := some 7 }
    [7]
  exact ⟨hpin.1, hpin.2, hnowr, hmap1, hmap2, hmap3, hup, hperm1, hperm2, hprot⟩

theorem canary_part2A_trusted_machineState_multiParam_overlay :
    let u32Ty : Ty := ⟨.uint .u32, 0⟩
    let mutU32RefTy : Ty := ⟨.ref .mut (.uint .u32), 1⟩
    let mutUnitRefTy : Ty := ⟨.ref .mut (.tuple []), 2⟩
    let decls : List LocalDecl := [
      ⟨.mut, u32Ty, some "_0"⟩,
      ⟨.not, mutU32RefTy, some "_1"⟩,
      ⟨.not, mutU32RefTy, some "_2"⟩,
      ⟨.not, mutUnitRefTy, some "_3"⟩
    ]
    let parentUnique : BorrowEntry :=
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .unique,
        rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 }
    let parentFrozen : BorrowEntry :=
      { tag := 2, targetLocal := 0, targetProjection := [], perm := .frozen,
        rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 }
    let parentZst : BorrowEntry :=
      { tag := 3, targetLocal := 0, targetProjection := [], perm := .frozen,
        rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none, targetFrameDepth := 0 }
    let st : MachineState := {
      frame := {
        blockIdx := 0, stmtIdx := 0,
        locals := [
          .init (.scalar ⟨7, 4⟩),
          .init (.ptr ⟨1, 0⟩ 8),
          .init (.ptr ⟨2, 0⟩ 8),
          .init (.ptr ⟨3, 0⟩ 8)
        ]
      }
      memory := {
        borrows := [parentUnique, parentFrozen, parentZst]
        nextTag := 10
        nextProtector := 100
      }
    }
    let pmap := ((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .writableChildWrite).set 3 .writableChildWrite
    evalFnEntryRetagWithParamMap pmap st ⟨1, []⟩ "p1" decls emptyLayoutTable =
      evalStmt st ⟨.retag .fnEntry ⟨1, []⟩, "p1"⟩ decls emptyLayoutTable ∧
    evalFnEntryRetagWithParamMap pmap st ⟨2, []⟩ "p2" decls emptyLayoutTable = MirStepNode.fail .ub ∧
    applyParamFnEntryImplicitWrite st decls emptyLayoutTable ⟨3, []⟩ = MirStepNode.step st := by
  dsimp only
  have h1 := evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt
    (((FnParamRetagMap.empty.set 1 .rustcNoWritable).set 2 .writableChildWrite).set 3 .writableChildWrite)
    { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8), .init (.ptr ⟨3, 0⟩ 8)] }
      memory := {
        borrows := [
          { tag := 1, targetLocal := 0, targetProjection := [], perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 },
          { tag := 2, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 },
          { tag := 3, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none, targetFrameDepth := 0 }
        ],
        nextTag := 10, nextProtector := 100 } }
    ⟨1, []⟩ "p1"
    [⟨.mut, ⟨.uint .u32, 0⟩, some "_0"⟩, ⟨.not, ⟨.ref .mut (.uint .u32), 1⟩, some "_1"⟩, ⟨.not, ⟨.ref .mut (.uint .u32), 1⟩, some "_2"⟩, ⟨.not, ⟨.ref .mut (.tuple []), 2⟩, some "_3"⟩]
    emptyLayoutTable rfl
  have h3 := applyParamFnEntryImplicitWrite_zst_noop
    { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8), .init (.ptr ⟨2, 0⟩ 8), .init (.ptr ⟨3, 0⟩ 8)] }
      memory := {
        borrows := [
          { tag := 1, targetLocal := 0, targetProjection := [], perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 },
          { tag := 2, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none, parentTag := none, targetFrameDepth := 0 },
          { tag := 3, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 0, protector := none, parentTag := none, targetFrameDepth := 0 }
        ],
        nextTag := 10, nextProtector := 100 } }
    [⟨.mut, ⟨.uint .u32, 0⟩, some "_0"⟩, ⟨.not, ⟨.ref .mut (.uint .u32), 1⟩, some "_1"⟩, ⟨.not, ⟨.ref .mut (.uint .u32), 1⟩, some "_2"⟩, ⟨.not, ⟨.ref .mut (.tuple []), 2⟩, some "_3"⟩]
    emptyLayoutTable ⟨3, []⟩ ⟨.ref .mut (.tuple []), 2⟩ (.tuple []) rfl rfl rfl
  exact ⟨h1, rfl, h3⟩

theorem canary_part2A_twoPass_vs_upstream_and_uninit_frozen :
    (execFnEntryMutRetag (mkTwoBranchWorld .unique .frozen none false) 1 0 0 .writableChildWrite true =
      execFnEntryMutRetag (mkTwoBranchWorld .unique .frozen none false) 1 0 0 .rustcNoWritable true) ∧
    (execFnEntryMutRetag (mkTwoBranchWorld .unique .frozen) 1 0 4 .rustcNoWritable false =
      execFnEntryMutRetagUpstream (mkTwoBranchWorld .unique .frozen) 1 0 4 .rustcNoWritable false) ∧
    (execFnEntryMutRetag (mkTwoBranchWorld .unique .frozen) 1 0 4 .writableChildWrite false =
      execFnEntryMutRetagUpstream (mkTwoBranchWorld .unique .frozen) 1 0 4 .writableChildWrite false) ∧
    (∃ w' tag, execFnEntryMutRetagSourceOrder (mkTwoBranchWorld .unique .frozen none false) 1 0 4 .rustcNoWritable true = .ok (w', tag) ∧
      (findNode? w'.nodes 2).map (·.perm) = some .frozen ∧
      (findNode? w'.nodes tag).map (·.perm) = some (.reservedFrz false)) ∧
    (execFnEntryMutRetagSourceOrder (mkTwoBranchWorld .unique .frozen none false) 1 0 4 .writableChildWrite true =
      .error .uninitializedPointeeWrite) ∧
    (match execFnEntryMutRetagSourceOrder (mkTwoBranchWorld .unique .frozen none true) 1 0 4 .rustcNoWritable false with
     | .ok (w1, childTag) =>
       match execWorldRangeRead w1 2 0 4 with
       | .ok w2 =>
         (findNode? w2.nodes childTag).map (·.perm) = some (.reservedFrz true) ∧
         execWorldRangeWrite w2 childTag 0 4 = .error (.conflictedProtectedChildWrite childTag)
       | .error _ => False
     | .error _ => False) ∧
    (match execFnEntryMutRetagSourceOrder (mkTwoBranchWorld .unique .frozen none true) 1 0 4 .rustcNoWritable false with
     | .ok (w1, childTag) => execWorldRangeWrite w1 1 0 4 = .error (.protectedForeignConflict childTag)
     | .error _ => False) ∧
    (stepNodeOnRangeWrite [7] false 0 4
      { tag := 5, parentTag := some 1, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := some 7 } =
      .error (.protectedForeignConflict 5)) ∧
    (∃ w, execFnEntryMutRetag w 1 0 4 .writableChildWrite false = .error (.disabledParentTag 0) ∧
      execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 0)) ∧
    (∃ w, execFnEntryMutRetag w 1 0 4 .writableChildWrite false = .error (.protectedForeignConflict 5) ∧
      execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 1)) := by
  have hzst := fnEntryMutRetag_zst_no_write (mkTwoBranchWorld .unique .frozen none false) 1 0 true
  have hno := execFnEntryMutRetag_eq_upstream_when_no_implicitWrite (mkTwoBranchWorld .unique .frozen) 1 0 4 false
  have htwo := execFnEntryMutRetag_mkTwoBranch_eq_upstream .frozen none true .writableChildWrite false
  have huninit := rustcNoWritable_preserves_uninit_and_frozen_sibling
  have hlat := rustcNoWritable_foreignRead_latches_conflicted
  have hpar := rustcNoWritable_parentWrite_faults_on_protected_child
  have hnodeProt := stepNodeOnRangeWrite_foreign_protected_conflict
    [7] 0 4
    { tag := 5, parentTag := some 1, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := some 7 }
    rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl)))
  have hdis := execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream
  have hfrz := execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream
  exact ⟨hzst.1, hno, htwo, huninit.1, huninit.2.1, hlat, hpar, hnodeProt, ⟨_, hdis⟩, ⟨_, hfrz⟩⟩

theorem canary_part2A_sourceOrder_bottomUp_and_equivalence :
    (ancestorPathTagsAux multiLevelBorrowWorld.nodes 5 2).head? = some 2 ∧
    (ancestorPathTags multiLevelBorrowWorld.nodes 2).head? = some 2 ∧
    (ancestorPathNodes multiLevelBorrowWorld.nodes 2).head? =
      some { tag := 2, parentTag := some 1, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none } ∧
    (∃ w, execFnEntryMutRetagUpstream w 1 0 4 .writableChildWrite false = .error (.protectedForeignConflict 5) ∧
      execFnEntryMutRetagSourceOrder w 1 0 4 .writableChildWrite false = .error (.ancestorWriteForbidden 1)) ∧
    (∃ w, checkAncestorsFlatM w 2 (stepNodeOnRangeWrite w.activeProtectors true 0 4) = .error (.ancestorWriteForbidden 1) ∧
      execFnEntryMutRetagSourceOrder w 2 0 4 .writableChildWrite false = .error (.conflictedProtectedChildWrite 2)) ∧
    (execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 .writableChildWrite false =
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .writableChildWrite false) ∧
    (execFnEntryMutRetagUpstream multiLevelBorrowWorld 2 0 4 .writableChildWrite false =
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .writableChildWrite false) ∧
    (∀ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok r ↔
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok r) ∧
    (∃ w' tag, execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok (w', tag) ∧
      { tag := 3, parentTag := some 1, perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none } ∈ w'.nodes) := by
  have hheadAux := ancestorPathTagsAux_head multiLevelBorrowWorld.nodes 4 2
  have hheadTags := ancestorPathTags_head multiLevelBorrowWorld.nodes 2
  have hheadNodes := ancestorPathNodes_head multiLevelBorrowWorld.nodes 2
    { tag := 2, parentTag := some 1, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none } rfl
  have hrev := execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder
  have hbot := execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors
  have hforAligned : ForeignReadWriteErrorAligned multiLevelBorrowWorld 2 0 4 := by
    left
    intro n hn hnot
    simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact False.elim (by simp [multiLevelBorrowWorld, ancestorPathTags, ancestorPathTagsAux, findNode?] at hnot)
    · exact False.elim (by simp [multiLevelBorrowWorld, ancestorPathTags, ancestorPathTagsAux, findNode?] at hnot)
    · exact False.elim (by simp [multiLevelBorrowWorld, ancestorPathTags, ancestorPathTagsAux, findNode?] at hnot)
    · exact ⟨_, rfl⟩
  have heq3 := execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors
    multiLevelBorrowWorld multiLevelBorrowWorld_wf 2 0 4 .writableChildWrite false
    multiLevelBorrowWorld_ancWritable hforAligned
  have heqUp := execFnEntryMutRetagUpstream_eq_sourceOrder_of_writableAncestors
    multiLevelBorrowWorld 2 0 4 .writableChildWrite false multiLevelBorrowWorld_ancWritable
  have hokEquiv : ∀ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok r ↔
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok r := by
    intro r
    have h := execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok
      multiLevelBorrowWorld multiLevelBorrowWorld_wf 2 0 4 .rustcNoWritable false r
    exact h.1.trans h.2
  have hrun : ∃ w' tag, execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .ok (w', tag) ∧
      { tag := 3, parentTag := some 1, perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none } ∈ w'.nodes := by
    cases hr : execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false with
    | error e =>
      have hbad : execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false = .error e := hr
      simp [execFnEntryMutRetagSourceOrder, multiLevelBorrowWorld, findNode?, checkAncestorPathM,
        ancestorPathNodes, ancestorPathTags, ancestorPathTagsAux, checkNodesM, mapNodesM,
        stepNodeOnRangeRead, rangesOverlap] at hbad
    | ok res =>
      rcases res with ⟨w', tag⟩
      rcases sourceOrder_rustcNoWritable_preserves_all_frozen_nodes
        multiLevelBorrowWorld w' 2 0 4 tag false hr
        { tag := 3, parentTag := some 1, perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none }
        (by simp [multiLevelBorrowWorld]) rfl with
        ⟨n', hn'Mem, _, _, _, heq⟩
      exact ⟨w', tag, rfl, heq rfl ▸ hn'Mem⟩
  exact ⟨hheadAux, hheadTags, hheadNodes, ⟨_, hrev⟩, ⟨_, hbot.2.1, hbot.2.2⟩, heq3, heqUp, hokEquiv, hrun⟩

theorem canary_part2A_readOnlyAlloc_implicitWrite_rejected_noWritable_ok :
    let wMut : FnEntryBorrowWorld := mkTwoBranchWorld .unique .frozen
    let wRo : FnEntryBorrowWorld := { mkTwoBranchWorld .unique .frozen with allocReadOnly := true }
    execFnEntryMutRetag wRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagUpstream wRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagSourceOrder wRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc ∧
    execFnEntryMutRetagPrunedSourceOrder wRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc ∧
    (execFnEntryMutRetagSourceOrder wRo 1 0 4 .rustcNoWritable).isOk = true ∧
    (execFnEntryMutRetagSourceOrder wRo 1 0 4 .rustcNoWritable).map
        (fun r => (r.1.nodes, r.1.activeProtectors, r.1.nextTag, r.1.nextProtector, r.2)) =
      (execFnEntryMutRetagSourceOrder wMut 1 0 4 .rustcNoWritable).map
        (fun r => (r.1.nodes, r.1.activeProtectors, r.1.nextTag, r.1.nextProtector, r.2)) ∧
    (execFnEntryMutRetagSourceOrder wRo 1 0 0 .writableChildWrite).isOk = true ∧
    (execFnEntryMutRetagSourceOrder wMut 1 0 4 .writableChildWrite).isOk = true := by
  dsimp only
  have hrej := fnEntryMutRetag_readOnlyAlloc_writable_rejected
    { mkTwoBranchWorld .unique .frozen with allocReadOnly := true } 1 0 4 false
    ⟨1, some 0, .unique, 0, 4, none, true⟩ rfl rfl (by decide)
  have hign := sourceOrder_rustcNoWritable_ignores_allocReadOnly
    (mkTwoBranchWorld .unique .frozen) true 1 0 4 false
  exact ⟨hrej.1, hrej.2.1, hrej.2.2.1, hrej.2.2.2, by decide, hign, by decide, by decide⟩

theorem canary_part2A_disabledParent_unaccessedProtected_and_skipSelfAndChildren :
    let unaccNode : TreeTagNode :=
      { tag := 9, parentTag := some 0, perm := .reservedFrz false, rangeOffset := 0, rangeLen := 4,
        protector := some 7, accessed := false }
    stepNodeOnRangeWrite [7] false 0 4 unaccNode = .ok { unaccNode with perm := .disabled } ∧
    (let wDis : FnEntryBorrowWorld := {
       nodes := [⟨0, none, .unique, 0, 8, none, true⟩, ⟨1, some 0, .disabled, 0, 4, none, true⟩]
       activeProtectors := []
       nextTag := 2
       nextProtector := 10
     }
     let wDisRo : FnEntryBorrowWorld := { wDis with allocReadOnly := true }
     (execFnEntryMutRetagSourceOrder wDis 1 0 0 .rustcNoWritable).isOk = true ∧
     (execFnEntryMutRetagSourceOrder wDis 1 4 4 .writableChildWrite).isOk = true ∧
     execFnEntryMutRetagSourceOrder wDis 1 0 4 .rustcNoWritable = .error (.disabledParentTag 1) ∧
     execFnEntryMutRetagSourceOrder wDisRo 1 0 4 .writableChildWrite = .error .writeToReadOnlyAlloc) ∧
    (execFnEntryMutRetagPrunedSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false =
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .rustcNoWritable false) ∧
    (let wDisSub : FnEntryBorrowWorld := {
       nodes := [
         ⟨0, none, .unique, 0, 4, none, true⟩,
         ⟨1, some 0, .unique, 0, 4, none, true⟩,
         ⟨2, some 0, .disabled, 0, 4, none, true⟩,
         ⟨3, some 2, .cell, 0, 4, none, true⟩,
         ⟨4, some 3, .unique, 0, 4, some 7, true⟩
       ]
       activeProtectors := [7]
       nextTag := 5
       nextProtector := 10
     }
     let wFrzSub : FnEntryBorrowWorld := {
       nodes := [
         ⟨0, none, .unique, 0, 4, none, true⟩,
         ⟨1, some 0, .unique, 0, 4, none, true⟩,
         ⟨2, some 0, .frozen, 0, 4, none, true⟩,
         ⟨3, some 2, .unique, 0, 4, some 7, true⟩
       ]
       activeProtectors := [7]
       nextTag := 4
       nextProtector := 10
     }
     execFnEntryMutRetagSourceOrder wDisSub 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 4) ∧
     (execFnEntryMutRetagPrunedSourceOrder wDisSub 1 0 4 .writableChildWrite).isOk = true ∧
     execFnEntryMutRetagSourceOrder wFrzSub 1 0 4 .rustcNoWritable = .error (.protectedForeignConflict 3) ∧
     (execFnEntryMutRetagPrunedSourceOrder wFrzSub 1 0 4 .rustcNoWritable).isOk = true ∧
     execFnEntryMutRetagPrunedSourceOrder wFrzSub 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 3)) := by
  have hunacc := stepNodeOnRangeWrite_unaccessed_protected_foreign_disables_without_ub
    [7] 0 4
    { tag := 9, parentTag := some 0, perm := .reservedFrz false, rangeOffset := 0, rangeLen := 4,
      protector := some 7, accessed := false }
    rfl rfl rfl (Or.inl rfl)
  have hdis := fnEntryMutRetag_disabledParent_zst_disjoint_and_readOnly_precedence
  have heqPruned := execFnEntryMutRetagPrunedSourceOrder_eq_sourceOrder_of_noSkippedForeignSubtree
    multiLevelBorrowWorld 2 0 4 .rustcNoWritable false (by
      intro n hn
      simp only [multiLevelBorrowWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> rfl)
  have hsep := execFnEntryMutRetagPrunedSourceOrder_skipSelfAndChildren_separation
  exact ⟨hunacc, ⟨hdis.1, hdis.2.2.2.1, hdis.2.2.2.2.1, hdis.2.2.2.2.2.2⟩, heqPruned,
    ⟨hsep.2.1, hsep.2.2.2.1, hsep.2.2.2.2.1, hsep.2.2.2.2.2.1, hsep.2.2.2.2.2.2.2⟩⟩

theorem canary_part2B_pureFreeze_pureUnsafeCell_mixed_and_zstUnsafeCell :
    evalRawMutStaticWriteTB (retagStaticPreservedAt (.freezeScalar 4) 1 2) 0 1 = .ub ∧
    evalRawMutStaticWriteTB (retagStaticErasedAt (.freezeScalar 4) 1) 0 1 = .ok ∧
    evalRawMutStaticWriteMiri (.freezeScalar 4) (retagStaticErasedAt (.freezeScalar 4) 1) 0 1 = .readOnlyAlloc ∧
    evalRawMutStaticWriteMiri (.unsafeCell 4) (retagStaticPreservedAt (.unsafeCell 4) 1 2) 0 1 = .ok ∧
    (let mixed : StaticTyDesc := .composite 12 [(0, .freezeScalar 4), (4, .unsafeCell 4), (8, .padding 4)]
     staticAllocMutability mixed = .mut ∧
     evalRawMutStaticWriteMiri mixed (retagStaticPreservedAt mixed 10 20) 1 1 = .ub ∧
     evalRawMutStaticWriteMiri mixed (retagStaticErasedAt mixed 10) 1 1 = .ok ∧
     evalRawMutStaticWriteMiri mixed (retagStaticPreservedAt mixed 10 20) 8 1 = .ub ∧
     evalRawMutStaticWriteMiri mixed (retagStaticPreservedAt mixed 10 20) 4 1 = .ok) ∧
    (let zstCell : StaticTyDesc := .composite 1 [(0, .freezeScalar 1), (1, .unsafeCell 0)]
     (staticFreezeSegments zstCell).2 = [⟨0, 1, .freeze⟩] ∧
     zstCell.isSyntacticFreeze = false ∧
     staticAllocMutability zstCell = .mut ∧
     evalRawMutStaticWriteMiri zstCell (retagStaticPreservedAt zstCell 1 2) 0 1 = .ub ∧
     evalRawMutStaticWriteMiri zstCell (retagStaticErasedAt zstCell 1) 0 1 = .ok) := by
  have h1 := static_pureFreeze_preserved_ub_vs_erased_unsound 4 1 2 0 (by decide) (by decide)
  have h2 := static_pureFreeze_erased_write_caught_by_readOnly_alloc 4 1 0 (by decide)
  have h3 := static_pureUnsafeCell_preserved_write_ok 4 1 2 0 (by decide) (by decide)
  have hmix1 := static_mixed_miri_separation 4 4 4 10 20 1 (by decide) (by decide) (Or.inl (by decide))
  have hmix2 := static_mixed_miri_separation 4 4 4 10 20 8 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩)
  have hmixCell := static_mixed_miri_unsafeCell_write_ok 4 4 4 10 20 4 (by decide) (by decide) (by decide) (by decide)
  have hzst := static_zstUnsafeCell_composite_miri_separation 1 1 2 0 (by decide) (by decide)
  exact ⟨h1.1, h1.2, h2.2, h3.2, ⟨hmix1.1, hmix1.2.1, hmix1.2.2, hmix2.2.1, hmixCell⟩, hzst⟩

/-! ## Section 3: Part 3A, 3B, & 3C Closed Canaries (`lean-miri#79/#75/#82`) -/

theorem canary_part3A_syntacticSized_customDst_and_safeThinRef :
    isSyntacticallySized (.array (.uint 1) 16) = (unsizedMetadataTail (.array (.uint 1) 16)).isNone ∧
    fieldsTailSyntacticallySized [.uint 4, .slice (.uint 1)] =
      (fieldsUnsizedMetadataTail [.uint 4, .slice (.uint 1)]).isNone ∧
    fieldsTailSyntacticallySized [.uint 4, .slice (.uint 1)] = false ∧
    fieldsUnsizedMetadataTail [.uint 4, .slice (.uint 1)] = some .sliceLen ∧
    validateRawPtrFastPath (.array (.uint 1) 16) (.thin 4096) =
      validateRawPtrLayoutFirst (.array (.uint 1) 16) (.thin 4096) ∧
    validateRawPtrFastPath (.slice (.uint 1)) (.wideSlice 4096 8) =
      validateRawPtrLayoutFirst (.slice (.uint 1)) (.wideSlice 4096 8) ∧
    validateRawPtrFastPath (.array (.uint 1) usizeMax64) (.thin 4096) = .ok () ∧
    validateRawPtrLayoutFirst (.array (.uint 1) usizeMax64) (.thin 4096) =
      .error (.layoutFailed .layoutOverflow) ∧
    (isSyntacticallySized (.array (.uint 1) usizeMax64) = true ∧
      ∃ e, computeTyLayout (.array (.uint 1) usizeMax64) = .error e) ∧
    validateRawPtrFastPath (.slice (.uint 1)) (.thin 4096) = .error .expectedWideSliceMeta ∧
    validateRawPtrFastPath (.tuple [.array (.uint 1) usizeMax64, .slice (.uint 1)]) (.wideSlice 4096 1) =
      .error (.layoutFailed .layoutOverflow) ∧
    (let wStatic := KeyedAllocWorld.empty.registerGlobal id1 ⟨.static, 4, 2, .not, []⟩
     validateSafeThinRef wStatic (.uint 4) ⟨16, some (id1, 0)⟩ = .ok () ∧
     validateSafeThinRef wStatic .unit ⟨0, some (id1, 0)⟩ = .error .nullSafePtr ∧
     validateSafeThinRef wStatic (.uint 4) ⟨2, none⟩ = .error .danglingOrOutOfBoundsSafePtr) := by
  have hmeta := isSyntacticallySized_eq_metadataTail_isNone (.array (.uint 1) 16)
  have hfmeta := fieldsTailSized_eq_metadataTail_isNone [.uint 4, .slice (.uint 1)]
  have hfok := fieldsTailSyntacticallySized_eq_of_ok 0 1 true [.uint 4, .slice (.uint 1)]
    (lay := ⟨4, 4, false, true, some .sliceLen⟩) rfl
  have hok := validateRawPtrFastPath_eq_layoutFirst_of_layoutOk (.array (.uint 1) 16) (.thin 4096)
    (lay := ⟨16, 1, true, true, none⟩) rfl
  have huns := validateRawPtrFastPath_eq_layoutFirst_of_unsized (.slice (.uint 1)) (.wideSlice 4096 8) rfl
  have hsep := oversized_array_rawPtr_separation 4096
  have himp := validateRawPtrFastPath_ne_layoutFirst_imp (.array (.uint 1) usizeMax64) (.thin 4096)
    (by rw [hsep.1, hsep.2]; intro h; cases h)
  have hsl := slice_dst_rawPtr_requires_wideSliceMeta 4096 8
  have hov := unsized_rawPtr_layoutOverflow_rejected_like_upstream 4096 1
  have hthin := validateSafeThinRef_staticGlobal_nullProv_and_accessOrder
  exact ⟨hmeta, hfmeta, hfok.1, hfok.2, hok, huns, hsep.1, hsep.2, himp, hsl.1, hov.1, ⟨hthin.2.1, hthin.2.2.1, hthin.2.2.2⟩⟩

theorem canary_part3A_safeThinRef_zstNeverDangles_and_nullDeadFn_classification :
    let wMix : KeyedAllocWorld :=
      (KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩
    validateSafeThinRef wMix .unit ⟨16, some (id3, 0)⟩ = .ok () ∧
    validateSafeThinRef wMix .unit ⟨16, some (id10, 999)⟩ = .ok () ∧
    validateSafeThinRef wMix .unit ⟨0, some (id3, 0)⟩ = .error .nullSafePtr ∧
    validateSafeThinRef wMix (.uint 4) ⟨0, none⟩ = .error .nullSafePtr ∧
    validateSafeThinRef wMix (.uint 4) ⟨16, none⟩ = .error .danglingOrOutOfBoundsSafePtr ∧
    validateSafeThinRef wMix (.uint 4) ⟨16, some (id3, 0)⟩ = .error .danglingOrOutOfBoundsSafePtr ∧
    validateSafeThinRef wMix (.uint 4) ⟨16, some (id2, 0)⟩ = .error .danglingOrOutOfBoundsSafePtr ∧
    wMix.isAllocLive id2 = true ∧
    wMix.isAllocLive id3 = false ∧
    wMix.getAllocInfo id3 = some ⟨4, 2, .dead, .not⟩ ∧
    wMix.getLiveAllocSizeAndAlign id3 = .error (.useAfterFree id3) ∧
    wMix.getLiveAllocSizeAndAlign id10 = .error (.unavailable id10) ∧
    wMix.getAllocInfo id2 = some ⟨0, 0, .function, .not⟩ := by
  dsimp only
  have hdeadNotLive : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findLive? id3 = none := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have hdeadNotGlobal : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findGlobal? id3 = none := by
    simp only [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id3 ≠ id2), ExtTreeMap0.get?_empty]
  have hdead : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findDead? id3 = some ⟨4, 2⟩ := by
    simp [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead, ExtTreeMap0.get?_insert_self]
  have hfnNotLive : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findLive? id2 = none := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have hfn : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findGlobal? id2 =
      some ⟨.function, 0, 0, .not, []⟩ := by
    simp [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      ExtTreeMap0.get?_insert_self]
  have h10NotLive : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findLive? id10 = none := by
    simp [KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
  have h10NotGlobal : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findGlobal? id10 = none := by
    simp only [KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id10 ≠ id2), ExtTreeMap0.get?_empty]
  have h10NotDead : ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩).findDead? id10 = none := by
    simp only [KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
      KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id10 ≠ id3), ExtTreeMap0.get?_empty]
  have hz1 := validateSafeThinRef_zst_never_dangles
    ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩) ⟨16, some (id3, 0)⟩
  have hz2 := validateSafeThinRef_zst_never_dangles
    ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩) ⟨16, some (id10, 999)⟩
  have hz3 := validateSafeThinRef_zst_never_dangles
    ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩) ⟨0, some (id3, 0)⟩
  have hcls := validateSafeThinRef_nullInt_dead_and_fnGlobal_classification
    ((KeyedAllocWorld.empty.registerGlobal id2 ⟨.function, 0, 0, .not, []⟩).insertDead id3 ⟨4, 2⟩)
    id3 id2 ⟨4, 2⟩ ⟨.function, 0, 0, .not, []⟩ hdeadNotLive hdeadNotGlobal hdead hfnNotLive hfn (Or.inl rfl)
  have hliveG := keyedIsAllocLive_of_global _ id2 _ hfn
  have hdeadInfo := (keyedGetAllocInfo_dead_and_unavailable _ id3 hdeadNotLive hdeadNotGlobal).1 ⟨4, 2⟩ hdead
  have hunavail := (keyedGetAllocInfo_dead_and_unavailable _ id10 h10NotLive h10NotGlobal).2 h10NotDead
  have hfnInfo := (keyedGetAllocInfo_global_kinds _ id2 _ hfnNotLive hfn).1
  exact ⟨hz1.trans rfl, hz2.trans rfl, hz3.trans rfl, hcls.1, hcls.2.1, hcls.2.2.1, hcls.2.2.2,
    hliveG, hdeadInfo.2.2, hdeadInfo.1, hdeadInfo.2.1, hunavail.2, hfnInfo⟩

theorem canary_part3B_autoTraits_keys_and_principalLess_vtables :
    AutoTrait.rank .send ≠ AutoTrait.rank .sync ∧
    (.send ∈ canonicalizeAutoTraits [.sync, .send, .sync]) ∧
    canonicalizeAutoTraits (canonicalizeAutoTraits [.sync, .send]) = canonicalizeAutoTraits [.sync, .send] ∧
    (AutoTraitSet.ofList [.send, .sync]).mask < 32 ∧
    mkCanonicalVTableKey 42 none [.send, .sync] = mkCanonicalVTableKey 42 none [.sync, .send, .send] ∧
    (⟨42, none, AutoTraitSet.ofList [.send]⟩ : VTableKey) ≠ ⟨42, some 7, AutoTraitSet.ofList [.send]⟩ ∧
    encodeVTableKeyCode (mkCanonicalVTableKey 42 none [.send]) ≠
      encodeVTableKeyCode (mkCanonicalVTableKey 42 (some 7) [.send]) ∧
    (buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]).spec.principal = none ∧
    resolveVirtualMethod (buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]) 0 = none ∧
    (let vt := buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]
     let k := mkCanonicalVTableKey 42 none [.send]
     match VTableRegistry.empty.intern KeyedAllocWorld.empty k vt with
     | .ok (reg1, w1, vid) => reg1.intern w1 k vt = .ok (reg1, w1, vid)
     | .error _ => False) := by
  have hrank : AutoTrait.rank .send ≠ AutoTrait.rank .sync := fun h => by
    have := AutoTrait.rank_injective h; cases this
  have hmem : .send ∈ canonicalizeAutoTraits [.sync, .send, .sync] :=
    (mem_canonicalizeAutoTraits_iff _ _).2 (by decide)
  have hidem := canonicalizeAutoTraits_idem [.sync, .send]
  have hmaskLt := (AutoTraitSet.ofList [.send, .sync]).mask_lt
  have hperm := mkCanonicalVTableKey_perm_eq 42 none (xs := [.send, .sync]) (ys := [.sync, .send, .send])
    (fun a => by cases a <;> decide)
  have hneKey := vtableKey_principalLess_ne_principalBearing 42 7
    (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList [.send])
  have hneCode : encodeVTableKeyCode (mkCanonicalVTableKey 42 none [.send]) ≠
      encodeVTableKeyCode (mkCanonicalVTableKey 42 (some 7) [.send]) := fun heq =>
    hneKey (encodeVTableKeyCode_injective heq)
  have hspec := buildPrincipalLessVTable_spec (.uint 4) 42 none 4 2 [.send]
  have hmeth := principalLess_resolveVirtualMethod_fails (.uint 4) 42 none 4 2 [.send] 0
  have hidemp :
      match VTableRegistry.empty.intern KeyedAllocWorld.empty (mkCanonicalVTableKey 42 none [.send])
          (buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]) with
      | .ok (reg1, w1, vid) =>
          reg1.intern w1 (mkCanonicalVTableKey 42 none [.send])
            (buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]) = .ok (reg1, w1, vid)
      | .error _ => False := by
    cases h : VTableRegistry.empty.intern KeyedAllocWorld.empty (mkCanonicalVTableKey 42 none [.send])
        (buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]) with
    | error e => simp [VTableRegistry.intern, VTableRegistry.empty, KeyedAllocWorld.reserveAllocId,
        KeyedAllocWorld.empty, KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?,
        KeyedAllocWorld.findDead?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_empty,
        KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?, MiriAllocId.ofUInt64] at h
    | ok res =>
      rcases res with ⟨reg1, w1, vid⟩
      exact VTableRegistry.vtableRegistry_intern_idempotent _ _ _ _ _ h
  exact ⟨hrank, hmem, hidem, hmaskLt, hperm, hneKey, hneCode, hspec.1, hmeth, hidemp⟩

theorem canary_part3B_traitCheck_upcast_and_worldWF_roundTrip :
    vtableMatchesExpectedSpec
      ⟨some 7, AutoTraitSet.ofList [.send], [⟨10, 10, false⟩, ⟨99, 99, true⟩]⟩
      ⟨some 7, AutoTraitSet.ofList [.sync], [⟨10, 10, false⟩, ⟨88, 88, true⟩]⟩ = true ∧
    vtableMatchesExpectedSpec
      ⟨none, AutoTraitSet.empty, [⟨20, 20, false⟩, ⟨10, 10, false⟩]⟩
      ⟨none, AutoTraitSet.empty, [⟨10, 10, false⟩, ⟨20, 20, false⟩]⟩ = true ∧
    (let vtSend := buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]
     let kSend := mkCanonicalVTableKey 42 none [.send]
     let kDebug := mkCanonicalVTableKey 42 (some 7) [.send]
     let vtDebug : VTableData :=
       { concreteTy := .uint 4, concreteTyCode := 42, dropFnId := none,
         sizeBytes := 4, alignPow2 := 2, spec := ⟨some 7, AutoTraitSet.ofList [.send], []⟩, methodSlots := [id10] }
     -- Exhibit orphanCachedKeyReg: KeyWF ∧ AllocWF alone cannot guarantee cached intern validates against an arbitrary unrelated world
     let orphanCachedKeyReg : VTableRegistry :=
       { keyToAlloc := ExtTreeMap0.empty.insert (encodeVTableKeyCode kSend) id1
         allocToData := ExtTreeMap0.empty.insert id1 vtSend }
     let wOrphan : KeyedAllocWorld := KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩
     VTableRegistry.KeyWF orphanCachedKeyReg ∧
     VTableRegistry.AllocWF orphanCachedKeyReg wOrphan ∧
     validateVTableHalf KeyedAllocWorld.empty orphanCachedKeyReg (.provenanced id1 0) ⟨none, AutoTraitSet.empty, []⟩ =
       .error (.invalidVTableNotGlobalVTable id1) ∧
     validateVTableHalf wOrphan orphanCachedKeyReg (.provenanced id1 0) ⟨none, AutoTraitSet.ofList [.sync], []⟩ = .ok vtSend ∧
     validateVTableHalf wOrphan orphanCachedKeyReg (.provenanced id1 0) ⟨some 7, AutoTraitSet.ofList [.send], []⟩ =
       .error (.invalidVTableTrait vtSend.spec ⟨some 7, AutoTraitSet.ofList [.send], []⟩) ∧
     -- VTableWorldWF round-trip + upcast preservation
     (match VTableRegistry.empty.intern KeyedAllocWorld.empty kDebug vtDebug with
      | .ok (reg1, w1, idD) =>
        VTableWorldWF reg1 w1 ∧
        (∃ d, validateVTableHalf w1 reg1 (.provenanced idD 0) ⟨some 7, AutoTraitSet.empty, []⟩ = .ok d) ∧
        (match upcastVTableToAutoTraits reg1 w1 idD [.send] with
         | some (.ok (reg2, _, idUp)) =>
           ∃ dUp, reg2.allocToData.get? idUp = some dUp ∧ dUp.spec.principal = none ∧
             dUp.dropFnId = none ∧ dUp.sizeBytes = 4 ∧ dUp.alignPow2 = 2
         | _ => False)
      | .error _ => False) ∧
     -- SaltedVTableWorldWF round-trip + distinct salts produce distinct valid alloc IDs
     (match SaltedVTableRegistry.empty.internSalted KeyedAllocWorld.empty ⟨1, kSend⟩ vtSend with
      | .ok (sreg1, sw1, sid1) =>
        match sreg1.internSalted sw1 ⟨2, kSend⟩ vtSend with
        | .ok (sreg2, sw2, sid2) =>
          sid1 ≠ sid2 ∧
          (∃ d1, validateVTableHalf sw2 sreg2.toVTableRegistry (.provenanced sid1 0) ⟨none, AutoTraitSet.empty, []⟩ = .ok d1) ∧
          (∃ d2, validateVTableHalf sw2 sreg2.toVTableRegistry (.provenanced sid2 0) ⟨none, AutoTraitSet.empty, []⟩ = .ok d2)
        | .error _ => False
      | .error _ => False)) := by
  have hign := vtableMatchesExpectedSpec_ignores_autoTraits (some 7)
    (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList [.sync])
    [⟨10, 10, false⟩] [⟨99, 99, true⟩] [⟨88, 88, true⟩]
    (fun q hq => by simp at hq; rw [hq]) (fun q hq => by simp at hq; rw [hq])
  have hpermSpec : vtableMatchesExpectedSpec
      ⟨none, AutoTraitSet.empty, [⟨20, 20, false⟩, ⟨10, 10, false⟩]⟩
      ⟨none, AutoTraitSet.empty, [⟨10, 10, false⟩, ⟨20, 20, false⟩]⟩ = true := by
    have hp := vtableMatchesExpectedSpec_predicate_perm
      ⟨none, AutoTraitSet.empty, [⟨10, 10, false⟩, ⟨20, 20, false⟩]⟩
      ⟨none, AutoTraitSet.empty, [⟨10, 10, false⟩, ⟨20, 20, false⟩]⟩
      [⟨20, 20, false⟩, ⟨10, 10, false⟩] (List.Perm.swap _ _ [])
    simpa [vtableMatchesExpectedSpec] using hp
  dsimp only
  let vtSend := buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]
  let kSend := mkCanonicalVTableKey 42 none [.send]
  let kDebug := mkCanonicalVTableKey 42 (some 7) [.send]
  let vtDebug : VTableData :=
    { concreteTy := .uint 4, concreteTyCode := 42, dropFnId := none,
      sizeBytes := 4, alignPow2 := 2, spec := ⟨some 7, AutoTraitSet.ofList [.send], []⟩, methodSlots := [id10] }
  have hMatchSend : VTableDataMatchesKey kSend vtSend := ⟨rfl, rfl, rfl, rfl⟩
  have hMatchDebug : VTableDataMatchesKey kDebug vtDebug := ⟨rfl, rfl, rfl, rfl⟩
  have hOrphKeyWF : VTableRegistry.KeyWF
      { keyToAlloc := ExtTreeMap0.empty.insert (encodeVTableKeyCode kSend) id1
        allocToData := ExtTreeMap0.empty.insert id1 vtSend } := by
    refine ⟨?_, ?_⟩
    · intro k q hq
      by_cases heq : encodeVTableKeyCode k = encodeVTableKeyCode kSend
      · have hk := encodeVTableKeyCode_injective heq
        subst hk
        rw [ExtTreeMap0.get?_insert_self] at hq; injection hq with hq; subst hq
        exact ⟨vtSend, by simp [ExtTreeMap0.get?_insert_self], hMatchSend⟩
      · rw [ExtTreeMap0.get?_insert_ne _ _ heq, ExtTreeMap0.get?_empty] at hq; cases hq
    · intro i₁ d₁ i₂ d₂ h1 h2 _
      by_cases hi1 : i₁ = id1 <;> by_cases hi2 : i₂ = id1
      · subst hi1; subst hi2
        rw [ExtTreeMap0.get?_insert_self] at h1 h2
        injection h1 with h1; injection h2 with h2; subst h1; subst h2; exact ⟨rfl, rfl, rfl⟩
      · rw [ExtTreeMap0.get?_insert_ne _ _ hi2, ExtTreeMap0.get?_empty] at h2; cases h2
      · rw [ExtTreeMap0.get?_insert_ne _ _ hi1, ExtTreeMap0.get?_empty] at h1; cases h1
      · rw [ExtTreeMap0.get?_insert_ne _ _ hi1, ExtTreeMap0.get?_empty] at h1; cases h1
  have hOrphAllocWF : VTableRegistry.AllocWF
      { keyToAlloc := ExtTreeMap0.empty.insert (encodeVTableKeyCode kSend) id1
        allocToData := ExtTreeMap0.empty.insert id1 vtSend }
      (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩) := by
    refine ⟨fun q dq hq => ?_⟩
    by_cases hq1 : q = id1
    · subst hq1
      exact ⟨⟨.vtable, 24, 3, .not, []⟩,
        by simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_insert_self], rfl⟩
    · rw [ExtTreeMap0.get?_insert_ne _ _ hq1, ExtTreeMap0.get?_empty] at hq; cases hq
  have hValAuto := validateVTableHalf_principalLess_ignores_autoTraits
    (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩)
    { keyToAlloc := ExtTreeMap0.empty.insert (encodeVTableKeyCode kSend) id1
      allocToData := ExtTreeMap0.empty.insert id1 vtSend }
    id1 vtSend (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList [.sync])
    hOrphAllocWF (by simp [ExtTreeMap0.get?_insert_self]) rfl
  have hValMis := validateVTableHalf_principalLess_vs_principal_invalidTrait
    (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩)
    { keyToAlloc := ExtTreeMap0.empty.insert (encodeVTableKeyCode kSend) id1
      allocToData := ExtTreeMap0.empty.insert id1 vtSend }
    id1 vtSend (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList [.send]) 7
    hOrphAllocWF (by simp [ExtTreeMap0.get?_insert_self]) rfl
  have hWorldRoundTrip :
      match VTableRegistry.empty.intern KeyedAllocWorld.empty kDebug vtDebug with
      | .ok (reg1, w1, idD) =>
        VTableWorldWF reg1 w1 ∧
        (∃ d, validateVTableHalf w1 reg1 (.provenanced idD 0) ⟨some 7, AutoTraitSet.empty, []⟩ = .ok d) ∧
        (match upcastVTableToAutoTraits reg1 w1 idD [.send] with
         | some (.ok (reg2, _, idUp)) =>
           ∃ dUp, reg2.allocToData.get? idUp = some dUp ∧ dUp.spec.principal = none ∧
             dUp.dropFnId = none ∧ dUp.sizeBytes = 4 ∧ dUp.alignPow2 = 2
         | _ => False)
      | .error _ => False := by
    cases h1 : VTableRegistry.empty.intern KeyedAllocWorld.empty kDebug vtDebug with
    | error e =>
      simp [VTableRegistry.intern, VTableRegistry.empty, KeyedAllocWorld.reserveAllocId,
        KeyedAllocWorld.empty, KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?,
        KeyedAllocWorld.findDead?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_empty,
        KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?, MiriAllocId.ofUInt64] at h1
    | ok res =>
      rcases res with ⟨reg1, w1, idD⟩
      dsimp only
      have hrt := VTableWorldWF.intern_roundTrip VTableWorldWF.empty hMatchDebug
        (fun _ _ h => by simp [VTableRegistry.empty, ExtTreeMap0.get?_empty] at h) h1
      have hsrc : reg1.allocToData.get? idD = some vtDebug := by
        unfold VTableRegistry.intern at h1; dsimp only at h1
        simp [VTableRegistry.empty, ExtTreeMap0.get?_empty] at h1
        cases hres : KeyedAllocWorld.empty.reserveAllocId with
        | mk wTmp ores =>
          rw [hres] at h1
          cases ores with
          | error _ => cases h1
          | ok idNew =>
            simp only at h1; injection h1 with hp
            rcases Prod.mk.inj hp with ⟨rfl, hr⟩; rcases Prod.mk.inj hr with ⟨rfl, rfl⟩
            simp [ExtTreeMap0.get?_insert_self]
      refine ⟨hrt.1, hrt.2 ⟨some 7, AutoTraitSet.empty, []⟩ rfl, ?_⟩
      cases hup : upcastVTableToAutoTraits reg1 w1 idD [.send] with
      | none => simp [upcastVTableToAutoTraits, hsrc] at hup
      | some eres =>
        cases eres with
        | error e =>
          simp [upcastVTableToAutoTraits, hsrc, VTableRegistry.intern,
            KeyedAllocWorld.reserveAllocId, MiriAllocId.ofUInt64] at hup
          unfold VTableRegistry.intern at h1; dsimp only at h1
          simp [VTableRegistry.empty, KeyedAllocWorld.empty, KeyedAllocWorld.reserveAllocId,
            KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
            KeyedAllocWorld.findGlobal?, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
            ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty, MiriAllocId.ofUInt64] at h1
          rcases h1 with ⟨rfl, rfl, rfl⟩
          simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued, KeyedAllocWorld.containsId,
            KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?, KeyedAllocWorld.findGlobal?,
            ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert, ExtTreeMap0.get?_empty,
            kDebug, vtDebug, mkCanonicalVTableKey, encodeVTableKeyCode, cantorPair,
            AutoTraitSet.ofList, AutoTraitSet.mask, canonicalizeAutoTraits, AutoTrait.allTraits] at hup
        | ok res2 =>
          rcases res2 with ⟨reg2, w2, idUp⟩
          exact upcastVTableToAutoTraits_preserves_drop_size_align reg1 reg2 w1 w2 idD idUp vtDebug [.send]
            hrt.1.keyWF hsrc hup
  have hSalted :
      match SaltedVTableRegistry.empty.internSalted KeyedAllocWorld.empty ⟨1, kSend⟩ vtSend with
      | .ok (sreg1, sw1, sid1) =>
        match sreg1.internSalted sw1 ⟨2, kSend⟩ vtSend with
        | .ok (sreg2, sw2, sid2) =>
          sid1 ≠ sid2 ∧
          (∃ d1, validateVTableHalf sw2 sreg2.toVTableRegistry (.provenanced sid1 0) ⟨none, AutoTraitSet.empty, []⟩ = .ok d1) ∧
          (∃ d2, validateVTableHalf sw2 sreg2.toVTableRegistry (.provenanced sid2 0) ⟨none, AutoTraitSet.empty, []⟩ = .ok d2)
        | .error _ => False
      | .error _ => False := by
    cases h1 : SaltedVTableRegistry.empty.internSalted KeyedAllocWorld.empty ⟨1, kSend⟩ vtSend with
    | error _ =>
      simp [SaltedVTableRegistry.internSalted, SaltedVTableRegistry.empty, KeyedAllocWorld.reserveAllocId,
        KeyedAllocWorld.empty, KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?,
        KeyedAllocWorld.findDead?, KeyedAllocWorld.findGlobal?, ExtTreeMap0.get?_empty,
        KeyedAllocWorld.hasIssued, ExtTreeMap0.contains_eq_isSome_get?, MiriAllocId.ofUInt64] at h1
    | ok res1 =>
      rcases res1 with ⟨sreg1, sw1, sid1⟩
      dsimp only
      cases h2 : sreg1.internSalted sw1 ⟨2, kSend⟩ vtSend with
      | error _ =>
        unfold SaltedVTableRegistry.internSalted at h1 h2; dsimp only at h1 h2
        simp [SaltedVTableRegistry.empty, KeyedAllocWorld.empty, KeyedAllocWorld.reserveAllocId,
          KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
          KeyedAllocWorld.findGlobal?, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.hasIssued,
          ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_empty, MiriAllocId.ofUInt64] at h1
        rcases h1 with ⟨rfl, rfl, rfl⟩
        simp [KeyedAllocWorld.registerGlobal, KeyedAllocWorld.reserveAllocId, KeyedAllocWorld.hasIssued,
          KeyedAllocWorld.containsId, KeyedAllocWorld.findLive?, KeyedAllocWorld.findDead?,
          KeyedAllocWorld.findGlobal?, ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert,
          ExtTreeMap0.get?_empty, MiriAllocId.ofUInt64, encodeSaltedVTableKeyCode, encodeVTableKeyCode,
          cantorPair, kSend, mkCanonicalVTableKey, AutoTraitSet.ofList, AutoTraitSet.mask,
          canonicalizeAutoTraits, AutoTrait.allTraits] at h2
      | ok res2 =>
        rcases res2 with ⟨sreg2, sw2, sid2⟩
        dsimp only
        exact saltedVTable_distinct_salts_distinct_allocIds_both_valid
          SaltedVTableRegistry.empty sreg1 sreg2 KeyedAllocWorld.empty sw1 sw2
          1 2 kSend vtSend sid1 sid2 ⟨none, AutoTraitSet.empty, []⟩
          SaltedVTableWorldWF.empty hMatchSend (by decide) rfl h1 h2
  dsimp only [kDebug, vtDebug, kSend, vtSend] at hWorldRoundTrip hSalted
  exact ⟨hign, hpermSpec, hOrphKeyWF, hOrphAllocWF, rfl, hValAuto, hValMis, hWorldRoundTrip, hSalted⟩

theorem canary_part3C_wideDyn_vtable_precedence_and_mayDangle :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let vtUninhab := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 500 none 4 2 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtUninhab }
    let w : KeyedAllocWorld :=
      (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).insertLive id10 entryU32
    validateWideDynSafePtr w reg .null .null spec false false = .error .invalidVTableNull ∧
    validateWideDynSafePtr w reg (.danglingInt 16) (.danglingInt 0) spec false true =
      .error (.invalidVTableDanglingInt 16) ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) .null spec false true = .error .nullSafePointer ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.danglingInt 16) spec false false =
      .error (.danglingOrOutOfBoundsData 16) ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.maybeNull id2 0 0) spec false false =
      .error (.danglingOrOutOfBoundsData 0) ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.danglingInt 0) spec false true = .error .nullSafePointer ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.danglingInt (UInt64.ofNat (usizeMax64 - 4))) spec true true =
      .error (.addressTooClose 4) ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.danglingInt 16) spec true true = .ok vtUninhab ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id10 0 2) spec false true =
      .error (.unalignedSafePointer 4 2) ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id10 0 16) spec false false = .ok vtUninhab ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id10 0 16) spec false true =
      .error .uninhabitedPointee ∧
    validateRawWideDynPtrMeta w reg (.provenanced id1 0) .null spec true = .ok vtUninhab ∧
    validateRawPtrFastPath (.dynamic "Send") (.wideDyn 0 0) = .ok () ∧
    validateRawWideDynPtrMeta w reg .null .null spec = .error .invalidVTableNull := by
  dsimp only
  let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
  let vtUninhab := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 500 none 4 2 [.send]
  let reg : VTableRegistry :=
    { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtUninhab }
  let w : KeyedAllocWorld :=
    (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).insertLive id10 entryU32
  have hvtOk : validateVTableHalf w reg (.provenanced id1 0) spec = .ok vtUninhab := by
    have hmatch : vtableMatchesExpectedSpec vtUninhab.spec spec = true := rfl
    simp [w, reg, vtUninhab, spec, validateVTableHalf, KeyedAllocWorld.findGlobal?,
      KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, ExtTreeMap0.get?_insert_self, hmatch]
  have hlive : w.findLive? id10 = some entryU32 := by
    simp [w, KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]
  have hno2 : w.getAllocInfo id2 = none := by
    simp only [w, KeyedAllocWorld.getAllocInfo, KeyedAllocWorld.findLive?, KeyedAllocWorld.findGlobal?,
      KeyedAllocWorld.findDead?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal, KeyedAllocWorld.empty]
    rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id10), ExtTreeMap0.get?_empty,
        ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id1), ExtTreeMap0.get?_empty,
        ExtTreeMap0.get?_empty]
  have hdbl := wideDyn_doubleNull_separation w reg spec false false
  have hprec := wideDyn_invalidVTable_precedes_all_data_ub w reg (.danglingInt 16) (.danglingInt 0) spec false true
    (.invalidVTableDanglingInt 16) rfl
  have hnull := wideDyn_validVTable_nullData_reports_nullSafePointer w reg (.provenanced id1 0) spec vtUninhab false true
    hvtOk (by decide)
  have hdang := wideDyn_validVTable_dangling_and_unaligned w reg (.provenanced id1 0) spec vtUninhab id10 entryU32
    hvtOk rfl rfl hlive (by decide)
  have hmaybe := wideDyn_validVTable_maybeNull_dangling_precedes_null w reg (.provenanced id1 0) spec vtUninhab id2
    hvtOk (by decide) (fun info hinfo => by rw [hno2] at hinfo; cases hinfo)
  have hdzero := wideDyn_validVTable_danglingIntZero_reports_null w reg (.provenanced id1 0) spec vtUninhab true hvtOk
  have hclose := wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok w reg (.provenanced id1 0) spec vtUninhab
    hvtOk rfl rfl rfl
  have hunal := wideDyn_unaligned_precedes_concrete_uninhabited w reg (.provenanced id1 0) spec vtUninhab id10 entryU32
    hvtOk rfl rfl rfl hlive (by decide)
  have hraw := rawWideDyn_vtable_checked_data_unchecked w reg (.provenanced id1 0) .null spec true vtUninhab hvtOk
  have hshape := rawWideDyn_shapeCheck_misses_invalid_vtable w reg spec 0 .null
  exact ⟨hdbl, hprec, hnull, hdang.1, hmaybe, hdzero, hclose.1, hclose.2,
    hunal.2.1, hunal.2.2.1, hunal.2.2.2, hraw, hshape.1, hshape.2⟩

theorem canary_part3C_zstConcrete_neverDangles_and_provenanced_addressTooClose :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let vtZst := buildPrincipalLessVTable .unit 501 none 0 0 [.send]
    let vtU32 := buildPrincipalLessVTable (.uint 4) 502 none 4 2 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty,
        allocToData := (ExtTreeMap0.empty.insert id1 vtZst).insert id2 vtU32 }
    let w : KeyedAllocWorld :=
      ((KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).registerGlobal id2
        ⟨.vtable, 24, 3, .not, []⟩).insertDead id3 ⟨4, 2⟩
    validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id3 0 16) spec false false = .ok vtZst ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.maybeNull id10 77 16) spec false false = .ok vtZst ∧
    validateWideDynSafePtr w reg (.provenanced id1 0) (.maybeNull id3 0 0) spec false false =
      .error .nullSafePointer ∧
    validateWideDynSafePtr w reg (.provenanced id2 0) (.maybeNull id3 0 0) spec false false =
      .error (.danglingOrOutOfBoundsData 0) ∧
    validateWideDynSafePtr w reg (.provenanced id2 0)
      (.provenanced id3 0 (UInt64.ofNat (usizeMax64 - 4))) spec true false = .error (.addressTooClose 4) ∧
    validateWideDynSafePtr w reg (.provenanced id2 0)
      (.maybeNull id3 0 (UInt64.ofNat (usizeMax64 - 4))) spec true true = .error (.addressTooClose 4) ∧
    checkNestedSafeRefChildSession (.uint 4)
      [(0xFB, some id3), (0xFF, some id3), (0xFF, some id3), (0xFF, some id3),
       (0xFF, some id3), (0xFF, some id3), (0xFF, some id3), (0xFF, some id3)] =
      .error (.nestedAddressTooClose 4) ∧
    checkNestedSafeRefChildSession (.uint 4)
      [(0xFB, none), (0xFF, none), (0xFF, none), (0xFF, none),
       (0xFF, none), (0xFF, none), (0xFF, none), (0xFF, none)] =
      .error (.nestedAddressTooClose 4) := by
  dsimp only
  let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
  let vtZst := buildPrincipalLessVTable .unit 501 none 0 0 [.send]
  let vtU32 := buildPrincipalLessVTable (.uint 4) 502 none 4 2 [.send]
  let reg : VTableRegistry :=
    { keyToAlloc := ExtTreeMap0.empty,
      allocToData := (ExtTreeMap0.empty.insert id1 vtZst).insert id2 vtU32 }
  let w : KeyedAllocWorld :=
    ((KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).registerGlobal id2
      ⟨.vtable, 24, 3, .not, []⟩).insertDead id3 ⟨4, 2⟩
  have hvtZst : validateVTableHalf w reg (.provenanced id1 0) spec = .ok vtZst := by
    have hmatch : vtableMatchesExpectedSpec vtZst.spec spec = true := rfl
    have hg : w.findGlobal? id1 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp only [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id2), ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id1 = some vtZst := by
      simp only [reg]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id2), ExtTreeMap0.get?_insert_self]
    simp [validateVTableHalf, hg, hd, hmatch]
  have hvtU32 : validateVTableHalf w reg (.provenanced id2 0) spec = .ok vtU32 := by
    have hmatch : vtableMatchesExpectedSpec vtU32.spec spec = true := rfl
    have hg : w.findGlobal? id2 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
        ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id2 = some vtU32 := by
      simp [reg, ExtTreeMap0.get?_insert_self]
    simp [validateVTableHalf, hg, hd, hmatch]
  have hdeadInfo : w.getAllocInfo id3 = some ⟨4, 2, .dead, .not⟩ := by
    have hnotLive : w.findLive? id3 = none := by
      simp [w, KeyedAllocWorld.findLive?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
        KeyedAllocWorld.empty, ExtTreeMap0.get?_empty]
    have hnotGlobal : w.findGlobal? id3 = none := by
      simp only [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertDead, KeyedAllocWorld.registerGlobal,
        KeyedAllocWorld.empty]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id3 ≠ id2),
        ExtTreeMap0.get?_insert_ne _ _ (by decide : id3 ≠ id1), ExtTreeMap0.get?_empty]
    have hdead : w.findDead? id3 = some ⟨4, 2⟩ := by
      simp [w, KeyedAllocWorld.findDead?, KeyedAllocWorld.insertDead, ExtTreeMap0.get?_insert_self]
    exact ((keyedGetAllocInfo_dead_and_unavailable w id3 hnotLive hnotGlobal).1 ⟨4, 2⟩ hdead).1
  have hzst1 := wideDyn_zstConcrete_never_dangles w reg (.provenanced id1 0) spec vtZst id3 0 16
    hvtZst rfl rfl (by decide)
  have hzst2 := wideDyn_zstConcrete_never_dangles w reg (.provenanced id1 0) spec vtZst id10 77 16
    hvtZst rfl rfl (by decide)
  have hmaybe := wideDyn_validVTable_maybeNull_dangling_precedes_null w reg (.provenanced id2 0) spec vtU32 id3
    hvtU32 (by decide) (fun info hinfo => by
      rw [hdeadInfo] at hinfo
      injection hinfo with hinfo
      subst hinfo
      rfl)
  have hclose1 := wideDyn_mayDangle_provenanced_addressTooClose w reg (.provenanced id2 0) spec vtU32 id3 0 false
    hvtU32 rfl
  have hclose2 := wideDyn_mayDangle_provenanced_addressTooClose w reg (.provenanced id2 0) spec vtU32 id3 0 true
    hvtU32 rfl
  exact ⟨hzst1.1, hzst2.2.1, hzst1.2.2, hmaybe, hclose1.1, hclose2.2,
    checkNestedSafeRefChildSession_addressTooClose_ignores_provenance (some id3),
    checkNestedSafeRefChildSession_addressTooClose_ignores_provenance none⟩

theorem canary_part3C_unified_validateRawPtrFull :
    let resolve : String → DynExistentialSpec := fun _ => ⟨none, AutoTraitSet.ofList [.send], []⟩
    let vtSend := buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]
    let reg : VTableRegistry := { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtSend }
    let w : KeyedAllocWorld := KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩
    (unsizedDynTailTrait? (.adt "MyDynDst" [.uint 4, .dynamic "Send"])).isSome =
      (unsizedMetadataTail (.adt "MyDynDst" [.uint 4, .dynamic "Send"]) == some .dynVTable) ∧
    (fieldsUnsizedDynTailTrait? [.uint 4, .dynamic "Send"]).isSome =
      (fieldsUnsizedMetadataTail [.uint 4, .dynamic "Send"] == some .dynVTable) ∧
    validateRawPtrFull w reg resolve (.array (.uint 1) usizeMax64) (.thin 4096) = .ok () ∧
    validateRawPtrFull w reg resolve (.adt "OverflowDst" [.array (.uint 1) usizeMax64, .dynamic "Send"])
      (.wideDyn .null .null) = .error (.shapeOrLayout (.layoutFailed .layoutOverflow)) ∧
    validateRawPtrFull w reg resolve (.adt "MyDynDst" [.uint 4, .dynamic "Send"])
      (.wideDyn .null (.provenanced id1 0)) = .ok () ∧
    validateRawPtrFull w reg resolve (.adt "MyDynDst" [.uint 4, .dynamic "Send"])
      (.wideDyn .null .null) = .error (.vtableInvalid .invalidVTableNull) := by
  dsimp only
  let resolve : String → DynExistentialSpec := fun _ => ⟨none, AutoTraitSet.ofList [.send], []⟩
  let vtSend := buildPrincipalLessVTable (.uint 4) 42 none 4 2 [.send]
  let reg : VTableRegistry := { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtSend }
  let w : KeyedAllocWorld := KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩
  have h1 := unsizedDynTailTrait?_isSome_eq_dynMeta (.adt "MyDynDst" [.uint 4, .dynamic "Send"])
  have h2 := fieldsDynTailTrait?_isSome_eq_dynMeta [.uint 4, .dynamic "Send"]
  have h3 := validateRawPtrFull_sized_skips_layout_and_vtable w reg resolve (.array (.uint 1) usizeMax64) 4096 rfl
  have hcustOk := validateRawPtrFull_customDynDst_layout_and_vtable_soundness w reg resolve "Send" .null (.provenanced id1 0)
  have hcustErr := validateRawPtrFull_customDynDst_layout_and_vtable_soundness w reg resolve "Send" .null .null
  have hvtOk : validateVTableHalf w reg (.provenanced id1 0) (resolve "Send") = .ok vtSend := by
    have hmatch : vtableMatchesExpectedSpec vtSend.spec (resolve "Send") = true := rfl
    simp [w, reg, vtSend, resolve, validateVTableHalf, KeyedAllocWorld.findGlobal?,
      KeyedAllocWorld.registerGlobal, ExtTreeMap0.get?_insert_self, hmatch]
  exact ⟨h1, h2, h3, hcustErr.1, hcustOk.2.1 vtSend hvtOk, hcustErr.2.2 .invalidVTableNull rfl⟩

theorem canary_part3C_recursive_pointee_bytes :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let idVtBool : MiriAllocId := ⟨1, by decide⟩
    let idVtRefU32 : MiriAllocId := ⟨2, by decide⟩
    let idVtRefNever : MiriAllocId := ⟨3, by decide⟩
    let idVtDeep : MiriAllocId := ⟨7, by decide⟩
    let vtBool := buildPrincipalLessVTable .bool 101 none 1 0 [.send]
    let vtRefU32 := buildPrincipalLessVTable (.ref false (.uint 4)) 102 none 8 3 [.send]
    let vtRefNever := buildPrincipalLessVTable (.ref false .never) 103 none 8 3 [.send]
    let reg1 : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := ((ExtTreeMap0.empty.insert idVtBool vtBool).insert idVtRefU32 vtRefU32).insert idVtRefNever vtRefNever }
    let wBase1 : KeyedAllocWorld :=
      ((KeyedAllocWorld.empty.registerGlobal idVtBool ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtRefU32 ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtRefNever ⟨.vtable, 24, 3, .not, []⟩
    let wDanglingRef := wBase1.insertLive id10 ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 16⟩
    validateWideDynSafePtrWithBytes wDanglingRef reg1 (.provenanced idVtRefU32 0) (.provenanced id10 0 16) spec false true =
      .ok vtRefU32 ∧
    (let vtChar := buildPrincipalLessVTable .char 202 none 4 2 [.send]
     let idVtPair : MiriAllocId := ⟨1, by decide⟩
     let idVtChar : MiriAllocId := ⟨2, by decide⟩
     let idVtFn : MiriAllocId := ⟨3, by decide⟩
     let idVtUninhab : MiriAllocId := ⟨4, by decide⟩
     let vtPair := buildPrincipalLessVTable (.tuple [.uint 1, .bool]) 201 none 2 0 [.send]
     let vtFn := buildPrincipalLessVTable .fnPtr 203 none 8 3 [.send]
     let vtUninhab := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 204 none 4 2 [.send]
     let reg2 : VTableRegistry :=
       { keyToAlloc := ExtTreeMap0.empty
         allocToData := (((ExtTreeMap0.empty.insert idVtPair vtPair).insert idVtChar vtChar).insert idVtFn vtFn).insert idVtUninhab vtUninhab }
     let wBase2 : KeyedAllocWorld :=
       (((KeyedAllocWorld.empty.registerGlobal idVtPair ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtChar ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtFn ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtUninhab ⟨.vtable, 24, 3, .not, []⟩
     let wCharSurr := wBase2.insertLive id10 ⟨4, 2, .stack, .mut, encodeLeUInt32Bytes 0xD800⟩
     validateWideDynSafePtrWithBytes wCharSurr reg2 (.provenanced idVtChar 0) (.provenanced id10 0 16) spec false true =
       .error (.pointeeErr (.invalidCharScalar 0xD800))) ∧
    (let idVtBoolNever : MiriAllocId := ⟨1, by decide⟩
     let idVtU32Never : MiriAllocId := ⟨2, by decide⟩
     let idVtFn : MiriAllocId := ⟨3, by decide⟩
     let idVtZstUnitArr : MiriAllocId := ⟨4, by decide⟩
     let idVtZstNeverEmpty : MiriAllocId := ⟨5, by decide⟩
     let idVtZstNeverBig : MiriAllocId := ⟨6, by decide⟩
     let vtBoolNever := buildPrincipalLessVTable (.tuple [.bool, .never]) 301 none 1 0 [.send]
     let vtU32Never := buildPrincipalLessVTable (.tuple [.uint 4, .never]) 302 none 4 2 [.send]
     let vtFn := buildPrincipalLessVTable .fnPtr 303 none 8 3 [.send]
     let vtZstUnitArr := buildPrincipalLessVTable (.array .unit usizeMax64) 304 none 0 0 [.send]
     let vtZstNeverEmpty := buildPrincipalLessVTable (.array .never 0) 305 none 0 0 [.send]
     let vtZstNeverBig := buildPrincipalLessVTable (.array .never usizeMax64) 306 none 0 0 [.send]
     let vtDeep := buildPrincipalLessVTable (nestSingleElemArray 64 .bool) 307 none 1 0 [.send]
     let reg3 : VTableRegistry :=
       { keyToAlloc := ExtTreeMap0.empty
         allocToData := ((((((ExtTreeMap0.empty.insert idVtBoolNever vtBoolNever).insert idVtU32Never vtU32Never).insert idVtFn vtFn).insert idVtZstUnitArr vtZstUnitArr).insert idVtZstNeverEmpty vtZstNeverEmpty).insert idVtZstNeverBig vtZstNeverBig).insert idVtDeep vtDeep }
     let wBase3 : KeyedAllocWorld :=
       ((((((KeyedAllocWorld.empty.registerGlobal idVtBoolNever ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtU32Never ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtFn ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstUnitArr ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstNeverEmpty ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtZstNeverBig ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtDeep ⟨.vtable, 24, 3, .not, []⟩
     let wDeepBool := wBase3.insertLive id10 ⟨1, 0, .stack, .mut, [.init 1 none]⟩
     validateWideDynSafePtrWithBytes wDeepBool reg3 (.provenanced idVtDeep 0) (.provenanced id10 0 16) spec false true 64 =
       .error (.pointeeErr .traversalFuelExhausted)) := by
  exact ⟨wideDyn_recursive_bytes_and_childSession_mayDangle.2.2.2.2.2.2,
    wideDyn_recursive_aggregate_char_fnPtr_contents.2.2.2.1,
    wideDyn_recursive_fieldOrder_nullProvFn_zstArray_and_fuel.2.2.2.2.2.2⟩

theorem canary_part3C_widePtrLayout_malformedAlign_unsizedNestedRef_and_staticBytes :
    computeTyLayout (.ref false (.uint 4)) = .ok ⟨8, 8, true, true, none⟩ ∧
    computeTyLayout (.ref false (.slice (.uint 4))) = .ok ⟨16, 8, true, true, none⟩ ∧
    computeTyLayout (.rawPtr false (.dynamic "Send")) = .ok ⟨16, 8, true, true, none⟩ ∧
    checkNestedSafeRefChildSession (.slice (.uint 4)) (List.replicate 8 (16, none)) =
      .error (.layoutErr .unsizedField) ∧
    checkNestedSafeRefChildSession (.dynamic "Send") (List.replicate 8 (16, none)) =
      .error (.layoutErr .unsizedField) ∧
    (let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
     let vtBad64 := buildPrincipalLessVTable (.uint 4) 601 none 4 64 [.send]
     let vtBad30 := buildPrincipalLessVTable (.uint 4) 602 none 4 30 [.send]
     let vtBadLay := buildPrincipalLessVTable (.uint 3) 603 none 4 2 [.send]
     let reg : VTableRegistry :=
       { keyToAlloc := ExtTreeMap0.empty
         allocToData := ((ExtTreeMap0.empty.insert id1 vtBad64).insert id2 vtBad30).insert id3 vtBadLay }
     let w : KeyedAllocWorld :=
       (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩)
         |>.registerGlobal id2 ⟨.vtable, 24, 3, .not, []⟩)
         |>.registerGlobal id3 ⟨.vtable, 24, 3, .not, []⟩)
         |>.insertLive id10 entryU32
     validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id10 0 16) spec false false =
       .error (.malformedVTableAlign 64) ∧
     validateWideDynSafePtr w reg (.provenanced id2 0) (.provenanced id10 0 16) spec false false =
       .error (.malformedVTableAlign 30) ∧
     validateWideDynSafePtr w reg (.provenanced id3 0) (.provenanced id10 0 16) spec false true =
       .error (.pointeeErr (.layoutErr (.invalidScalarSize 3)))) ∧
    (let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
     let idVtBool : MiriAllocId := ⟨1, by decide⟩
     let idStaticOk : MiriAllocId := ⟨20, by decide⟩
     let idStaticBad : MiriAllocId := ⟨21, by decide⟩
     let idMemUninit : MiriAllocId := ⟨22, by decide⟩
     let vtBool := buildPrincipalLessVTable .bool 401 none 1 0 [.send]
     let reg : VTableRegistry :=
       { keyToAlloc := ExtTreeMap0.empty
         allocToData := ExtTreeMap0.empty.insert idVtBool vtBool }
     let w : KeyedAllocWorld :=
       (((KeyedAllocWorld.empty.registerGlobal idVtBool ⟨.vtable, 24, 3, .not, []⟩)
         |>.registerGlobal idStaticOk ⟨.static, 1, 0, .not, [.init 1 none]⟩)
         |>.registerGlobal idStaticBad ⟨.static, 1, 0, .not, [.init 2 none]⟩)
         |>.registerGlobal idMemUninit ⟨.memory, 1, 0, .not, [.uninit]⟩
     validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idStaticOk 0 16) spec false true =
       .ok vtBool ∧
     validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idStaticBad 0 16) spec false true =
       .error (.pointeeErr (.invalidBoolScalar 2)) ∧
     validateWideDynSafePtrWithBytes w reg (.provenanced idVtBool 0) (.provenanced idMemUninit 0 16) spec false true =
       .error (.pointeeErr .uninitPointeeByte)) := by
  have hwp := computeTyLayout_widePtr_vs_thinPtr_size
  have huns := checkNestedSafeRefChildSession_unsizedInner_rejected (List.replicate 8 (16, none))
  have hst := wideDyn_recursive_staticGlobal_bytes_validated
  let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
  let vtBad64 := buildPrincipalLessVTable (.uint 4) 601 none 4 64 [.send]
  let vtBad30 := buildPrincipalLessVTable (.uint 4) 602 none 4 30 [.send]
  let vtBadLay := buildPrincipalLessVTable (.uint 3) 603 none 4 2 [.send]
  let reg : VTableRegistry :=
    { keyToAlloc := ExtTreeMap0.empty
      allocToData := ((ExtTreeMap0.empty.insert id1 vtBad64).insert id2 vtBad30).insert id3 vtBadLay }
  let w : KeyedAllocWorld :=
    (((KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩)
      |>.registerGlobal id2 ⟨.vtable, 24, 3, .not, []⟩)
      |>.registerGlobal id3 ⟨.vtable, 24, 3, .not, []⟩)
      |>.insertLive id10 entryU32
  have hlive10 : w.findLive? id10 = some entryU32 := by
    simp [w, KeyedAllocWorld.findLive?, KeyedAllocWorld.insertLive, ExtTreeMap0.get?_insert_self]
  have hvt1 : validateVTableHalf w reg (.provenanced id1 0) spec = .ok vtBad64 := by
    have hg : w.findGlobal? id1 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp only [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id3),
        ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id2), ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id1 = some vtBad64 := by
      simp only [reg]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id3),
        ExtTreeMap0.get?_insert_ne _ _ (by decide : id1 ≠ id2), ExtTreeMap0.get?_insert_self]
    have hm : vtableMatchesExpectedSpec vtBad64.spec spec = true := rfl
    simp [validateVTableHalf, hg, hd, hm]
  have hvt2 : validateVTableHalf w reg (.provenanced id2 0) spec = .ok vtBad30 := by
    have hg : w.findGlobal? id2 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp only [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id3), ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id2 = some vtBad30 := by
      simp only [reg]
      rw [ExtTreeMap0.get?_insert_ne _ _ (by decide : id2 ≠ id3), ExtTreeMap0.get?_insert_self]
    have hm : vtableMatchesExpectedSpec vtBad30.spec spec = true := rfl
    simp [validateVTableHalf, hg, hd, hm]
  have hvt3 : validateVTableHalf w reg (.provenanced id3 0) spec = .ok vtBadLay := by
    have hg : w.findGlobal? id3 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal,
        ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id3 = some vtBadLay := by
      simp [reg, ExtTreeMap0.get?_insert_self]
    have hm : vtableMatchesExpectedSpec vtBadLay.spec spec = true := rfl
    simp [validateVTableHalf, hg, hd, hm]
  have hfc1 := (wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed w reg (.provenanced id1 0) spec
    vtBad64 vtBad30 vtBadLay id10 entryU32 hlive10 (by decide)).1 hvt1 rfl rfl
  have hfc2 := (wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed w reg (.provenanced id2 0) spec
    vtBad64 vtBad30 vtBadLay id10 entryU32 hlive10 (by decide)).2.1 hvt2 rfl rfl
  have hfc3 := (wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed w reg (.provenanced id3 0) spec
    vtBad64 vtBad30 vtBadLay id10 entryU32 hlive10 (by decide)).2.2 hvt3 rfl rfl rfl
  exact ⟨hwp.1, hwp.2.2.2.1, hwp.2.2.2.2.2.2.2, huns.1, huns.2, ⟨hfc1, hfc2, hfc3⟩,
    ⟨hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2⟩⟩

/-! ## Section 3D: Model 4 / Model 5 Retag Canaries and Nested Wide-Pointer Canaries -/

private theorem ok_of_isOk {ε α : Type} {x : Except ε α} (h : x.isOk = true) : ∃ r, x = .ok r := by
  cases x with
  | ok r => exact ⟨r, rfl⟩
  | error e => cases h

private def isReservedIMInvariantFailure {α : Type} : Except RetagStepErr α → Bool
  | .error (.protectedReservedIMInvariant _) => true
  | _ => false

private def disabledSubtreeWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 4, none, true⟩,
    ⟨1, some 0, .unique, 0, 4, none, true⟩,
    ⟨2, some 0, .disabled, 0, 4, none, true⟩,
    ⟨3, some 2, .cell, 0, 4, none, true⟩,
    ⟨4, some 3, .unique, 0, 4, some 7, true⟩
  ]
  activeProtectors := [7]
  nextTag := 5
  nextProtector := 10

private def frozenSubtreeWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 4, none, true⟩,
    ⟨1, some 0, .unique, 0, 4, none, true⟩,
    ⟨2, some 0, .frozen, 0, 4, none, true⟩,
    ⟨3, some 2, .unique, 0, 4, some 7, true⟩
  ]
  activeProtectors := [7]
  nextTag := 4
  nextProtector := 10

private def protectedReservedIMWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 4, none, true⟩,
    ⟨1, some 0, .unique, 0, 4, none, true⟩,
    ⟨2, some 0, .reservedIM, 0, 4, some 7, true⟩
  ]
  activeProtectors := [7]
  nextTag := 3
  nextProtector := 10

theorem canary_part2A_upstream_childPerms_and_sharedScope :
    (MiriRetagPolicyMirror.create ⟨true, true, false⟩ .mutable .fnEntry ⟨true, false⟩).map
        (fun p => (p.freezePermission, p.nonfreezePermission, p.outsidePermission, p.protector)) =
      some (.unique, .unique, .reservedFrz false, some .strongProtector) ∧
    (MiriRetagPolicyMirror.create ⟨true, true, true⟩ .box .fnEntry ⟨true, true⟩).map
        (fun p => (p.freezePermission, p.nonfreezePermission, p.outsidePermission, p.protector)) =
      some (.reservedFrz false, .reservedFrz false, .reservedFrz false, some .weakProtector) ∧
    selectFnEntryPolicy ⟨true, true, false⟩ .shared ⟨true, false⟩ = .rustcNoWritable ∧
    (MiriRetagPolicyMirror.create ⟨true, true, false⟩ .shared .fnEntry ⟨true, false⟩).map
        (fun p => (p.freezePermission, p.nonfreezePermission, p.outsidePermission, p.protector)) =
      some (.frozen, .cell, .cell, some .strongProtector) := by
  have h1 := fnEntry_mutOrBox_childPerms_eq_upstream_create ⟨true, true, false⟩ .mutable ⟨true, false⟩
    (by decide)
  have h2 := fnEntry_mutOrBox_childPerms_eq_upstream_create ⟨true, true, true⟩ .box ⟨true, true⟩
    (by decide)
  have h3 := fnEntry_shared_childPerms_outside_mut_models ⟨true, true, false⟩ ⟨true, false⟩
  exact ⟨h1, h2, h3.1, h3.2⟩

theorem canary_part2A_pruned_inversion_frozen_refinement_and_reservedIM :
    (∃ w' c, execFnEntryMutRetagPrunedSourceOrder frozenSubtreeWorld 1 0 4 .rustcNoWritable false =
        .ok (w', c) ∧
      ∃ n' ∈ w'.nodes, n' = ⟨2, some 0, .frozen, 0, 4, none, true⟩) ∧
    (∃ w' c, execFnEntryMutRetagPrunedSourceOrder disabledSubtreeWorld 1 0 4 .writableChildWrite false =
        .ok (w', c) ∧
      c = 5 ∧ w'.activeProtectors = [10, 7] ∧ w'.nextTag = 6 ∧
      ∃ nodes', w'.nodes = ⟨5, some 1, .unique, 0, 4, some 10, true⟩ :: nodes') ∧
    (∃ w4, execFnEntryMutRetagPrunedSourceOrder multiLevelBorrowWorld 2 0 4 .writableChildWrite false =
        .ok (w4, 10) ∧
      w4.nodes.length = 5 ∧ w4.nextProtector = 101) ∧
    isReservedIMInvariantFailure
      (execFnEntryMutRetagPrunedSourceOrder frozenSubtreeWorld 1 0 4 .writableChildWrite false) = false ∧
    execFnEntryMutRetagPrunedSourceOrder protectedReservedIMWorld 1 0 4 .rustcNoWritable false =
      .error (.protectedReservedIMInvariant 2) := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · obtain ⟨⟨w', c⟩, hok⟩ := ok_of_isOk
      (rfl : (execFnEntryMutRetagPrunedSourceOrder frozenSubtreeWorld 1 0 4 .rustcNoWritable false).isOk = true)
    obtain ⟨n', hn', _, _, _, hsame⟩ :=
      prunedSourceOrder_rustcNoWritable_preserves_all_frozen_nodes frozenSubtreeWorld w' 1 0 4 c false hok
        ⟨2, some 0, .frozen, 0, 4, none, true⟩ (by decide) rfl
    exact ⟨w', c, hok, n', hn', hsame rfl⟩
  · obtain ⟨⟨w', c⟩, hok⟩ := ok_of_isOk
      (rfl : (execFnEntryMutRetagPrunedSourceOrder disabledSubtreeWorld 1 0 4 .writableChildWrite false).isOk = true)
    obtain ⟨_, _, hc, hprot, hnt, _, nodes', hnodes, _⟩ :=
      execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_inv disabledSubtreeWorld w' 1 0 4 c false
        (by decide) hok
    exact ⟨w', c, hok, hc, hprot, hnt, nodes', hnodes⟩
  · obtain ⟨⟨w3, c3⟩, h3⟩ := ok_of_isOk
      (rfl : (execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 .writableChildWrite false).isOk = true)
    obtain ⟨w4, h4, _, _, _, _, _⟩ :=
      execFnEntryMutRetagSourceOrder_ok_imp_prunedSourceOrder_ok multiLevelBorrowWorld w3 2 0 4 c3
        .writableChildWrite false h3
    obtain ⟨_, _, hc, _, _, hnp, nodes', hnodes, hrel⟩ :=
      execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_inv multiLevelBorrowWorld w4 2 0 4 c3 false
        (by decide) h4
    subst hc
    refine ⟨w4, h4, ?_, hnp⟩
    rw [hnodes, List.length_cons, ListRel.length_eq hrel]
    rfl
  · have hwf : NoProtectedReservedIM frozenSubtreeWorld := by
      intro n hn hperm
      simp only [frozenSubtreeWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> cases hperm
    have hne := prunedSourceOrder_never_reservedIMInvariant_of_noProtectedReservedIM frozenSubtreeWorld hwf
      1 0 4 .writableChildWrite false
    cases hr : execFnEntryMutRetagPrunedSourceOrder frozenSubtreeWorld 1 0 4 .writableChildWrite false with
    | ok r => rfl
    | error e =>
      cases e with
      | protectedReservedIMInvariant t => exact absurd hr (hne t)
      | _ => rfl

private def twoProtectedSiblingsWorld : FnEntryBorrowWorld where
  nodes := [
    ⟨0, none, .unique, 0, 4, none, true⟩,
    ⟨1, some 0, .unique, 0, 4, none, true⟩,
    ⟨2, some 0, .unique, 0, 4, some 7, true⟩,
    ⟨3, some 0, .unique, 0, 4, some 8, true⟩
  ]
  activeProtectors := [7, 8]
  nextTag := 4
  nextProtector := 10

theorem canary_part2A_traversalOrder_foreign_error_attribution :
    (foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
        twoProtectedSiblingsWorld 1 true 0 4).map (·.tag) = [3, 2] ∧
    execFnEntryMutRetagPrunedSourceOrder twoProtectedSiblingsWorld 1 0 4 .writableChildWrite =
      .error (.protectedForeignConflict 2) ∧
    execFnEntryMutRetagTraversalOrder (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
        twoProtectedSiblingsWorld 1 0 4 .writableChildWrite = .error (.protectedForeignConflict 3) ∧
    execFnEntryMutRetagTraversalOrder (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
        twoProtectedSiblingsWorld 1 0 4 .rustcNoWritable = .error (.protectedForeignConflict 3) ∧
    (∃ n ∈ foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
        twoProtectedSiblingsWorld 1 true 0 4,
      n.isProtected twoProtectedSiblingsWorld.activeProtectors = true ∧ n.tag = 3) ∧
    (∃ r, execFnEntryMutRetagTraversalOrder (childTagsInListOrder disabledSubtreeWorld.nodes)
        disabledSubtreeWorld 1 0 4 .writableChildWrite false = .ok r ∧ r.2 = 5) := by
  have hsep := execFnEntryMutRetagTraversalOrder_foreignErrorTag_separation
  refine ⟨hsep.1, hsep.2.1, hsep.2.2.1, hsep.2.2.2.2, ?_, ?_⟩
  · rcases execFnEntryMutRetagTraversalOrder_error_cases
        (childTagsInListOrder twoProtectedSiblingsWorld.nodes) twoProtectedSiblingsWorld 1 0 4
        .writableChildWrite false _ hsep.2.2.1 with h4 | ⟨_, n, hn, hprot, he⟩
    · have h2 : execFnEntryMutRetagPrunedSourceOrder twoProtectedSiblingsWorld 1 0 4 .writableChildWrite false =
          .error (.protectedForeignConflict 2) := hsep.2.1
      rw [h2] at h4
      simp at h4
    · rcases he with he | he
      · injection he with ht
        exact ⟨n, hn, hprot, ht.symm⟩
      · cases he
  · obtain ⟨⟨w', c⟩, hok⟩ := ok_of_isOk
      (rfl : (execFnEntryMutRetagPrunedSourceOrder disabledSubtreeWorld 1 0 4 .writableChildWrite false).isOk = true)
    have h5 := (execFnEntryMutRetagTraversalOrder_ok_iff_prunedSourceOrder_ok
      (childTagsInListOrder disabledSubtreeWorld.nodes) disabledSubtreeWorld 1 0 4 .writableChildWrite false
      (w', c)).2 hok
    obtain ⟨_, _, hc, _⟩ :=
      execFnEntryMutRetagPrunedSourceOrder_writableChildWrite_ok_inv disabledSubtreeWorld w' 1 0 4 c false
        (by decide) hok
    exact ⟨(w', c), h5, hc⟩

theorem canary_part3_isizeMax_access_gate_and_vtable_layout_consistency :
    KeyedAllocWorld.empty.checkPtrAccess none 9223372036854775808 = false ∧
    (KeyedAllocWorld.empty.insertLive id10 ⟨18446744073709551615, 0, .heap, .mut, []⟩).checkPtrAccess
      (some (id10, 0)) 9223372036854775807 = true ∧
    (KeyedAllocWorld.empty.insertLive id10 ⟨18446744073709551615, 0, .heap, .mut, []⟩).checkPtrAccess
      (some (id10, 0)) 9223372036854775808 = false ∧
    (∃ lay, computeTyLayout (.uint 4) = .ok lay ∧ lay.sizeBytes = 4 ∧ lay.alignBytes = 4) ∧
    (buildPrincipalLessVTable (.uint 8) 504 none 0 0 [.send]).layoutConsistent = false ∧
    validateWideDynSafePtrDeep KeyedAllocWorld.empty VTableRegistry.empty
      (fun _ => ⟨none, AutoTraitSet.empty, []⟩) (fun _ => none) .null .null
      ⟨none, AutoTraitSet.empty, []⟩ true true = .error .invalidVTableNull := by
  have hgate := checkPtrAccess_size_exceeding_isizeMax_rejected KeyedAllocWorld.empty none
    9223372036854775808 (by decide)
  have hlive : (KeyedAllocWorld.empty.insertLive id10 ⟨18446744073709551615, 0, .heap, .mut, []⟩).findLive?
      id10 = some ⟨18446744073709551615, 0, .heap, .mut, []⟩ := by
    simp [KeyedAllocWorld.insertLive, KeyedAllocWorld.findLive?, ExtTreeMap0.get?_insert_self]
  have hbound := checkPtrAccess_isizeMax_boundary
    (KeyedAllocWorld.empty.insertLive id10 ⟨18446744073709551615, 0, .heap, .mut, []⟩) id10
    ⟨18446744073709551615, 0, .heap, .mut, []⟩ hlive rfl
  obtain ⟨lay, hl, _, hs, ha, _, _⟩ := VTableData.layoutConsistent_spec
    (buildPrincipalLessVTable (.uint 4) 502 none 4 2 [.send]) rfl
  have hdeep := (validateWideDynSafePtrDeep_nonrecursive_eq_root KeyedAllocWorld.empty VTableRegistry.empty
    (fun _ => ⟨none, AutoTraitSet.empty, []⟩) (fun _ => none) .null .null
    ⟨none, AutoTraitSet.empty, []⟩ true true 64 rfl (fun _ h => by cases h)).trans
    (wideDyn_doubleNull_separation KeyedAllocWorld.empty VTableRegistry.empty
      ⟨none, AutoTraitSet.empty, []⟩ true false)
  exact ⟨hgate, hbound.1, hbound.2, ⟨lay, hl, hs.symm, ha.symm⟩, rfl, hdeep⟩

theorem canary_part3C_nested_wide_pointer_validation :
    checkNestedWideSafeRefChildSession (fun _ _ => .ok (0, 1)) (.slice (.uint 4))
      [(16, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
       (2, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none)] = .ok () ∧
    checkNestedWideSafeRefChildSession (fun _ _ => .ok (0, 1)) (.slice (.uint 4))
      [(16, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
       (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0x40, none)] =
      .error .nestedSliceTooBig ∧
    checkNestedWideSafeRefChildSession (fun _ _ => .error .nestedInvalidVTable) (.dynamic "Send")
      (List.replicate 16 (0, none)) = .error .nestedInvalidVTable ∧
    checkNestedWideSafeRefChildSession (fun _ _ => .ok (4, 4)) (.dynamic "Send")
      [(66, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
       (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none)] =
      .error (.nestedUnalignedSafeRef 4 66) ∧
    visitConcreteValue 1 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0 (.rawPtr false (.dynamic "Send"))
      (fun _ _ => .error .nestedInvalidVTable) = .error .nestedInvalidVTable ∧
    visitConcreteValue 1 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0 (.rawPtr false (.dynamic "Send"))
      (fun _ _ => .ok (4, 4)) = .ok () ∧
    visitConcreteValue 1 (encodeLeUInt64Bytes 16) 0 (.ref false (.slice (.uint 4))) =
      .error .outOfBoundsPointeeRead ∧
    visitConcreteValue 4 (encodeLeUInt64Bytes 16 ++ encodeLeUInt64Bytes 2) 0
      (.ref false (.slice (.uint 4))) = .ok () ∧
    visitConcreteValue 4 (encodeLeUInt64Bytes 16 ++ List.replicate 8 MemByte.uninit) 0
      (.ref false (.slice (.uint 4))) = .error .uninitPointeeByte ∧
    visitConcreteValue 4 (encodeLeUInt64Bytes 16 ++ encodeLeUInt64Bytes 32) 0
      (.ref false (.dynamic "Send")) = .error .nestedDynVTableUnresolved ∧
    dynSizeAlign (.sliceLen 3) (.tuple [.uint 1, .slice (.uint 4)]) = .ok (16, 4) ∧
    dynSizeAlign (.vtable 4 4) (.tuple [.uint 1, .dynamic "Send"]) = .ok (8, 4) ∧
    worldNestedDynOracle KeyedAllocWorld.empty VTableRegistry.empty
      (fun _ => ⟨none, AutoTraitSet.empty, []⟩) (fun _ => none) "Send" (List.replicate 8 (0, none)) =
      .error .nestedInvalidVTable ∧
    decodeVTableWord (fun _ => none) (List.replicate 8 (0, none)) = .null := by
  have hslice1 := (checkNestedWideSafeRefChildSession_slice (fun _ _ => .ok (0, 1)) (.uint 4)
    ⟨4, 4, true, true, none⟩
    [(16, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
     (2, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none)] rfl rfl rfl).trans rfl
  have hslice2 := (checkNestedWideSafeRefChildSession_slice (fun _ _ => .ok (0, 1)) (.uint 4)
    ⟨4, 4, true, true, none⟩
    [(16, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
     (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0x40, none)] rfl rfl rfl).trans rfl
  have hdyn1 := (checkNestedWideSafeRefChildSession_dyn (fun _ _ => .error .nestedInvalidVTable) "Send"
    (List.replicate 16 (0, none)) rfl).trans rfl
  have hdyn2 := (checkNestedWideSafeRefChildSession_dyn (fun _ _ => .ok (4, 4)) "Send"
    [(66, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none),
     (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none), (0, none)] rfl).trans rfl
  have hraw1 := (visitConcreteValue_nestedRawWideDyn 0 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0
    false "Send" (fun _ _ => .error .nestedInvalidVTable)).trans rfl
  have hraw2 := (visitConcreteValue_nestedRawWideDyn 0 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0
    false "Send" (fun _ _ => .ok (4, 4))).trans rfl
  have hfull := (visitConcreteValue_nestedWideRef_reads_full_pointer 0 (encodeLeUInt64Bytes 16) 0 false
    (.slice (.uint 4)) NestedDynMetaOracle.failClosed (Or.inl rfl)).trans rfl
  have hcases := visitConcreteValue_nestedWidePointer_cases
  have hdst := dynSizeAlign_customDst_cases
  have horacle := (worldNestedDynOracle_spec KeyedAllocWorld.empty VTableRegistry.empty
    (fun _ => ⟨none, AutoTraitSet.empty, []⟩) (fun _ => none) "Send" (List.replicate 8 (0, none))).2.2
    .invalidVTableNull rfl
  have hdecode := decodeVTableWord_cases
  exact ⟨hslice1, hslice2, hdyn1, hdyn2, hraw1, hraw2, hfull, hcases.1, hcases.2.2.2.2.1,
    hcases.2.2.2.2.2.2.2.2.2.2.1, hdst.1, hdst.2.1, horacle, hdecode.1⟩

theorem canary_part3C_deep_validator_nested_dyn_and_layout_mismatch :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let rt : String → DynExistentialSpec := fun _ => spec
    let idVtOuter : MiriAllocId := ⟨1, by decide⟩
    let idVtInner : MiriAllocId := ⟨2, by decide⟩
    let idVtRaw : MiriAllocId := ⟨3, by decide⟩
    let idVtBad : MiriAllocId := ⟨4, by decide⟩
    let idLive : MiriAllocId := ⟨10, by decide⟩
    let vtOuter := buildPrincipalLessVTable (.ref false (.dynamic "Send")) 501 none 16 3 [.send]
    let vtInner := buildPrincipalLessVTable (.uint 4) 502 none 4 2 [.send]
    let vtRaw := buildPrincipalLessVTable (.rawPtr false (.dynamic "Send")) 503 none 16 3 [.send]
    let vtBad := buildPrincipalLessVTable (.uint 8) 504 none 0 0 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty
        allocToData := (((ExtTreeMap0.empty.insert idVtOuter vtOuter).insert idVtInner vtInner).insert idVtRaw vtRaw).insert idVtBad vtBad }
    let wBase : KeyedAllocWorld :=
      (((KeyedAllocWorld.empty.registerGlobal idVtOuter ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtInner ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtRaw ⟨.vtable, 24, 3, .not, []⟩).registerGlobal idVtBad ⟨.vtable, 24, 3, .not, []⟩
    let vb : MiriAllocId → Option UInt64 := fun q =>
      if q = idVtInner then some 4096 else if q = idVtBad then some 8192 else none
    let wGood := wBase.insertLive idLive
      ⟨16, 3, .stack, .mut, encodeLeUInt64Bytes 64 ++ encodeLeUInt64Bytes 4096 (some idVtInner)⟩
    let wNullVt := wBase.insertLive idLive
      ⟨16, 3, .stack, .mut, encodeLeUInt64Bytes 64 ++ encodeLeUInt64Bytes 0⟩
    let wBadInner := wBase.insertLive idLive
      ⟨16, 3, .stack, .mut, encodeLeUInt64Bytes 64 ++ encodeLeUInt64Bytes 8192 (some idVtBad)⟩
    let wU64 := wBase.insertLive idLive ⟨8, 3, .stack, .mut, encodeLeUInt64Bytes 7⟩
    validateWideDynSafePtrWithBytes wGood reg (.provenanced idVtOuter 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nestedDynVTableUnresolved) ∧
    validateWideDynSafePtrDeep wGood reg rt vb (.provenanced idVtOuter 0) (.provenanced idLive 0 16) spec false true =
      .ok vtOuter ∧
    validateWideDynSafePtrDeep wNullVt reg rt vb (.provenanced idVtOuter 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nestedInvalidVTable) ∧
    validateWideDynSafePtrDeep wNullVt reg rt vb (.provenanced idVtRaw 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nestedInvalidVTable) ∧
    validateWideDynSafePtrWithBytes wU64 reg (.provenanced idVtBad 0) (.provenanced idLive 4 16) spec false true =
      .error (.pointeeErr .outOfBoundsPointeeRead) ∧
    validateWideDynSafePtrDeep wU64 reg rt vb (.provenanced idVtBad 0) (.provenanced idLive 4 16) spec false false =
      .error (.pointeeErr .vtableLayoutMismatch) ∧
    validateWideDynSafePtrDeep wU64 reg rt vb (.provenanced idVtBad 0) (.danglingInt 18446744073709551611) spec true false =
      .error (.pointeeErr .vtableLayoutMismatch) ∧
    validateWideDynSafePtrDeep wBadInner reg rt vb (.provenanced idVtOuter 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nestedInvalidVTable) ∧
    validateWideDynSafePtrDeep wBadInner reg rt vb (.provenanced idVtRaw 0) (.provenanced idLive 0 16) spec false true =
      .error (.pointeeErr .nestedInvalidVTable) := by
  have h := wideDynDeep_nestedDyn_rawDyn_and_layoutMismatch
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem canary_part3C_deep_validator_rejects_inconsistent_vtable_layout :
    let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
    let vtBad := buildPrincipalLessVTable (.uint 8) 504 none 0 0 [.send]
    let reg : VTableRegistry :=
      { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtBad }
    let w : KeyedAllocWorld :=
      (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).insertLive id10 entryU64
    validateWideDynSafePtr w reg (.provenanced id1 0) (.provenanced id10 0 16) spec false false = .ok vtBad ∧
    validateWideDynSafePtrDeep w reg (fun _ => spec) (fun _ => none) (.provenanced id1 0)
      (.provenanced id10 0 16) spec false true = .error (.pointeeErr .vtableLayoutMismatch) ∧
    validateWideDynSafePtrDeep w reg (fun _ => spec) (fun _ => none) (.provenanced id1 0)
      (.danglingInt 16) spec false false = .error (.pointeeErr .vtableLayoutMismatch) ∧
    validateWideDynSafePtrDeep w reg (fun _ => spec) (fun _ => none) (.provenanced id1 0)
      .null spec true false = .error (.pointeeErr .vtableLayoutMismatch) := by
  dsimp only
  let spec : DynExistentialSpec := ⟨none, AutoTraitSet.ofList [.send], []⟩
  let vtBad := buildPrincipalLessVTable (.uint 8) 504 none 0 0 [.send]
  let reg : VTableRegistry :=
    { keyToAlloc := ExtTreeMap0.empty, allocToData := ExtTreeMap0.empty.insert id1 vtBad }
  let w : KeyedAllocWorld :=
    (KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩).insertLive id10 entryU64
  have hvt : validateVTableHalf w reg (.provenanced id1 0) spec = .ok vtBad := by
    have hmatch : vtableMatchesExpectedSpec vtBad.spec spec = true := rfl
    have hg : w.findGlobal? id1 = some ⟨.vtable, 24, 3, .not, []⟩ := by
      simp [w, KeyedAllocWorld.findGlobal?, KeyedAllocWorld.insertLive, KeyedAllocWorld.registerGlobal,
        ExtTreeMap0.get?_insert_self]
    have hd : reg.allocToData.get? id1 = some vtBad := by
      simp [reg, ExtTreeMap0.get?_insert_self]
    simp [validateVTableHalf, hg, hd, hmatch]
  have hroot := (wideDyn_zstConcrete_never_dangles w reg (.provenanced id1 0) spec vtBad id10 0 16
    hvt rfl rfl (by decide)).1
  have hdeepRec := validateWideDynSafePtrDeep_layoutMismatch_rejected w reg (fun _ => spec) (fun _ => none)
    (.provenanced id1 0) (.provenanced id10 0 16) spec false true 64 vtBad hvt rfl
  have hdeepSh := validateWideDynSafePtrDeep_layoutMismatch_rejected w reg (fun _ => spec) (fun _ => none)
    (.provenanced id1 0) (.danglingInt 16) spec false false 64 vtBad hvt rfl
  have hdeepMd := validateWideDynSafePtrDeep_layoutMismatch_rejected w reg (fun _ => spec) (fun _ => none)
    (.provenanced id1 0) .null spec true false 64 vtBad hvt rfl
  exact ⟨hroot, hdeepRec, hdeepSh, hdeepMd⟩

theorem canary_part1_allocate_ok_inv_and_linear_checkPtrAccess :
    let lw1 := LinearAllocWorld.empty.insertLive id1 entryU32
    let kw1 := KeyedAllocWorld.empty.insertLive id1 entryU32
    (∃ w', KeyedAllocWorld.empty.allocate entryU32 = (w', .ok id1) ∧
      w'.hasIssued id1 = true ∧ w'.findLive? id1 = some entryU32 ∧ w'.findLive? id2 = none) ∧
    lw1.checkPtrAccess (some (id1, 0)) 4 = kw1.checkPtrAccess (some (id1, 0)) 4 ∧
    lw1.checkPtrAccess (some (id1, 0)) 4 = true ∧
    lw1.checkPtrAccess (some (id1, 0)) 8 = false := by
  dsimp only
  have halloc : KeyedAllocWorld.empty.allocate entryU32 =
      ((KeyedAllocWorld.empty.allocate entryU32).1, .ok id1) := rfl
  rcases keyedAllocate_ok_inv halloc with ⟨_, _, hissued, hlive, hother, _, _, _⟩
  have hrel : AllocWorldRel (LinearAllocWorld.empty.insertLive id1 entryU32)
      (KeyedAllocWorld.empty.insertLive id1 entryU32) :=
    allocWorldRel_insertLive allocWorldRel_empty id1 entryU32
  have hacc := allocWorldRel_checkPtrAccess hrel (some (id1, 0)) 4
  refine ⟨⟨_, halloc, hissued, hlive, ?_⟩, hacc, rfl, rfl⟩
  rw [hother id2 (by decide)]
  rfl

theorem canary_part2A_rootedWF_schedule_completeness_and_direct_model5 :
    (⟨3, some 0, .unique, 0, 4, some 8, true⟩ ∈
      foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
        twoProtectedSiblingsWorld 1 true 0 4) ∧
    (∃ e', checkNodesM (stepNodeOnRangeWrite twoProtectedSiblingsWorld.activeProtectors false 0 4)
        (foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
          twoProtectedSiblingsWorld 1 true 0 4) = .error e' ∧
      e' = .protectedForeignConflict 3) ∧
    execFnEntryMutRetagTraversalOrderDirect twoProtectedSiblingsWorld 1 0 4 .writableChildWrite false =
      .error (.protectedForeignConflict 3) ∧
    execFnEntryMutRetagTraversalOrderDirect disabledSubtreeWorld 1 0 4 .writableChildWrite false =
      execFnEntryMutRetagTraversalOrder (childTagsInListOrder disabledSubtreeWorld.nodes)
        disabledSubtreeWorld 1 0 4 .writableChildWrite false := by
  have hwfSib : BorrowTreeRootedWF twoProtectedSiblingsWorld 0 := by
    refine ⟨by decide, ?_⟩
    intro n hn
    have h0 : ReachesRoot twoProtectedSiblingsWorld.nodes 0 0 0 :=
      ReachesRoot.root ⟨0, none, .unique, 0, 4, none, true⟩ rfl rfl
    simp only [twoProtectedSiblingsWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, h0⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 1 0 _ rfl rfl h0⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 2 0 _ rfl rfl h0⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 3 0 _ rfl rfl h0⟩
  have hwfDis : BorrowTreeRootedWF disabledSubtreeWorld 0 := by
    refine ⟨by decide, ?_⟩
    intro n hn
    have h0 : ReachesRoot disabledSubtreeWorld.nodes 0 0 0 :=
      ReachesRoot.root ⟨0, none, .unique, 0, 4, none, true⟩ rfl rfl
    have h2 : ReachesRoot disabledSubtreeWorld.nodes 0 1 2 :=
      ReachesRoot.step 0 2 0 _ rfl rfl h0
    have h3 : ReachesRoot disabledSubtreeWorld.nodes 0 2 3 :=
      ReachesRoot.step 1 3 2 _ rfl rfl h2
    simp only [disabledSubtreeWorld, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, h0⟩
    · exact ⟨1, by decide, ReachesRoot.step 0 1 0 _ rfl rfl h0⟩
    · exact ⟨1, by decide, h2⟩
    · exact ⟨2, by decide, h3⟩
    · exact ⟨3, by decide, ReachesRoot.step 2 4 3 _ rfl rfl h3⟩
  have hmem3 := (mem_foreignVisitScheduleNodes_iff_activeForeign_of_rootedWF hwfSib (parentTag := 1)
    (pNode := ⟨1, some 0, .unique, 0, 4, none, true⟩) rfl true 0 4
    ⟨3, some 0, .unique, 0, 4, some 8, true⟩).2 ⟨by decide, rfl, rfl, rfl⟩
  have hsep := execFnEntryMutRetagTraversalOrder_foreignErrorTag_separation
  rcases execFnEntryMutRetagTraversalOrder_noFallback_of_rootedWF hwfSib .writableChildWrite false 2
      (Or.inl hsep.2.1) with ⟨e', he'⟩
  have heq3 : e' = .protectedForeignConflict 3 := by
    have hr : checkNodesM (stepNodeOnRangeWrite twoProtectedSiblingsWorld.activeProtectors false 0 4)
        (foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
          twoProtectedSiblingsWorld 1 true 0 4) = .error (.protectedForeignConflict 3) := rfl
    have he'' : checkNodesM (stepNodeOnRangeWrite twoProtectedSiblingsWorld.activeProtectors false 0 4)
        (foreignVisitScheduleNodes (childTagsInListOrder twoProtectedSiblingsWorld.nodes)
          twoProtectedSiblingsWorld 1 true 0 4) = .error e' := he'
    rw [hr] at he''
    injection he'' with hEq
    exact hEq.symm
  have hdirSib := (execFnEntryMutRetagTraversalOrderDirect_eq_traversalOrder_of_rootedWF hwfSib
    1 0 4 .writableChildWrite false).trans hsep.2.2.1
  have hdirDis := execFnEntryMutRetagTraversalOrderDirect_eq_traversalOrder_of_rootedWF hwfDis
    1 0 4 .writableChildWrite false
  exact ⟨hmem3, ⟨e', he', heq3⟩, hdirSib, hdirDis⟩

theorem canary_part2A_sifa_idempotence_and_local_reset :
    let uNode : TreeTagNode := ⟨1, some 0, .unique, 0, 4, none, true⟩
    let pResNode : TreeTagNode := ⟨2, some 0, .reservedFrz false, 0, 4, some 7, true⟩
    stepNodeOnRangeRead [] false 0 4 { uNode with perm := .frozen } = .ok { uNode with perm := .frozen } ∧
    stepNodeOnRangeRead [7] false 0 4 { pResNode with perm := .reservedFrz true } =
      .ok { pResNode with perm := .reservedFrz true } ∧
    stepNodeOnRangeRead [] false 0 4 { uNode with perm := .disabled } = .ok { uNode with perm := .disabled } ∧
    stepNodeOnRangeWrite [] false 0 4 { uNode with perm := .disabled } = .ok { uNode with perm := .disabled } ∧
    IdempotentForeignAccess.canSkipForeign .read .write = false ∧
    IdempotentForeignAccess.recordNew .read true true = .none ∧
    stepNodeOnRangeRead [] false 0 4 { uNode with perm := .unique } = .ok { uNode with perm := .frozen } := by
  dsimp only
  have hrr := sifa_foreign_transition_idempotent [] 0 4 false false
    ⟨1, some 0, .unique, 0, 4, none, true⟩ ⟨1, some 0, .frozen, 0, 4, none, true⟩ rfl rfl
  have hpr := sifa_foreign_transition_idempotent [7] 0 4 false false
    ⟨2, some 0, .reservedFrz false, 0, 4, some 7, true⟩ ⟨2, some 0, .reservedFrz true, 0, 4, some 7, true⟩ rfl rfl
  have hwr := sifa_foreign_transition_idempotent [] 0 4 true false
    ⟨1, some 0, .unique, 0, 4, none, true⟩ ⟨1, some 0, .disabled, 0, 4, none, true⟩ rfl rfl
  have hww := sifa_foreign_transition_idempotent [] 0 4 true true
    ⟨1, some 0, .unique, 0, 4, none, true⟩ ⟨1, some 0, .disabled, 0, 4, none, true⟩ rfl rfl
  have hsep := sifa_rank_and_localReset_separation
  exact ⟨hrr, hpr, hwr, hww, hsep.1, hsep.2.2.1, hsep.2.2.2.2.1⟩

theorem canary_part3C_truncated_wide_ref_raw_layout_and_nested_bad_vtable :
    checkNestedWideSafeRefChildSession NestedDynMetaOracle.failClosed (.slice (.uint 4))
      (List.replicate 8 (16, none)) = .error .outOfBoundsPointeeRead ∧
    checkNestedWideSafeRefChildSession NestedDynMetaOracle.failClosed (.dynamic "Send")
      (List.replicate 8 (16, none)) = .error .outOfBoundsPointeeRead ∧
    dynSizeAlign (.sliceLen 2) (.slice (.slice (.uint 4))) = .error (.layoutErr .unsizedField) ∧
    visitConcreteValue 4 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0
      (.rawPtr false (.tuple [.array (.uint 1) (maxObjectSize64 + 1), .slice (.uint 1)]))
      NestedDynMetaOracle.failClosed = .error (.layoutErr .layoutOverflow) ∧
    visitConcreteValue 4 (encodeLeUInt64Bytes 0 ++ encodeLeUInt64Bytes 0) 0
      (.rawPtr false (.tuple [.slice (.uint 1), .dynamic "Send"]))
      (fun _ _ => .ok (4, 4)) = .error (.layoutErr .unsizedField) ∧
    decodeVTableWord (fun _ => some 0) (List.replicate 8 (0, some id1)) = .danglingInt 0 := by
  have htr := checkNestedWideSafeRefChildSession_truncated_rejected NestedDynMetaOracle.failClosed
    (List.replicate 8 (16, none)) (by decide)
  have hds := dynSizeAlign_unsizedSliceElem_rejected 2
  have hraw1 := visitConcreteValue_nestedRawUnsized_layout_checked NestedDynMetaOracle.failClosed
  have hraw2 := visitConcreteValue_nestedRawUnsized_layout_checked (fun _ _ => .ok (4, 4))
  exact ⟨htr.1, htr.2, hds.1, hraw1.1, hraw2.2.2.1, rfl⟩

theorem canary_part1_part3_helper_defs_coverage :
    MiriAllocId.one.value = 1 ∧
    MiriAllocId.maxMinusOne.value = UInt64.ofNat (2^64 - 2) ∧
    KeyedAllocTable.empty.live.size = 0 ∧
    (ExtTreeMap0.ofList (cmp := compare) [(MiriAllocId.one, 42), (id2, 99)]).get? MiriAllocId.one = some 42 ∧
    fieldsDynSizeAlign (.sliceLen 3) 0 1 [.uint 1, .slice (.uint 4)] = .ok (16, 4) ∧
    stringToRawNatBytes "" = [] := by
  refine ⟨rfl, rfl, ExtTreeMap0.size_empty, ?_, rfl, by simp [stringToRawNatBytes]⟩
  simp [ExtTreeMap0.ofList, ExtTreeMap0.get?_insert, MiriAllocId.one, id2]

/-! ## Section 4: Fast `M = 16` Closed Workload Canary -/

private def mkSmallAllocId (n : Nat) (h : n < 1000) : MiriAllocId :=
  ⟨UInt64.ofNat (n + 1), by
    intro heq
    have hv := congrArg UInt64.toNat heq
    have hlt : n + 1 < UInt64.size := by
      have : UInt64.size = 18446744073709551616 := rfl
      omega
    have h1 : (UInt64.ofNat (n + 1)).toNat = n + 1 := by
      simp only [UInt64.ofNat, UInt64.toNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hlt
    have h0 : (0 : UInt64).toNat = 0 := rfl
    omega⟩

private def workloadAllocMapM16 : Bool :=
  let ids : List MiriAllocId :=
    [ mkSmallAllocId 0 (by decide), mkSmallAllocId 1 (by decide), mkSmallAllocId 2 (by decide), mkSmallAllocId 3 (by decide),
      mkSmallAllocId 4 (by decide), mkSmallAllocId 5 (by decide), mkSmallAllocId 6 (by decide), mkSmallAllocId 7 (by decide),
      mkSmallAllocId 8 (by decide), mkSmallAllocId 9 (by decide), mkSmallAllocId 10 (by decide), mkSmallAllocId 11 (by decide),
      mkSmallAllocId 12 (by decide), mkSmallAllocId 13 (by decide), mkSmallAllocId 14 (by decide), mkSmallAllocId 15 (by decide) ]
  let lw := ids.foldl (fun w id => w.insertLive id entryU32) LinearAllocWorld.empty
  let kw := ids.foldl (fun w id => w.insertLive id entryU32) KeyedAllocWorld.empty
  ids.all (fun id => lw.isAllocLive id && kw.isAllocLive id)

private def workloadFnEntryRetagM16 : Bool :=
  let siblings : List TreeTagNode := (List.range 16).map fun i =>
    { tag := i + 2, parentTag := some 0, perm := .frozen, rangeOffset := 0, rangeLen := 4, protector := none }
  let w : FnEntryBorrowWorld := {
    nodes :=
      { tag := 0, parentTag := none, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none } ::
      { tag := 1, parentTag := some 0, perm := .unique, rangeOffset := 0, rangeLen := 4, protector := none } ::
      siblings
    activeProtectors := []
    nextTag := 100
    nextProtector := 200
    pointeeInitialized := true
  }
  match execFnEntryMutRetagSourceOrder w 1 0 4 .rustcNoWritable false,
        execFnEntryMutRetagSourceOrder w 1 0 4 .writableChildWrite false with
  | .ok (wNoWr, _), .ok (wWr, _) =>
    (findNode? wNoWr.nodes 2).map TreeTagNode.perm == some .frozen &&
    (findNode? wWr.nodes 2).map TreeTagNode.perm == some .disabled
  | _, _ => false

private def workloadRawPtrArrayM16 : Bool :=
  let ty := nestSingleElemArray 16 (.uint 1)
  match validateRawPtrFastPath ty (.thin 4096), validateRawPtrLayoutFirst ty (.thin 4096) with
  | .ok (), .ok () => true
  | _, _ => false

theorem canary_workload_M16_all_three_suites :
    workloadAllocMapM16 = true ∧
    workloadFnEntryRetagM16 = true ∧
    workloadRawPtrArrayM16 = true := by
  exact ⟨by decide, by decide, by decide⟩

/-! ## Section 5: `#guard_msgs in #print axioms` Pins (Zero `Classical.choice`) -/

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.MiriAllocId.toTrustedAllocId_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.MiriAllocId.toTrustedAllocId_injective

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.ext_get?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.ext_get?

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.ext_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.ext_getElem?

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.linearFind?_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.ExtTreeMap0.linearFind?_toList

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.KeyedAllocWorld.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.KeyedAllocWorld.ext

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_iff_eq_ofLinear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_iff_eq_ofLinear

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_allocateMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_allocateMachine

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_deallocateMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_deallocateMachine

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_perThreadClock_catches_unsynced_reader' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_perThreadClock_catches_unsynced_reader

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedAllocateMachine_deallocateMachine_sameThread_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedAllocateMachine_deallocateMachine_sameThread_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.selectFnEntryPolicy_eq_upstream_create' depends on axioms: [propext] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.selectFnEntryPolicy_eq_upstream_create

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.applyParamFnEntryImplicitWrite_zst_noop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.applyParamFnEntryImplicitWrite_zst_noop

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors' depends on axioms: [propext] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.sourceOrder_rustcNoWritable_preserves_all_frozen_nodes' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.sourceOrder_rustcNoWritable_preserves_all_frozen_nodes

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.static_mixed_miri_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.static_mixed_miri_separation

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.static_mixed_miri_unsafeCell_write_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.static_mixed_miri_unsafeCell_write_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.static_zstUnsafeCell_composite_miri_separation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.static_zstUnsafeCell_composite_miri_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.validateRawPtrFastPath_eq_layoutFirst_of_layoutOk' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.validateRawPtrFastPath_eq_layoutFirst_of_layoutOk

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.oversized_array_rawPtr_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.oversized_array_rawPtr_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.unsized_rawPtr_layoutOverflow_rejected_like_upstream' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.unsized_rawPtr_layoutOverflow_rejected_like_upstream

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.validateSafeThinRef_staticGlobal_nullProv_and_accessOrder' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.validateSafeThinRef_staticGlobal_nullProv_and_accessOrder

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.encodeVTableKeyCode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.encodeVTableKeyCode_injective

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.vtableMatchesExpectedSpec_predicate_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.vtableMatchesExpectedSpec_predicate_perm

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.upcastVTableToAutoTraits_preserves_drop_size_align' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.upcastVTableToAutoTraits_preserves_drop_size_align

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.VTableWorldWF.intern_roundTrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.VTableWorldWF.intern_roundTrip

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.SaltedVTableWorldWF.internSalted_roundTrip' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.SaltedVTableWorldWF.internSalted_roundTrip

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_invalidVTable_precedes_all_data_ub' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_invalidVTable_precedes_all_data_ub

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.validateRawPtrFull_customDynDst_layout_and_vtable_soundness' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.validateRawPtrFull_customDynDst_layout_and_vtable_soundness

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_bytes_and_childSession_mayDangle' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_bytes_and_childSession_mayDangle

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_aggregate_char_fnPtr_contents' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_aggregate_char_fnPtr_contents

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_fieldOrder_nullProvFn_zstArray_and_fuel' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_fieldOrder_nullProvFn_zstArray_and_fuel

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedReserveAllocId_wrapAround_latches_exhausted' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedReserveAllocId_wrapAround_latches_exhausted

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_live_always_detaches_entry_and_clock' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_live_always_detaches_entry_and_clock

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_race_checked_before_cleanup' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedDeallocateMachine_race_checked_before_cleanup

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.fnEntryMutRetag_readOnlyAlloc_writable_rejected' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.fnEntryMutRetag_readOnlyAlloc_writable_rejected

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.sourceOrder_rustcNoWritable_ignores_allocReadOnly' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.sourceOrder_rustcNoWritable_ignores_allocReadOnly

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.validateSafeThinRef_zst_never_dangles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.validateSafeThinRef_zst_never_dangles

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_zstConcrete_never_dangles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_zstConcrete_never_dangles

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_mayDangle_provenanced_addressTooClose' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_mayDangle_provenanced_addressTooClose

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_findAllocBytes?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_findAllocBytes?

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.stepNodeOnRangeWrite_unaccessed_protected_foreign_disables_without_ub' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.stepNodeOnRangeWrite_unaccessed_protected_foreign_disables_without_ub

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.fnEntryMutRetag_disabledParent_zst_disjoint_and_readOnly_precedence' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.fnEntryMutRetag_disabledParent_zst_disjoint_and_readOnly_precedence

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_eq_sourceOrder_of_noSkippedForeignSubtree' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_eq_sourceOrder_of_noSkippedForeignSubtree

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_skipSelfAndChildren_separation' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_skipSelfAndChildren_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_malformedAlign_and_malformedConcreteLayout_failClosed

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_staticGlobal_bytes_validated' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDyn_recursive_staticGlobal_bytes_validated

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.fnEntry_mutOrBox_childPerms_eq_upstream_create' does not depend on any axioms
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.fnEntry_mutOrBox_childPerms_eq_upstream_create

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.fnEntry_shared_childPerms_outside_mut_models' does not depend on any axioms
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.fnEntry_shared_childPerms_outside_mut_models

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.prunedSourceOrder_rustcNoWritable_preserves_all_frozen_nodes' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.prunedSourceOrder_rustcNoWritable_preserves_all_frozen_nodes

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagSourceOrder_ok_imp_prunedSourceOrder_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagSourceOrder_ok_imp_prunedSourceOrder_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_error_provenance' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagPrunedSourceOrder_error_provenance

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.prunedSourceOrder_never_reservedIMInvariant_of_noProtectedReservedIM' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.prunedSourceOrder_never_reservedIMInvariant_of_noProtectedReservedIM

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_ok_iff_prunedSourceOrder_ok' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_ok_iff_prunedSourceOrder_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_error_cases' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_error_cases

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_foreignErrorTag_separation' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_foreignErrorTag_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.checkPtrAccess_size_exceeding_isizeMax_rejected' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.checkPtrAccess_size_exceeding_isizeMax_rejected

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.VTableData.layoutConsistent_spec' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.VTableData.layoutConsistent_spec

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.validateWideDynSafePtrDeep_layoutMismatch_rejected' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.validateWideDynSafePtrDeep_layoutMismatch_rejected

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_slice' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_slice

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_dyn' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_dyn

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedRawWideDyn' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedRawWideDyn

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedWidePointer_cases' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedWidePointer_cases

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.worldNestedDynOracle_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.worldNestedDynOracle_spec

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.wideDynDeep_nestedDyn_rawDyn_and_layoutMismatch' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.wideDynDeep_nestedDyn_rawDyn_and_layoutMismatch

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.keyedAllocate_ok_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.keyedAllocate_ok_inv

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_checkPtrAccess' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.allocWorldRel_checkPtrAccess

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.mem_foreignVisitScheduleNodes_iff_activeForeign_of_rootedWF' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.mem_foreignVisitScheduleNodes_iff_activeForeign_of_rootedWF

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_noFallback_of_rootedWF' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrder_noFallback_of_rootedWF

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrderDirect_eq_traversalOrder_of_rootedWF' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.execFnEntryMutRetagTraversalOrderDirect_eq_traversalOrder_of_rootedWF

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.sifa_foreign_transition_idempotent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.sifa_foreign_transition_idempotent

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.sifa_rank_and_localReset_separation' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.sifa_rank_and_localReset_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_truncated_rejected' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.checkNestedWideSafeRefChildSession_truncated_rejected

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.dynSizeAlign_unsizedSliceElem_rejected' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.dynSizeAlign_unsizedSliceElem_rejected

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedRawUnsized_layout_checked' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms Anneal.ExtTreeMapAllocAndNoWritable.visitConcreteValue_nestedRawUnsized_layout_checked

/-! ## Section 6: Meta-Level `run_cmd` Audit & Rolled-Back Self-Tests -/

section MetaAudit

open Lean Elab Command

private def isAuditedTheoryDecl (env : Environment) (theoryModIdx? : Option ModuleIdx) (nm : Name) : Bool :=
  match theoryModIdx?, env.getModuleIdxFor? nm with
  | some targetIdx, some idx => idx == targetIdx
  | _, _ => false

private def isAuditedTestDecl (env : Environment) (nm : Name) : Bool :=
  env.constants.map₂.contains nm

private def isAuditedDecl (env : Environment) (theoryModIdx? : Option ModuleIdx) (nm : Name) : Bool :=
  isAuditedTheoryDecl env theoryModIdx? nm || isAuditedTestDecl env nm

private def nameHasComponent (nm : Name) (pred : String → Bool) : Bool :=
  match nm with
  | .anonymous => false
  | .str p s => pred s || nameHasComponent p pred
  | .num p _ => nameHasComponent p pred

private def isNonEmptyDigits (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all Char.isDigit

private def isDigitUnderscoreSuffix (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all (fun c => c.isDigit || c == '_') && cs.any Char.isDigit

private def hasNumericPrefix (s pfx : String) : Bool :=
  s.startsWith pfx && isNonEmptyDigits (s.toList.drop pfx.length)

private def isCompilerGeneratedAuxThm (env : Environment) (nm : Name) : Bool :=
  if env.isProjectionFn nm then true
  else if nameHasComponent nm (fun s => s == "decEq" || s.startsWith "_sparseCasesOn" || s == "_unary") then true
  else
    match nm with
    | .str p s =>
      let hasParentDecl := env.contains p
      let isExactAuxSuffix :=
        s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "ext_iff" ||
        s == "ext_get?_iff" || s == "ofNat_ctorIdx" || s == "ctorIdx_eq" ||
        s == "else_eq" || s == "eq" || s == "eq_def" || s == "congr_simp" ||
        s == "noConfusion_eq" || s == "induct_unfolding" || s == "brecOn"
      let isNumericAuxSuffix :=
        hasNumericPrefix s "eq_" || hasNumericPrefix s "match_" || hasNumericPrefix s "proof_" ||
        (s.startsWith "_proof_" && isDigitUnderscoreSuffix (s.toList.drop "_proof_".length)) ||
        (s.startsWith "_simp_" && isDigitUnderscoreSuffix (s.toList.drop "_simp_".length)) ||
        hasNumericPrefix s "_cstage" ||
        (s.startsWith "_sizeOf_" &&
          (isNonEmptyDigits (s.toList.drop "_sizeOf_".length) ||
           (s.endsWith "_eq" &&
             isNonEmptyDigits ((s.toList.drop "_sizeOf_".length).dropLast.dropLast.dropLast))))
      (hasParentDecl && (isExactAuxSuffix || isNumericAuxSuffix)) ||
        (s.startsWith "_proof_" && isDigitUnderscoreSuffix (s.toList.drop "_proof_".length)) ||
        (s.startsWith "_simp_" && isDigitUnderscoreSuffix (s.toList.drop "_simp_".length)) ||
        hasNumericPrefix s "_cstage"
    | _ => false

private def isCompilerGeneratedAuxDef (env : Environment) (nm : Name) : Bool :=
  if env.isProjectionFn nm then true
  else if nameHasComponent nm (fun s =>
      s == "decEq" || s == "repr" || s == "reprPrec" || s == "beq" ||
      s == "ctorIdx" || s == "toCtorIdx" || s == "ofNat" ||
      s == "ctorElim" || s == "ctorElimType" ||
      s == "noConfusion" || s == "noConfusionType" ||
      s == "recOn" || s == "casesOn" || s == "brecOn" || s == "binductionOn" ||
      s == "below" || s == "ibelow" || s == "sizeOf" ||
      s == "_unary" || s == "_sparseCasesOn" || s == "_mutual" ||
      s == "_default" || s == "_sunfold" || s == "_unsafe_rec" || s == "_flat_ctor" ||
      s == "default" || s.startsWith "match_" || s.startsWith "_sizeOf_" ||
      hasNumericPrefix s "brecOn_" || hasNumericPrefix s "below_" || hasNumericPrefix s "ibelow_" ||
      s.startsWith "instDecidableEq" || s.startsWith "instRepr" ||
      s.startsWith "instInhabited" || s.startsWith "instBEq") then true
  else
    match nm with
    | .str p s =>
      let hasParentDecl := env.contains p
      hasParentDecl && (s == "mk" || s == "elim" || s == "induct" ||
        hasNumericPrefix s "match_" || hasNumericPrefix s "_cstage")
    | _ => false

/-- Collect unpruned transitive constant closure (used for axiom soundness — never prunes dead code). -/
private partial def collectTransitiveClosure (env : Environment) (roots : List Name) : NameSet :=
  let rec go (worklist : List Name) (seen : NameSet) : NameSet :=
    match worklist with
    | [] => seen
    | n :: rest =>
      if seen.contains n then go rest seen
      else
        let seen' := seen.insert n
        match env.find? n with
        | none => go rest seen'
        | some ci =>
          let addArr (arr : Array Name) (acc : List Name) :=
            arr.foldl (fun a c => if !seen'.contains c then c :: a else a) acc
          let next1 := addArr ci.type.getUsedConstants rest
          let next2 := match ci.value? (allowOpaque := true) with
            | some val => addArr val.getUsedConstants next1
            | none => next1
          go next2 seen'
  go roots {}

/-- Collect constants from an `Expr` while pruning dead `.letE`, beta-redex, and `letFun` bindings.
DAG-aware: every shared subterm is visited once (collection is context-free per subterm), so heavily
shared `simp` / `decide` proof terms are traversed in time linear in their DAG size. -/
private partial def collectPrunedExprConsts (e : Expr) (acc : NameSet) : NameSet :=
  ((go e).run ({}, acc)).2.2
where
  go (e : Expr) : StateM (Std.HashSet Expr × NameSet) Unit := do
    if (← get).1.contains e then return
    modify fun st => (st.1.insert e, st.2)
    match e with
    | .const n _ => modify fun st => (st.1, st.2.insert n)
    | .letE _ t v b _ =>
      if !b.hasLooseBVar 0 then go b
      else
        go t
        go v
        go b
    | .app fn arg =>
      let head := e.getAppFn
      let args := e.getAppArgs
      if head.isConstOf ``letFun && args.size == 4 then
        match args[3]! with
        | .lam _ _ b _ =>
          if !b.hasLooseBVar 0 then go b
          else
            go args[2]!
            go b
        | other =>
          go args[2]!
          go other
      else
        match fn with
        | .lam _ _ b _ =>
          if !b.hasLooseBVar 0 then go b
          else
            go arg
            go b
        | _ =>
          go fn
          go arg
    | .lam _ d b _ =>
      go d
      go b
    | .forallE _ d b _ =>
      go d
      go b
    | .mdata _ inner => go inner
    | .proj _ _ s => go s
    | _ => pure ()

/-- Pruned transitive closure scoped to audited modules for genuine theorem reachability. -/
private partial def collectPrunedReachableClosure (env : Environment)
    (theoryModIdx? : Option ModuleIdx) (roots : List Name) : NameSet :=
  let rec go (worklist : List Name) (seen : NameSet) : NameSet :=
    match worklist with
    | [] => seen
    | n :: rest =>
      if seen.contains n then go rest seen
      else
        let seen' := seen.insert n
        if !isAuditedDecl env theoryModIdx? n then go rest seen'
        else
          match env.find? n with
          | none => go rest seen'
          | some ci =>
            let used :=
              match ci.value? (allowOpaque := true) with
              | some val => collectPrunedExprConsts val (collectPrunedExprConsts ci.type {})
              | none => collectPrunedExprConsts ci.type {}
            let next := used.foldl (fun acc c => if !seen'.contains c then c :: acc else acc) rest
            go next seen'
  go roots {}

private def exprMentionsAudited (env : Environment) (theoryModIdx? : Option ModuleIdx) (e : Expr) : Bool :=
  e.getUsedConstants.any (isAuditedDecl env theoryModIdx?)

private def isAuditedTheoryThm (env : Environment) (theoryModIdx? : Option ModuleIdx) (nm : Name) : Bool :=
  if isAuditedTheoryDecl env theoryModIdx? nm then
    match env.find? nm with
    | some (.thmInfo _) => !isCompilerGeneratedAuxThm env nm
    | _ => false
  else false

private def exprMentionsAuditedThm (env : Environment) (theoryModIdx? : Option ModuleIdx) (e : Expr) : Bool :=
  e.getUsedConstants.any (isAuditedTheoryThm env theoryModIdx?)

/-- Detect dead placeholder bindings (`.letE`, beta-redex, `letFun` where binder `0` is unused
and the discarded value satisfies `mentions`). DAG-aware: every shared subterm is inspected once
(detection is context-free per subterm). -/
private partial def hasPlaceholderBindingWith (mentions : Expr → Bool) (e : Expr) : Bool :=
  ((go e).run {}).1
where
  go (e : Expr) : StateM (Std.HashSet Expr) Bool := do
    if (← get).contains e then return false
    modify fun vis => vis.insert e
    match e with
    | .letE _ t v b _ =>
      if (!b.hasLooseBVar 0) && mentions v then return true
      if ← go t then return true
      if ← go v then return true
      go b
    | .app fn arg =>
      let head := e.getAppFn
      let args := e.getAppArgs
      if head.isConstOf ``letFun && args.size == 4 then
        match args[3]! with
        | .lam _ _ b _ =>
          if (!b.hasLooseBVar 0) && mentions args[2]! then return true
          if ← go args[2]! then return true
          go b
        | other =>
          if ← go args[2]! then return true
          go other
      else
        match fn with
        | .lam _ _ b _ =>
          if (!b.hasLooseBVar 0) && mentions arg then return true
          if ← go arg then return true
          go b
        | _ =>
          if ← go fn then return true
          go arg
    | .lam _ d b _ =>
      if ← go d then return true
      go b
    | .forallE _ d b _ =>
      if ← go d then return true
      go b
    | .mdata _ inner => go inner
    | .proj _ _ s => go s
    | _ => return false

private def hasPlaceholderBinding (env : Environment) (theoryModIdx? : Option ModuleIdx)
    (e : Expr) : Bool :=
  hasPlaceholderBindingWith (exprMentionsAudited env theoryModIdx?) e

private def hasTheoryThmPlaceholderBinding (env : Environment) (theoryModIdx? : Option ModuleIdx)
    (e : Expr) : Bool :=
  hasPlaceholderBindingWith (exprMentionsAuditedThm env theoryModIdx?) e

/-- Detect constructor-projection laundering: a projection (`Expr.proj` or a projection function such
as `And.right`, `PProd.snd`, `Subtype.val`, `PSigma.fst`) applied directly to a constructor of ANY
`Prop`-valued structure OR `Sort`/`Prop`-capable `Type`-valued container (`PProd`, `PSigma`, `Subtype`)
whose DISCARDED field satisfies `mentions`. Excludes `Type`-only data tuples/records (`Prod`, `Sigma`,
`ExtTreeMap0`) that cannot directly hold a `Prop` proof field. DAG-aware. -/
private partial def hasDiscardedCtorFieldWith (env : Environment) (mentions : Expr → Bool) (e : Expr) : Bool :=
  ((go e).run {}).1
where
  discarded (ctorApp : Expr) (keep : Nat) : Bool :=
    match ctorApp.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.ctorInfo v) =>
        let isPropStruct :=
          match env.find? v.induct with
          | some (.inductInfo iv) => iv.type.getForallBody.isProp
          | _ => false
        let isProofCarryingContainer :=
          v.induct == ``PProd || v.induct == ``PSigma || v.induct == ``Subtype
        let args := ctorApp.getAppArgs
        (isPropStruct || isProofCarryingContainer) &&
          (List.range v.numFields).any fun j =>
            j != keep &&
              (match args[v.numParams + j]? with
               | some a => mentions a
               | none => false)
      | _ => false
    | _ => false
  go (e : Expr) : StateM (Std.HashSet Expr) Bool := do
    if (← get).contains e then return false
    modify fun vis => vis.insert e
    match e with
    | .proj _ idx s =>
      if discarded s idx then return true
      go s
    | .app fn arg =>
      let head := e.getAppFn
      let args := e.getAppArgs
      let laundered : Bool :=
        match head with
        | .const c _ =>
          match env.getProjectionFnInfo? c with
          | some info =>
            match args[info.numParams]? with
            | some structArg => discarded structArg info.i
            | none => false
          | none => false
        | _ => false
      if laundered then return true
      if ← go fn then return true
      go arg
    | .lam _ d b _ =>
      if ← go d then return true
      go b
    | .forallE _ d b _ =>
      if ← go d then return true
      go b
    | .letE _ t v b _ =>
      if ← go t then return true
      if ← go v then return true
      go b
    | .mdata _ inner => go inner
    | _ => return false

/-- Strip `let`/`letFun` wrappers from a `Prop` expression for tautology inspection. -/
private partial def stripLetBindings (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => stripLetBindings (b.instantiate1 v)
  | .mdata _ inner => stripLetBindings inner
  | _ =>
    let head := e.getAppFn
    let args := e.getAppArgs
    if head.isConstOf ``letFun && args.size == 4 then
      match args[3]! with
      | .lam _ _ b _ => stripLetBindings (b.instantiate1 args[2]!)
      | _ => e
    else e

/-- Check whether a `Prop` expression contains a tautological conjunct (`a = a`, `a ↔ a`, `True`,
`False → P`, `P ∨ True`, `a ≤ a`, `a ≥ a`, `HEq a a`, `¬ False`, `(x == x) = true`), also underneath
existential binders (`∃ x, True`, `∃ x, x = x`, `∃ x, P x ∧ x = x`). -/
private partial def hasTautologicalConjunct (e : Expr) : Bool :=
  let e' := stripLetBindings e
  let head := e'.getAppFn
  let args := e'.getAppArgs
  if head.isConstOf ``And && args.size == 2 then
    hasTautologicalConjunct args[0]! || hasTautologicalConjunct args[1]!
  else if head.isConstOf ``True then
    true
  else if head.isConstOf ``Or && args.size == 2 then
    (stripLetBindings args[0]!).getAppFn.isConstOf ``True ||
    (stripLetBindings args[1]!).getAppFn.isConstOf ``True
  else if head.isConstOf ``Eq && args.size == 3 then
    let lhs := stripLetBindings args[1]!
    let rhs := stripLetBindings args[2]!
    if lhs == rhs then true
    else if rhs.isConstOf ``Bool.true && lhs.getAppFn.isConstOf ``BEq.beq && lhs.getAppArgs.size == 4 then
      stripLetBindings lhs.getAppArgs[2]! == stripLetBindings lhs.getAppArgs[3]!
    else false
  else if head.isConstOf ``Iff && args.size == 2 then
    stripLetBindings args[0]! == stripLetBindings args[1]!
  else if head.isConstOf ``LE.le && args.size == 4 then
    stripLetBindings args[2]! == stripLetBindings args[3]!
  else if head.isConstOf ``GE.ge && args.size == 4 then
    stripLetBindings args[2]! == stripLetBindings args[3]!
  else if head.isConstOf ``HEq && args.size == 4 then
    stripLetBindings args[1]! == stripLetBindings args[3]!
  else if head.isConstOf ``Not && args.size == 1 then
    (stripLetBindings args[0]!).getAppFn.isConstOf ``False
  else if head.isConstOf ``Exists && args.size == 2 then
    match stripLetBindings args[1]! with
    | .lam _ _ body _ => hasTautologicalConjunct body
    | _ => false
  else
    match e' with
    | .forallE _ d _ _ => (stripLetBindings d).getAppFn.isConstOf ``False
    | _ => false

/-- Check whether a constant's transitive closure contains any forbidden/unexpected axiom. -/
private def checkDeclAxioms (env : Environment) (nm : Name) : List Name :=
  let closure := collectTransitiveClosure env [nm]
  closure.foldl (fun bad c =>
    match env.find? c with
    | some (.axiomInfo _) =>
      if c == ``propext || c == ``Quot.sound then bad else c :: bad
    | _ => bad) []

private def isConditionalPublicTestThm (env : Environment) (nm : Name) (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ =>
    if !isPrivateName nm && !isCompilerGeneratedAuxThm env nm then
      let isCanary := match nm with | .str _ s => s.startsWith "canary_" | _ => false
      (stripLetBindings ci.type).isForall || !isCanary
    else false
  | _ => false

run_cmd do
  let env ← getEnv
  let theoryModIdx? := env.getModuleIdx? `Anneal.ExtTreeMapAllocAndNoWritable
  if theoryModIdx?.isNone then
    throwError "AUDIT FAILURE: module Anneal.ExtTreeMapAllocAndNoWritable not found in environment"
  let allowedAxioms : List Name := [``propext, ``Quot.sound]
  let mut auditedRoots : List Name := []
  let mut totalDecls : Nat := 0
  let mut theoryPubThms : List Name := []
  let mut theoryPubDefs : List Name := []
  let mut closedCanaries : List Name := []
  let mut unsafeDecls : List Name := []
  let mut placeholderDecls : List Name := []
  let mut launderedDecls : List Name := []
  let mut tautologyCanaries : List Name := []
  let mut conditionalCanaries : List Name := []

  for (nm, ci) in env.constants.map₁.toList do
    if isAuditedTheoryDecl env theoryModIdx? nm then
      auditedRoots := nm :: auditedRoots
      totalDecls := totalDecls + 1
      if ci.isUnsafe then
        unsafeDecls := nm :: unsafeDecls
      match ci with
      | .thmInfo _ =>
        if !isPrivateName nm && !isCompilerGeneratedAuxThm env nm then
          theoryPubThms := nm :: theoryPubThms
      | .defnInfo _ =>
        if !isPrivateName nm && !isCompilerGeneratedAuxDef env nm then
          theoryPubDefs := nm :: theoryPubDefs
      | _ => pure ()
      if !isCompilerGeneratedAuxThm env nm then
        if let some val := ci.value? (allowOpaque := true) then
          if hasTheoryThmPlaceholderBinding env theoryModIdx? val then
            placeholderDecls := nm :: placeholderDecls
          if hasDiscardedCtorFieldWith env (exprMentionsAuditedThm env theoryModIdx?) val then
            launderedDecls := nm :: launderedDecls

  for (nm, ci) in env.constants.map₂.toList do
    -- Skip the meta-audit helpers themselves (MetaAudit uses `Lean.Elab` / `NameSet`, not object-level proofs)
    let isMetaHelper :=
      match nm with
      | .str _ s =>
        s == "isAuditedTheoryDecl" || s == "isAuditedTestDecl" || s == "isAuditedDecl" ||
        s == "isAuditedTheoryThm" ||
        s == "nameHasComponent" || s == "isNonEmptyDigits" || s == "isDigitUnderscoreSuffix" ||
        s == "hasNumericPrefix" || s == "isCompilerGeneratedAuxThm" || s == "isCompilerGeneratedAuxDef" ||
        s == "collectTransitiveClosure" || s == "collectPrunedExprConsts" ||
        s == "collectPrunedReachableClosure" || s == "exprMentionsAudited" ||
        s == "exprMentionsAuditedThm" || s == "hasPlaceholderBindingWith" ||
        s == "hasPlaceholderBinding" || s == "hasTheoryThmPlaceholderBinding" ||
        s == "hasDiscardedCtorFieldWith" || s == "stripLetBindings" ||
        s == "hasTautologicalConjunct" || s == "checkDeclAxioms" ||
        s == "isConditionalPublicTestThm"
      | _ => false
    if !isMetaHelper && !nameHasComponent nm (fun s =>
        s == "collectTransitiveClosure" || s == "collectPrunedExprConsts" ||
        s == "collectPrunedReachableClosure" || s == "hasPlaceholderBindingWith" ||
        s == "hasPlaceholderBinding" || s == "hasTheoryThmPlaceholderBinding" ||
        s == "hasDiscardedCtorFieldWith" ||
        s == "stripLetBindings" || s == "hasTautologicalConjunct" ||
        s == "isCompilerGeneratedAuxThm" || s == "isCompilerGeneratedAuxDef" ||
        s == "nameHasComponent" ||
        s == "isNonEmptyDigits" || s == "isDigitUnderscoreSuffix" || s == "hasNumericPrefix") then
      auditedRoots := nm :: auditedRoots
      totalDecls := totalDecls + 1
      if ci.isUnsafe then
        unsafeDecls := nm :: unsafeDecls
      if isConditionalPublicTestThm env nm ci then
        conditionalCanaries := nm :: conditionalCanaries
      else
        match ci with
        | .thmInfo _ =>
          if !isPrivateName nm && !isCompilerGeneratedAuxThm env nm then
            closedCanaries := nm :: closedCanaries
            if hasTautologicalConjunct ci.type then
              tautologyCanaries := nm :: tautologyCanaries
        | _ => pure ()
      if let some val := ci.value? (allowOpaque := true) then
        if hasPlaceholderBinding env theoryModIdx? val then
          placeholderDecls := nm :: placeholderDecls
        if hasDiscardedCtorFieldWith env (exprMentionsAuditedThm env theoryModIdx?) val then
          launderedDecls := nm :: launderedDecls

  -- Single-pass unpruned union axiom check (O(|reachable|)); per-decl blame only if a bad axiom is present
  let unionClosure := collectTransitiveClosure env auditedRoots
  let unionBadAxioms := unionClosure.foldl (fun bad c =>
    match env.find? c with
    | some (.axiomInfo _) =>
      if c == ``propext || c == ``Quot.sound then bad else c :: bad
    | _ => bad) []
  let mut badAxioms : List (Name × List Name) := []
  if !unionBadAxioms.isEmpty then
    for nm in auditedRoots do
      let bad := checkDeclAxioms env nm
      if !bad.isEmpty then
        badAxioms := (nm, bad) :: badAxioms

  -- Pruned transitive reachability from closed canaries to ALL public theory theorems AND public defs/abbrevs
  let reachable := collectPrunedReachableClosure env theoryModIdx? closedCanaries
  let unreachableThms := theoryPubThms.filter fun t => !reachable.contains t
  let unreachableDefs := theoryPubDefs.filter fun d => !reachable.contains d

  -- Verify zero findings (report all categories together)
  let mut failures : List MessageData := []
  if !unsafeDecls.isEmpty then
    failures := m!"unsafe declarations found: {unsafeDecls}" :: failures
  if !badAxioms.isEmpty then
    failures := m!"unexpected axioms (allowed: {allowedAxioms}): {badAxioms}" :: failures
  if !placeholderDecls.isEmpty then
    failures := m!"dead placeholder bindings found: {placeholderDecls}" :: failures
  if !launderedDecls.isEmpty then
    failures := m!"theory theorems discarded through constructor projections: {launderedDecls}" :: failures
  if !tautologyCanaries.isEmpty then
    failures := m!"tautological conjuncts in canaries: {tautologyCanaries}" :: failures
  if !conditionalCanaries.isEmpty then
    failures := m!"non-closed or non-canary public test theorems: {conditionalCanaries}" :: failures
  if !unreachableThms.isEmpty then
    failures := m!"{unreachableThms.length} public theory theorems unreachable from closed canaries: {unreachableThms}" :: failures
  if !unreachableDefs.isEmpty then
    failures := m!"{unreachableDefs.length} public theory defs/abbrevs unreachable from closed canaries: {unreachableDefs}" :: failures
  if !failures.isEmpty then
    throwError m!"AUDIT FAILURE:\n{MessageData.joinSep failures.reverse "\n"}"

  -- 19 Rolled-Back Self-Tests proving the audit detects every defect class with zero false positives
  -- Self-test 1: Classical.choice detection
  let st1 := (checkDeclAxioms env ``Classical.choice).contains ``Classical.choice
  unless st1 do throwError "SELF-TEST 1 FAILED: Classical.choice not caught"

  -- Self-test 2: sorryAx & Lean.ofReduceBool detection
  let st2 := !(checkDeclAxioms env ``sorryAx).isEmpty && !(checkDeclAxioms env ``Lean.ofReduceBool).isEmpty
  unless st2 do throwError "SELF-TEST 2 FAILED: sorryAx / Lean.ofReduceBool not caught"

  -- Self-test 3: foreign user-declared axiom detection via addDecl (rolled back)
  let st3 : Bool ← withoutModifyingEnv do
    let axName := `Anneal.ExtTreeMapAllocAndNoWritableTests._selftest_foreignAxiom
    liftCoreM <| addDecl (.axiomDecl { name := axName, levelParams := [], type := mkConst ``True, isUnsafe := false })
    let bad := checkDeclAxioms (← getEnv) axName
    pure (bad.contains axName)
  unless st3 do throwError "SELF-TEST 3 FAILED: user-declared foreign axiom not caught"

  -- Self-test 4: dead `.letE` placeholder referencing a theory theorem
  let deadLet := Expr.letE `unused (mkConst ``True) (mkConst ``MiriAllocId.ofUInt64_zero) (mkNatLit 2) false
  unless hasPlaceholderBinding env theoryModIdx? deadLet do
    throwError "SELF-TEST 4 FAILED: dead .letE placeholder not caught"

  -- Self-test 5: dead beta-redex placeholder referencing a theory theorem
  let deadBeta := Expr.app (Expr.lam `unused (mkConst ``True) (mkNatLit 2) .default) (mkConst ``MiriAllocId.ofUInt64_zero)
  unless hasPlaceholderBinding env theoryModIdx? deadBeta do
    throwError "SELF-TEST 5 FAILED: dead beta-redex placeholder not caught"

  -- Self-test 6: dead `letFun` placeholder + pruned reachability skips dead letFun target
  let deadLetFun := mkApp4 (mkConst ``letFun [Level.zero, Level.zero])
    (mkConst ``True) (Expr.lam `_ (mkConst ``True) (mkConst ``Nat) .default)
    (mkConst ``MiriAllocId.ofUInt64_zero)
    (Expr.lam `unused (mkConst ``True) (mkNatLit 2) .default)
  let pruned := collectPrunedExprConsts deadLetFun {}
  unless hasPlaceholderBinding env theoryModIdx? deadLetFun && !pruned.contains ``MiriAllocId.ofUInt64_zero do
    throwError "SELF-TEST 6 FAILED: dead letFun placeholder not caught/pruned"

  -- Self-test 7: live `.letE` false-positive guard
  let liveLet := Expr.letE `x (mkConst ``True) (mkConst ``MiriAllocId.ofUInt64_zero) (Expr.bvar 0) false
  unless !hasPlaceholderBinding env theoryModIdx? liveLet do
    throwError "SELF-TEST 7 FAILED: live .letE falsely flagged"

  -- Self-test 8: `_`-prefixed undischarged conditional test theorem detection (rolled back)
  let st8 : Bool ← withoutModifyingEnv do
    let condName := `Anneal.ExtTreeMapAllocAndNoWritableTests._cond_probe
    let ty := Expr.forallE `h (mkConst ``True) (mkConst ``True) .default
    let val := Expr.lam `h (mkConst ``True) (Expr.bvar 0) .default
    liftCoreM <| addDecl (.thmDecl { name := condName, levelParams := [], type := ty, value := val })
    let e ← getEnv
    match e.find? condName with
    | some ci => pure (isConditionalPublicTestThm e condName ci)
    | none => pure false
  unless st8 do throwError "SELF-TEST 8 FAILED: _-prefixed conditional test theorem not caught"

  -- Self-test 9: private-def placeholder laundering detection (rolled back)
  let st9 : Bool ← withoutModifyingEnv do
    let e0 ← getEnv
    let some ciThm := e0.find? ``MiriAllocId.ofUInt64_zero | pure false
    let privName := mkPrivateName e0 `Anneal.ExtTreeMapAllocAndNoWritableTests.priv_launder
    let val := Expr.lam `x (mkConst ``Nat)
      (Expr.letE `unused ciThm.type (mkConst ``MiriAllocId.ofUInt64_zero) (Expr.bvar 1) false) .default
    liftCoreM <| addDecl (.defnDecl {
      name := privName, levelParams := [],
      type := Expr.forallE `x (mkConst ``Nat) (mkConst ``Nat) .default,
      value := val, hints := .abbrev, safety := .safe
    })
    let e ← getEnv
    match e.find? privName with
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => pure (hasPlaceholderBinding e theoryModIdx? v)
      | none => pure false
    | none => pure false
  unless st9 do throwError "SELF-TEST 9 FAILED: private-def placeholder laundering not caught"

  -- Self-test 10: tautology detection (`2 = 2`, `True ∧ ...`, `let x := 2; x = 2`, `BEq`, `False → P`, `P ∨ True`, `3 ≤ 3`)
  let tautEq := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit 2) (mkNatLit 2)
  let tautTrue := mkApp2 (mkConst ``And) (mkConst ``True) tautEq
  let tautLet := Expr.letE `x (mkConst ``Nat) (mkNatLit 2)
    (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (Expr.bvar 0) (Expr.bvar 0)) false
  let tautBeq := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp4 (mkConst ``BEq.beq [Level.zero]) (mkConst ``Nat) (mkConst ``instBEqOfDecidableEq [Level.zero]) (mkNatLit 5) (mkNatLit 5))
    (mkConst ``Bool.true)
  let tautImp := Expr.forallE `_ (mkConst ``False) (mkConst ``Nat) .default
  let tautOr := mkApp2 (mkConst ``Or) (mkConst ``False) (mkConst ``True)
  let tautLe := mkApp4 (mkConst ``LE.le [Level.zero]) (mkConst ``Nat) (mkConst ``instLENat) (mkNatLit 3) (mkNatLit 3)
  unless hasTautologicalConjunct tautEq && hasTautologicalConjunct tautTrue &&
      hasTautologicalConjunct tautLet && hasTautologicalConjunct tautBeq &&
      hasTautologicalConjunct tautImp && hasTautologicalConjunct tautOr &&
      hasTautologicalConjunct tautLe do
    throwError "SELF-TEST 10 FAILED: tautology detector missed a case"

  -- Self-test 11: non-tautological equality false-positive guard
  let nonTaut := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  unless !hasTautologicalConjunct nonTaut do throwError "SELF-TEST 11 FAILED: non-tautology falsely flagged"

  -- Self-test 12: clean theory constant false-positive guard
  let st12 := (checkDeclAxioms env ``ExtTreeMap0.ext_get?).isEmpty
  unless st12 do throwError "SELF-TEST 12 FAILED: clean ExtTreeMap0.ext_get? falsely flagged"

  -- Self-test 13: user-written theorems named `eq_*` / `proof_*` / `match_*` are NOT exempted
  let st13 : Bool ← withoutModifyingEnv do
    let fakeEq := `Anneal.ExtTreeMapAllocAndNoWritable.eq_fake_untested
    let fakeProof := `Anneal.ExtTreeMapAllocAndNoWritable.proof_fake_untested
    let fakeMatch := `Anneal.ExtTreeMapAllocAndNoWritable.match_fake_untested
    let fakeNum := `Anneal.ExtTreeMapAllocAndNoWritable.eq_1
    let e ← getEnv
    pure (!isCompilerGeneratedAuxThm e fakeEq &&
          !isCompilerGeneratedAuxThm e fakeProof &&
          !isCompilerGeneratedAuxThm e fakeMatch &&
          !isCompilerGeneratedAuxThm e fakeNum)
  unless st13 do throwError "SELF-TEST 13 FAILED: user-named eq_/proof_/match_ theorem falsely exempted"

  -- Self-test 14: `let`-wrapped universally quantified canary is caught as conditional (rolled back)
  let st14 : Bool ← withoutModifyingEnv do
    let letCondName := `Anneal.ExtTreeMapAllocAndNoWritableTests.canary_let_wrapped_forall
    let ty := Expr.letE `k (mkConst ``Nat) (mkNatLit 1)
      (Expr.forallE `x (mkConst ``Nat)
        (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (Expr.bvar 0) (Expr.bvar 0)) .default) false
    let val := Expr.letE `k (mkConst ``Nat) (mkNatLit 1)
      (Expr.lam `x (mkConst ``Nat)
        (mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) (Expr.bvar 0)) .default) false
    liftCoreM <| addDecl (.thmDecl { name := letCondName, levelParams := [], type := ty, value := val })
    let e ← getEnv
    match e.find? letCondName with
    | some ci => pure (isConditionalPublicTestThm e letCondName ci)
    | none => pure false
  unless st14 do throwError "SELF-TEST 14 FAILED: let-wrapped conditional canary not caught"

  -- Self-test 15: dead theorem placeholder inside a theory declaration is caught by `hasTheoryThmPlaceholderBinding`
  let st15 := hasTheoryThmPlaceholderBinding env theoryModIdx?
    (Expr.lam `x (mkConst ``Nat)
      (Expr.letE `unused (mkConst ``True) (mkConst ``MiriAllocId.ofUInt64_zero) (Expr.bvar 1) false) .default)
  unless st15 do throwError "SELF-TEST 15 FAILED: dead theorem placeholder inside lambda body not caught"

  -- Self-test 16: constructor-projection laundering of a theory theorem is caught in BOTH forms
  -- (`And.right ⟨thm, trivial⟩` and `Expr.proj`), while keeping the theorem's own field is not flagged
  let tTrue := mkConst ``True
  let andIntroThmFirst := mkApp4 (mkConst ``And.intro) tTrue tTrue
    (mkConst ``MiriAllocId.ofUInt64_zero) (mkConst ``True.intro)
  let launderApp := mkApp3 (mkConst ``And.right) tTrue tTrue andIntroThmFirst
  let launderProj := Expr.proj ``And 1 andIntroThmFirst
  let keepThm := mkApp3 (mkConst ``And.left) tTrue tTrue andIntroThmFirst
  let mentionsThm := exprMentionsAuditedThm env theoryModIdx?
  unless hasDiscardedCtorFieldWith env mentionsThm launderApp &&
      hasDiscardedCtorFieldWith env mentionsThm launderProj &&
      !hasDiscardedCtorFieldWith env mentionsThm keepThm do
    throwError "SELF-TEST 16 FAILED: constructor-projection laundering not caught / falsely flagged"

  -- Self-test 17: extended tautology shapes (`3 ≥ 3`, `¬ False`, `HEq 2 2`, `∃ x, True`, `∃ x, x = x`)
  -- and a non-tautological existential false-positive guard (`∃ x, x = 2`)
  let natTy := mkConst ``Nat
  let tautGe := mkApp4 (mkConst ``GE.ge [Level.zero]) natTy (mkConst ``instLENat) (mkNatLit 3) (mkNatLit 3)
  let tautNotFalse := mkApp (mkConst ``Not) (mkConst ``False)
  let tautHEq := mkApp4 (mkConst ``HEq [Level.succ Level.zero]) natTy (mkNatLit 2) natTy (mkNatLit 2)
  let tautExTrue := mkApp2 (mkConst ``Exists [Level.succ Level.zero]) natTy
    (Expr.lam `x natTy (mkConst ``True) .default)
  let tautExRefl := mkApp2 (mkConst ``Exists [Level.succ Level.zero]) natTy
    (Expr.lam `x natTy
      (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) natTy (Expr.bvar 0) (Expr.bvar 0)) .default)
  let nonTautEx := mkApp2 (mkConst ``Exists [Level.succ Level.zero]) natTy
    (Expr.lam `x natTy
      (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) natTy (Expr.bvar 0) (mkNatLit 2)) .default)
  unless hasTautologicalConjunct tautGe && hasTautologicalConjunct tautNotFalse &&
      hasTautologicalConjunct tautHEq && hasTautologicalConjunct tautExTrue &&
      hasTautologicalConjunct tautExRefl && !hasTautologicalConjunct nonTautEx do
    throwError "SELF-TEST 17 FAILED: extended tautology detector missed a case / false positive"

  -- Self-test 18: Type-valued constructor-projection laundering (`PProd.snd ⟨thm, ()⟩`, `Subtype.val ⟨(), thm⟩`,
  -- and `Expr.proj` on `PProd`) is caught, while keeping the theorem field or projecting data fields is allowed
  let unitTy := mkConst ``Unit
  let unitVal := mkConst ``Unit.unit
  let pprodApp := mkApp4 (mkConst ``PProd.mk [Level.zero, Level.succ Level.zero])
    tTrue unitTy (mkConst ``MiriAllocId.ofUInt64_zero) unitVal
  let pprodLaunderSnd := mkApp3 (mkConst ``PProd.snd [Level.zero, Level.succ Level.zero])
    tTrue unitTy pprodApp
  let pprodLaunderProj := Expr.proj ``PProd 1 pprodApp
  let pprodKeepFst := mkApp3 (mkConst ``PProd.fst [Level.zero, Level.succ Level.zero])
    tTrue unitTy pprodApp
  let subtypeApp := mkApp4 (mkConst ``Subtype.mk [Level.succ Level.zero])
    unitTy (Expr.lam `_ unitTy tTrue .default) unitVal (mkConst ``MiriAllocId.ofUInt64_zero)
  let subtypeLaunderVal := mkApp3 (mkConst ``Subtype.val [Level.succ Level.zero])
    unitTy (Expr.lam `_ unitTy tTrue .default) subtypeApp
  let dataProd := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    natTy natTy (mkNatLit 1) (mkNatLit 2)
  let dataProdSnd := mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero])
    natTy natTy dataProd
  unless hasDiscardedCtorFieldWith env mentionsThm pprodLaunderSnd &&
      hasDiscardedCtorFieldWith env mentionsThm pprodLaunderProj &&
      hasDiscardedCtorFieldWith env mentionsThm subtypeLaunderVal &&
      !hasDiscardedCtorFieldWith env mentionsThm pprodKeepFst &&
      !hasDiscardedCtorFieldWith env mentionsThm dataProdSnd do
    throwError "SELF-TEST 18 FAILED: Type-valued constructor-projection laundering not caught / falsely flagged"

  -- Self-test 19: unreachable public theory `def` detection (rolled back)
  let st19 : Bool ← withoutModifyingEnv do
    let deadDefName := `Anneal.ExtTreeMapAllocAndNoWritable._selftest_deadPublicDef
    liftCoreM <| addDecl (.defnDecl {
      name := deadDefName, levelParams := [],
      type := natTy, value := mkNatLit 42, hints := .abbrev, safety := .safe
    })
    let e ← getEnv
    pure (!isPrivateName deadDefName && !isCompilerGeneratedAuxDef e deadDefName && !reachable.contains deadDefName)
  unless st19 do throwError "SELF-TEST 19 FAILED: unreachable public theory def not caught"

  logInfo m!"audit passed: {totalDecls} declarations ({theoryPubThms.length} theory public theorems, {theoryPubDefs.length} theory public defs/abbrevs, {closedCanaries.length} closed test canaries, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 sorryAx, 0 unexpected axioms, 0 placeholder uses, 0 constructor-projection launderings, 0 tautological conjuncts, 0 conditional test theorems, 100% pruned theorem & def reachability; 19/19 rolled-back self-tests passed)"

end MetaAudit

end Anneal.ExtTreeMapAllocAndNoWritableTests
