import Anneal
import Anneal.ExtTreeMapAllocAndNoWritableProto
import Lean

/-!
# Closed Canaries, Axiom Audit, & Elaboration Benchmarks (`ws-proto-ext-treemap-alloc-and-no-writable-retag`)

Starts with `import Anneal` and `import Anneal.ExtTreeMapAllocAndNoWritableProto` to verify zero
namespace, notation, or typeclass collisions against the full `Anneal` umbrella.

Covers:
1. **Part 1 (`lean-miri#73`)**: full-width `UInt64` `MiriAllocId`, `0 Classical.choice` `ExtTreeMap0`
   & `RawAATree` laws, `LinearAllocWorld` permutation non-equality vs. `KeyedAllocWorld.ext`,
   bidirectional `AllocWorldRel` lifecycle, high-water & `0`-wrap-around exhaustion, and all 6
   deallocation failure-ordering & state-retention cases.
2. **Part 2A (`charon#1619` + `minirust#295`)**: `FnEntryRetagPolicy`, `!Unpin` guard, `FnParamRetagMap`,
   `rustcNoWritable` uninit & `.frozen` sibling preservation, `ReservedFrz { conflicted }` foreign-read
   latch, active-protector foreign-write conflict, ZST (`len = 0`) safety, and multi-parameter
   `Trusted.MirSemantics` `MachineState` operational overlay.
3. **Part 2B (`charon#1620`)**: static-access temporary retag preservation before `&raw const STATIC`
   across pure `Freeze`, pure `UnsafeCell` (`AtomicI32` multi-write `.cell` persistence), and mixed
   composite `(u8, pad[3], AtomicI32, trailPad[4])` statics.
4. **Part 3A (`lean-miri#79`)**: syntactic `[T; N]` `Sized` fast-path agreement when layout succeeds,
   strict separation on `*const [u8; usize::MAX]` & `*const [[u8; 2]; usize::MAX]` & oversized tuple
   tails vs. safe `&[u8; usize::MAX]`, and slice DST `*const [u8]` wide-metadata requirement.
5. **Part 3B (`lean-miri#75`)**: principal-less `dyn Send` / `dyn Send + Sync` vtable header
   preservation, permutation-canonical deduplication in `VTableRegistry`, non-collision with
   principal-bearing `dyn Debug + Send`, method-slot rejection, and auto-trait upcast soundness.
6. **Part 3C (`lean-miri#82`)**: wide `dyn` safe-pointer validation checking all 6 invalid-vtable
   cases *before* null/dangling/unaligned data UB (including double-null separation vs. legacy
   data-first validation), while preserving data checks when the vtable is valid.
7. **`#print axioms` Guards, Warmed Interleaved `IO.getNumHeartbeats` Benchmarks (`M = 16, 64, 128, 256`),
   and Compile-Time Meta-Level Axiom / Placeholder / Conditional-Test / 100%-Theorem-Reachability Audit
   with Rolled-Back Self-Tests**.
-/

namespace Anneal.ExtTreeMapAllocAndNoWritableProtoTests

open Std
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Memory
open Anneal.ExtTreeMapAllocAndNoWritableProto

/-! ## Section 1: Part 1 Closed Canaries (`lean-miri#73`) -/

def testId1 : MiriAllocId := ⟨1, by decide⟩
def testId2 : MiriAllocId := ⟨2, by decide⟩
def testId3 : MiriAllocId := ⟨3, by decide⟩
def testIdMaxPrev : MiriAllocId := ⟨0xFFFF_FFFF_FFFF_FFFE, by decide⟩
def testIdMax : MiriAllocId := ⟨0xFFFF_FFFF_FFFF_FFFF, by decide⟩

/-- Closed canary for full-width `UInt64` `MiriAllocId` (`0` sentinel rejection, `2^64 - 2` and
`2^64 - 1` boundary keys, `toTrustedAllocId` positivity and injectivity, and `MiriAllocId.ext`). -/
theorem canary_part1_miriAllocId_fullWidth :
    MiriAllocId.ofUInt64 0 = none ∧
    MiriAllocId.ofUInt64 0xFFFF_FFFF_FFFF_FFFF = some testIdMax ∧
    (∃ h : (0xFFFF_FFFF_FFFF_FFFE : UInt64) ≠ 0, testIdMaxPrev = ⟨0xFFFF_FFFF_FFFF_FFFE, h⟩) ∧
    0 < testIdMax.toTrustedAllocId ∧
    testIdMaxPrev < testIdMax ∧
    (⟨1, by decide⟩ : MiriAllocId) = testId1 := by
  have hprev : MiriAllocId.ofUInt64 0xFFFF_FFFF_FFFF_FFFE = some testIdMaxPrev := rfl
  have hinj : (⟨1, by decide⟩ : MiriAllocId) = testId1 :=
    MiriAllocId.toTrustedAllocId_injective rfl
  have hext : testId1 = ⟨1, by decide⟩ := MiriAllocId.ext rfl
  exact ⟨
    MiriAllocId.ofUInt64_zero,
    rfl,
    (MiriAllocId.ofUInt64_eq_some_iff).mp hprev,
    MiriAllocId.toTrustedAllocId_pos testIdMax,
    by decide,
    hinj.trans hext.symm
  ⟩

def sampleRawTree : RawAATree MiriAllocId Nat :=
  ((RawAATree.leaf.insert compare testIdMax 99).insert compare testId1 11).insert
    compare testIdMaxPrev 88

def sampleExtMapAsc : ExtTreeMap0 MiriAllocId Nat :=
  (((∅ : ExtTreeMap0 MiriAllocId Nat).insert testId1 11).insert testIdMaxPrev 88).insert testIdMax 99

def sampleExtMapDesc : ExtTreeMap0 MiriAllocId Nat :=
  (((ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat).insert testIdMax 99).insert testIdMaxPrev 88).insert
    testId1 11

/-- Closed canary exercising `RawAATree` structural/BST/rebalance theorems and `ExtTreeMap0`
lookup, insert, erase, size, `toList_inj`, `ext_get?`, `ext_getElem?`, overwrite/erase cancellation,
and `Std.TreeMap.Raw` agreement (`0 Classical.choice`). -/
theorem canary_part1_rawAATree_and_extTreeMap0_laws :
    (RawAATree.leaf : RawAATree MiriAllocId Nat).toList = [] ∧
    (RawAATree.node 1 .leaf testId1 11 .leaf).toList = [(testId1, 11)] ∧
    RawAATree.toList (RawAATree.setLevel 2 sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.skew sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.split sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.decreaseLevel sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.skewRight sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.skewRightRight sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.splitRight sampleRawTree) = sampleRawTree.toList ∧
    RawAATree.toList (RawAATree.rebalanceAfterErase sampleRawTree) = sampleRawTree.toList ∧
    (∃ mk mv t', RawAATree.popMin (.node 1 .leaf testId1 11 .leaf) = some (mk, mv, t') ∧
      RawAATree.toList (.node 1 .leaf testId1 11 .leaf) = (mk, mv) :: t'.toList) ∧
    sampleRawTree.size = sampleRawTree.toList.length ∧
    (ExtTreeMap0.empty : ExtTreeMap0 MiriAllocId Nat) = ∅ ∧
    (∅ : ExtTreeMap0 MiriAllocId Nat).size = 0 ∧
    (∅ : ExtTreeMap0 MiriAllocId Nat).get? testId1 = none ∧
    sampleExtMapAsc[testIdMax]? = sampleExtMapAsc.get? testIdMax ∧
    sampleExtMapAsc.size = sampleExtMapAsc.toList.length ∧
    sampleExtMapAsc.contains testIdMaxPrev = (sampleExtMapAsc.get? testIdMaxPrev).isSome ∧
    ((sampleExtMapAsc.insert testId2 22).get? testId2 = some 22) ∧
    ((sampleExtMapAsc.insert testId2 22).get? testId1 = sampleExtMapAsc.get? testId1) ∧
    (((sampleExtMapAsc.insert testId2 22).erase testId2).get? testId2 = none) ∧
    (((sampleExtMapAsc.insert testId2 22).erase testId2).get? testIdMax =
      (sampleExtMapAsc.insert testId2 22).get? testIdMax) ∧
    ((sampleExtMapAsc.insert testId1 77).insert testId1 11 = sampleExtMapAsc.insert testId1 11) ∧
    ((sampleExtMapAsc.insert testId2 22).erase testId2 = sampleExtMapAsc) ∧
    sampleExtMapAsc = sampleExtMapDesc ∧
    sampleExtMapAsc.toList = sampleExtMapDesc.toList ∧
    ExtTreeMap0.AgreesWithStdRaw
      (∅ : ExtTreeMap0 MiriAllocId Nat)
      (Std.TreeMap.Raw.empty : Std.TreeMap.Raw MiriAllocId Nat compare) ∧
    (let ops : List (ExtTreeMap0.MapTraceOp MiriAllocId Nat) :=
       [.insert testId1 10, .insert testIdMax 90, .insert testId1 77, .insert testId2 20, .erase testIdMax]
     (ExtTreeMap0.execMapTraceExt0 (cmp := compare) (ops ++ [.insert testId3 33])).get? testId3 = some 33 ∧
     ∀ k ∈ [testId1, testId2, testId3, testIdMax],
       (ExtTreeMap0.execMapTraceExt0 (cmp := compare) ops).get? k =
         (ExtTreeMap0.execMapTraceStdRaw (cmp := compare) ops).get? k) := by
  have hne21 : testId2 ≠ testId1 := by decide
  have hne2Max : testId2 ≠ testIdMax := by decide
  have hnone2 : sampleExtMapAsc.get? testId2 = none := rfl
  have hextElem : sampleExtMapAsc = sampleExtMapDesc := by
    apply ExtTreeMap0.ext_getElem?
    intro k
    rw [ExtTreeMap0.getElem?_eq_get?, ExtTreeMap0.getElem?_eq_get?]
    unfold sampleExtMapAsc sampleExtMapDesc
    rw [ExtTreeMap0.empty_eq_emptyc]
    repeat rw [ExtTreeMap0.get?_insert]
    repeat rw [ExtTreeMap0.get?_empty]
    by_cases h1 : compare testId1 k = .eq
    · have hk : testId1 = k := LawfulEqCmp.eq_of_compare h1
      subst hk
      decide
    · by_cases h2 : compare testIdMaxPrev k = .eq
      · have hk : testIdMaxPrev = k := LawfulEqCmp.eq_of_compare h2
        subst hk
        decide
      · by_cases h3 : compare testIdMax k = .eq
        · have hk : testIdMax = k := LawfulEqCmp.eq_of_compare h3
          subst hk
          decide
        · simp [h1, h2, h3]
  refine ⟨
    RawAATree.toList_leaf,
    RawAATree.toList_node 1 .leaf testId1 11 .leaf,
    RawAATree.toList_setLevel 2 sampleRawTree,
    RawAATree.toList_skew sampleRawTree,
    RawAATree.toList_split sampleRawTree,
    RawAATree.toList_decreaseLevel sampleRawTree,
    RawAATree.toList_skewRight sampleRawTree,
    RawAATree.toList_skewRightRight sampleRawTree,
    RawAATree.toList_splitRight sampleRawTree,
    RawAATree.toList_rebalanceAfterErase sampleRawTree,
    RawAATree.popMin_node_isSome 1 .leaf testId1 11 .leaf,
    RawAATree.size_eq_length_toList sampleRawTree,
    ExtTreeMap0.empty_eq_emptyc,
    ExtTreeMap0.size_empty,
    ExtTreeMap0.get?_empty testId1,
    ExtTreeMap0.getElem?_eq_get? sampleExtMapAsc testIdMax,
    ExtTreeMap0.size_eq_length_toList sampleExtMapAsc,
    ExtTreeMap0.contains_eq_isSome_get? sampleExtMapAsc testIdMaxPrev,
    ExtTreeMap0.get?_insert_self sampleExtMapAsc testId2 22,
    ExtTreeMap0.get?_insert_ne sampleExtMapAsc hne21 22,
    ExtTreeMap0.get?_erase_self (sampleExtMapAsc.insert testId2 22) testId2,
    ExtTreeMap0.get?_erase_ne (sampleExtMapAsc.insert testId2 22) hne2Max,
    ExtTreeMap0.insert_insert_same sampleExtMapAsc testId1 77 11,
    ExtTreeMap0.erase_insert_self_of_none sampleExtMapAsc testId2 22 hnone2,
    hextElem,
    (ExtTreeMap0.toList_inj).mpr hextElem,
    ExtTreeMap0.agreesWithStdRaw_empty,
    ⟨(ExtTreeMap0.execMapTraceExt0_snoc_insert (cmp := compare)
        [.insert testId1 10, .insert testIdMax 90, .insert testId1 77, .insert testId2 20, .erase testIdMax]
        testId3 testId3 33).trans (by decide +kernel),
     by decide +kernel⟩
  ⟩

def entryHeap8 : LocalAllocEntry :=
  ⟨.heap, 8, 8, .mut, [(.init 0x11 none), (.init 0x22 none)]⟩

def entryStack16 : LocalAllocEntry :=
  ⟨.stack, 16, 8, .mut, [(.init 0x33 none)]⟩

def lwPermAsc : LinearAllocWorld :=
  (LinearAllocWorld.empty.insertLive testId1 entryHeap8).insertLive testIdMax entryStack16

def lwPermDesc : LinearAllocWorld :=
  (LinearAllocWorld.empty.insertLive testIdMax entryStack16).insertLive testId1 entryHeap8

def kwPermAsc : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 entryHeap8).insertLive testIdMax entryStack16

def kwPermDesc : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testIdMax entryStack16).insertLive testId1 entryHeap8

/-- **Permutation Burden vs. `KeyedAllocWorld.ext` Canary**: inserting `(testId1, entryHeap8)` and
`(testIdMax, entryStack16)` in opposite orders yields *distinct* `LinearAllocWorld` values
(`lwPermAsc ≠ lwPermDesc`) despite pointwise lookup agreement, whereas `kwPermAsc = kwPermDesc` holds
propositionally in `KeyedAllocWorld`! -/
theorem canary_part1_permutation_burden_vs_keyed_ext :
    lwPermAsc ≠ lwPermDesc ∧
    (∀ id : MiriAllocId, lwPermAsc.findLive? id = lwPermDesc.findLive? id) ∧
    kwPermAsc = kwPermDesc := by
  refine ⟨by decide, ?_, ?_⟩
  · intro id
    unfold lwPermAsc lwPermDesc LinearAllocWorld.insertLive LinearAllocWorld.findLive? LinearAllocWorld.empty
    repeat rw [linearFind?_upsert]
    by_cases h1 : testId1 = id
    · subst h1
      have hne : testIdMax ≠ testId1 := by decide
      simp [hne]
    · by_cases h2 : testIdMax = id
      · subst h2
        simp [h1]
      · simp [h1, h2]
  · apply KeyedAllocWorld.ext
    · rfl
    · rfl
    · intro _; rfl
    · intro id
      unfold kwPermAsc kwPermDesc KeyedAllocWorld.insertLive KeyedAllocWorld.empty
      dsimp only
      repeat rw [ExtTreeMap0.get?_insert]
      repeat rw [ExtTreeMap0.get?_empty]
      by_cases h1 : compare testId1 id = .eq
      · have hk : testId1 = id := LawfulEqCmp.eq_of_compare h1
        subst hk
        decide
      · by_cases h2 : compare testIdMax id = .eq
        · have hk : testIdMax = id := LawfulEqCmp.eq_of_compare h2
          subst hk
          decide
        · simp [h1, h2]
    · intro _; rfl
    · intro _; rfl
    · intro _; rfl

/-- Closed lifecycle canary exercising all `AllocWorldRel` preservation, lookup, uniqueness, and
`linearFind?` helper theorems across `empty -> reserveAllocId -> allocate -> updateLiveBytes ->
setRace -> removeRace -> registerGlobal -> removeLive -> insertDead -> deallocate`. -/
theorem canary_part1_allocWorldRel_lifecycle :
    linearFind? (linearErase (linearUpsert ([] : List (MiriAllocId × Nat)) testId1 5) testId1) testId1 = none ∧
    linearContains [(testId1, 5)] testId1 = (linearFind? [(testId1, 5)] testId1).isSome ∧
    (let lw0 := LinearAllocWorld.empty
     let kw0 := KeyedAllocWorld.empty
     let lw1 := (lw0.reserveAllocId).1
     let kw1 := (kw0.reserveAllocId).1
     let lw2 := (lw1.allocate entryHeap8 1024 (some ⟨1, 10, 5, false, none, []⟩)).1
     let kw2 := (kw1.allocate entryHeap8 1024 (some ⟨1, 10, 5, false, none, []⟩)).1
     let lw8 := ((((lw2.setRace testId2 ⟨2, 20, 12, false, none, []⟩).removeRace testId2).registerGlobal
       ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩).insertLive testId3 entryStack16).removeLive testId3 |>.1.insertDead
       ⟨testId3, 16, 8⟩
     let kw8 := ((((kw2.setRace testId2 ⟨2, 20, 12, false, none, []⟩).removeRace testId2).registerGlobal
       ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩).insertLive testId3 entryStack16).removeLive testId3 |>.1.insertDead
       ⟨testId3, 16, 8⟩
     (lw8.containsId testId2 = kw8.containsId testId2) ∧
     (lw8.isAllocLive testId2 = kw8.isAllocLive testId2) ∧
     (lw8.getAllocInfo testId3 = kw8.getAllocInfo testId3) ∧
     (lw8.getLiveAllocSizeAndAlign testId3 = kw8.getLiveAllocSizeAndAlign testId3) ∧
     KeyedAllocWorld.ofLinear lwPermAsc = kwPermAsc ∧
     (match lw0.updateLiveBytes testId1 [(.init 9 none)], kw0.updateLiveBytes testId1 [(.init 9 none)] with
      | .error e₁, .error e₂ => e₁ = e₂
      | .ok lw', .ok kw' => AllocWorldRel lw' kw'
      | _, _ => False) ∧
     (match lw2.updateLiveBytes testId2 [(.init 0xAA none), (.init 0xBB none)],
          kw2.updateLiveBytes testId2 [(.init 0xAA none), (.init 0xBB none)] with
      | .error e₁, .error e₂ => e₁ = e₂
      | .ok lw', .ok kw' => AllocWorldRel lw' kw'
      | _, _ => False) ∧
     AllocWorldRel
       (lw8.deallocate (.provenanced testId2 0) (some (8, 8)) .heap .ok).1
       (kw8.deallocate (.provenanced testId2 0) (some (8, 8)) .heap .ok).1) := by
  have hlin1 :
      linearFind? (linearErase (linearUpsert ([] : List (MiriAllocId × Nat)) testId1 5) testId1) testId1 = none := by
    rw [linearFind?_linearErase]
    simp
  have hlin2 := linearContains_eq_isSome_linearFind? [(testId1, 5)] testId1
  have r0 := allocWorldRel_empty
  -- `[adv B1]`: A0 instantiated uniqueness on the *same* world twice (`kw0 = kw0`, a tautology);
  -- here two syntactically different keyed constructions — the `foldr` first-match projection and
  -- an `insertLive` history — are identified by `allocWorldRel_keyed_unique`.
  have hrelAsc : AllocWorldRel lwPermAsc kwPermAsc :=
    allocWorldRel_insertLive (allocWorldRel_insertLive r0 testId1 entryHeap8) testIdMax entryStack16
  have huniq : KeyedAllocWorld.ofLinear lwPermAsc = kwPermAsc :=
    allocWorldRel_keyed_unique (allocWorldRel_ofLinear lwPermAsc) hrelAsc
  have hupd_miss := allocWorldRel_updateLiveBytes r0 testId1 [(.init 9 none)]
  have ⟨_, r1⟩ := allocWorldRel_reserveAllocId r0
  have ⟨_, r2⟩ := allocWorldRel_allocate r1 entryHeap8 1024 (some ⟨1, 10, 5, false, none, []⟩)
  have hupd_hit := allocWorldRel_updateLiveBytes r2 testId2 [(.init 0xAA none), (.init 0xBB none)]
  have r3 := allocWorldRel_setRace r2 testId2 ⟨2, 20, 12, false, none, []⟩
  have r4 := allocWorldRel_removeRace r3 testId2
  have r5 := allocWorldRel_registerGlobal r4 ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩
  have r6 := allocWorldRel_insertLive r5 testId3 entryStack16
  have ⟨_, r7⟩ := allocWorldRel_removeLive r6 testId3
  have r8 := allocWorldRel_insertDead r7 ⟨testId3, 16, 8⟩
  have hdealloc := allocWorldRel_deallocate r8 (.provenanced testId2 0) (some (8, 8)) .heap .ok
  exact ⟨
    hlin1,
    hlin2,
    allocWorldRel_containsId_eq r8 testId2,
    allocWorldRel_isAllocLive_eq r8 testId2,
    allocWorldRel_getAllocInfo_eq r8 testId3,
    allocWorldRel_getLiveAllocSizeAndAlign_eq r8 testId3,
    huniq,
    hupd_miss,
    hupd_hit,
    hdealloc.2.2
  ⟩

def worldAtMaxId : KeyedAllocWorld :=
  { KeyedAllocWorld.empty with nextAllocId := 0xFFFF_FFFF_FFFF_FFFF }

/-- Closed canary proving high-water `0xFFFF_FFFF_FFFF_FFFF` reservation succeeds, wraps `nextAllocId`
to `0`, and latches `idSupplyExhausted = true` on the very next `reserveAllocId` (`0` sentinel is
never issued, nor does `1` get re-issued!). -/
theorem canary_part1_highWater_and_wrapAround_exhaustion :
    let wAfterMax := (worldAtMaxId.reserveAllocId).1
    let resMax := (worldAtMaxId.reserveAllocId).2
    let wExhausted := (wAfterMax.reserveAllocId).1
    let resWrap := (wAfterMax.reserveAllocId).2
    let resAfterLatch := (wExhausted.reserveAllocId).2
    resMax = .ok testIdMax ∧
    wAfterMax.nextAllocId = 0 ∧
    wAfterMax.hasIssuedId testIdMax = true ∧
    resWrap = .error .exhausted ∧
    wExhausted.idSupplyExhausted = true ∧
    resAfterLatch = .error .exhausted := by
  have hhigh := keyedReserveAllocId_of_highWater worldAtMaxId
    rfl (by decide)
    (fun id h => by rw [worldAtMaxId, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty] at h; nomatch h)
    (fun id h => by rw [worldAtMaxId, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty] at h; nomatch h)
    (fun id h => by rw [worldAtMaxId, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty] at h; nomatch h)
    (fun id h => by rw [worldAtMaxId, KeyedAllocWorld.empty, ExtTreeMap0.get?_empty] at h; nomatch h)
  dsimp only at hhigh ⊢
  let wAfterExpected : KeyedAllocWorld :=
    { worldAtMaxId with
      nextAllocId := worldAtMaxId.nextAllocId + 1
      issuedIds := worldAtMaxId.issuedIds.insert testIdMax () }
  have hfst : (worldAtMaxId.reserveAllocId).1 = wAfterExpected := congrArg Prod.fst hhigh
  have hsnd : (worldAtMaxId.reserveAllocId).2 = .ok testIdMax := congrArg Prod.snd hhigh
  have hnext0 : wAfterExpected.nextAllocId = 0 := by decide
  have hexh0 : wAfterExpected.idSupplyExhausted = false := rfl
  have hiss : wAfterExpected.hasIssuedId testIdMax = true := by
    unfold KeyedAllocWorld.hasIssuedId wAfterExpected
    dsimp only
    rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_self]
    rfl
  have hwrap := keyedReserveAllocId_wrapAround_latches_exhausted wAfterExpected hexh0 hnext0
  dsimp only at hwrap
  obtain ⟨hresWrap, hlatch, hpersist⟩ := hwrap
  rw [hfst, hsnd]
  exact ⟨rfl, hnext0, hiss, hresWrap, hlatch, congrArg Prod.snd hpersist⟩

def deallocRichKeyedWorld : KeyedAllocWorld :=
  (((((KeyedAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1 ⟨1, 7, 3, false, none, []⟩).insertDead
      ⟨testId2, 32, 16⟩).registerGlobal ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩).insertLive
      testId3 ⟨.heap, 16, 8, .not, [(.init 1 none)]⟩)

def dupDeadEntry : LocalAllocEntry := ⟨.heap, 16, 8, .mut, []⟩

def dupDeadKeyedWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 dupDeadEntry).insertDead ⟨testId1, 4, 4⟩

/-- Closed canary proving all 6 Miri deallocation failure-ordering & post-removal state-retention
properties:
1. Dangling address `.danglingAddress 0x1000` -> `.danglingPointer`,
2. Nonzero offset `.provenanced testId1 4` -> `.nonzeroAllocationOffset` & `testId1` stays live,
3. Double-free `.provenanced testId2 0` with wrong layout & wrong kind -> `.useAfterFree`
   beats layout/kind mismatch,
4. Global vtable `.provenanced testIdMaxPrev 0` -> `.globalAllocationDeallocation _ .vtable`,
5. Post-removal failure (immutable, wrong kind, wrong layout, AND hook fault) detaches `live` & `race`
   and does NOT add `testId1` to `dead`!
6. Duplicate-`dead` entry updates the `dead` tombstone layout *before* reporting `.duplicateDeadAllocation`! -/
theorem canary_part1_deallocate_failure_ordering_and_state_retention :
    (deallocRichKeyedWorld.deallocate (.danglingAddress 0x1000) none .heap .ok).2.2 =
      .error (.danglingPointer 0x1000) ∧
    deallocRichKeyedWorld.deallocate (.provenanced testId1 4) (some (8, 8)) .heap .ok =
      (deallocRichKeyedWorld, none, .error (.nonzeroAllocationOffset testId1 4)) ∧
    (deallocRichKeyedWorld.deallocate (.provenanced testId2 0) (some (999, 64)) .stack .ok).2.2 =
      .error (.useAfterFree testId2) ∧
    deallocRichKeyedWorld.deallocate (.provenanced testIdMaxPrev 0) none .heap .ok =
      (deallocRichKeyedWorld, none, .error (.globalAllocationDeallocation testIdMaxPrev .vtable)) ∧
    (let resK := deallocRichKeyedWorld.deallocate (.provenanced testId1 0) (some (8, 8)) .stack .ok
     resK.2.1 = some (testId1, entryHeap8) ∧
     resK.2.2.isOk = false ∧
     resK.1.findLive? testId1 = none ∧
     resK.1.findRace? testId1 = none ∧
     resK.1.findDead? testId1 = deallocRichKeyedWorld.findDead? testId1) ∧
    (let resH := deallocRichKeyedWorld.deallocate (.provenanced testId1 0) (some (8, 8)) .heap (.protectedBorrowFault 9)
     resH.2.1 = some (testId1, entryHeap8) ∧
     resH.2.2.isOk = false ∧
     resH.1.findLive? testId1 = none ∧
     resH.1.findRace? testId1 = none ∧
     resH.1.findDead? testId1 = deallocRichKeyedWorld.findDead? testId1) ∧
    (let resD := dupDeadKeyedWorld.deallocate (.provenanced testId1 0) (some (16, 8)) .heap .ok
     resD.2.1 = some (testId1, dupDeadEntry) ∧
     resD.2.2 = .error (.duplicateDeadAllocation testId1) ∧
     resD.1.findLive? testId1 = none ∧
     resD.1.findRace? testId1 = none ∧
     resD.1.findDead? testId1 = some ⟨testId1, 16, 8⟩) := by
  have hLive1 : deallocRichKeyedWorld.findLive? testId1 = some entryHeap8 := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotLive2 : deallocRichKeyedWorld.findLive? testId2 = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotGlob2 : deallocRichKeyedWorld.findGlobal? testId2 = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findGlobal? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hDead2 : deallocRichKeyedWorld.findDead? testId2 = some ⟨testId2, 32, 16⟩ := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findDead? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotLiveGlob : deallocRichKeyedWorld.findLive? testIdMaxPrev = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hGlob : deallocRichKeyedWorld.findGlobal? testIdMaxPrev = some ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩ := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findGlobal? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hdf := keyedDeallocate_doubleFree_precedes_layout_and_kind
    deallocRichKeyedWorld testId2 ⟨testId2, 32, 16⟩ hNotLive2 hNotGlob2 hDead2
    (some (999, 64)) .stack .ok
  have hglobErr := keyedDeallocate_global_reports_globalErr
    deallocRichKeyedWorld testIdMaxPrev ⟨testIdMaxPrev, .vtable, 0, 8, .not⟩
    hNotLiveGlob hGlob none .heap .ok
  have hpostKind := keyedDeallocate_postRemovalFailure_retains_detached_state
    deallocRichKeyedWorld testId1 entryHeap8 hLive1 (some (8, 8)) .stack .ok
    (Or.inr (Or.inl (by decide)))
  have hpostHook := keyedDeallocate_postRemovalFailure_retains_detached_state
    deallocRichKeyedWorld testId1 entryHeap8 hLive1 (some (8, 8)) .heap (.protectedBorrowFault 9)
    (Or.inr (Or.inr (Or.inr (by decide))))
  have hDupLive : dupDeadKeyedWorld.findLive? testId1 = some dupDeadEntry := by
    unfold dupDeadKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.insertDead KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hDupDead : dupDeadKeyedWorld.findDead? testId1 = some ⟨testId1, 4, 4⟩ := by
    unfold dupDeadKeyedWorld KeyedAllocWorld.findDead? KeyedAllocWorld.insertLive
      KeyedAllocWorld.insertDead KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hdup := keyedDeallocate_duplicateDead_replaces_before_error
    dupDeadKeyedWorld testId1 dupDeadEntry ⟨testId1, 4, 4⟩ hDupLive rfl hDupDead
  dsimp only at hdf hpostKind hpostHook hdup ⊢
  exact ⟨
    rfl,
    keyedDeallocate_nonzeroOffset_preserves_live deallocRichKeyedWorld testId1 4 (by decide) (some (8, 8)) .heap .ok,
    hdf.2.2.1,
    hglobErr,
    hpostKind,
    hpostHook,
    hdup
  ⟩

/-- `[adv B1]` keyed world: live heap allocation `testId1` whose race clock records a write by
thread `1` at time `7` (last read at `3`). -/
def raceWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1 ⟨1, 7, 3, false, none, []⟩

/-- Linear twin of `raceWorld`. -/
def raceWorldLinear : LinearAllocWorld :=
  (LinearAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1 ⟨1, 7, 3, false, none, []⟩

/-- Linear world with a *shadowed duplicate* `live` key (unreachable by `filter`+`push`). -/
def lwShadow : LinearAllocWorld :=
  { LinearAllocWorld.empty with live := [(testId1, entryHeap8), (testId1, entryStack16)] }

/-- **`[adv B1]` Closed canary — upstream `useAfterFree`, bidirectional totality, race-check order**:
1. Freeing a never-issued id (`testIdMax`) and a double free whose tombstone was GC-pruned
   (`dead := ∅`) both report `.useAfterFree` — `deallocate` never consults `dead`.
2. `AllocWorldRel` is total both ways: a shadowed-duplicate linear world projects with first-match
   semantics, every keyed world has a linear partner, and the relation is the graph of `ofLinear`.
3. The race verdict is computed from the race entry *before* cleanup: a racing actor (thread `2`,
   view `5 < 7`) faults with `DataRace` and the entry is dropped only afterwards; cleaning the entry
   *first* (buggy order) is reported as a lost clock (`MissingVectorClockExtra`, `[adv B2]`) rather
   than the race; a synchronized actor (view `9`) succeeds; a race-free actor then reaches the Tree
   Borrows protector verdict; linear and keyed machines agree. -/
theorem canary_part1_useAfterFree_totality_and_race_order :
    deallocRichKeyedWorld.deallocate (.provenanced testIdMax 0) (some (8, 8)) .heap .ok =
      (deallocRichKeyedWorld, none, .error (.useAfterFree testIdMax)) ∧
    ({ deallocRichKeyedWorld with dead := ∅ } : KeyedAllocWorld).deallocate (.provenanced testId2 0)
        (some (999, 64)) .stack .ok =
      ({ deallocRichKeyedWorld with dead := ∅ }, none, .error (.useAfterFree testId2)) ∧
    (KeyedAllocWorld.ofLinear lwShadow).findLive? testId1 = some entryHeap8 ∧
    AllocWorldRel (LinearAllocWorld.ofKeyed kwPermDesc) kwPermDesc ∧
    (AllocWorldRel lwPermAsc kwPermDesc ↔ kwPermDesc = KeyedAllocWorld.ofLinear lwPermAsc) ∧
    (let r := raceWorld.deallocateMachine (.provenanced testId1 0)
       (some (entryHeap8.sizeBytes, entryHeap8.alignBytes)) entryHeap8.kind ⟨2, 5, []⟩ .ok
     r.2.1 = some (testId1, entryHeap8) ∧
     r.2.2 = .error (.hookFailure "DataRace") ∧
     r.1.findLive? testId1 = none ∧
     r.1.findRace? testId1 = none ∧
     r.1.findDead? testId1 = none ∧
     ((raceWorld.removeRace testId1).deallocateMachine (.provenanced testId1 0)
       (some (entryHeap8.sizeBytes, entryHeap8.alignBytes)) entryHeap8.kind ⟨2, 5, []⟩ .ok).2.2 =
       .error (.hookFailure "MissingVectorClockExtra")) ∧
    (raceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨2, 9, []⟩ .ok).2.2 =
      .ok () ∧
    (raceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨1, 0, []⟩
      (.protectedBorrowFault 4)).2.2 = .error (.hookFailure "TreeBorrowsProtectedDealloc") ∧
    (let (lw', detL, outL) := raceWorldLinear.deallocateMachine (.provenanced testId1 0)
       (some (8, 8)) .heap ⟨2, 5, []⟩ .ok
     let (kw', detK, outK) := raceWorld.deallocateMachine (.provenanced testId1 0)
       (some (8, 8)) .heap ⟨2, 5, []⟩ .ok
     detL = detK ∧ outL = outK ∧ AllocWorldRel lw' kw') := by
  have hNotLiveMax : deallocRichKeyedWorld.findLive? testIdMax = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotGlobMax : deallocRichKeyedWorld.findGlobal? testIdMax = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findGlobal? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotLive2 : deallocRichKeyedWorld.findLive? testId2 = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have hNotGlob2 : deallocRichKeyedWorld.findGlobal? testId2 = none := by
    unfold deallocRichKeyedWorld KeyedAllocWorld.findGlobal? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.insertDead KeyedAllocWorld.registerGlobal
      KeyedAllocWorld.empty
    dsimp only
    repeat rw [ExtTreeMap0.get?_insert]
    rw [ExtTreeMap0.get?_empty]
    decide
  have huafMax := keyedDeallocate_absent_reports_useAfterFree deallocRichKeyedWorld testIdMax
    hNotLiveMax hNotGlobMax (some (8, 8)) .heap .ok ∅
  have huaf2 := keyedDeallocate_absent_reports_useAfterFree deallocRichKeyedWorld testId2
    hNotLive2 hNotGlob2 (some (999, 64)) .stack .ok ∅
  have hshadow : (KeyedAllocWorld.ofLinear lwShadow).findLive? testId1 = some entryHeap8 :=
    ((allocWorldRel_ofLinear lwShadow).live_eq testId1).symm.trans (by decide)
  have hRaceLive : raceWorld.findLive? testId1 = some entryHeap8 := by
    unfold raceWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive KeyedAllocWorld.setRace
      KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hRaceNoDead : raceWorld.findDead? testId1 = none := by
    unfold raceWorld KeyedAllocWorld.findDead? KeyedAllocWorld.insertLive KeyedAllocWorld.setRace
      KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_empty]
  have hRaceClk : raceWorld.findRace? testId1 = some ⟨1, 7, 3, false, none, []⟩ := by
    unfold raceWorld KeyedAllocWorld.findRace? KeyedAllocWorld.insertLive KeyedAllocWorld.setRace
      KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hracy : raceDeallocVerdict ⟨2, 5, []⟩ ⟨1, 7, 3, false, none, []⟩ ≠ .ok := by decide
  have horder := keyedDeallocateMachine_race_checked_before_cleanup raceWorld testId1 entryHeap8
    ⟨1, 7, 3, false, none, []⟩ ⟨2, 5, []⟩ .ok hRaceLive (by decide) rfl hRaceNoDead hRaceClk hracy
  have hrelRace : AllocWorldRel raceWorldLinear raceWorld :=
    allocWorldRel_setRace (allocWorldRel_insertLive allocWorldRel_empty testId1 entryHeap8)
      testId1 ⟨1, 7, 3, false, none, []⟩
  have hmachine := allocWorldRel_deallocateMachine hrelRace (.provenanced testId1 0)
    (some (8, 8)) .heap ⟨2, 5, []⟩ .ok (.configured true)
  exact ⟨
    huafMax.1,
    huaf2.2,
    hshadow,
    allocWorldRel_ofKeyed kwPermDesc,
    allocWorldRel_iff_eq_ofLinear lwPermAsc kwPermDesc,
    horder,
    rfl,
    rfl,
    hmachine
  ⟩

def sameWriterForeignReadWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1 ⟨1, 2, 7, false, some 2, []⟩

def zstRaceEntry : LocalAllocEntry :=
  ⟨.heap, 0, 1, .mut, []⟩

def zstRaceWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 zstRaceEntry).setRace testId1 ⟨1, 99, 88, false, some 2, []⟩

/-- **`[adv A1]` Closed canary — same-writer foreign-read deallocation race & ZST race-skip**:
1. Thread `1` writes at `t = 2`, Thread `2` reads concurrently at `t = 7` (`lastReaderThread = some 2`),
   and **Thread `1` itself** (`actor = ⟨1, 3, []⟩`, `actor.thread == writerThread`!) deallocates before
   synchronizing with Thread `2` (`3 < 7`): faults with `.hookFailure "DataRace"` (`[adv B1]` missed
   this by gating both checks behind `writerThread != actor.thread`).
2. Once Thread `1` synchronizes (`actor = ⟨1, 7, []⟩`), its deallocation succeeds with `.ok ()`.
3. Deallocating a zero-sized (`sizeBytes = 0`) heap allocation skips the per-byte race detector
   (`DataRace.runRangeLoop` `remaining = 0`) and succeeds with `.ok ()` while dropping the `race`
   entry (`[adv B1]` falsely reported `DataRace` on ZST deallocations). -/
theorem canary_part1_sameWriter_foreignRead_and_zst_race_fixes :
    (sameWriterForeignReadWorld.deallocateMachine (.provenanced testId1 0)
      (some (8, 8)) .heap ⟨1, 3, []⟩ .ok).2.2 = .error (.hookFailure "DataRace") ∧
    (sameWriterForeignReadWorld.deallocateMachine (.provenanced testId1 0)
      (some (8, 8)) .heap ⟨1, 7, []⟩ .ok).2.2 = .ok () ∧
    (let rz := zstRaceWorld.deallocateMachine (.provenanced testId1 0)
       (some (0, 1)) .heap ⟨3, 0, []⟩ .ok
     rz.2.2 = .ok () ∧ rz.1.findLive? testId1 = none ∧ rz.1.findRace? testId1 = none) := by
  have hLiveSW : sameWriterForeignReadWorld.findLive? testId1 = some entryHeap8 := by
    unfold sameWriterForeignReadWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hNoDeadSW : sameWriterForeignReadWorld.findDead? testId1 = none := by
    unfold sameWriterForeignReadWorld KeyedAllocWorld.findDead? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_empty]
  have hClkSW : sameWriterForeignReadWorld.findRace? testId1 = some ⟨1, 2, 7, false, some 2, []⟩ := by
    unfold sameWriterForeignReadWorld KeyedAllocWorld.findRace? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hsw := keyedDeallocateMachine_sameWriter_foreignRead_races
    sameWriterForeignReadWorld testId1 entryHeap8 ⟨1, 2, 7, false, some 2, []⟩ ⟨1, 3, []⟩ 2 .ok
    hLiveSW (by decide) rfl hNoDeadSW hClkSW rfl rfl (by decide) (by decide)
  have hLiveZ : zstRaceWorld.findLive? testId1 = some zstRaceEntry := by
    unfold zstRaceWorld KeyedAllocWorld.findLive? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hNoDeadZ : zstRaceWorld.findDead? testId1 = none := by
    unfold zstRaceWorld KeyedAllocWorld.findDead? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_empty]
  have hClkZ : zstRaceWorld.findRace? testId1 = some ⟨1, 99, 88, false, some 2, []⟩ := by
    unfold zstRaceWorld KeyedAllocWorld.findRace? KeyedAllocWorld.insertLive
      KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hzst := keyedDeallocateMachine_zst_skips_race_check
    zstRaceWorld testId1 zstRaceEntry ⟨1, 99, 88, false, some 2, []⟩ ⟨3, 0, []⟩ hLiveZ rfl rfl hNoDeadZ hClkZ
  exact ⟨hsw, by decide +kernel, hzst⟩

/-- **`[adv B2]` Closed canary — race-detector configuration follows `memoryRaceAccess`**:
1. With the (default) configured detector, a live allocation that *lost* its race clock is an
   invalid program (`MissingVectorClockExtra`), even when zero-sized — B1/A1 silently treated a
   missing clock as race-free.
2. With no detector configured (`dataRace = none`), the same deallocation is plain `deallocate`.
3. With a configured but not-yet-detecting detector (single-threaded), a clock that would race
   (`raceWorld` vs. actor view `5 < 7`) is not inspected and the deallocation succeeds. -/
theorem canary_part1_raceDetectorMode_missingClock_and_singleThreaded :
    (let r := (raceWorld.removeRace testId1).deallocateMachine (.provenanced testId1 0)
       (some (entryHeap8.sizeBytes, entryHeap8.alignBytes)) entryHeap8.kind ⟨2, 5, []⟩ .ok
       (.configured true)
     r.2.1 = some (testId1, entryHeap8) ∧
     r.2.2 = .error (.hookFailure "MissingVectorClockExtra") ∧
     r.1.findLive? testId1 = none) ∧
    (let rz := (zstRaceWorld.removeRace testId1).deallocateMachine (.provenanced testId1 0)
       (some (zstRaceEntry.sizeBytes, zstRaceEntry.alignBytes)) zstRaceEntry.kind ⟨3, 0, []⟩ .ok
       (.configured false)
     rz.2.1 = some (testId1, zstRaceEntry) ∧
     rz.2.2 = .error (.hookFailure "MissingVectorClockExtra") ∧
     rz.1.findLive? testId1 = none) ∧
    (raceWorld.removeRace testId1).deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap
        ⟨2, 5, []⟩ .ok .unconfigured =
      (raceWorld.removeRace testId1).deallocate (.provenanced testId1 0) (some (8, 8)) .heap .ok ∧
    raceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨2, 5, []⟩ .ok
        (.configured false) =
      raceWorld.deallocate (.provenanced testId1 0) (some (8, 8)) .heap .ok ∧
    (raceWorld.deallocate (.provenanced testId1 0) (some (8, 8)) .heap .ok).2.2 = .ok () := by
  have hLiveR : (raceWorld.removeRace testId1).findLive? testId1 = some entryHeap8 := by
    unfold raceWorld KeyedAllocWorld.findLive? KeyedAllocWorld.removeRace
      KeyedAllocWorld.insertLive KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hNoRaceR : (raceWorld.removeRace testId1).findRace? testId1 = none := by
    unfold KeyedAllocWorld.findRace? KeyedAllocWorld.removeRace
    exact ExtTreeMap0.get?_erase_self _ _
  have hLiveZR : (zstRaceWorld.removeRace testId1).findLive? testId1 = some zstRaceEntry := by
    unfold zstRaceWorld KeyedAllocWorld.findLive? KeyedAllocWorld.removeRace
      KeyedAllocWorld.insertLive KeyedAllocWorld.setRace KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hNoRaceZR : (zstRaceWorld.removeRace testId1).findRace? testId1 = none := by
    unfold KeyedAllocWorld.findRace? KeyedAllocWorld.removeRace
    exact ExtTreeMap0.get?_erase_self _ _
  have hClk : raceWorld.findRace? testId1 = some ⟨1, 7, 3, false, none, []⟩ := by
    unfold raceWorld KeyedAllocWorld.findRace? KeyedAllocWorld.insertLive KeyedAllocWorld.setRace
      KeyedAllocWorld.empty
    dsimp only
    rw [ExtTreeMap0.get?_insert_self]
  have hmiss := keyedDeallocateMachine_missingClock_invalid (raceWorld.removeRace testId1)
    testId1 entryHeap8 ⟨2, 5, []⟩ .ok true hLiveR rfl hNoRaceR
  have hmissZ := keyedDeallocateMachine_missingClock_invalid (zstRaceWorld.removeRace testId1)
    testId1 zstRaceEntry ⟨3, 0, []⟩ .ok false hLiveZR rfl hNoRaceZR
  have hunconf := keyedDeallocateMachine_unconfigured_eq_deallocate (raceWorld.removeRace testId1)
    (.provenanced testId1 0) (some (8, 8)) .heap ⟨2, 5, []⟩ .ok
  have hsingle := keyedDeallocateMachine_notDetecting_eq_deallocate raceWorld testId1 0
    ⟨1, 7, 3, false, none, []⟩ (some (8, 8)) .heap ⟨2, 5, []⟩ .ok hClk
  exact ⟨hmiss, hmissZ, hunconf, hsingle, by decide +kernel⟩

def multiReaderRaceWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1
    ⟨1, 10, 4, false, some 2, [(3, 6)]⟩

/-- **`[adv A2]` Closed canary — `allocateMachine` → `deallocateMachine` lifecycle pairing &
multi-reader / per-thread vector-clock race detection**:
1. `allocWorldRel_allocateMachine` preserves `AllocWorldRel` and `keyedAllocateMachine_deallocateMachine_sameThread_ok`
   proves that `allocateMachine` followed by same-thread `deallocateMachine` succeeds with `.ok ()`
   under all three `RaceDetectorMode` settings (`unconfigured`, `configured false`, `configured true`).
2. Thread `1` writes at `t = 10`, Thread `2` reads at `t = 4`, Thread `3` also reads at `t = 6`
   (`extraReaders = [(3, 6)]`), and Thread `4` (`observedTimestamp = 10`, `perThreadView = [(1, 10),
   (2, 4), (3, 2)]`) has synchronized with Thread `1` and Thread `2` — so a scalar-clock projection
   (`10 >= 6`) would falsely call it race-free, whereas `actor.viewFor 3 = 2 < 6` catches the
   unsynchronized reader on Thread `3` (`DataRace`)! Once Thread `4` synchronizes with Thread `3`
   (`(3, 6)`), deallocation succeeds with `.ok ()`. -/
theorem canary_part1_allocateMachine_lifecycle_and_perThread_multiReader_clock :
    (let (lw1, outL) := LinearAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured true)
     let (kw1, outK) := KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured true)
     outL = outK ∧ AllocWorldRel lw1 kw1 ∧
     (kw1.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨7, 42, []⟩ .ok
       (.configured true)).2.2 = .ok ()) ∧
    (let (kwU, _) := KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 .unconfigured
     (kwU.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨7, 42, []⟩ .ok
       .unconfigured).2.2 = .ok ()) ∧
    (let (kwS, _) := KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured false)
     (kwS.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap ⟨7, 42, []⟩ .ok
       (.configured false)).2.2 = .ok ()) ∧
    (multiReaderRaceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap
      ⟨4, 10, [(1, 10), (2, 4), (3, 2)]⟩ .ok).2.2 = .error (.hookFailure "DataRace") ∧
    (multiReaderRaceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap
      ⟨4, 10, [(1, 10), (2, 4), (3, 6)]⟩ .ok).2.2 = .ok () := by
  have hrelAlloc := allocWorldRel_allocateMachine allocWorldRel_empty entryHeap8 1024 7 42 (.configured true)
  let kwC := (KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured true)).1
  have hallocC : KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured true) =
      (kwC, .ok testId1) := rfl
  have hokC := keyedAllocateMachine_deallocateMachine_sameThread_ok
    KeyedAllocWorld.empty kwC entryHeap8 1024 7 42 ⟨7, 42, []⟩ (.configured true) testId1
    hallocC rfl rfl rfl
  let kwU := (KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 .unconfigured).1
  have hallocU : KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 .unconfigured =
      (kwU, .ok testId1) := rfl
  have hokU := keyedAllocateMachine_deallocateMachine_sameThread_ok
    KeyedAllocWorld.empty kwU entryHeap8 1024 7 42 ⟨7, 42, []⟩ .unconfigured testId1
    hallocU rfl rfl rfl
  let kwS := (KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured false)).1
  have hallocS : KeyedAllocWorld.empty.allocateMachine entryHeap8 1024 7 42 (.configured false) =
      (kwS, .ok testId1) := rfl
  have hokS := keyedAllocateMachine_deallocateMachine_sameThread_ok
    KeyedAllocWorld.empty kwS entryHeap8 1024 7 42 ⟨7, 42, []⟩ (.configured false) testId1
    hallocS rfl rfl rfl
  have hLiveM : multiReaderRaceWorld.findLive? testId1 = some entryHeap8 :=
    ExtTreeMap0.get?_insert_self _ _ _
  have hNoDeadM : multiReaderRaceWorld.findDead? testId1 = none :=
    ExtTreeMap0.get?_empty _
  have hClkM : multiReaderRaceWorld.findRace? testId1 =
      some ⟨1, 10, 4, false, some 2, [(3, 6)]⟩ :=
    ExtTreeMap0.get?_insert_self _ _ _
  have hracePerThread := keyedDeallocateMachine_perThreadClock_catches_unsynced_reader
    multiReaderRaceWorld testId1 entryHeap8 ⟨1, 10, 4, false, some 2, [(3, 6)]⟩
    ⟨4, 10, [(1, 10), (2, 4), (3, 2)]⟩ 3 6 .ok
    hLiveM (by decide) rfl hNoDeadM hClkM (by decide) (by decide) (by decide)
  exact ⟨⟨hrelAlloc.1, hrelAlloc.2, hokC.2.1⟩, hokU.2.1, hokS.2.1, hracePerThread, by decide +kernel⟩

def unlistedReaderRaceWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.insertLive testId1 entryHeap8).setRace testId1
    ⟨1, 2, 5, false, some 3, []⟩

/-- **`[adv A3]` Closed canary — `DeallocActor.ofVClock` unlisted-zero semantics vs. nonzero scalar
fallback (`VectorClock.lean:221–223`)**:
Thread `1` writes at `t = 2`, Thread `3` (absent from `entries = [(2, 10)]`) reads at `t = 5`:
1. `DeallocActor.ofVClock 1 [(2, 10)]` evaluates `viewFor 3 = 0` (`VTimestamp.ZERO`) and catches
   `.error (.hookFailure "DataRace")`.
2. Mixing a nonzero scalar fallback `observedTimestamp = 10` with the partial list `[(2, 10)]`
   (`⟨1, 10, [(2, 10)]⟩`) falsely treats unlisted Thread `3` as observed at `t = 10 ≥ 5` and
   unsoundly returns `.ok ()` (closing B3's §1.1 scope `(iv)` gap). -/
theorem canary_part1_ofVClock_unlisted_zero_vs_nonzeroFallback_race :
    (DeallocActor.ofVClock 1 [(2, 10)]).viewFor 3 = 0 ∧
    (unlistedReaderRaceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap
      (DeallocActor.ofVClock 1 [(2, 10)]) .ok).2.2 = .error (.hookFailure "DataRace") ∧
    (unlistedReaderRaceWorld.deallocateMachine (.provenanced testId1 0) (some (8, 8)) .heap
      ⟨1, 10, [(2, 10)]⟩ .ok).2.2 = .ok () := by
  have hLive : unlistedReaderRaceWorld.findLive? testId1 = some entryHeap8 :=
    ExtTreeMap0.get?_insert_self _ _ _
  have hNoDead : unlistedReaderRaceWorld.findDead? testId1 = none :=
    ExtTreeMap0.get?_empty _
  have hClk : unlistedReaderRaceWorld.findRace? testId1 = some ⟨1, 2, 5, false, some 3, []⟩ :=
    ExtTreeMap0.get?_insert_self _ _ _
  exact deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback
    unlistedReaderRaceWorld testId1 entryHeap8 ⟨1, 2, 5, false, some 3, []⟩
    1 3 10 [(2, 10)] hLive (by decide) rfl hNoDead hClk rfl rfl (by decide) (by decide)
    (by decide) rfl (by decide)

/-! ## Section 2: Part 2A & 2B Closed Canaries (`charon#1619/#1620` + `minirust#295`) -/

def unpinFreezeFacts : RetagTypeFacts := ⟨true, true, true⟩
def unpinNonFreezeFacts : RetagTypeFacts := ⟨false, true, true⟩
def pinnedFacts : RetagTypeFacts := ⟨true, false, true⟩

/-- Closed canary for `selectFnEntryPolicy`, `!Unpin` guard (`PhantomPinned`), `FnParamRetagMap`,
`TreeTagNode.isProtected_eq_toByteRangePerm`, and ZST (`len = 0`, `&mut ()`) no-write invariance. -/
theorem canary_part2A_policy_and_unpin_and_zst :
    selectFnEntryPolicy pinnedFacts .mutable true .writableChildWrite = none ∧
    selectFnEntryPolicy pinnedFacts .box true .rustcNoWritable = none ∧
    selectFnEntryPolicy unpinNonFreezeFacts .mutable true .rustcNoWritable =
      some ⟨.reservedFrz false, .reservedFrz false, .reservedFrz false, .strong, false⟩ ∧
    (((FnParamRetagMap.mk ∅).set 1 .rustcNoWritable).policyFor 1 = .rustcNoWritable) ∧
    (((FnParamRetagMap.mk ∅).set 1 .rustcNoWritable).policyFor 2 = .writableChildWrite) ∧
    (TreeTagNode.mk 3 10 0 4 (.reservedFrz false) (some 1) (some 1)).isProtected
      (ProtectorSet.empty.insert 1) = true ∧
    execFnEntryMutRetag (mkTwoBranchBorrowWorld 10 0 []) 1 0 0 unpinFreezeFacts true .writableChildWrite true =
      execFnEntryMutRetag (mkTwoBranchBorrowWorld 10 0 []) 1 0 0 unpinFreezeFacts true .rustcNoWritable true := by
  have hset1 := FnParamRetagMap.policyFor_set ⟨∅⟩ 1 1 .rustcNoWritable
  have hset2 := FnParamRetagMap.policyFor_set ⟨∅⟩ 1 2 .rustcNoWritable
  simp only [↓reduceIte] at hset1
  have hne12 : (1 : Nat) ≠ 2 := by decide
  simp only [hne12, ↓reduceIte] at hset2
  have hdef2 : (FnParamRetagMap.mk ∅).policyFor 2 = .writableChildWrite := rfl
  have hprot := TreeTagNode.isProtected_eq_toByteRangePerm
    (TreeTagNode.mk 3 10 0 4 (.reservedFrz false) (some 1) (some 1))
    (ProtectorSet.empty.insert 1)
  exact ⟨
    pinned_mutable_or_box_fnEntry_skips_retag pinnedFacts .mutable true .writableChildWrite (Or.inl rfl) rfl,
    pinned_mutable_or_box_fnEntry_skips_retag pinnedFacts .box true .rustcNoWritable (Or.inr rfl) rfl,
    selectFnEntryPolicy_rustcNoWritable_mut unpinNonFreezeFacts true rfl,
    hset1,
    hset2.trans hdef2,
    hprot.trans rfl,
    fnEntryMutRetag_zst_no_write (mkTwoBranchBorrowWorld 10 0 []) 1 0 unpinFreezeFacts true true
  ⟩

/-- Closed canary proving `#[rustc_no_writable]` separation on uninitialized pointees & `.frozen`
siblings (`core::mem::forget` / `<[MaybeUninit<u8>]>::get_mut`), active-protector foreign-write
conflict (`Anneal.Memory.protector_forbids_conflicting_foreign_write`), foreign-read `conflicted`
latch + child-write UB, and subsequent explicit child-write `.unique` activation! -/
theorem canary_part2A_uninit_frozen_sibling_and_conflicted_latch :
    let uninitBytes : List AbstractByte := [.uninit, .uninit, .uninit, .uninit]
    let initWrite : List AbstractByte := [(.init 0x2A none), (.init 0x00 none), (.init 0x00 none), (.init 0x00 none)]
    let w := mkTwoBranchBorrowWorld 10 4 uninitBytes
    (execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .rustcNoWritable true).isOk = true ∧
    execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .writableChildWrite true =
      .error .uninitializedPointeeWrite ∧
    (execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .writableChildWrite false =
      .ok ({
        w with
        nodes := [
          ⟨3, 10, 0, 4, .unique, some 1, some 1⟩,
          ⟨2, 10, 0, 4, .disabled, none, some 1⟩,
          ⟨1, 10, 0, 4, .unique, none, none⟩
        ]
        activeProtectors := ProtectorSet.empty.insert 1
        nextTag := 4
        nextProtector := 2
      }, some 3)) ∧
    (let childProtected : TreeTagNode := ⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩
     let nodesAfter := [
       childProtected,
       ⟨2, 10, 0, 4, .frozen, none, some 1⟩,
       ⟨1, 10, 0, 4, .unique, none, none⟩
     ]
     stepNodeOnRangeWrite nodesAfter (ProtectorSet.empty.insert 1) 10 0 4 1 childProtected =
       .error .protectedForeignConflict ∧
     stepForeignWriteByteRange (ProtectorSet.empty.insert 1) childProtected.toByteRangePerm 10 0 4 = none) ∧
    (let ps := ProtectorSet.empty.insert 1
     let wAfter : FnEntryBorrowWorld := {
       allocId := 10
       bytes := uninitBytes
       nodes := [
         ⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩,
         ⟨2, 10, 0, 4, .frozen, none, some 1⟩,
         ⟨1, 10, 0, 4, .unique, none, none⟩
       ]
       activeProtectors := ps
       nextTag := 4
       nextProtector := 2
     }
     let wLatched : FnEntryBorrowWorld := {
       wAfter with
       nodes := [
         ⟨3, 10, 0, 4, .reservedFrz true, some 1, some 1⟩,
         ⟨2, 10, 0, 4, .frozen, none, some 1⟩,
         ⟨1, 10, 0, 4, .unique, none, none⟩
       ]
     }
     execBorrowRead wAfter 2 0 4 = .ok wLatched ∧
     execBorrowWrite wLatched 3 0 initWrite = .error .conflictedProtectedChildWrite ∧
     execBorrowWrite wAfter 3 0 initWrite =
       .ok {
         wAfter with
         nodes := [
           ⟨3, 10, 0, 4, .unique, some 1, some 1⟩,
           ⟨2, 10, 0, 4, .disabled, none, some 1⟩,
           ⟨1, 10, 0, 4, .unique, none, none⟩
         ]
         bytes := initWrite
       }) := by
  have hsep := rustcNoWritable_preserves_uninit_and_frozen_sibling
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl
  dsimp only at hsep
  obtain ⟨hokNoWr, huninitFail, hwrAct⟩ := hsep
  have hprotConflict := stepNodeOnRangeWrite_foreign_protected_conflict
    [⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩,
     ⟨2, 10, 0, 4, .frozen, none, some 1⟩,
     ⟨1, 10, 0, 4, .unique, none, none⟩]
    (ProtectorSet.empty.insert 1) 10 0 4 1
    ⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩
    rfl rfl rfl rfl (by decide) (by decide)
  have hlatch := rustcNoWritable_foreignRead_latches_conflicted
    10 [.uninit, .uninit, .uninit, .uninit]
    [(.init 0x2A none), (.init 0x00 none), (.init 0x00 none), (.init 0x00 none)]
    [(.init 0x2A none), (.init 0x00 none), (.init 0x00 none), (.init 0x00 none)]
    (by decide) (by decide) rfl
  refine ⟨by rw [hokNoWr]; rfl, huninitFail rfl, hwrAct, hprotConflict, hlatch⟩

def extractNextMachineState? : MirStepNode → Option MachineState
  | .tau (.running s') => some s'
  | _ => none

def protoRefMutU32Ty : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
def protoRefMutUnitTy : Ty := { kind := .ref .mut (.tuple []), layoutIdx := 0 }

def protoMultiParamDecls : List LocalDecl := [
  { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := some "_0" },
  { mutability := .not, ty := protoRefMutU32Ty, debugName := some "_1_no_writable" },
  { mutability := .not, ty := protoRefMutU32Ty, debugName := some "_2_writable" },
  { mutability := .not, ty := protoRefMutUnitTy, debugName := some "_3_zst" }
]

def protoEmptyLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [] }

def protoMultiParamMap : FnParamRetagMap :=
  ((FnParamRetagMap.mk ∅).set 1 .rustcNoWritable).set 2 .writableChildWrite

def protoMultiParamState : MachineState where
  frame := {
    blockIdx := 0
    stmtIdx := 0
    locals := [
      .init .unit,
      .init (.ptr ⟨10, 0⟩ 8),
      .init (.ptr ⟨20, 0⟩ 8),
      .init (.ptr ⟨30, 0⟩ 8)
    ]
  }
  memory := {
    emptyMemory with
    borrows := [
      { tag := 10, targetLocal := 4, targetProjection := [], perm := .unique, rangeOffset := 0, rangeLen := 4 },
      { tag := 11, targetLocal := 4, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 4, parentTag := some 10 },
      { tag := 20, targetLocal := 5, targetProjection := [], perm := .unique, rangeOffset := 0, rangeLen := 4 },
      { tag := 21, targetLocal := 5, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 4, parentTag := some 20 },
      { tag := 30, targetLocal := 6, targetProjection := [], perm := .unique, rangeOffset := 0, rangeLen := 0 },
      { tag := 31, targetLocal := 6, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 0, parentTag := some 30 }
    ]
    nextTag := 100
    nextProtector := 1
  }

def protoFrozenParentState : MachineState :=
  { protoMultiParamState with
    memory := {
      protoMultiParamState.memory with
      borrows := [
        { tag := 20, targetLocal := 5, targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 4 }
      ]
    } }

/-- **Operational `Trusted.MirSemantics.MachineState` Multi-Parameter Overlay Canary**:
1. Parameter `_1` (`#[rustc_no_writable]`): `evalFnEntryRetagWithParamMap` equals `evalStmt`, mints
   protected child `tag = 100` in `.reservedFrz false`, and preserves coexisting sibling `tag = 11`
   at `.frozen`!
2. Parameter `_2` (`.writableChildWrite`, `rangeLen = 4`): activates child `tag = 100` to `.unique`
   and disables coexisting `.frozen` sibling `tag = 21` to `.disabled` — AND when `_2`'s parent tag
   `20` is `.frozen`, `evalFnEntryRetagWithParamMap` faults with `MirStepNode.fail .ub`!
3. Parameter `_3` (ZST `&mut ()`, `rangeLen = 0`): `applyParamFnEntryImplicitWrite_zst_noop` leaves
   coexisting `.frozen` sibling `tag = 31` alive at `.frozen` even under `.writableChildWrite`! -/
theorem canary_part2A_trusted_machineState_multiParam_overlay :
    evalFnEntryRetagWithParamMap protoMultiParamState ⟨1, []⟩ "fn.rs:1:1"
      protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true =
      evalStmt protoMultiParamState ⟨.retag .fnEntry ⟨1, []⟩, "fn.rs:1:1"⟩
        protoMultiParamDecls protoEmptyLayouts ∧
    (match extractNextMachineState?
        (evalFnEntryRetagWithParamMap protoMultiParamState ⟨1, []⟩ "fn.rs:1:1"
          protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true) with
     | some s1 =>
       (lookupBorrow s1.memory.borrows 100).map BorrowEntry.perm = some (.reservedFrz false) ∧
       (lookupBorrow s1.memory.borrows 11).map BorrowEntry.perm = some .frozen
     | none => False) ∧
    (match extractNextMachineState?
        (evalFnEntryRetagWithParamMap protoMultiParamState ⟨2, []⟩ "fn.rs:1:2"
          protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true) with
     | some s2 =>
       (lookupBorrow s2.memory.borrows 100).map BorrowEntry.perm = some .unique ∧
       (lookupBorrow s2.memory.borrows 21).map BorrowEntry.perm = some .disabled
     | none => False) ∧
    evalFnEntryRetagWithParamMap protoFrozenParentState ⟨2, []⟩ "fn.rs:1:2"
      protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true =
      MirStepNode.fail .ub ∧
    (match extractNextMachineState?
        (evalFnEntryRetagWithParamMap protoMultiParamState ⟨3, []⟩ "fn.rs:1:3"
          protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true) with
     | some s3 =>
       (lookupBorrow s3.memory.borrows 100).map BorrowEntry.perm = some (.reservedFrz false) ∧
       (lookupBorrow s3.memory.borrows 31).map BorrowEntry.perm = some .frozen
     | none => False) := by
  have hpol1 : protoMultiParamMap.policyFor (⟨1, []⟩ : Place).local_ = .rustcNoWritable := by
    unfold protoMultiParamMap
    rw [FnParamRetagMap.policyFor_set, FnParamRetagMap.policyFor_set]
    decide
  have heqStmt := evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt
    protoMultiParamState ⟨1, []⟩ "fn.rs:1:1" protoMultiParamDecls protoEmptyLayouts
    true protoMultiParamMap true hpol1
  let hzstHead : BorrowEntry :=
    { tag := 100, targetLocal := 6, targetProjection := [], perm := .reservedFrz false,
      rangeOffset := 0, rangeLen := 0, protector := some 1, parentTag := some 30 }
  let hzstState : MachineState :=
    { frame := { protoMultiParamState.frame with
        stmtIdx := 1
        locals := [
          .init .unit,
          .init (.ptr ⟨10, 0⟩ 8),
          .init (.ptr ⟨20, 0⟩ 8),
          .init (.ptr ⟨100, 0⟩ 8)
        ] }
      memory := { protoMultiParamState.memory with
        borrows := hzstHead :: protoMultiParamState.memory.borrows
        nextTag := 101
        activeProtectors := [1]
        nextProtector := 2 } }
  have hzstNoop := applyParamFnEntryImplicitWrite_zst_noop
    100 hzstState hzstHead protoMultiParamState.memory.borrows
    protoMultiParamDecls protoEmptyLayouts ⟨3, []⟩ true protoMultiParamMap true rfl rfl
  have hraw3 : evalStmt protoMultiParamState ⟨.retag .fnEntry ⟨3, []⟩, "fn.rs:1:3"⟩
      protoMultiParamDecls protoEmptyLayouts = .tau (.running hzstState) := rfl
  have heval3 : evalFnEntryRetagWithParamMap protoMultiParamState ⟨3, []⟩ "fn.rs:1:3"
      protoMultiParamDecls protoEmptyLayouts true protoMultiParamMap true =
      .tau (.running hzstState) := by
    unfold evalFnEntryRetagWithParamMap
    rw [hraw3]
    exact hzstNoop
  refine ⟨heqStmt, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ?_⟩
  rw [heval3]
  exact ⟨rfl, rfl⟩

/-- Closed canary for Part 2B pure `Freeze` (`static S: i32 = 42`) and pure `UnsafeCell`
(`static A: AtomicI32 = AtomicI32::new(0)`), including multi-write `.cell` persistence across two
successive interior-mutable writes! -/
theorem canary_part2B_pureFreeze_and_pureUnsafeCell_statics :
    let init4 : List AbstractByte := [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)]
    let w1 : List AbstractByte := [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)]
    let w2 : List AbstractByte := [(.init 77 none), (.init 1 none), (.init 0 none), (.init 0 none)]
    evalRawMutStaticWrite (retagStaticPreserved 50 (.freezeScalar 4) init4) 0 w1 = .ub ∧
    (∃ stErased, evalRawMutStaticWrite (retagStaticErased 50 (.freezeScalar 4) init4) 0 w1 = .ok stErased) ∧
    (match evalRawMutStaticWrite (retagStaticPreserved 51 (.unsafeCell 4) init4) 0 w1 with
     | .ok st1 =>
       st1.bytes = w1 ∧
       (match evalRawMutStaticWrite st1 0 w2 with
        | .ok st2 => st2.bytes = w2 ∧ st2.perms = st1.perms
        | .ub => False)
     | .ub => False) := by
  have hfrz := static_pureFreeze_preserved_ub_vs_erased_unsound
    50 4 [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)] [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)]
    (by decide) (by decide) (by decide) (by decide)
  have hcell1 := static_pureUnsafeCell_preserved_write_ok
    51 4 [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)] [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)]
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨hfrz.1, hfrz.2, ?_⟩
  rw [hcell1]
  exact ⟨rfl, rfl, rfl⟩

/-- `#[repr(C)] struct MixedStatic { flag: u8, /* pad[1..4) */ counter: AtomicI32, /* trailPad[8..12) */ }` -/
def mixedCompositeStaticDesc : StaticTyDesc :=
  .composite 12 [(0, .freezeScalar 1), (4, .unsafeCell 4)]

def mixedCompositeInitBytes : List AbstractByte :=
  List.replicate 12 ((.init 0 none))

/-- Closed canary proving byte-range `FreezeVisitor` precision on a mixed composite `static` with
both inter-field padding `[1, 4)` and trailing padding `[8, 12)`:
1. Writing 4 bytes to the `AtomicI32` `UnsafeCell` field `[4, 8)` succeeds (`.ok`)!
2. Writing 1 byte to the `u8` `Freeze` field `[0, 1)` faults with `.ub`!
3. Writing 1 byte to inter-field padding `[1, 2)` faults with `.ub`!
4. Writing 1 byte to trailing padding `[8, 9)` faults with `.ub`!
5. Writing 2 bytes straddling `[3, 5)` (padding + `UnsafeCell`) faults with `.ub`! -/
theorem canary_part2B_mixed_composite_static_with_padding :
    staticFreezeSegments mixedCompositeStaticDesc =
      (12, [
        ⟨0, 1, .freeze⟩,
        ⟨1, 3, .freeze⟩,
        ⟨4, 4, .unsafeCell⟩,
        ⟨8, 4, .freeze⟩
      ]) ∧
    (let st := retagStaticPreserved 60 mixedCompositeStaticDesc mixedCompositeInitBytes
     (match evalRawMutStaticWrite st 4 [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)] with
      | .ok _ => true
      | .ub => false) = true ∧
     evalRawMutStaticWrite st 0 [(.init 1 none)] = .ub ∧
     evalRawMutStaticWrite st 1 [(.init 1 none)] = .ub ∧
     evalRawMutStaticWrite st 8 [(.init 1 none)] = .ub ∧
     evalRawMutStaticWrite st 3 [(.init 1 none), (.init 2 none)] = .ub) := by
  decide +kernel

/-- **`[adv B1]` Closed canary — upstream `RetagPolicy.create` mirror & world-level protector
conflict**:
1. Pinned upstream `create` at `FnEntry` gives `&mut T` an inside permission `.Unique` (parent
   `.Write` access) with implicit writes, but `.ReservedFrz false` (parent `.Read` access only) under
   `#[rustc_no_writable]`; implicit writes never occur outside `FnEntry` (`.Default` mode).
2. `selectFnEntryPolicy_eq_upstream_create` instantiated on both policies.
3. After a `rustcNoWritable` retag, a write through the parent tag `1` faults with
   `.protectedForeignConflict` at the `execBorrowWrite` level. -/
theorem canary_part2A_upstream_create_mirror_and_parent_write_conflict :
    (MiriRetagPolicyMirror.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨true, false⟩).map
      (·.freezePermission) = some .Unique ∧
    MiriRetagPolicyMirror.Permission.associatedAccess .Unique = some .Write ∧
    (MiriRetagPolicyMirror.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨true, true⟩).map
      (·.freezePermission) = some (.ReservedFrz false) ∧
    MiriRetagPolicyMirror.Permission.associatedAccess (.ReservedFrz false) = some .Read ∧
    (MiriRetagPolicyMirror.create ⟨true, true, true⟩ .Mutable .Default ⟨true, false⟩).map
      (·.freezePermission) = some (.ReservedFrz false) ∧
    (selectFnEntryPolicy unpinFreezeFacts .mutable true .writableChildWrite).map
        (fun s => (s.freezePerm, s.nonfreezePerm, s.outsidePerm, some s.protector,
          s.performsImplicitWrite)) =
      (MiriRetagPolicyMirror.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨true, false⟩).map
        (fun n => (n.freezePermission.toAbstractPerm, n.nonfreezePermission.toAbstractPerm,
          n.outsidePermission.toAbstractPerm,
          n.protector.map MiriRetagPolicyMirror.ProtectorKind.toStrength,
          n.freezePermission.associatedAccess == some .Write)) ∧
    (selectFnEntryPolicy unpinNonFreezeFacts .box true .rustcNoWritable).map
        (fun s => (s.freezePerm, s.nonfreezePerm, s.outsidePerm, some s.protector,
          s.performsImplicitWrite)) =
      (MiriRetagPolicyMirror.create ⟨true, true, false⟩ .Box .FnEntry ⟨true, true⟩).map
        (fun n => (n.freezePermission.toAbstractPerm, n.nonfreezePermission.toAbstractPerm,
          n.outsidePermission.toAbstractPerm,
          n.protector.map MiriRetagPolicyMirror.ProtectorKind.toStrength,
          n.freezePermission.associatedAccess == some .Write)) ∧
    execBorrowWrite {
        allocId := 10
        bytes := [.uninit, .uninit, .uninit, .uninit]
        nodes := [
          ⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩,
          ⟨2, 10, 0, 4, .frozen, none, some 1⟩,
          ⟨1, 10, 0, 4, .unique, none, none⟩
        ]
        activeProtectors := ProtectorSet.empty.insert 1
        nextTag := 4
        nextProtector := 2
      } 1 0 [(.init 0x2A none), (.init 0x00 none), (.init 0x00 none), (.init 0x00 none)] =
      .error .protectedForeignConflict := by
  have hmirW := selectFnEntryPolicy_eq_upstream_create unpinFreezeFacts .mutable true false
  have hmirN := selectFnEntryPolicy_eq_upstream_create unpinNonFreezeFacts .box true true
  have hparent := rustcNoWritable_parentWrite_faults_on_protected_child 10
    [.uninit, .uninit, .uninit, .uninit]
    [(.init 0x2A none), (.init 0x00 none), (.init 0x00 none), (.init 0x00 none)]
    (by decide) (by decide)
  exact ⟨rfl, rfl, rfl, rfl, rfl, hmirW, hmirN, hparent⟩

/-- **`[adv A1]` Closed canary — upstream `RetagPipeline.accessTreeForReborrow` single-access
equivalence & disabled-ancestor diagnostic separation**:
1. Node-level `stepNode_read_then_childWrite_eq_parentWrite` on a foreign `.frozen` sibling,
2. Unconditional world-level equality `execFnEntryMutRetag_eq_upstream_when_no_implicitWrite` under
   `rustcNoWritable`,
3. Two-branch world equality `execFnEntryMutRetag_mkTwoBranch_eq_upstream` under
   `writableChildWrite`, and
4. Exact diagnostic separation `execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream`
   (`.parentDisabled` vs. `.ancestorWriteForbidden`) when a grandparent is `.disabled`! -/
theorem canary_part2A_upstream_reborrow_equivalence_and_disabled_ancestor :
    (let allNodes : List TreeTagNode :=
       [⟨2, 10, 0, 4, .frozen, none, some 1⟩, ⟨1, 10, 0, 4, .unique, none, none⟩]
     let withChild : List TreeTagNode :=
       ⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩ :: allNodes
     let ps := ProtectorSet.empty
     let ps' := ps.insert 1
     let sib : TreeTagNode := ⟨2, 10, 0, 4, .frozen, none, some 1⟩
     (stepNodeOnRangeRead allNodes ps 10 0 4 1 sib >>=
        stepNodeOnRangeWrite withChild ps' 10 0 4 3) =
      stepNodeOnRangeWrite allNodes ps 10 0 4 1 sib) ∧
    (let w := mkTwoBranchBorrowWorld 10 4 [.uninit, .uninit, .uninit, .uninit]
     execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .rustcNoWritable false =
       execFnEntryMutRetagUpstream w 1 0 4 unpinFreezeFacts true .rustcNoWritable ∧
     execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .writableChildWrite false =
       execFnEntryMutRetagUpstream w 1 0 4 unpinFreezeFacts true .writableChildWrite) ∧
    (let wDis : FnEntryBorrowWorld := {
       allocId := 10
       bytes := [.uninit, .uninit, .uninit, .uninit]
       nodes := [⟨2, 10, 0, 4, .unique, none, some 1⟩, ⟨1, 10, 0, 4, .disabled, none, none⟩]
       activeProtectors := ProtectorSet.empty
       nextTag := 3
       nextProtector := 1
     }
     execFnEntryMutRetag wDis 2 0 4 unpinFreezeFacts true .writableChildWrite false =
       .error .parentDisabled ∧
     execFnEntryMutRetagUpstream wDis 2 0 4 unpinFreezeFacts true .writableChildWrite =
       .error .ancestorWriteForbidden) := by
  have hnode := stepNode_read_then_childWrite_eq_parentWrite
    [⟨2, 10, 0, 4, .frozen, none, some 1⟩, ⟨1, 10, 0, 4, .unique, none, none⟩]
    [⟨3, 10, 0, 4, .reservedFrz false, some 1, some 1⟩,
     ⟨2, 10, 0, 4, .frozen, none, some 1⟩, ⟨1, 10, 0, 4, .unique, none, none⟩]
    ProtectorSet.empty (ProtectorSet.empty.insert 1) 10 0 4 1 3
    ⟨2, 10, 0, 4, .frozen, none, some 1⟩
    rfl rfl (fun h _ _ => by nomatch h)
  have hnoWr := execFnEntryMutRetag_eq_upstream_when_no_implicitWrite
    (mkTwoBranchBorrowWorld 10 4 [.uninit, .uninit, .uninit, .uninit])
    1 0 4 unpinFreezeFacts true .rustcNoWritable (.inl rfl)
  have htwoBr := execFnEntryMutRetag_mkTwoBranch_eq_upstream
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts true .writableChildWrite (by decide)
  have hdiv := execFnEntryMutRetag_disabledGrandparent_diverges_from_upstream
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl
  exact ⟨hnode, ⟨hnoWr, htwoBr⟩, hdiv⟩

/-- **`[adv B2]` Closed canary — two-pass vs. upstream reborrow diverge without any `.disabled`
node**: a `.frozen` parent listed before a protected `.unique` foreign node makes the two-pass model
report the read pass's `.protectedForeignConflict`, while upstream's single parent write stops at the
frozen parent with `.ancestorWriteForbidden` (A1's docstring called the disabled-grandparent witness
"the sole case"). -/
theorem canary_part2A_frozenParent_protectedChild_divergence :
    (let w : FnEntryBorrowWorld := {
       allocId := 10
       bytes := [.uninit, .uninit, .uninit, .uninit]
       nodes := [
         ⟨1, 10, 0, 4, .frozen, none, none⟩,
         ⟨5, 10, 0, 4, .unique, some 7, some 1⟩
       ]
       activeProtectors := ProtectorSet.empty.insert 7
       nextTag := 6
       nextProtector := 8
     }
     execFnEntryMutRetag w 1 0 4 unpinFreezeFacts true .writableChildWrite false =
       .error .protectedForeignConflict ∧
     execFnEntryMutRetagUpstream w 1 0 4 unpinFreezeFacts true .writableChildWrite =
       .error .ancestorWriteForbidden) :=
  execFnEntryMutRetag_frozenParent_protectedChild_diverges_from_upstream 10 4
    [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl

def multiLevelBorrowWorld : FnEntryBorrowWorld where
  allocId := 10
  bytes := [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit]
  nodes := [
    ⟨4, 10, 0, 4, .frozen, none, some 2⟩,
    ⟨3, 10, 4, 4, .reservedFrz false, some 1, some 1⟩,
    ⟨2, 10, 0, 4, .reservedIM, none, some 1⟩,
    ⟨1, 10, 0, 8, .unique, none, none⟩
  ]
  activeProtectors := ProtectorSet.empty.insert 1
  nextTag := 5
  nextProtector := 2

/-- **`[adv A2]` Closed canary — `execFnEntryMutRetagUpstream` reversed-list traversal bug,
arbitrary-world 3-model equivalence (`execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors`),
and arbitrary-world `.frozen` preservation (`sourceOrder_rustcNoWritable_preserves_all_frozen_nodes`)**:
1. On actual `childNode :: nodes` insertion order `[⟨5 (protected .unique child)⟩, ⟨1 (.frozen parent)⟩]`,
   `execFnEntryMutRetagUpstream` visits foreign child `5` before accessed parent `1` and falsely
   reports `.protectedForeignConflict`, violating `TraversalTree.traverse` (`localEvents ++
   foreignEvents`), whereas `execFnEntryMutRetagSourceOrder` visits parent `1` first and reports
   `.ancestorWriteForbidden`!
2. On a 4-node multi-level borrow world (`root 1 -> mid 2 -> grandchild 4 (.frozen)`, plus disjoint
   protected sibling `3`), `BorrowTreeTagsWF` and `AncestorsWritableIn` hold at `parentTag = 2`, so
   `execFnEntryMutRetag`, `execFnEntryMutRetagUpstream`, AND `execFnEntryMutRetagSourceOrder` are
   propositionally equal across both `.writableChildWrite` and `.rustcNoWritable`!
3. Under `.rustcNoWritable` on `multiLevelBorrowWorld`, `sourceOrder_rustcNoWritable_preserves_all_frozen_nodes`
   guarantees grandchild `4` (`.frozen` at depth 2) survives in `w'.nodes`! -/
theorem canary_part2A_sourceOrder_traversal_and_arbitraryWorld_equivalence :
    (let wChildFirst : FnEntryBorrowWorld := {
       allocId := 10
       bytes := [.uninit, .uninit, .uninit, .uninit]
       nodes := [
         ⟨5, 10, 0, 4, .unique, some 7, some 1⟩,
         ⟨1, 10, 0, 4, .frozen, none, none⟩
       ]
       activeProtectors := ProtectorSet.empty.insert 7
       nextTag := 6
       nextProtector := 8
     }
     execFnEntryMutRetagUpstream wChildFirst 1 0 4 unpinFreezeFacts true .writableChildWrite =
       .error .protectedForeignConflict ∧
     execFnEntryMutRetagSourceOrder wChildFirst 1 0 4 unpinFreezeFacts true .writableChildWrite =
       .error .ancestorWriteForbidden) ∧
    (execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite false =
       execFnEntryMutRetagUpstream multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite ∧
     execFnEntryMutRetagUpstream multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite =
       execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite) ∧
    (match execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .rustcNoWritable with
     | .ok (w', some _) => TreeTagNode.mk 4 10 0 4 .frozen none (some 2) ∈ w'.nodes
     | _ => False) := by
  have hrev := execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl
  have hwf : BorrowTreeTagsWF multiLevelBorrowWorld := by
    intro n hmem
    unfold multiLevelBorrowWorld at hmem
    rcases List.mem_cons.mp hmem with rfl | h1
    · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide, fun pr hpr => nomatch hpr⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide,
          fun pr hpr => by injection hpr with hpr'; subst hpr'; decide⟩
      · rcases List.mem_cons.mp h2 with rfl | h3
        · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide, fun pr hpr => nomatch hpr⟩
        · rcases List.mem_cons.mp h3 with rfl | h4
          · refine ⟨by decide, (fun p hp => nomatch hp), (fun pr hpr => nomatch hpr)⟩
          · nomatch h4
  have hwrit : AncestorsWritableIn multiLevelBorrowWorld 2 := by
    intro n hmem hanc _
    unfold multiLevelBorrowWorld at hmem hanc
    rcases List.mem_cons.mp hmem with rfl | h1
    · nomatch hanc
    · rcases List.mem_cons.mp h1 with rfl | h2
      · nomatch hanc
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact ⟨by decide, by decide, fun hc => nomatch hc⟩
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact ⟨by decide, by decide, fun hc => nomatch hc⟩
          · nomatch h4
  have heq3 := execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors
    multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite hwf hwrit
  let wExpected : FnEntryBorrowWorld := {
    multiLevelBorrowWorld with
    nodes := ⟨5, 10, 0, 4, .reservedFrz false, some 2, some 2⟩ :: multiLevelBorrowWorld.nodes
    activeProtectors := multiLevelBorrowWorld.activeProtectors.insert 2
    nextTag := 6
    nextProtector := 3
  }
  have hrunNoWr :
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .rustcNoWritable =
        .ok (wExpected, some 5) := rfl
  have hpres := sourceOrder_rustcNoWritable_preserves_all_frozen_nodes
    multiLevelBorrowWorld wExpected 2 0 4 5 unpinFreezeFacts true hrunNoWr
    ⟨4, 10, 0, 4, .frozen, none, some 2⟩ (List.mem_cons_self ..) rfl
  refine ⟨hrev, heq3, ?_⟩
  rw [hrunNoWr]
  exact hpres

/-- **`[adv B3]` Closed canary — success-path equivalence of all three `FnEntry` models, failure
agreement with error-only divergence**:
1. On the well-formed child-first world (`BorrowTreeTagsWF`), two-pass `execFnEntryMutRetag` and
   ancestor-first `execFnEntryMutRetagSourceOrder` *both fail*, but with different diagnostics
   (`.protectedForeignConflict` vs. `.ancestorWriteForbidden`), so the equivalence below cannot be
   strengthened to equality of results.
2. On `multiLevelBorrowWorld`, the two-pass success result transfers — via
   `execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok`, not by recomputation — to the flat
   single-pass and ancestor-first models, under both `.writableChildWrite` and `.rustcNoWritable`. -/
theorem canary_part2A_successEquivalence_and_errorOnlyDivergence :
    (let wChildFirst : FnEntryBorrowWorld := {
       allocId := 10
       bytes := [.uninit, .uninit, .uninit, .uninit]
       nodes := [
         ⟨5, 10, 0, 4, .unique, some 7, some 1⟩,
         ⟨1, 10, 0, 4, .frozen, none, none⟩
       ]
       activeProtectors := ProtectorSet.empty.insert 7
       nextTag := 6
       nextProtector := 8
     }
     BorrowTreeTagsWF wChildFirst ∧
     execFnEntryMutRetag wChildFirst 1 0 4 unpinFreezeFacts true .writableChildWrite false =
       .error .protectedForeignConflict ∧
     execFnEntryMutRetagSourceOrder wChildFirst 1 0 4 unpinFreezeFacts true .writableChildWrite =
       .error .ancestorWriteForbidden) ∧
    (∃ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .writableChildWrite
        false = .ok r ∧
      execFnEntryMutRetagUpstream multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true
        .writableChildWrite = .ok r ∧
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true
        .writableChildWrite = .ok r) ∧
    (∃ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true .rustcNoWritable
        false = .ok r ∧
      execFnEntryMutRetagSourceOrder multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true
        .rustcNoWritable = .ok r) := by
  have hwfML : BorrowTreeTagsWF multiLevelBorrowWorld := by
    intro n hmem
    unfold multiLevelBorrowWorld at hmem
    rcases List.mem_cons.mp hmem with rfl | h1
    · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide, fun pr hpr => nomatch hpr⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide,
          fun pr hpr => by injection hpr with hpr'; subst hpr'; decide⟩
      · rcases List.mem_cons.mp h2 with rfl | h3
        · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide, fun pr hpr => nomatch hpr⟩
        · rcases List.mem_cons.mp h3 with rfl | h4
          · refine ⟨by decide, (fun p hp => nomatch hp), (fun pr hpr => nomatch hpr)⟩
          · nomatch h4
  have hwfCF : BorrowTreeTagsWF {
      allocId := 10
      bytes := [.uninit, .uninit, .uninit, .uninit]
      nodes := [
        ⟨5, 10, 0, 4, .unique, some 7, some 1⟩,
        ⟨1, 10, 0, 4, .frozen, none, none⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 7
      nextTag := 6
      nextProtector := 8 } := by
    intro n hmem
    rcases List.mem_cons.mp hmem with rfl | h1
    · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide,
        fun pr hpr => by injection hpr with hpr'; subst hpr'; decide⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact ⟨by decide, (fun p hp => nomatch hp), (fun pr hpr => nomatch hpr)⟩
      · nomatch h2
  have hrev := execFnEntryMutRetagUpstream_reversedList_violates_traversalOrder
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl
  obtain ⟨rW, hW⟩ : ∃ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true
      .writableChildWrite false = .ok r := ⟨_, rfl⟩
  have hiffW := execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok multiLevelBorrowWorld 2 0 4
    unpinFreezeFacts true .writableChildWrite hwfML rW
  obtain ⟨rN, hN⟩ : ∃ r, execFnEntryMutRetag multiLevelBorrowWorld 2 0 4 unpinFreezeFacts true
      .rustcNoWritable false = .ok r := ⟨_, rfl⟩
  have hiffN := execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok multiLevelBorrowWorld 2 0 4
    unpinFreezeFacts true .rustcNoWritable hwfML rN
  exact ⟨⟨hwfCF, by decide, hrev.2⟩, ⟨rW, hW, hiffW.1.mp hW, hiffW.2.mp (hiffW.1.mp hW)⟩,
    ⟨rN, hN, hiffN.2.mp (hiffN.1.mp hN)⟩⟩

/-- **`[adv A3]` Closed canary — bottom-up `ancestorPathNodes` local diagnostic precedence vs.
flat-list `checkAncestorsM` (`Traversal.lean:45–53, 114`)**:
On a well-formed (`BorrowTreeTagsWF`) root-first world `[⟨1 (.frozen root)⟩, ⟨2 (protected
.reservedFrz true child, parent = some 1)⟩]` retagging `parentTag = 2` under `.writableChildWrite`:
1. `ancestorPathNodes` visits accessed node `2` first (`ancestorPathNodes_head`),
2. A2's flat-list `checkAncestorsM` visits root `1` first and reports `.ancestorWriteForbidden`,
3. Upgraded `execFnEntryMutRetagSourceOrder` walks `ancestorPathNodes` bottom-up (`[2, 1]`) and
   reports `.conflictedProtectedChildWrite` (discharging B3 open item `(i)`). -/
theorem canary_part2A_bottomUp_ancestorPath_precedence :
    let wRootFirst : FnEntryBorrowWorld := {
      allocId := 10
      bytes := [.uninit, .uninit, .uninit, .uninit]
      nodes := [
        ⟨1, 10, 0, 4, .frozen, none, none⟩,
        ⟨2, 10, 0, 4, .reservedFrz true, some 7, some 1⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 7
      nextTag := 3
      nextProtector := 8
    }
    BorrowTreeTagsWF wRootFirst ∧
    (ancestorPathNodes wRootFirst.nodes (wRootFirst.nodes.length + 1) 2).head? =
      findTagNode? wRootFirst.nodes 2 ∧
    checkAncestorsM wRootFirst.nodes 2
      (stepNodeOnRangeWrite wRootFirst.nodes wRootFirst.activeProtectors 10 0 4 2)
      wRootFirst.nodes = .error .ancestorWriteForbidden ∧
    execFnEntryMutRetagSourceOrder wRootFirst 2 0 4 unpinFreezeFacts true .writableChildWrite =
      .error .conflictedProtectedChildWrite := by
  have hwfRF : BorrowTreeTagsWF {
      allocId := 10
      bytes := [.uninit, .uninit, .uninit, .uninit]
      nodes := [
        ⟨1, 10, 0, 4, .frozen, none, none⟩,
        ⟨2, 10, 0, 4, .reservedFrz true, some 7, some 1⟩
      ]
      activeProtectors := ProtectorSet.empty.insert 7
      nextTag := 3
      nextProtector := 8 } := by
    intro n hmem
    rcases List.mem_cons.mp hmem with rfl | h1
    · exact ⟨by decide, (fun p hp => nomatch hp), (fun pr hpr => nomatch hpr)⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · refine ⟨by decide, fun p hp => by injection hp with hp'; subst hp'; decide,
          fun pr hpr => by injection hpr with hpr'; subst hpr'; decide⟩
      · nomatch h2
  have hhead := ancestorPathNodes_head
    [⟨1, 10, 0, 4, .frozen, none, none⟩, ⟨2, 10, 0, 4, .reservedFrz true, some 7, some 1⟩] 2 2
  have hsep := execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors
    10 4 [.uninit, .uninit, .uninit, .uninit] unpinFreezeFacts (by decide) (by decide) rfl
  exact ⟨hwfRF, hhead, hsep⟩

/-- **`[adv B1]` Closed canary — `charon#1620` separation under Miri's allocation mutability**:
a mixed `(Freeze, UnsafeCell)` static is interned *mutable*, so the read-only check does not save
the erased lowering: writing the `Freeze` `flag` byte through pre-`#1620` erased
`&raw const STATIC` succeeds (genuinely unsound), the preserved temporary retag faults, and the
`UnsafeCell` field stays writable. A pure `Freeze` static, by contrast, is interned read-only, so
Miri catches the erased write anyway (A0's pure-`Freeze` separation needs a semantics without
allocation mutability). -/
theorem canary_part2B_mixed_static_erasure_unsound_under_miri_mutability :
    staticAllocMutability mixedCompositeStaticDesc = .mut ∧
    staticAllocMutability (.unsafeCell 4) = .mut ∧
    (match evalRawMutStaticWriteMiri mixedCompositeStaticDesc
        (retagStaticErased 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 0
        [(.init 1 none)] with
     | .ok st => st.bytes.head? == some (.init 1 none)
     | .ub => false) = true ∧
    evalRawMutStaticWriteMiri mixedCompositeStaticDesc
      (retagStaticPreserved 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 0
      [(.init 1 none)] = .ub ∧
    (match evalRawMutStaticWriteMiri mixedCompositeStaticDesc
        (retagStaticPreserved 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 4
        [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)] with
     | .ok _ => true
     | .ub => false) = true ∧
    (staticAllocMutability (.freezeScalar 4) = .not ∧
     evalRawMutStaticWriteMiri (.freezeScalar 4)
       (retagStaticErased 50 (.freezeScalar 4)
         [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)]) 0
       [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)] = .ub ∧
     evalRawMutStaticWriteMiri (.freezeScalar 4)
       (retagStaticPreserved 50 (.freezeScalar 4)
         [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)]) 0
       [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)] = .ub) := by
  have hpure := static_pureFreeze_erased_write_caught_by_readOnly_alloc 50 4 0
    [(.init 42 none), (.init 0 none), (.init 0 none), (.init 0 none)]
    [(.init 99 none), (.init 0 none), (.init 0 none), (.init 0 none)] (by decide)
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, hpure⟩

/-- **`[adv A1]` Closed canary — general mixed-static Miri separation (`static_mixed_miri_separation`
& `static_mixed_miri_unsafeCell_write_ok`) at non-default tags (`rootTag = 10, childTag = 20`) and
multiple byte offsets**:
1. Writing to inter-field padding (`writeOff = 1`) OR trailing padding (`writeOff = 8`) on
   `mixedCompositeStaticDesc` faults with `.ub` under `retagStaticPreservedAt 10 20` while
   unsoundly succeeding under `retagStaticErasedAt 10`!
2. Writing 4 bytes to the `AtomicI32` `UnsafeCell` sub-range (`writeOff = 4`) succeeds on
   `retagStaticPreservedAt 10 20` and preserves every segment permission! -/
theorem canary_part2B_general_mixed_static_miri_theorems :
    (staticAllocMutability mixedCompositeStaticDesc = .mut ∧
     evalRawMutStaticWriteMiri mixedCompositeStaticDesc
       (retagStaticPreservedAt 10 20 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 1
       [(.init 7 none)] = .ub ∧
     ∃ st', evalRawMutStaticWriteMiri mixedCompositeStaticDesc
       (retagStaticErasedAt 10 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 1
       [(.init 7 none)] = .ok st') ∧
    (staticAllocMutability mixedCompositeStaticDesc = .mut ∧
     evalRawMutStaticWriteMiri mixedCompositeStaticDesc
       (retagStaticPreservedAt 10 20 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 8
       [(.init 9 none)] = .ub ∧
     ∃ st', evalRawMutStaticWriteMiri mixedCompositeStaticDesc
       (retagStaticErasedAt 10 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 8
       [(.init 9 none)] = .ok st') ∧
    evalRawMutStaticWriteMiri mixedCompositeStaticDesc
      (retagStaticPreservedAt 10 20 60 mixedCompositeStaticDesc mixedCompositeInitBytes) 4
      [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)] =
      .ok {
        retagStaticPreservedAt 10 20 60 mixedCompositeStaticDesc mixedCompositeInitBytes with
        bytes := (writeAbstractBytesAt mixedCompositeInitBytes 4
          [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)]).getD
          mixedCompositeInitBytes
      } := by
  have hhasUC : ∃ uc ∈ (staticFreezeSegments mixedCompositeStaticDesc).2, uc.kind = .unsafeCell :=
    ⟨⟨4, 4, .unsafeCell⟩, by decide, rfl⟩
  have hpad1 : ∃ frz ∈ (staticFreezeSegments mixedCompositeStaticDesc).2,
      frz.kind = .freeze ∧ byteRangesOverlapBool frz.offset frz.len 1 1 = true :=
    ⟨⟨1, 3, .freeze⟩, by decide, rfl, rfl⟩
  have hpad8 : ∃ frz ∈ (staticFreezeSegments mixedCompositeStaticDesc).2,
      frz.kind = .freeze ∧ byteRangesOverlapBool frz.offset frz.len 8 1 = true :=
    ⟨⟨8, 4, .freeze⟩, by decide, rfl, rfl⟩
  have hsep1 := static_mixed_miri_separation mixedCompositeStaticDesc 10 20 60 1
    mixedCompositeInitBytes [(.init 7 none)]
    (by decide) (by decide) (by decide) (by decide) hhasUC hpad1
  have hsep8 := static_mixed_miri_separation mixedCompositeStaticDesc 10 20 60 8
    mixedCompositeInitBytes [(.init 9 none)]
    (by decide) (by decide) (by decide) (by decide) hhasUC hpad8
  have hucOk := static_mixed_miri_unsafeCell_write_ok mixedCompositeStaticDesc 10 20 60 4
    mixedCompositeInitBytes [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)]
    (by decide) (by decide) (by decide) (by decide) hhasUC (by decide)
  exact ⟨hsep1, hsep8, hucOk⟩

/-- **`[adv A3]` Closed canary — zero-sized `UnsafeCell<()>` composite static separation under Miri
allocation mutability (`rustc_const_eval/src/interpret/intern.rs:222–229` + `FreezeVisitor.lean:69`)**:
On `static S: (u8, UnsafeCell<()>) = (42, UnsafeCell::new(()))` (`zstUcStaticDesc`):
1. `FreezeVisitor` skips the `0`-byte `UnsafeCell<()>`, emitting **only** `[⟨0, 1, .freeze⟩]` (zero
   `.unsafeCell` segments — B1's segment-scan `staticAllocMutability` falsely returned `.not`!),
2. Yet `isSyntacticFreeze = false`, so rustc (`intern.rs:225`) interns `S` with
   `staticAllocMutability = .mut`,
3. Under `evalRawMutStaticWriteMiri`, `charon#1620`'s preserved temporary retag faults with `.ub` on
   mutating byte `0`, whereas pre-`#1620` erased `&raw const S` unsoundly succeeds with `.ok`! -/
theorem canary_part2B_zstUnsafeCell_composite_static_miri_separation :
    let desc : StaticTyDesc := .composite 1 [(0, .freezeScalar 1), (1, .unsafeCell 0)]
    (staticFreezeSegments desc).2 = [⟨0, 1, .freeze⟩] ∧
    ((staticFreezeSegments desc).2.any (fun seg => seg.kind == .unsafeCell)) = false ∧
    desc.isSyntacticFreeze = false ∧
    staticAllocMutability desc = .mut ∧
    evalRawMutStaticWriteMiri desc
      (retagStaticPreservedAt 10 20 70 desc [(.init 42 none)]) 0 [(.init 99 none)] = .ub ∧
    ∃ st', evalRawMutStaticWriteMiri desc
      (retagStaticErasedAt 10 70 desc [(.init 42 none)]) 0 [(.init 99 none)] = .ok st' :=
  static_zstUnsafeCell_composite_miri_separation 10 20 70 1 0
    [(.init 42 none)] [(.init 99 none)] (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Section 3: Part 3A, 3B, & 3C Closed Canaries (`lean-miri#75/#79/#82`) -/

/-- Closed canary for Part 3A (`lean-miri#79`):
1. Agreement between `isSyntacticallySized` / `validateRawPtrFastPath` and `computeTyLayout` /
   `validateRawPtrLayoutFirst` on layout-valid sized & unsized types (`[u8; 64]`, `(u32, [u16; 8])`,
   `(u32, [u8])`),
2. Strict separation on `*const [u8; usize::MAX]` and nested `*const [[u8; 2]; usize::MAX]` (both
   null `.thin 0 none` and dangling `.thin 16 none`), plus oversized aggregate tail
   `*const (u32, [u8; usize::MAX])` vs. safe reference `&[u8; usize::MAX]`,
3. Slice DST `*const [u8]` contrast (`thin` rejected, `wideSlice` accepted), and `ProtoTy.toRigidTy`
   correspondence. -/
theorem canary_part3A_syntacticSized_agreement_and_separation :
    isSyntacticallySized (.array .u8 64) = true ∧
    fieldsTailSyntacticallySized true [.u32, .array .u16 8] = true ∧
    validateRawPtrFastPath maxRepresentableSize64 (.tuple [.u32, .array .u16 8]) (.thin 16 none) =
      validateRawPtrLayoutFirst maxRepresentableSize64 (.tuple [.u32, .array .u16 8]) (.thin 16 none) ∧
    validateRawPtrFastPath maxRepresentableSize64 (.tuple [.u32, .slice .u8]) (.thin 16 none) =
      validateRawPtrLayoutFirst maxRepresentableSize64 (.tuple [.u32, .slice .u8]) (.thin 16 none) ∧
    validateRawPtrFastPath maxRepresentableSize64 (.array .u8 usizeMax64) (.thin 0 none) = .ok () ∧
    validateRawPtrLayoutFirst maxRepresentableSize64 (.array .u8 usizeMax64) (.thin 0 none) =
      .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64)) ∧
    validateSafeThinRef maxRepresentableSize64 KeyedAllocWorld.empty (.array .u8 usizeMax64) 16 (some testId1) =
      .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64)) ∧
    validateRawPtrFastPath maxRepresentableSize64 (.array (.array .u8 2) usizeMax64) (.thin 16 none) = .ok () ∧
    validateRawPtrLayoutFirst maxRepresentableSize64 (.array (.array .u8 2) usizeMax64) (.thin 16 none) =
      .error (.layoutErr (.sizeOverflow (2 * usizeMax64) maxRepresentableSize64)) ∧
    validateRawPtrFastPath maxRepresentableSize64 (.tuple [.u32, .array .u8 usizeMax64]) (.thin 0 none) = .ok () ∧
    validateRawPtrFastPath maxRepresentableSize64 (.slice .u8) (.thin 16 none) = .error .expectedWideSliceMeta ∧
    validateRawPtrFastPath maxRepresentableSize64 (.slice .u8) (.wideSlice 16 none 5) = .ok () ∧
    (ProtoTy.array .u8 usizeMax64).toRigidTy = RigidTy.array (.uint .u8) usizeMax64 := by
  have hlayTup :
      computeTyLayout maxRepresentableSize64 (.tuple [.u32, .array .u16 8]) =
        .ok ⟨20, 4, true, true⟩ := by decide
  have hlayDstTup :
      computeTyLayout maxRepresentableSize64 (.tuple [.u32, .slice .u8]) =
        .ok ⟨4, 4, false, true⟩ := by decide
  have hszEq := isSyntacticallySized_eq_of_computeTyLayout_ok
    maxRepresentableSize64 (.array .u8 64) ⟨64, 1, true, true⟩ (by decide)
  have hfieldsEq := fieldsTailSyntacticallySized_eq_of_ok
    maxRepresentableSize64 0 1 true [.u32, .array .u16 8] true ⟨20, 4, true, true⟩
    (fun h => nomatch h) (by decide)
  have hag1 := validateRawPtrFastPath_eq_layoutFirst_of_layoutOk
    maxRepresentableSize64 (.tuple [.u32, .array .u16 8]) ⟨20, 4, true, true⟩ (.thin 16 none) hlayTup
  have hag2 := validateRawPtrFastPath_eq_layoutFirst_of_layoutOk
    maxRepresentableSize64 (.tuple [.u32, .slice .u8]) ⟨4, 4, false, true⟩ (.thin 16 none) hlayDstTup
  have hsep1 := oversized_array_rawPtr_separation
    maxRepresentableSize64 KeyedAllocWorld.empty .u8 ⟨1, 1, true, true⟩ usizeMax64 0 none
    rfl rfl (by decide)
  have hsep1Ref := oversized_array_rawPtr_separation
    maxRepresentableSize64 KeyedAllocWorld.empty .u8 ⟨1, 1, true, true⟩ usizeMax64 16 (some testId1)
    rfl rfl (by decide)
  have hsep2 := oversized_array_rawPtr_separation
    maxRepresentableSize64 KeyedAllocWorld.empty (.array .u8 2) ⟨2, 1, true, true⟩ usizeMax64 16 none
    (by decide) rfl (by decide)
  have hslice := slice_dst_rawPtr_requires_wideSliceMeta maxRepresentableSize64 .u8
    ⟨1, 1, true, true⟩ 16 5 none rfl rfl
  exact ⟨
    hszEq,
    hfieldsEq,
    hag1,
    hag2,
    hsep1.1,
    hsep1.2.1,
    hsep1Ref.2.2,
    hsep2.1,
    hsep2.2.1,
    rfl,
    hslice.2.1,
    hslice.2.2,
    rfl
  ⟩

/-- **`[adv A2]` + `[adv B3]` Closed canary — custom struct/tuple DST metadata tails & upstream
unsized-pointee layout query**:
1. `isSyntacticallySized_eq_metadataTail_isNone` & `fieldsTailSized_eq_metadataTail_isNone` classify
   `(u32, [u8])` as `some .sliceMeta` and `MyDynDst(u32, dyn Send)` as `some .dynMeta`; the fast path
   accepts `.wideSlice` on `(u32, [u8])`, a non-null `.wideDyn` on `MyDynDst` (metadata *shape* only —
   vtable identity is `validateRawWideDynPtrMeta`), and `.thin` on `MyExtern(u32, extern F)`
   (`[adv A2]`; A0–B2 rejected all three).
2. `[adv B3]` `unsized_rawPtr_layoutOverflow_rejected_like_upstream`: upstream computes the pointee
   layout for every *unsized* raw-pointer pointee, so `*const ([u8; usize::MAX], [u8])` and
   `*const [[u8; usize::MAX]]` are rejected by **both** validators with `.sizeOverflow` (A2 claimed the
   fast path accepts the former); `validateRawPtrFastPath_eq_layoutFirst_of_unsized` gives the same
   agreement on that DST's thin pointer.
3. `[adv B3]` `validateRawPtrFastPath_ne_layoutFirst_imp`: the observed `*const [u8; usize::MAX]`
   disagreement forces a syntactically `Sized` pointee whose layout fails. -/
theorem canary_part3A_customDst_metadataTail_and_unsizedLayout_like_upstream :
    isSyntacticallySized (.tuple [.u32, .slice .u8]) =
      (unsizedMetadataTail (.tuple [.u32, .slice .u8])).isNone ∧
    fieldsTailSyntacticallySized true [.u32, .dynamic "Send"] =
      (fieldsUnsizedMetadataTail none [.u32, .dynamic "Send"]).isNone ∧
    validateRawPtrFastPath maxRepresentableSize64 (.tuple [.u32, .slice .u8]) (.wideSlice 16 none 5) =
      .ok () ∧
    validateRawPtrFastPath maxRepresentableSize64 (.adt "MyDynDst" [.u32, .dynamic "Send"])
      (.wideDyn 16 none 0x1000 (some testId1)) = .ok () ∧
    validateRawPtrFastPath maxRepresentableSize64 (.adt "MyDynDst" [.u32, .dynamic "Send"])
      (.wideDyn 16 none 0 none) = .error .expectedWideDynMeta ∧
    validateRawPtrFastPath maxRepresentableSize64 (.adt "MyExtern" [.u32, .foreign "ExternF"])
      (.thin 16 none) = .ok () ∧
    (let dstTy : ProtoTy := .tuple [.array .u8 usizeMax64, .slice .u8]
     unsizedMetadataTail dstTy = some .sliceMeta ∧
     validateRawPtrFastPath maxRepresentableSize64 dstTy (.wideSlice 0 none 3) =
       .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64)) ∧
     validateRawPtrLayoutFirst maxRepresentableSize64 dstTy (.wideSlice 0 none 3) =
       .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64)) ∧
     validateRawPtrFastPath maxRepresentableSize64 (.slice (.array .u8 usizeMax64))
       (.wideSlice 0 none 3) =
       .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64))) ∧
    validateRawPtrFastPath maxRepresentableSize64 (.tuple [.array .u8 usizeMax64, .slice .u8])
      (.thin 0 none) =
      validateRawPtrLayoutFirst maxRepresentableSize64 (.tuple [.array .u8 usizeMax64, .slice .u8])
        (.thin 0 none) ∧
    (isSyntacticallySized (.array .u8 usizeMax64) = true ∧
      ∃ e, computeTyLayout maxRepresentableSize64 (.array .u8 usizeMax64) = .error e) := by
  have h1 := isSyntacticallySized_eq_metadataTail_isNone (.tuple [.u32, .slice .u8])
  have h2 := fieldsTailSized_eq_metadataTail_isNone none [.u32, .dynamic "Send"]
  have hrej := unsized_rawPtr_layoutOverflow_rejected_like_upstream
    maxRepresentableSize64 .u8 .u8 ⟨1, 1, true, true⟩ usizeMax64 0 3 none rfl rfl (by decide)
  have hunsz := validateRawPtrFastPath_eq_layoutFirst_of_unsized maxRepresentableSize64
    (.tuple [.array .u8 usizeMax64, .slice .u8]) (.thin 0 none) rfl
  have hsep := oversized_array_rawPtr_separation maxRepresentableSize64 KeyedAllocWorld.empty .u8
    ⟨1, 1, true, true⟩ usizeMax64 0 none rfl rfl (by decide)
  have hne : validateRawPtrFastPath maxRepresentableSize64 (.array .u8 usizeMax64) (.thin 0 none) ≠
      validateRawPtrLayoutFirst maxRepresentableSize64 (.array .u8 usizeMax64) (.thin 0 none) := by
    rw [hsep.1, hsep.2.1]
    intro h
    nomatch h
  exact ⟨h1, h2, rfl, rfl, rfl, rfl, hrej, hunsz,
    validateRawPtrFastPath_ne_layoutFirst_imp maxRepresentableSize64 _ _ hne⟩

def debugPrincipal : PrincipalTraitRef :=
  { traitDefPath := "core::fmt::Debug", normalizedPredicates := [1], methodNames := ["u64::fmt"] }

/-- Closed canary for Part 3B (`lean-miri#75`):
1. `AutoTrait` canonicalization, `VTableKey` injectivity, permutation invariance (`dyn Send + Sync` ==
   `dyn Sync + Send + Send`), and non-collision between principal-less and principal-bearing keys,
2. `buildPrincipalLessVTable_spec` header preservation (`dropInPlace`, `size = 8`, `align = 8`, zero
   synthetic method slots),
3. `VTableRegistry.intern` idempotent deduplication (`vtableRegistry_intern_idempotent`),
4. `resolveVirtualMethod` `.notAMethodSlot` on `dyn Send + Sync` vs. `.ok "u64::fmt"` on
   `dyn Debug + Send + Sync`, and
5. `upcastVTableToAutoTraits` succeeding on `dyn Debug + Send + Sync -> dyn Send` while rejecting
   `dyn Send -> dyn Sync` with `.invalidVTableTrait`! -/
theorem canary_part3B_principalLess_vtables_and_upcast :
    ((canonicalizeAutoTraits [.sync, .send]).headD .unpin = AutoTrait.send) ∧
    (AutoTrait.sync ∈ canonicalizeAutoTraits [.sync, .send, .sync]) ∧
    AutoTraitSet.ofList [.send, .sync] = AutoTraitSet.ofList [.sync, .send, .send] ∧
    mkCanonicalVTableKey .u64 none [.send, .sync] =
      mkCanonicalVTableKey .u64 none [.sync, .send, .send] ∧
    mkCanonicalVTableKey .u64 none [.send, .sync] ≠
      mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync] ∧
    buildVTableDescriptor maxRepresentableSize64 testId1 .u64 "core::ptr::drop_in_place::<u64>"
      (.principalLess [.send, .sync]) =
      .ok ⟨testId1, .u64, .principalLess [.send, .sync], "core::ptr::drop_in_place::<u64>", 8, 8,
        [.dropInPlace "core::ptr::drop_in_place::<u64>", .size 8, .align 8]⟩ ∧
    (match ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64
        .u64 "drop_u64" none [.send, .sync] with
     | .ok (reg1, w1, descSendSync) =>
       reg1.intern w1 maxRepresentableSize64 .u64 "drop_u64" none [.sync, .send, .send] =
         .ok (reg1, w1, descSendSync) ∧
       reg1.byKey.get? (mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync]) = none ∧
       resolveVirtualMethod descSendSync 3 = .error .notAMethodSlot ∧
       ((match reg1.intern w1 maxRepresentableSize64 .u64 "drop_u64" (some debugPrincipal) [.send, .sync] with
         | .ok (reg2, w2, descDebug) =>
           (descDebug.allocId != descSendSync.allocId) &&
           (resolveVirtualMethod descDebug 3 == .ok "u64::fmt") &&
           (match upcastVTableToAutoTraits reg2 w2 maxRepresentableSize64 descDebug [.send] with
            | .ok (_, _, descUp) =>
              (descUp.spec == .principalLess [.send]) &&
              (descUp.sizeBytes == 8) &&
              (descUp.alignBytes == 8) &&
              (match upcastVTableToAutoTraits reg2 w2 maxRepresentableSize64 descUp [.sync] with
               | .error .invalidVTableTrait => true
               | _ => false)
            | .error _ => false)
         | .error _ => false) = true)
     | .error _ => False) := by
  -- `[adv B2]`: A0 "exercised" `rank_injective` via the tautology `send = send`; here it identifies
  -- a *computed* canonical head with `send` from equal ranks.
  have hrank : (canonicalizeAutoTraits [.sync, .send]).headD .unpin = AutoTrait.send :=
    AutoTrait.rank_injective (by decide)
  have hmemCanon : AutoTrait.sync ∈ canonicalizeAutoTraits [.sync, .send, .sync] :=
    (mem_canonicalizeAutoTraits_iff [.sync, .send, .sync] .sync).mpr (by decide)
  have hpermMem : ∀ x : AutoTrait, x ∈ [.send, .sync] ↔ x ∈ [.sync, .send, .send] := by
    intro x; cases x <;> decide
  have hsetEq := AutoTraitSet.ofList_eq_of_mem_iff hpermMem
  have hkeyPerm := mkCanonicalVTableKey_perm_eq .u64 none [.send, .sync] [.sync, .send, .send] hpermMem
  have hkeyInj :
      mkCanonicalVTableKey .u64 none [.send, .sync] =
        mkCanonicalVTableKey .u64 none [.sync, .send, .send] :=
    encodeVTableKeyCode_injective (congrArg encodeVTableKeyCode hkeyPerm)
  have hne := vtableKey_principalLess_ne_principalBearing .u64 .u64 debugPrincipal [.send, .sync] [.send, .sync]
  have hbuild := buildPrincipalLessVTable_spec
    maxRepresentableSize64 testId1 .u64 ⟨8, 8, true, true⟩
    "core::ptr::drop_in_place::<u64>" [.send, .sync] rfl rfl
  refine ⟨hrank, hmemCanon, hsetEq, hkeyInj, hne, hbuild, ?_⟩
  have hintern1 :
      ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64
        .u64 "drop_u64" none [.send, .sync] =
      .ok (
        { byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
            (mkCanonicalVTableKey .u64 none [.send, .sync])
            ⟨testId1, .u64, .principalLess [.send, .sync], "drop_u64", 8, 8,
              [.dropInPlace "drop_u64", .size 8, .align 8]⟩
          byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1
            ⟨testId1, .u64, .principalLess [.send, .sync], "drop_u64", 8, 8,
              [.dropInPlace "drop_u64", .size 8, .align 8]⟩ },
        (KeyedAllocWorld.empty.reserveAllocId).1.registerGlobal ⟨testId1, .vtable, 0, 8, .not⟩,
        ⟨testId1, .u64, .principalLess [.send, .sync], "drop_u64", 8, 8,
          [.dropInPlace "drop_u64", .size 8, .align 8]⟩) := rfl
  rw [hintern1]
  dsimp only
  let desc1 : VTableDescriptor :=
    ⟨testId1, .u64, .principalLess [.send, .sync], "drop_u64", 8, 8,
      [.dropInPlace "drop_u64", .size 8, .align 8]⟩
  let reg1 : VTableRegistry :=
    { byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
        (mkCanonicalVTableKey .u64 none [.send, .sync]) desc1
      byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 desc1 }
  let w1 : KeyedAllocWorld :=
    (KeyedAllocWorld.empty.reserveAllocId).1.registerGlobal ⟨testId1, .vtable, 0, 8, .not⟩
  have hexist1 : reg1.byKey.get? (mkCanonicalVTableKey .u64 none [.send, .sync]) = some desc1 :=
    ExtTreeMap0.get?_insert_self ∅ (mkCanonicalVTableKey .u64 none [.send, .sync]) desc1
  have hneLookup :
      reg1.byKey.get? (mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync]) = none :=
    (ExtTreeMap0.get?_insert_ne (∅ : ExtTreeMap0 VTableKey VTableDescriptor) hne desc1).trans
      (ExtTreeMap0.get?_empty _)
  have hidemp := vtableRegistry_intern_idempotent
    reg1 w1 maxRepresentableSize64 .u64 "drop_u64" none [.send, .sync] [.sync, .send, .send]
    desc1 hpermMem hexist1
  have hslotFail := principalLess_resolveVirtualMethod_fails
    testId1 .u64 "drop_u64" 8 8 [.send, .sync] 3
  refine ⟨hidemp, hneLookup, hslotFail, ?_⟩
  decide +kernel

/-- **`[adv B1]` Closed canary — upstream `checkForTypeRead` ignores auto traits and predicate
order**:
1. A principal-less `dyn Send` vtable matches an expected `dyn Sync` (A0 rejected it: false UB),
2. `dyn Debug + Send + Sync` matches `dyn Debug`,
3. principal-less vs principal-bearing still mismatches, as do distinct principals (`Debug` vs
   `Display`),
4. permuted/duplicated normalized predicates `[3, 1, 3]` vs `[1, 3]` match. -/
theorem canary_part3B_vtable_trait_check_ignores_autoTraits :
    vtableMatchesExpectedSpec (.principalLess [.send]) (.principalLess [.sync]) = true ∧
    vtableMatchesExpectedSpec ⟨some debugPrincipal, AutoTraitSet.ofList [.send, .sync]⟩
      ⟨some debugPrincipal, AutoTraitSet.ofList []⟩ = true ∧
    vtableMatchesExpectedSpec (.principalLess [.send])
      ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩ = false ∧
    vtableMatchesExpectedSpec ⟨some ⟨"core::fmt::Debug", [1], []⟩, AutoTraitSet.ofList []⟩
      ⟨some ⟨"core::fmt::Display", [1], []⟩, AutoTraitSet.ofList []⟩ = false ∧
    vtableMatchesExpectedSpec ⟨some ⟨"core::fmt::Debug", [3, 1, 3], []⟩, AutoTraitSet.ofList [.send]⟩
      ⟨some ⟨"core::fmt::Debug", [1, 3], []⟩, AutoTraitSet.ofList []⟩ = true ∧
    natListSubset [3, 1, 3] [1, 3] = true := by
  have hign1 := vtableMatchesExpectedSpec_ignores_autoTraits none none
    (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList []) (AutoTraitSet.ofList [.sync])
    (AutoTraitSet.ofList [])
  have hign2 := vtableMatchesExpectedSpec_ignores_autoTraits (some debugPrincipal)
    (some debugPrincipal) (AutoTraitSet.ofList [.send, .sync]) (AutoTraitSet.ofList [])
    (AutoTraitSet.ofList []) (AutoTraitSet.ofList [])
  have hmem : ∀ x : Nat, x ∈ [3, 1, 3] ↔ x ∈ [1, 3] := by
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h) <;> simp [h]
    · rintro (h | h) <;> simp [h]
  have hperm := vtableMatchesExpectedSpec_predicate_perm "core::fmt::Debug" "core::fmt::Debug"
    [3, 1, 3] [1, 3] [1, 3] [] [] (AutoTraitSet.ofList [.send]) (AutoTraitSet.ofList []) hmem
  have hsub : natListSubset [3, 1, 3] [1, 3] = true :=
    (natListSubset_iff [3, 1, 3] [1, 3]).mpr (fun x hx => (hmem x).mp hx)
  exact ⟨hign1.trans (by decide +kernel), hign2.trans (by decide +kernel), by decide +kernel,
    by decide +kernel, hperm.trans (by decide +kernel), hsub⟩

def canonicalDropFnOf : ProtoTy → DefPath
  | .u64 => "core::ptr::drop_in_place::<u64>"
  | _ => "core::ptr::drop_in_place::<other>"

/-- **`[adv A1]` Closed canary — `VTableRegistry.KeyWF`, general upcast preservation
(`upcastVTableToAutoTraits_preserves_drop_size_align`), and salted vtable allocations
(`saltedVTable_distinct_salts_distinct_allocIds_both_valid`)**:
1. Starting from `VTableRegistry.keyWF_empty`, interning `u64 as dyn Debug + Send + Sync`
   preserves `KeyWF` (`VTableRegistry.keyWF_intern`),
2. `upcastVTableToAutoTraits_preserves_drop_size_align` proves `dyn Debug + Send + Sync -> dyn Send`
   preserves `KeyWF`, `concreteTy = .u64`, `dropInPlaceFn`, `sizeBytes = 8`, `alignBytes = 8`, and
   the 3-slot principal-less header while rejecting `dyn Send -> dyn Sync` with `.invalidVTableTrait`,
3. Interning `u64 as dyn Send` with distinct salts `salt₁ = 100 ≠ salt₂ = 200` mints two *distinct*
   `MiriAllocId`s (`desc₁.allocId ≠ desc₂.allocId`) that both pass `validateVTableHalf` with
   identical `(concreteTy, sizeBytes, alignBytes)`! -/
theorem canary_part3B_keyWF_general_upcast_and_salted_vtables :
    (SaltedVTableKey.mk (mkCanonicalVTableKey .u64 none [.send, .sync]) 100 =
      SaltedVTableKey.mk (mkCanonicalVTableKey .u64 none [.sync, .send, .send]) 100) ∧
    (∃ sreg₂ w₂ desc₁ desc₂,
      (do
        let (sreg₁, w₁, d₁) ←
          ({} : SaltedVTableRegistry).internSalted KeyedAllocWorld.empty maxRepresentableSize64
            .u64 "drop_u64" none [.send] 100
        let (sreg₂, w₂, d₂) ←
          sreg₁.internSalted w₁ maxRepresentableSize64 .u64 "drop_u64" none [.send] 200
        return (sreg₂, w₂, d₁, d₂)) = .ok (sreg₂, w₂, desc₁, desc₂) ∧
      desc₁.allocId ≠ desc₂.allocId ∧
      desc₁.concreteTy = desc₂.concreteTy ∧
      desc₁.sizeBytes = desc₂.sizeBytes ∧
      desc₁.alignBytes = desc₂.alignBytes ∧
      validateVTableHalf w₂ sreg₂.toVTableRegistry (.provenanced 0x1000 desc₁.allocId 0)
        (.principalLess [.send]) = .ok desc₁ ∧
      validateVTableHalf w₂ sreg₂.toVTableRegistry (.provenanced 0x2000 desc₂.allocId 0)
        (.principalLess [.send]) = .ok desc₂) ∧
    (match ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64
        .u64 (canonicalDropFnOf .u64) (some debugPrincipal) [.send, .sync] with
     | .ok (reg1, w1, descDebug) =>
       match upcastVTableToAutoTraits reg1 w1 maxRepresentableSize64 descDebug [.send] with
       | .ok (reg2, w2, descSend) =>
         reg2.KeyWF maxRepresentableSize64 canonicalDropFnOf ∧
         descSend.concreteTy = descDebug.concreteTy ∧
         descSend.spec = .principalLess [.send] ∧
         descSend.dropInPlaceFn = descDebug.dropInPlaceFn ∧
         descSend.sizeBytes = descDebug.sizeBytes ∧
         descSend.alignBytes = descDebug.alignBytes ∧
         descSend.entries =
           [.dropInPlace descDebug.dropInPlaceFn, .size descDebug.sizeBytes,
            .align descDebug.alignBytes] ∧
         upcastVTableToAutoTraits reg2 w2 maxRepresentableSize64 descSend [.sync] =
           .error .invalidVTableTrait
       | .error _ => False
     | .error _ => False) := by
  -- `[adv B2]`: A1 used the tautology `k = k` here; injectivity now identifies two *syntactically
  -- different* salted keys (permuted/duplicated auto traits) from their equal encodings.
  have hsaltedInj :
      SaltedVTableKey.mk (mkCanonicalVTableKey .u64 none [.send, .sync]) 100 =
        SaltedVTableKey.mk (mkCanonicalVTableKey .u64 none [.sync, .send, .send]) 100 :=
    encodeSaltedVTableKeyCode_injective (by decide +kernel)
  have hsalted := saltedVTable_distinct_salts_distinct_allocIds_both_valid
    maxRepresentableSize64 .u64 ⟨8, 8, true, true⟩ "drop_u64" none [.send] 100 200 0x1000 0x2000
    rfl rfl (by decide)
  let descDebug : VTableDescriptor :=
    ⟨testId1, .u64, ⟨some debugPrincipal, AutoTraitSet.ofList [.send, .sync]⟩,
      canonicalDropFnOf .u64, 8, 8,
      [.dropInPlace (canonicalDropFnOf .u64), .size 8, .align 8, .method "u64::fmt"]⟩
  let reg1 : VTableRegistry := {
    byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
      (mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync]) descDebug
    byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 descDebug
  }
  let w1 : KeyedAllocWorld :=
    (KeyedAllocWorld.empty.reserveAllocId).1.registerGlobal ⟨testId1, .vtable, 0, 8, .not⟩
  have hintern1 :
      ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64
        .u64 (canonicalDropFnOf .u64) (some debugPrincipal) [.send, .sync] =
      .ok (reg1, w1, descDebug) := rfl
  have hwf0 := VTableRegistry.keyWF_empty maxRepresentableSize64 canonicalDropFnOf
  have ⟨hwf1, _⟩ := VTableRegistry.keyWF_intern maxRepresentableSize64 canonicalDropFnOf
    {} reg1 KeyedAllocWorld.empty w1 .u64 (some debugPrincipal) [.send, .sync] descDebug
    hwf0 hintern1
  let descSend : VTableDescriptor :=
    ⟨testId2, .u64, .principalLess [.send], canonicalDropFnOf .u64, 8, 8,
      [.dropInPlace (canonicalDropFnOf .u64), .size 8, .align 8]⟩
  let reg2 : VTableRegistry := {
    byKey := reg1.byKey.insert (mkCanonicalVTableKey .u64 none [.send]) descSend
    byAlloc := reg1.byAlloc.insert testId2 descSend
  }
  let w2 : KeyedAllocWorld :=
    (w1.reserveAllocId).1.registerGlobal ⟨testId2, .vtable, 0, 8, .not⟩
  have hupOk : upcastVTableToAutoTraits reg1 w1 maxRepresentableSize64 descDebug [.send] =
      .ok (reg2, w2, descSend) := rfl
  have hupPres := (upcastVTableToAutoTraits_preserves_drop_size_align
    maxRepresentableSize64 canonicalDropFnOf reg1 w1 descDebug ⟨8, 8, true, true⟩ [.send]
    hwf1 rfl rfl rfl rfl).2 reg2 w2 descSend hupOk
  have hupRej := (upcastVTableToAutoTraits_preserves_drop_size_align
    maxRepresentableSize64 canonicalDropFnOf reg2 w2 descSend ⟨8, 8, true, true⟩ [.sync]
    hupPres.1 rfl rfl rfl rfl).1 (by decide)
  refine ⟨hsaltedInj, hsalted, ?_⟩
  rw [hintern1]
  dsimp only
  rw [hupOk]
  dsimp only
  exact ⟨hupPres.1, hupPres.2.1, hupPres.2.2.1, hupPres.2.2.2.1,
    hupPres.2.2.2.2.1, hupPres.2.2.2.2.2.1, hupPres.2.2.2.2.2.2, hupRej⟩

/-- `[adv B2]` descriptor for `u64 as dyn Debug + Send + Sync` interned with canonical drop glue. -/
def b2DescDebug : VTableDescriptor :=
  ⟨testId1, .u64, ⟨some debugPrincipal, AutoTraitSet.ofList [.send, .sync]⟩,
    canonicalDropFnOf .u64, 8, 8,
    [.dropInPlace (canonicalDropFnOf .u64), .size 8, .align 8, .method "u64::fmt"]⟩

def b2Reg1 : VTableRegistry := {
  byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
    (mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync]) b2DescDebug
  byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 b2DescDebug
}

def b2W1 : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.reserveAllocId).1.registerGlobal ⟨testId1, .vtable, 0, 8, .not⟩

/-- **`[adv B2]` Closed canary — `byAlloc` coherence & validation lookup soundness**: interning
`u64 as dyn Debug + Send + Sync` into the empty registry preserves `AllocWF`
(`VTableRegistry.allocWF_empty`, `VTableRegistry.allocWF_intern`; A1's `KeyWF` constrained only
`byKey`, which `validateVTableHalf` never reads), and the descriptor `validateVTableHalf` accepts as a
`dyn Debug + Send` vtable provably carries `canonicalDropFnOf .u64` and the `u64` layout
(`validateVTableHalf_sound_of_allocWF`). -/
theorem canary_part3B_allocWF_validation_lookup_soundness :
    ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64 .u64
        (canonicalDropFnOf .u64) (some debugPrincipal) [.send, .sync] =
      .ok (b2Reg1, b2W1, b2DescDebug) ∧
    b2Reg1.AllocWF maxRepresentableSize64 canonicalDropFnOf ∧
    validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 testId1 0)
        ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩ = .ok b2DescDebug ∧
    b2DescDebug.dropInPlaceFn = canonicalDropFnOf b2DescDebug.concreteTy ∧
    (∃ lay : ComputedTyLayout,
      computeTyLayout maxRepresentableSize64 b2DescDebug.concreteTy = .ok lay ∧
      lay.isSized = true ∧
      b2DescDebug.sizeBytes = UInt64.ofNat lay.sizeBytes ∧
      b2DescDebug.alignBytes = UInt64.ofNat lay.alignBytes) := by
  have hintern1 :
      ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64 .u64
        (canonicalDropFnOf .u64) (some debugPrincipal) [.send, .sync] =
      .ok (b2Reg1, b2W1, b2DescDebug) := rfl
  have hkwf0 := VTableRegistry.keyWF_empty maxRepresentableSize64 canonicalDropFnOf
  have hawf0 := VTableRegistry.allocWF_empty maxRepresentableSize64 canonicalDropFnOf
  have hawf1 := VTableRegistry.allocWF_intern maxRepresentableSize64 canonicalDropFnOf
    {} b2Reg1 KeyedAllocWorld.empty b2W1 .u64 (some debugPrincipal) [.send, .sync] b2DescDebug
    hkwf0 hawf0 hintern1
  have hv : validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 testId1 0)
      ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩ = .ok b2DescDebug := by decide +kernel
  have hsound := validateVTableHalf_sound_of_allocWF maxRepresentableSize64 canonicalDropFnOf
    b2W1 b2Reg1 _ _ b2DescDebug hawf1 hv
  exact ⟨hintern1, hawf1, hv, hsound.1, hsound.2⟩

/-- Registry exhibiting B2's `KeyWF ∧ AllocWF` cached-hit round-trip gap (`[adv A2]`): `byKey` maps
`u64 as dyn Send + Sync` to `b2DescDebug`, while `byAlloc` is empty! -/
def orphanCachedKeyReg : VTableRegistry := {
  byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
    (mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync]) b2DescDebug
  byAlloc := ∅
}

/-- **`[adv A2]` Closed canary — `KeyWF ∧ AllocWF` cached-hit gap vs. `VTableWorldWF.intern_roundTrip`
& `SaltedVTableWorldWF.internSalted_roundTrip`**:
1. `orphanCachedKeyReg` satisfies **both** `KeyWF` and `AllocWF`, and `intern` hits the cached
   `some existing` branch returning `b2DescDebug`, yet `validateVTableHalf` **fails** with
   `.error .invalidVTableNotGlobalVTable`!
2. `VTableWorldWF.empty` + `VTableWorldWF.intern_roundTrip` close this gap across both fresh
   interning and cached `byKey` reuse (and across subsequent fresh `u32` interning without clobbering
   `byAlloc`)!
3. `SaltedVTableWorldWF.empty` + `SaltedVTableWorldWF.internSalted_roundTrip` preserve
   `sreg'.toVTableRegistry.AllocWF` and guarantee `validateVTableHalf = .ok desc` across fresh and
   cached salted requests! -/
theorem canary_part3B_worldWF_and_saltedWorldWF_roundTrip :
    (orphanCachedKeyReg.KeyWF maxRepresentableSize64 canonicalDropFnOf ∧
     orphanCachedKeyReg.AllocWF maxRepresentableSize64 canonicalDropFnOf ∧
     orphanCachedKeyReg.intern KeyedAllocWorld.empty maxRepresentableSize64
       .u64 (canonicalDropFnOf .u64) (some debugPrincipal) [.sync, .send] =
       .ok (orphanCachedKeyReg, KeyedAllocWorld.empty, b2DescDebug) ∧
     validateVTableHalf KeyedAllocWorld.empty orphanCachedKeyReg (.provenanced 0x1000 testId1 0)
       ⟨some debugPrincipal, AutoTraitSet.ofList [.sync, .send]⟩ =
       .error .invalidVTableNotGlobalVTable) ∧
    (validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 b2DescDebug.allocId 0)
       ⟨some debugPrincipal, AutoTraitSet.ofList [.send, .sync]⟩ = .ok b2DescDebug ∧
     validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 b2DescDebug.allocId 0)
       ⟨some debugPrincipal, AutoTraitSet.ofList [.sync, .send]⟩ = .ok b2DescDebug) ∧
    (match ({} : SaltedVTableRegistry).internSalted KeyedAllocWorld.empty maxRepresentableSize64
        .u64 (canonicalDropFnOf .u64) none [.send] 100 with
     | .ok (sreg1, sw1, sdesc1) =>
       sreg1.toVTableRegistry.AllocWF maxRepresentableSize64 canonicalDropFnOf ∧
       validateVTableHalf sw1 sreg1.toVTableRegistry (.provenanced 0x3000 sdesc1.allocId 0)
         ⟨none, AutoTraitSet.ofList [.send]⟩ = .ok sdesc1 ∧
       (match sreg1.internSalted sw1 maxRepresentableSize64 .u64 (canonicalDropFnOf .u64) none [.send] 100 with
        | .ok (sreg2, sw2, sdesc2) =>
          validateVTableHalf sw2 sreg2.toVTableRegistry (.provenanced 0x3000 sdesc2.allocId 0)
            ⟨none, AutoTraitSet.ofList [.send]⟩ = .ok sdesc2
        | .error _ => False)
     | .error _ => False) := by
  have horphKeyWF : orphanCachedKeyReg.KeyWF maxRepresentableSize64 canonicalDropFnOf := by
    intro k d hget
    unfold orphanCachedKeyReg at hget
    dsimp only at hget
    rw [ExtTreeMap0.get?_insert] at hget
    split at hget
    · rename_i hcmp
      have hkeq : mkCanonicalVTableKey .u64 (some debugPrincipal) [.send, .sync] = k :=
        LawfulEqCmp.eq_of_compare hcmp
      subst hkeq
      injection hget with hd
      subst hd
      exact ⟨rfl, rfl, rfl, ⟨⟨8, 8, true, true⟩, rfl, rfl, rfl, rfl⟩, rfl⟩
    · rw [ExtTreeMap0.get?_empty] at hget; nomatch hget
  have horphAllocWF : orphanCachedKeyReg.AllocWF maxRepresentableSize64 canonicalDropFnOf :=
    VTableRegistry.allocWF_empty _ _
  have hwf0 := VTableWorldWF.empty maxRepresentableSize64 canonicalDropFnOf
  have hinternFresh :
      ({} : VTableRegistry).intern KeyedAllocWorld.empty maxRepresentableSize64 .u64
        (canonicalDropFnOf .u64) (some debugPrincipal) [.send, .sync] =
      .ok (b2Reg1, b2W1, b2DescDebug) := rfl
  have ⟨hwf1, hrtFresh⟩ := VTableWorldWF.intern_roundTrip maxRepresentableSize64 canonicalDropFnOf
    KeyedAllocWorld.empty b2W1 {} b2Reg1 .u64 (some debugPrincipal) [.send, .sync] b2DescDebug 0x1000
    hwf0 hinternFresh
  have hinternCached :
      b2Reg1.intern b2W1 maxRepresentableSize64 .u64
        (canonicalDropFnOf .u64) (some debugPrincipal) [.sync, .send] =
      .ok (b2Reg1, b2W1, b2DescDebug) := rfl
  have ⟨_, hrtCached⟩ := VTableWorldWF.intern_roundTrip maxRepresentableSize64 canonicalDropFnOf
    b2W1 b2W1 b2Reg1 b2Reg1 .u64 (some debugPrincipal) [.sync, .send] b2DescDebug 0x1000
    hwf1 hinternCached
  have hswf0 := SaltedVTableWorldWF.empty maxRepresentableSize64 canonicalDropFnOf
  let sdesc1 : VTableDescriptor :=
    ⟨testId1, .u64, .principalLess [.send], canonicalDropFnOf .u64, 8, 8,
      [.dropInPlace (canonicalDropFnOf .u64), .size 8, .align 8]⟩
  let sreg1 : SaltedVTableRegistry := {
    bySaltedKey := (∅ : ExtTreeMap0 SaltedVTableKey VTableDescriptor).insert
      ⟨mkCanonicalVTableKey .u64 none [.send], 100⟩ sdesc1
    byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 sdesc1
  }
  have hs1 :
      ({} : SaltedVTableRegistry).internSalted KeyedAllocWorld.empty maxRepresentableSize64
        .u64 (canonicalDropFnOf .u64) none [.send] 100 = .ok (sreg1, b2W1, sdesc1) := rfl
  have ⟨hswf1, hsawf1, hsrt1⟩ := SaltedVTableWorldWF.internSalted_roundTrip
    maxRepresentableSize64 canonicalDropFnOf KeyedAllocWorld.empty b2W1 {} sreg1
    .u64 none [.send] 100 sdesc1 0x3000 hswf0 hs1
  have hs2 :
      sreg1.internSalted b2W1 maxRepresentableSize64
        .u64 (canonicalDropFnOf .u64) none [.send] 100 = .ok (sreg1, b2W1, sdesc1) := rfl
  have ⟨_, _, hsrt2⟩ := SaltedVTableWorldWF.internSalted_roundTrip
    maxRepresentableSize64 canonicalDropFnOf b2W1 b2W1 sreg1 sreg1
    .u64 none [.send] 100 sdesc1 0x3000 hswf1 hs2
  refine ⟨⟨horphKeyWF, horphAllocWF, rfl, rfl⟩, ⟨hrtFresh, hrtCached⟩, ?_⟩
  rw [hs1]
  dsimp only
  rw [hs2]
  exact ⟨hsawf1, hsrt1, hsrt2⟩

def wideDynWorldAndReg : KeyedAllocWorld × VTableRegistry × VTableDescriptor :=
  let descU64 : VTableDescriptor :=
    ⟨testId1, .u64, .principalLess [.send], "drop_u64", 8, 8,
      [.dropInPlace "drop_u64", .size 8, .align 8]⟩
  let descUnit : VTableDescriptor :=
    ⟨testId2, .tuple [], .principalLess [.send], "drop_unit", 0, 1,
      [.dropInPlace "drop_unit", .size 0, .align 1]⟩
  let w :=
    (((KeyedAllocWorld.empty.registerGlobal ⟨testId1, .vtable, 0, 8, .not⟩).registerGlobal
        ⟨testId2, .vtable, 0, 1, .not⟩).registerGlobal
        ⟨testIdMaxPrev, .static, 8, 8, .not⟩).insertLive testId3 entryHeap8
  let reg : VTableRegistry :=
    { byKey := ((∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
          (mkCanonicalVTableKey .u64 none [.send]) descU64).insert
          (mkCanonicalVTableKey (.tuple []) none [.send]) descUnit
      byAlloc := ((∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 descU64).insert
          testId2 descUnit }
  (w, reg, descU64)

/-- Closed canary for Part 3C (`lean-miri#82`):
1. Double-null separation (`(.null, .null)` reports `.invalidVTableNull` vs. legacy data-first
   `.nullSafePointer false`),
2. All 6 invalid-vtable forms (`null`, `maybeNull`, `danglingInt`, `nonzeroOffset`, `notGlobalVTable`,
   `invalidVTableTrait`) beat simultaneously invalid `.null` or unaligned `.danglingInt 3` data! The
   trait-mismatch case uses a genuine *principal* mismatch (`u64 as dyn Send` vtable where
   `dyn Debug + Send` is expected); `[adv B1]`: A0 used an auto-trait-only mismatch
   (`dyn Send` vtable vs. expected `dyn Sync`), which upstream `checkForTypeRead` accepts — that
   pointer now correctly reaches the data checks and reports `.danglingSafePointer`.
3. When `vtablePtr` is valid (`u64 as dyn Send`), null data reports `.nullSafePointer false`,
   maybe-null data reports `.nullSafePointer true`, dangling data reports `.danglingSafePointer`
   (`mayDangle = false`), unaligned address `3` reports `.unalignedSafePointer 8 3` (`mayDangle = true`),
   valid live aligned `(addr = 16, testId3)` succeeds with `(.u64, 8, 8)`, and ZST `&() as &dyn Send`
   at aligned non-null address `8` succeeds with `(.tuple [], 0, 1)`! -/
theorem canary_part3C_wideDyn_vtable_precedence_and_valid_preservation :
    let (w, reg, _) := wideDynWorldAndReg
    let specSend := DynExistentialSpec.principalLess [.send]
    let specSync := DynExistentialSpec.principalLess [.sync]
    let specDebugSend : DynExistentialSpec := ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩
    let validVt := ScalarPtrHalf.provenanced 0x1000 testId1 0
    let validUnitVt := ScalarPtrHalf.provenanced 0x2000 testId2 0
    (validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null .null =
       .error .invalidVTableNull ∧
     validateWideDynLegacyDataFirst w reg maxRepresentableSize64 specSend false .null .null =
       .error (.nullSafePointer false)) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null (.maybeNull testId1 0) =
      .error .invalidVTableMaybeNull ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null (.danglingInt 0x400) =
      .error .invalidVTableDanglingInt ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null (.provenanced 0x1000 testId1 8) =
      .error .invalidVTableNonzeroOffset ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null (.provenanced 0x3000 testIdMaxPrev 0) =
      .error .invalidVTableNotGlobalVTable ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specDebugSend false (.danglingInt 3) validVt =
      .error .invalidVTableTrait ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSync false (.danglingInt 3) validVt =
      .error .danglingSafePointer ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null validVt =
      .error (.nullSafePointer false) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend true .null validUnitVt =
      .error (.nullSafePointer false) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.maybeNull testId3 0) validVt =
      .error (.nullSafePointer true) ∧
    (validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.maybeNull testIdMax 0) validVt =
       .error .danglingSafePointer ∧
     validateWideDynSafePtr w reg maxRepresentableSize64 specSend true (.maybeNull testIdMax 0) validVt =
       .error (.nullSafePointer true)) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.danglingInt 0) validVt =
      .error (.nullSafePointer false) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.danglingInt 3) validVt =
      .error .danglingSafePointer ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend true (.danglingInt 3) validVt =
      .error (.unalignedSafePointer 8 3) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.provenanced 16 testId3 0) validVt =
      .ok (.u64, 8, 8) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false (.danglingInt 8) validUnitVt =
      .ok (.tuple [], 0, 1) := by
  dsimp only [wideDynWorldAndReg]
  let w := wideDynWorldAndReg.1
  let reg := wideDynWorldAndReg.2.1
  let descU64 := wideDynWorldAndReg.2.2
  let descUnit : VTableDescriptor :=
    ⟨testId2, .tuple [], .principalLess [.send], "drop_unit", 0, 1,
      [.dropInPlace "drop_unit", .size 0, .align 1]⟩
  let specSend := DynExistentialSpec.principalLess [.send]
  let specSync := DynExistentialSpec.principalLess [.sync]
  let specDebugSend : DynExistentialSpec := ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩
  let validVt := ScalarPtrHalf.provenanced 0x1000 testId1 0
  let validUnitVt := ScalarPtrHalf.provenanced 0x2000 testId2 0
  have hdbl := wideDyn_doubleNull_separation w reg maxRepresentableSize64 specSend false
  have hvMaybe : validateVTableHalf w reg (.maybeNull testId1 0) specSend = .error .invalidVTableMaybeNull := rfl
  have hvDang : validateVTableHalf w reg (.danglingInt 0x400) specSend = .error .invalidVTableDanglingInt := rfl
  have hvOff : validateVTableHalf w reg (.provenanced 0x1000 testId1 8) specSend =
      .error .invalidVTableNonzeroOffset := rfl
  have hvNotGlob : validateVTableHalf w reg (.provenanced 0x3000 testIdMaxPrev 0) specSend =
      .error .invalidVTableNotGlobalVTable := by decide +kernel
  have hglob1 : w.findGlobal? testId1 = some ⟨testId1, .vtable, 0, 8, .not⟩ := by decide +kernel
  have hdesc1 : reg.byAlloc.get? testId1 = some descU64 := by decide +kernel
  have hvTrait : validateVTableHalf w reg validVt specDebugSend = .error .invalidVTableTrait :=
    validateVTableHalf_principalLess_vs_principal_invalidTrait w reg 0x1000 testId1
      ⟨testId1, .vtable, 0, 8, .not⟩ descU64 debugPrincipal (AutoTraitSet.ofList [.send])
      hglob1 rfl hdesc1 rfl
  have hvSyncOk : validateVTableHalf w reg validVt specSync = .ok descU64 :=
    validateVTableHalf_principalLess_ignores_autoTraits w reg 0x1000 testId1
      ⟨testId1, .vtable, 0, 8, .not⟩ descU64 (AutoTraitSet.ofList [.sync]) hglob1 rfl hdesc1 rfl
  have hvOkU64 : validateVTableHalf w reg validVt specSend = .ok descU64 := by decide +kernel
  have hvOkUnit : validateVTableHalf w reg validUnitVt specSend = .ok descUnit := by decide +kernel
  have hdangUnalign := wideDyn_validVTable_dangling_and_unaligned
    w reg maxRepresentableSize64 specSend validVt descU64 3
    hvOkU64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hdangSync := wideDyn_validVTable_dangling_and_unaligned
    w reg maxRepresentableSize64 specSync validVt descU64 3
    hvSyncOk (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨
    hdbl,
    wideDyn_invalidVTable_precedes_all_data_ub w reg maxRepresentableSize64 specSend false .null _ _ hvMaybe,
    wideDyn_invalidVTable_precedes_all_data_ub w reg maxRepresentableSize64 specSend false .null _ _ hvDang,
    wideDyn_invalidVTable_precedes_all_data_ub w reg maxRepresentableSize64 specSend false .null _ _ hvOff,
    wideDyn_invalidVTable_precedes_all_data_ub w reg maxRepresentableSize64 specSend false .null _ _ hvNotGlob,
    wideDyn_invalidVTable_precedes_all_data_ub w reg maxRepresentableSize64 specDebugSend false (.danglingInt 3) _ _ hvTrait,
    hdangSync.1,
    wideDyn_validVTable_nullData_reports_nullSafePointer w reg maxRepresentableSize64 specSend false validVt descU64 hvOkU64,
    wideDyn_validVTable_nullData_reports_nullSafePointer w reg maxRepresentableSize64 specSend true validUnitVt descUnit hvOkUnit,
    by decide +kernel,
    wideDyn_validVTable_maybeNull_dangling_precedes_null w reg maxRepresentableSize64 specSend validVt descU64 testIdMax 0 (.unavailable testIdMax) hvOkU64 (by decide) (by decide +kernel),
    wideDyn_validVTable_danglingIntZero_reports_null w reg maxRepresentableSize64 specSend false validVt descU64 hvOkU64 (by decide),
    hdangUnalign.1,
    hdangUnalign.2,
    by decide +kernel,
    by decide +kernel
  ⟩

def uninhDynDesc : VTableDescriptor :=
  ⟨testId1, .tuple [.u32, .never], .principalLess [.send], "drop_u32_never", 4, 4,
    [.dropInPlace "drop_u32_never", .size 4, .align 4]⟩

def uninhDynWorld : KeyedAllocWorld :=
  (KeyedAllocWorld.empty.registerGlobal ⟨testId1, .vtable, 0, 4, .not⟩).insertLive
    testId3 entryHeap8

def uninhDynReg : VTableRegistry :=
  { byKey := (∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
      (mkCanonicalVTableKey (.tuple [.u32, .never]) none [.send]) uninhDynDesc
    byAlloc := (∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 uninhDynDesc }

/-- **`[adv A2]` Closed canary — `mayDangle` `addressTooClose` guard, `mayDangle` uninhabited
concrete pointee validity (`ManuallyDrop<Box<dyn Send>>` from `(u32, !)`), and alignment-before-
concrete-uninhabitedness precedence**:
1. Under `mayDangle = true`, aligned `.danglingInt 0xFFFF_FFFF_FFFF_FFFC` (`addr + 4 = 2^64 >=
   usizeMax64`) faults with `.error (.addressTooClose 4)` (`ValidityVisitor.lean:217–218`)!
2. Under `mayDangle = true`, aligned `.danglingInt 16` **succeeds** with `.ok (.tuple [.u32, .never], 4, 4)`
   even though `(u32, !)` is uninhabited (A0–B2 falsely raised `.uninhabitedPointee`), whereas
   `mayDangle = false` on live aligned `.provenanced 16 testId3 0` faults with `.error .uninhabitedPointee`!
3. Under `mayDangle = false` at unaligned `.provenanced 2 testId3 0` on uninhabited `(u32, !)`,
   `validateWideDynSafePtr` reports `.error (.unalignedSafePointer 4 2)` **before**
   `.uninhabitedPointee` (A0–B2 swapped them)! -/
theorem canary_part3C_mayDangle_addressTooClose_and_unaligned_before_uninhabited :
    let specSend := DynExistentialSpec.principalLess [.send]
    let vtPtr := ScalarPtrHalf.provenanced 0x1000 testId1 0
    (validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       true (.danglingInt 0xFFFF_FFFF_FFFF_FFFC) vtPtr = .error (.addressTooClose 4) ∧
     validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       true (.danglingInt 16) vtPtr = .ok (.tuple [.u32, .never], 4, 4) ∧
     validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       false (.provenanced 16 testId3 0) vtPtr true = .error .uninhabitedPointee ∧
     validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       false (.provenanced 16 testId3 0) vtPtr = .ok (.tuple [.u32, .never], 4, 4)) ∧
    (validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       false (.provenanced 2 testId3 0) vtPtr true = .error (.unalignedSafePointer 4 2) ∧
     validateWideDynSafePtr uninhDynWorld uninhDynReg maxRepresentableSize64 specSend
       false (.provenanced 2 testId3 0) vtPtr = .error (.unalignedSafePointer 4 2) ∧
     (computeTyLayout maxRepresentableSize64 uninhDynDesc.concreteTy).map ComputedTyLayout.isInhabited =
       .ok false) := by
  have hv : validateVTableHalf uninhDynWorld uninhDynReg (.provenanced 0x1000 testId1 0)
      (.principalLess [.send]) = .ok uninhDynDesc := by decide +kernel
  have hlive : uninhDynWorld.getAllocInfo testId3 = .ok ⟨8, 8, .liveData, .mut⟩ := by decide +kernel
  have hlay : computeTyLayout maxRepresentableSize64 uninhDynDesc.concreteTy =
      .ok ⟨4, 4, true, false⟩ := by decide
  have hmay := wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok
    uninhDynWorld uninhDynReg maxRepresentableSize64 (.principalLess [.send])
    (.provenanced 0x1000 testId1 0) uninhDynDesc ⟨4, 4, true, false⟩
    0xFFFF_FFFF_FFFF_FFFC 16 testId3 ⟨8, 8, .liveData, .mut⟩
    hv (by decide) (by decide) (by decide) (fun _ => by decide) hlive rfl (by decide) hlay rfl
  have hunalR := wideDyn_unaligned_precedes_concrete_uninhabited
    uninhDynWorld uninhDynReg maxRepresentableSize64 (.principalLess [.send])
    (.provenanced 0x1000 testId1 0) uninhDynDesc ⟨4, 4, true, false⟩
    2 testId3 ⟨8, 8, .liveData, .mut⟩ true
    hv hlive rfl (by decide) (by decide) (by decide) (by decide) hlay rfl
  have hunalN := wideDyn_unaligned_precedes_concrete_uninhabited
    uninhDynWorld uninhDynReg maxRepresentableSize64 (.principalLess [.send])
    (.provenanced 0x1000 testId1 0) uninhDynDesc ⟨4, 4, true, false⟩
    2 testId3 ⟨8, 8, .liveData, .mut⟩ false
    hv hlive rfl (by decide) (by decide) (by decide) (by decide) hlay rfl
  exact ⟨hmay, hunalR.1, hunalN.1, hunalR.2⟩

/-- **`[adv B3]` Closed canary — raw `*const dyn Trait` vtable identity**: upstream
`checkMetadata` (`ValidityVisitor.lean:184–195, 317–327`) requires a raw wide `dyn` pointer to carry
a genuine vtable but checks nothing about its data half:
1. the Part 3A validators accept the integer vtable word `0x1000` (no provenance) on `*const dyn Send`
   (shape-only check), while `validateRawWideDynPtrMeta` rejects it with `.invalidVTableDanglingInt`
   (`rawWideDyn_shapeCheck_misses_invalid_vtable`);
2. with the valid `u64 as dyn Send` vtable the raw check succeeds although the *safe* validator rejects
   the null data half with `.nullSafePointer false`, and with a null vtable both report
   `.invalidVTableNull` (`rawWideDyn_vtable_checked_data_unchecked`). -/
theorem canary_part3C_rawWideDyn_vtable_identity :
    let (w, reg, _) := wideDynWorldAndReg
    let specSend := DynExistentialSpec.principalLess [.send]
    let validVt := ScalarPtrHalf.provenanced 0x1000 testId1 0
    validateRawPtrFastPath maxRepresentableSize64 (.dynamic "Send") (.wideDyn 16 none 0x1000 none) =
      .ok () ∧
    validateUnsizedRawPtrMeta .dynMeta (.wideDyn 16 none 0x1000 none) = .ok () ∧
    validateRawWideDynPtrMeta w reg specSend (.danglingInt 0x1000) = .error .invalidVTableDanglingInt ∧
    validateRawWideDynPtrMeta w reg specSend validVt = .ok () ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null validVt =
      .error (.nullSafePointer false) ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null validVt true =
      .error (.nullSafePointer false) ∧
    validateRawWideDynPtrMeta w reg specSend .null = .error .invalidVTableNull ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null .null =
      .error .invalidVTableNull ∧
    validateWideDynSafePtr w reg maxRepresentableSize64 specSend false .null .null true =
      .error .invalidVTableNull := by
  dsimp only [wideDynWorldAndReg]
  let w := wideDynWorldAndReg.1
  let reg := wideDynWorldAndReg.2.1
  let descU64 := wideDynWorldAndReg.2.2
  have hvOk : validateVTableHalf w reg (.provenanced 0x1000 testId1 0) (.principalLess [.send]) =
      .ok descU64 := by decide +kernel
  have hvNull : validateVTableHalf w reg .null (.principalLess [.send]) = .error .invalidVTableNull :=
    rfl
  have hshape := rawWideDyn_shapeCheck_misses_invalid_vtable w reg (.principalLess [.send]) 16 0x1000
    none (by decide)
  have hraw := rawWideDyn_vtable_checked_data_unchecked w reg maxRepresentableSize64
    (.principalLess [.send]) (.provenanced 0x1000 testId1 0) false
  have hrawNull := rawWideDyn_vtable_checked_data_unchecked w reg maxRepresentableSize64
    (.principalLess [.send]) .null false
  exact ⟨rfl, hshape.1, hshape.2, (hraw.2 descU64 false hvOk).1, (hraw.2 descU64 false hvOk).2,
    (hraw.2 descU64 true hvOk).2, (hrawNull.1 _ .null false hvNull).1,
    (hrawNull.1 _ .null false hvNull).2, (hrawNull.1 _ .null true hvNull).2⟩

def resolveTestProtoDynSpec : String → DynExistentialSpec
  | "Debug" => ⟨some debugPrincipal, AutoTraitSet.ofList [.send]⟩
  | _ => .principalLess [.send]

/-- **`[adv A3]` Closed canary — unified end-to-end `validateRawPtrFull` (`lean-miri#79/#75/#82`,
discharging B3 open item `(ii)`)**:
1. `unsizedDynTailTrait?_isSome_eq_dynMeta` & `fieldsDynTailTrait?_isSome_eq_dynMeta` bridge custom
   struct/tuple DSTs (`MyDynDst(u32, dyn Debug)`) to `DynExistentialSpec`.
2. `validateRawPtrFull_sized_skips_layout_and_vtable`: `*const [u8; usize::MAX]` still succeeds in
   `O(1)` without querying layout or vtables.
3. `validateRawPtrFull_customDynDst_layout_and_vtable_soundness`:
   - On `*const ([u8; usize::MAX], dyn Debug)` with `(data = .null, vtable = .null)`, layout overflow
     fires **before** `.vtableErr .invalidVTableNull` (`fromImmediate` line 81 before `checkMetadata`
     line 186),
   - On `*const MyDynDst(u32, dyn Debug)`, dangling integer `0x1000`, nonzero vtable offset `8`, and
     principal-less `u64 as dyn Send` vtable all fail with `.vtableErr`, while valid `b2DescDebug`
     vtable + `.null` data half **succeeds** with `.ok ()`! -/
theorem canary_part3A_3B_3C_unified_validateRawPtrFull :
    (unsizedDynTailTrait? (.adt "MyDynDst" [.u32, .dynamic "Debug"])).isSome =
      (unsizedMetadataTail (.adt "MyDynDst" [.u32, .dynamic "Debug"]) == some .dynMeta) ∧
    (fieldsUnsizedDynTailTrait? none [.u32, .dynamic "Debug"]).isSome =
      (fieldsUnsizedMetadataTail none [.u32, .dynamic "Debug"] == some .dynMeta) ∧
    validateRawPtrFull b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64
      (.array .u8 usizeMax64) (.thin .null) = .ok () ∧
    validateRawPtrFull b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64
      (.tuple [.array .u8 usizeMax64, .dynamic "Debug"]) (.wideDyn .null .null) =
      .error (.layoutErr (.sizeOverflow (1 * usizeMax64) maxRepresentableSize64)) ∧
    validateRawPtrFull b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64
      (.adt "MyDynDst" [.u32, .dynamic "Debug"]) (.wideDyn .null (.danglingInt 0x1000)) =
      .error (.vtableErr .invalidVTableDanglingInt) ∧
    validateRawPtrFull b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64
      (.adt "MyDynDst" [.u32, .dynamic "Debug"])
      (.wideDyn .null (.provenanced 0x1000 b2DescDebug.allocId 8)) =
      .error (.vtableErr .invalidVTableNonzeroOffset) ∧
    validateRawPtrFull wideDynWorldAndReg.1 wideDynWorldAndReg.2.1 resolveTestProtoDynSpec
      maxRepresentableSize64 (.adt "MyDynDst" [.u32, .dynamic "Debug"])
      (.wideDyn .null (.provenanced 0x1000 testId1 0)) =
      .error (.vtableErr .invalidVTableTrait) ∧
    validateRawPtrFull b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64
      (.adt "MyDynDst" [.u32, .dynamic "Debug"])
      (.wideDyn .null (.provenanced 0x1000 b2DescDebug.allocId 0)) = .ok () := by
  have hbr1 := unsizedDynTailTrait?_isSome_eq_dynMeta (.adt "MyDynDst" [.u32, .dynamic "Debug"])
  have hbr2 := fieldsDynTailTrait?_isSome_eq_dynMeta none none [.u32, .dynamic "Debug"] rfl
  have hszSkip := validateRawPtrFull_sized_skips_layout_and_vtable
    b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64 (.array .u8 usizeMax64) .null rfl
  have hdst := validateRawPtrFull_customDynDst_layout_and_vtable_soundness
    b2W1 b2Reg1 resolveTestProtoDynSpec maxRepresentableSize64 .u8 .u32
    ⟨1, 1, true, true⟩ ⟨4, 4, true, true⟩ usizeMax64 "MyDynDst" "Debug"
    rfl rfl (by decide) rfl rfl (by decide)
  have hdstMismatch := validateRawPtrFull_customDynDst_layout_and_vtable_soundness
    wideDynWorldAndReg.1 wideDynWorldAndReg.2.1 resolveTestProtoDynSpec maxRepresentableSize64
    .u8 .u32 ⟨1, 1, true, true⟩ ⟨4, 4, true, true⟩ usizeMax64 "MyDynDst" "Debug"
    rfl rfl (by decide) rfl rfl (by decide)
  have hvDang : validateVTableHalf b2W1 b2Reg1 (.danglingInt 0x1000)
      (resolveTestProtoDynSpec "Debug") = .error .invalidVTableDanglingInt := rfl
  have hvOff : validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 b2DescDebug.allocId 8)
      (resolveTestProtoDynSpec "Debug") = .error .invalidVTableNonzeroOffset := rfl
  have hvTrait : validateVTableHalf wideDynWorldAndReg.1 wideDynWorldAndReg.2.1
      (.provenanced 0x1000 testId1 0) (resolveTestProtoDynSpec "Debug") =
      .error .invalidVTableTrait := by decide +kernel
  have hvOk : validateVTableHalf b2W1 b2Reg1 (.provenanced 0x1000 b2DescDebug.allocId 0)
      (resolveTestProtoDynSpec "Debug") = .ok b2DescDebug := by decide +kernel
  exact ⟨
    hbr1,
    hbr2,
    hszSkip,
    hdst.1,
    hdst.2.1 _ .null _ hvDang,
    hdst.2.1 _ .null _ hvOff,
    hdstMismatch.2.1 _ .null _ hvTrait,
    hdst.2.2 b2DescDebug .null _ hvOk
  ⟩

def a3DescBool : VTableDescriptor :=
  ⟨testId1, .bool, .principalLess [.send], "drop_bool", 1, 1,
    [.dropInPlace "drop_bool", .size 1, .align 1]⟩

def a3DescRefU32 : VTableDescriptor :=
  ⟨testId2, .ref .not .u32, .principalLess [.send], "drop_ref_u32", 8, 8,
    [.dropInPlace "drop_ref_u32", .size 8, .align 8]⟩

def a3DescRefNever : VTableDescriptor :=
  ⟨testId3, .ref .not .never, .principalLess [.send], "drop_ref_never", 8, 8,
    [.dropInPlace "drop_ref_never", .size 8, .align 8]⟩

def a3ChildSessionWorld : KeyedAllocWorld :=
  ((KeyedAllocWorld.empty.registerGlobal ⟨testId1, .vtable, 0, 1, .not⟩).registerGlobal
    ⟨testId2, .vtable, 0, 8, .not⟩).registerGlobal
    ⟨testId3, .vtable, 0, 8, .not⟩

def a3ChildSessionReg : VTableRegistry where
  byKey := (((∅ : ExtTreeMap0 VTableKey VTableDescriptor).insert
      (mkCanonicalVTableKey .bool none [.send]) a3DescBool).insert
      (mkCanonicalVTableKey (.ref .not .u32) none [.send]) a3DescRefU32).insert
      (mkCanonicalVTableKey (.ref .not .never) none [.send]) a3DescRefNever
  byAlloc := (((∅ : ExtTreeMap0 MiriAllocId VTableDescriptor).insert testId1 a3DescBool).insert
      testId2 a3DescRefU32).insert testId3 a3DescRefNever

/-- **`[adv A3]` Closed canary — recursive pointee byte validation & `childSession` `mayDangle = true`
(`ValidityVisitor.lean:198–241, 308–310, 412–418, 527–556`, discharging B3 open item `(iii)`)**:
1. Non-recursive default (`recursive = false`) accepts `&dyn Send` pointing to `.uninit` or invalid
   `0x02 : bool` bytes, whereas `recursive = true` rejects `.uninit` with `.uninitPointeeByte` and
   `0x02 : bool` with `.invalidBoolScalar 2`.
2. Under `recursive = true`, `childSession` (`flags.mayDangle = true, refTracking = none`, line 552)
   rejects null nested `&u32` (`0x00`) with `.nullNestedSafePtr`, **accepts** aligned non-null
   dangling integer `&u32` (`addr = 4`, no provenance), and rejects aligned non-null `&!` with
   `.uninhabitedNestedSafePtr`! -/
theorem canary_part3C_recursive_pointee_bytes_and_childSession_mayDangle :
    let specSend := DynExistentialSpec.principalLess [.send]
    let vtB := ScalarPtrHalf.provenanced 0x1000 testId1 0
    let vtRU := ScalarPtrHalf.provenanced 0x2000 testId2 0
    let vtRN := ScalarPtrHalf.provenanced 0x3000 testId3 0
    let wUninit := a3ChildSessionWorld.insertLive testIdMax ⟨.heap, 8, 8, .mut, List.replicate 8 .uninit⟩
    let wBadBool := a3ChildSessionWorld.insertLive testIdMax ⟨.heap, 8, 8, .mut, [.init 2 none]⟩
    let wNullRef := a3ChildSessionWorld.insertLive testIdMax ⟨.heap, 8, 8, .mut, Anneal.BitValidity.zeroInitBytes 8⟩
    let wDangRef := a3ChildSessionWorld.insertLive testIdMax ⟨.heap, 8, 8, .mut, .init 4 none :: Anneal.BitValidity.zeroInitBytes 7⟩
    validateWideDynSafePtrWithBytes wUninit a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtB false = .ok (.bool, 1, 1) ∧
    validateWideDynSafePtrWithBytes wUninit a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtB true = .error (.pointeeErr .uninitPointeeByte) ∧
    validateWideDynSafePtrWithBytes wBadBool a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtB false = .ok (.bool, 1, 1) ∧
    validateWideDynSafePtrWithBytes wBadBool a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtB true = .error (.pointeeErr (.invalidBoolScalar 2)) ∧
    validateWideDynSafePtrWithBytes wNullRef a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtRU true = .error (.pointeeErr .nullNestedSafePtr) ∧
    validateWideDynSafePtrWithBytes wDangRef a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtRU true = .ok (.ref .not .u32, 8, 8) ∧
    validateWideDynSafePtrWithBytes wDangRef a3ChildSessionReg maxRepresentableSize64 specSend false
      (.provenanced 16 testIdMax 0) vtRN true = .error (.pointeeErr .uninhabitedNestedSafePtr) := by
  have hvB : validateVTableHalf a3ChildSessionWorld a3ChildSessionReg
      (.provenanced 0x1000 testId1 0) (.principalLess [.send]) = .ok a3DescBool := by decide +kernel
  have hvRU : validateVTableHalf a3ChildSessionWorld a3ChildSessionReg
      (.provenanced 0x2000 testId2 0) (.principalLess [.send]) = .ok a3DescRefU32 := by decide +kernel
  have hvRN : validateVTableHalf a3ChildSessionWorld a3ChildSessionReg
      (.provenanced 0x3000 testId3 0) (.principalLess [.send]) = .ok a3DescRefNever := by decide +kernel
  exact wideDyn_recursive_bytes_and_childSession_mayDangle
    a3ChildSessionWorld a3ChildSessionReg maxRepresentableSize64 (.principalLess [.send])
    (.provenanced 0x1000 testId1 0) (.provenanced 0x2000 testId2 0) (.provenanced 0x3000 testId3 0)
    a3DescBool a3DescRefU32 a3DescRefNever testIdMax 16
    hvB rfl rfl rfl hvRU rfl rfl rfl hvRN rfl rfl rfl (by decide) (by decide)

/-! ## Section 4: Explicit `#guard_msgs in #print axioms` Verification -/

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.allocWorldRel_deallocate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.allocWorldRel_deallocate

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocate_postRemovalFailure_retains_detached_state' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocate_postRemovalFailure_retains_detached_state

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.rustcNoWritable_preserves_uninit_and_frozen_sibling' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.rustcNoWritable_preserves_uninit_and_frozen_sibling

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.evalFnEntryRetagWithParamMap_rustcNoWritable_eq_evalStmt

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.static_pureFreeze_preserved_ub_vs_erased_unsound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.static_pureFreeze_preserved_ub_vs_erased_unsound

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.oversized_array_rawPtr_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.oversized_array_rawPtr_separation

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.vtableRegistry_intern_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.vtableRegistry_intern_idempotent

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_invalidVTable_precedes_all_data_ub' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_invalidVTable_precedes_all_data_ub

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.allocWorldRel_iff_eq_ofLinear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.allocWorldRel_iff_eq_ofLinear

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocateMachine_race_checked_before_cleanup' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocateMachine_race_checked_before_cleanup

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.selectFnEntryPolicy_eq_upstream_create' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.selectFnEntryPolicy_eq_upstream_create

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.vtableMatchesExpectedSpec_ignores_autoTraits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.vtableMatchesExpectedSpec_ignores_autoTraits

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocateMachine_sameWriter_foreignRead_races' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.keyedDeallocateMachine_sameWriter_foreignRead_races

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.stepNode_read_then_childWrite_eq_parentWrite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.stepNode_read_then_childWrite_eq_parentWrite

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.static_mixed_miri_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.static_mixed_miri_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.upcastVTableToAutoTraits_preserves_drop_size_align' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.upcastVTableToAutoTraits_preserves_drop_size_align

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.saltedVTable_distinct_salts_distinct_allocIds_both_valid' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.saltedVTable_distinct_salts_distinct_allocIds_both_valid

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.keyedAllocateMachine_deallocateMachine_sameThread_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.keyedAllocateMachine_deallocateMachine_sameThread_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetag_eq_sourceOrder_of_writableAncestors

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.sourceOrder_rustcNoWritable_preserves_all_frozen_nodes' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.sourceOrder_rustcNoWritable_preserves_all_frozen_nodes

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.unsized_rawPtr_layoutOverflow_rejected_like_upstream' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.unsized_rawPtr_layoutOverflow_rejected_like_upstream

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.validateRawPtrFastPath_ne_layoutFirst_imp' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.validateRawPtrFastPath_ne_layoutFirst_imp

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetag_ok_iff_upstream_ok_iff_sourceOrder_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.rawWideDyn_vtable_checked_data_unchecked' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.rawWideDyn_vtable_checked_data_unchecked

/-- info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.VTableWorldWF.intern_roundTrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.VTableWorldWF.intern_roundTrip

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.SaltedVTableWorldWF.internSalted_roundTrip' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.SaltedVTableWorldWF.internSalted_roundTrip

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_mayDangle_addressTooClose_and_uninhabited_concrete_ok

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.deallocActor_ofVClock_catches_unlisted_reader_vs_nonzeroFallback

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.execFnEntryMutRetagSourceOrder_bottomUp_vs_flatAncestors

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.static_zstUnsafeCell_composite_miri_separation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.static_zstUnsafeCell_composite_miri_separation

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.validateRawPtrFull_customDynDst_layout_and_vtable_soundness' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.validateRawPtrFull_customDynDst_layout_and_vtable_soundness

/--
info: 'Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_recursive_bytes_and_childSession_mayDangle' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Anneal.ExtTreeMapAllocAndNoWritableProto.wideDyn_recursive_bytes_and_childSession_mayDangle

/-! ## Section 5: Deterministic Workload Generators & Elaboration Benchmarks (`M = 16, 64, 128, 256`) -/

def benchAllocEntry : LocalAllocEntry :=
  ⟨.heap, 8, 8, .mut, []⟩

def benchIdSucc (k : Nat) : MiriAllocId :=
  ⟨UInt64.ofNat (k % 65535 + 1), by
    intro hz
    have htoNat : (UInt64.ofNat (k % 65535 + 1)).toNat = 0 := congrArg UInt64.toNat hz
    rw [UInt64.toNat_ofNat'] at htoNat
    have hlt : k % 65535 + 1 < UInt64.size := by
      have : k % 65535 < 65535 := Nat.mod_lt k (by decide)
      have : UInt64.size = 18446744073709551616 := rfl
      omega
    rw [Nat.mod_eq_of_lt hlt] at htoNat
    omega⟩

def buildLinearTable : Nat → LinearAllocWorld → LinearAllocWorld
  | 0, w => w
  | k + 1, w => buildLinearTable k (w.insertLive (benchIdSucc k) benchAllocEntry)

def queryAndRemoveLinear : Nat → LinearAllocWorld → Bool → Bool
  | 0, _, acc => acc
  | k + 1, w, acc =>
    let id := benchIdSucc k
    let foundOk :=
      match w.findLive? id with
      | some loc => Nat.beq loc.sizeBytes.toNat 8
      | none => false
    if k % 4 == 0 then
      let (w', rem?) := w.removeLive id
      queryAndRemoveLinear k w' (acc && foundOk && rem?.isSome)
    else
      queryAndRemoveLinear k w (acc && foundOk)

def runSuite1Linear (m : Nat) : Bool :=
  let wBuilt := buildLinearTable m LinearAllocWorld.empty
  queryAndRemoveLinear m wBuilt true

def buildKeyedTable : Nat → KeyedAllocWorld → KeyedAllocWorld
  | 0, w => w
  | k + 1, w => buildKeyedTable k (w.insertLive (benchIdSucc k) benchAllocEntry)

def queryAndRemoveKeyed : Nat → KeyedAllocWorld → Bool → Bool
  | 0, _, acc => acc
  | k + 1, w, acc =>
    let id := benchIdSucc k
    let foundOk :=
      match w.findLive? id with
      | some loc => Nat.beq loc.sizeBytes.toNat 8
      | none => false
    if k % 4 == 0 then
      let (w', rem?) := w.removeLive id
      queryAndRemoveKeyed k w' (acc && foundOk && rem?.isSome)
    else
      queryAndRemoveKeyed k w (acc && foundOk)

def runSuite1Keyed (m : Nat) : Bool :=
  let wBuilt := buildKeyedTable m KeyedAllocWorld.empty
  queryAndRemoveKeyed m wBuilt true

def mkFrozenSiblingNodes : Nat → List TreeTagNode
  | 0 => []
  | k + 1 => ⟨k + 2, 10, 0, 4, .frozen, none, some 1⟩ :: mkFrozenSiblingNodes k

def mkManySiblingsWorld (m : Nat) : FnEntryBorrowWorld where
  allocId := 10
  bytes := [(.init 1 none), (.init 2 none), (.init 3 none), (.init 4 none)]
  nodes := mkFrozenSiblingNodes m ++ [⟨1, 10, 0, 4, .unique, none, none⟩]
  activeProtectors := ProtectorSet.empty
  nextTag := m + 2
  nextProtector := 1

def runSuite2Writable (m : Nat) : Bool :=
  (execFnEntryMutRetag (mkManySiblingsWorld m) 1 0 4 unpinFreezeFacts true .writableChildWrite false).isOk

def runSuite2NoWritable (m : Nat) : Bool :=
  (execFnEntryMutRetag (mkManySiblingsWorld m) 1 0 4 unpinFreezeFacts true .rustcNoWritable false).isOk

def mkNestedUnitArrayTy : Nat → ProtoTy
  | 0 => .u8
  | k + 1 => .array (mkNestedUnitArrayTy k) 1

def runSuite3LayoutFirst (m : Nat) : Bool :=
  (validateRawPtrLayoutFirst maxRepresentableSize64 (mkNestedUnitArrayTy m) (.thin 16 none)).isOk

def runSuite3FastPath (m : Nat) : Bool :=
  (validateRawPtrFastPath maxRepresentableSize64 (mkNestedUnitArrayTy m) (.thin 16 none)).isOk

/-- Closed sanity check that every benchmark workload across `M = 16` reduces to `true` in the kernel. -/
theorem canary_benchmarks_all_succeed_M16 :
    runSuite1Linear 16 = true ∧
    runSuite1Keyed 16 = true ∧
    runSuite2Writable 16 = true ∧
    runSuite2NoWritable 16 = true ∧
    runSuite3LayoutFirst 16 = true ∧
    runSuite3FastPath 16 = true := by
  decide +kernel

/-! ## Section 6: Warmed Interleaved Kernel Heartbeat Benchmarks & Meta-Level Axiom / Reachability Audit -/

open Lean Elab Command Meta in
run_cmd do
  let measureKernelDecideArm (exprSrc : String) : CommandElabM (Nat × Float) := do
    let cmdSrc := s!"set_option maxHeartbeats 20000000 in example : {exprSrc} = true := by decide +kernel"
    let env ← getEnv
    let Except.ok stx := Parser.runParserCategory env `command cmdSrc "<bench>"
      | throwError "failed to parse benchmark command: {cmdSrc}"
    let hb0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    withoutModifyingEnv do
      elabCommand stx
    let t1 ← IO.monoNanosNow
    let hb1 ← IO.getNumHeartbeats
    let ms := (Float.ofNat (t1 - t0)) / 1000000.0
    return (hb1 - hb0, ms)

  -- 1. Warmed, interleaved kernel-reduction (`decide +kernel`) elaboration benchmarks across M = 16, 64, 128, 256
  let sizes : List Nat := [16, 64, 128, 256]
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Linear 8"
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Keyed 8"
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2Writable 8"
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2NoWritable 8"
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3LayoutFirst 8"
  let _ ← measureKernelDecideArm "Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3FastPath 8"

  let mut benchLines : Array String := #["=== BENCHMARK RECEIPTS (decide +kernel, warmed & interleaved, arm order alternates per scale) ==="]
  -- `[adv B1]`: A0 always ran the baseline arm first at every scale; the first arm now alternates
  -- (`M = 64, 256` run the second arm first) so neither arm systematically inherits warm caches.
  for m in sizes do
    let flip := m == 64 || m == 256
    let (hbL, msL, hbK, msK) ← if flip then do
        let (hbK, msK) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Keyed {m}"
        let (hbL, msL) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Linear {m}"
        pure (hbL, msL, hbK, msK)
      else do
        let (hbL, msL) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Linear {m}"
        let (hbK, msK) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite1Keyed {m}"
        pure (hbL, msL, hbK, msK)
    benchLines := benchLines.push
      s!"[Suite1 AllocWorld M={m}] Linear={hbL} hb ({msL.toString} ms) | Keyed={hbK} hb ({msK.toString} ms)"
  for m in sizes do
    let flip := m == 64 || m == 256
    let (hbW, msW, hbN, msN) ← if flip then do
        let (hbN, msN) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2NoWritable {m}"
        let (hbW, msW) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2Writable {m}"
        pure (hbW, msW, hbN, msN)
      else do
        let (hbW, msW) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2Writable {m}"
        let (hbN, msN) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite2NoWritable {m}"
        pure (hbW, msW, hbN, msN)
    benchLines := benchLines.push
      s!"[Suite2 FnEntryRetag M={m}] writableChildWrite={hbW} hb ({msW.toString} ms) | rustcNoWritable={hbN} hb ({msN.toString} ms)"
  for m in sizes do
    let flip := m == 64 || m == 256
    let (hbLF, msLF, hbFP, msFP) ← if flip then do
        let (hbFP, msFP) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3FastPath {m}"
        let (hbLF, msLF) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3LayoutFirst {m}"
        pure (hbLF, msLF, hbFP, msFP)
      else do
        let (hbLF, msLF) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3LayoutFirst {m}"
        let (hbFP, msFP) ← measureKernelDecideArm s!"Anneal.ExtTreeMapAllocAndNoWritableProtoTests.runSuite3FastPath {m}"
        pure (hbLF, msLF, hbFP, msFP)
    benchLines := benchLines.push
      s!"[Suite3 RawPtrSized M={m}] LayoutFirst={hbLF} hb ({msLF.toString} ms) | FastPath={hbFP} hb ({msFP.toString} ms)"
  logInfo (String.intercalate "\n" benchLines.toList)

open Lean Elab Command Meta in
run_cmd do
  let collectTransitiveClosure (env : Environment) (roots : Array Name) :
      NameSet × Array Name × Array Name × Array Name × Array Name := Id.run do
    let mut visited : NameSet := {}
    let mut worklist : Array Name := roots
    let mut unsafeDecls : Array Name := #[]
    let mut choiceAxioms : Array Name := #[]
    let mut sorryAxioms : Array Name := #[]
    let mut reduceBoolAxioms : Array Name := #[]
    while !worklist.isEmpty do
      let curr := worklist.back!
      worklist := worklist.pop
      if visited.contains curr then
        continue
      visited := visited.insert curr
      match env.find? curr with
      | none => continue
      | some ci =>
        if ci.isUnsafe then
          unsafeDecls := unsafeDecls.push curr
        match ci with
        | .axiomInfo _ =>
          if curr == ``Classical.choice then
            choiceAxioms := choiceAxioms.push curr
          else if curr == ``sorryAx then
            sorryAxioms := sorryAxioms.push curr
          else if curr == ``Lean.ofReduceBool || curr == ``Lean.ofReduceNat then
            reduceBoolAxioms := reduceBoolAxioms.push curr
        | _ => pure ()
        for dep in ci.getUsedConstantsAsSet do
          if !visited.contains dep then
            worklist := worklist.push dep
    return (visited, unsafeDecls, choiceAxioms, sorryAxioms, reduceBoolAxioms)

  let rec exprHasUnusedPlaceholderTo (targetSet : NameSet) (e : Expr) : Bool :=
    match e with
    | .letE _ ty val body _ =>
      -- `[adv A3]`: check `!body.hasLooseBVar 0` (the bound variable itself!) rather than
      -- `!body.hasLooseBVars`, which missed unused `let _ := @thm` inside parameterized helpers
      -- (`private def f (x : Nat) := let _ := @thm; x`, where `body = .bvar 1` has loose bvars!).
      let unusedAndMentionsTarget :=
        (!body.hasLooseBVar 0) && val.getUsedConstants.any (fun nm => targetSet.contains nm)
      unusedAndMentionsTarget ||
        exprHasUnusedPlaceholderTo targetSet ty ||
        exprHasUnusedPlaceholderTo targetSet val ||
        exprHasUnusedPlaceholderTo targetSet body
    | .app f a =>
      -- `[adv B1]` + `[adv A1]` + `[adv A3]`: flag beta-redex `(fun _ => b) thm` and `@letFun α β v f`
      -- using `!b.hasLooseBVar 0` on the continuation lambda `args[3]!` (NOT the return-type motive
      -- `args[1]!`, which previously false-positived on valid non-dependent term-mode `have h := thm; …`
      -- while missing parameterized `private def f (x : Nat) := have _ := @thm; x`).
      let betaUnused :=
        match f with
        | .lam _ _ b _ => (!b.hasLooseBVar 0) && a.getUsedConstants.any (fun nm => targetSet.contains nm)
        | _ => false
      let letFunUnused :=
        match e.getAppFn with
        | .const nm _ =>
          let args := e.getAppArgs
          if nm == ``letFun && args.size >= 4 then
            (match args[3]! with | .lam _ _ b _ => !b.hasLooseBVar 0 | _ => false) &&
              args[2]!.getUsedConstants.any (fun c => targetSet.contains c)
          else false
        | _ => false
      betaUnused || letFunUnused ||
        exprHasUnusedPlaceholderTo targetSet f || exprHasUnusedPlaceholderTo targetSet a
    | .lam _ ty b _ => exprHasUnusedPlaceholderTo targetSet ty || exprHasUnusedPlaceholderTo targetSet b
    | .forallE _ ty b _ => exprHasUnusedPlaceholderTo targetSet ty || exprHasUnusedPlaceholderTo targetSet b
    | .mdata _ e' => exprHasUnusedPlaceholderTo targetSet e'
    | .proj _ _ e' => exprHasUnusedPlaceholderTo targetSet e'
    | _ => false

  -- `[adv A3]`: prune dead `.letE` / beta-redex / `letFun` bindings across ALL modules (both
  -- `Proto.lean` and `Tests.lean`) when computing theorem reachability, so cross-module placeholder
  -- laundering (`have _ := @unreachedThm` inside a `Proto.lean` helper theorem) never counts toward
  -- 100% reachability, while keeping `collectTransitiveClosure` unpruned for axiom safety.
  let rec collectLiveConstantsAux (acc : NameSet) (e : Expr) : NameSet :=
    match e with
    | .const nm _ => acc.insert nm
    | .letE _ ty val body _ =>
      if !body.hasLooseBVar 0 then
        collectLiveConstantsAux acc body
      else
        collectLiveConstantsAux (collectLiveConstantsAux (collectLiveConstantsAux acc ty) val) body
    | .app f a =>
      match f with
      | .lam _ _ b _ =>
        if !b.hasLooseBVar 0 then
          collectLiveConstantsAux acc b
        else
          collectLiveConstantsAux (collectLiveConstantsAux acc f) a
      | _ =>
        match e.getAppFn with
        | .const nm _ =>
          let args := e.getAppArgs
          if nm == ``letFun && args.size >= 4 then
            match args[3]! with
            | .lam _ _ b _ =>
              if !b.hasLooseBVar 0 then
                let rest := (args.extract 4 args.size).foldl collectLiveConstantsAux (acc.insert nm)
                collectLiveConstantsAux rest b
              else
                collectLiveConstantsAux (collectLiveConstantsAux acc f) a
            | _ => collectLiveConstantsAux (collectLiveConstantsAux acc f) a
          else
            collectLiveConstantsAux (collectLiveConstantsAux acc f) a
        | _ => collectLiveConstantsAux (collectLiveConstantsAux acc f) a
    | .lam _ ty b _ => collectLiveConstantsAux (collectLiveConstantsAux acc ty) b
    | .forallE _ ty b _ => collectLiveConstantsAux (collectLiveConstantsAux acc ty) b
    | .mdata _ e' => collectLiveConstantsAux acc e'
    | .proj _ _ e' => collectLiveConstantsAux acc e'
    | _ => acc

  let collectPrunedReachableClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
    let mut visited : NameSet := {}
    let mut worklist : Array Name := roots
    while !worklist.isEmpty do
      let curr := worklist.back!
      worklist := worklist.pop
      if visited.contains curr then
        continue
      visited := visited.insert curr
      match env.find? curr with
      | none => continue
      | some ci =>
        let liveDeps : NameSet :=
          match ci.value? (allowOpaque := true) with
          | some val => collectLiveConstantsAux (collectLiveConstantsAux {} ci.type) val
          | none => ci.getUsedConstantsAsSet
        for dep in liveDeps do
          if !visited.contains dep then
            worklist := worklist.push dep
    return visited

  -- `[adv B2]` + `[adv A2]` + `[adv A3]`: tautological equations / iffs / inequalities (`a = a`,
  -- `a ↔ a`, `BEq.beq a a`, `a ≤ a`), `let`-aliased tautologies, vacuous `True` / duplicate
  -- conjuncts & disjuncts (`True ∧ P`, `P ∨ True`, `P ∧ P`, `P ∨ P`), `¬ False`, and vacuous
  -- embedded implications (`(False → P) ∧ Q`, `(P → True) ∧ Q`) anywhere in a closed witness
  -- *statement* are flagged.
  let rec resolveClosedLetAlias : Array (Option Expr) → Nat → Expr → Expr
    | _, 0, e => e
    | letCtx, fuel + 1, .mdata _ e' => resolveClosedLetAlias letCtx (fuel + 1) e'
    | letCtx, fuel + 1, .bvar idx =>
      if h : idx < letCtx.size then
        match letCtx[letCtx.size - 1 - idx] with
        | some val => resolveClosedLetAlias letCtx fuel val
        | none => .bvar idx
      else .bvar idx
    | _, _, e => e

  let rec exprHasTautologyAux (letCtx : Array (Option Expr)) (e : Expr) : Bool :=
    match e with
    | .app f a =>
      let args := e.getAppArgs
      let here :=
        match e.getAppFn with
        | .const nm _ =>
          if nm == ``Eq && args.size == 3 then
            let lhs := resolveClosedLetAlias letCtx 8 args[1]!
            let rhs := resolveClosedLetAlias letCtx 8 args[2]!
            lhs == rhs
          else if nm == ``Iff && args.size == 2 then
            let lhs := resolveClosedLetAlias letCtx 8 args[0]!
            let rhs := resolveClosedLetAlias letCtx 8 args[1]!
            lhs == rhs
          else if nm == ``BEq.beq && args.size == 4 then
            let lhs := resolveClosedLetAlias letCtx 8 args[2]!
            let rhs := resolveClosedLetAlias letCtx 8 args[3]!
            lhs == rhs
          else if nm == ``LE.le && args.size == 4 then
            let lhs := resolveClosedLetAlias letCtx 8 args[2]!
            let rhs := resolveClosedLetAlias letCtx 8 args[3]!
            lhs == rhs
          else if nm == ``And && args.size == 2 then
            let lhs := resolveClosedLetAlias letCtx 8 args[0]!
            let rhs := resolveClosedLetAlias letCtx 8 args[1]!
            lhs == rhs || lhs.isConstOf ``True || rhs.isConstOf ``True
          else if nm == ``Or && args.size == 2 then
            let lhs := resolveClosedLetAlias letCtx 8 args[0]!
            let rhs := resolveClosedLetAlias letCtx 8 args[1]!
            lhs == rhs || lhs.isConstOf ``True || rhs.isConstOf ``True
          else if nm == ``Not && args.size == 1 then
            (resolveClosedLetAlias letCtx 8 args[0]!).isConstOf ``False
          else false
        | _ => false
      here || exprHasTautologyAux letCtx f || exprHasTautologyAux letCtx a
    | .lam _ ty b _ =>
      exprHasTautologyAux letCtx ty || exprHasTautologyAux (letCtx.push none) b
    | .forallE _ ty b _ =>
      let dom := resolveClosedLetAlias letCtx 8 ty
      let cod := resolveClosedLetAlias (letCtx.push none) 8 b
      dom.isConstOf ``False || cod.isConstOf ``True ||
        exprHasTautologyAux letCtx ty || exprHasTautologyAux (letCtx.push none) b
    | .letE _ ty v b _ =>
      let resolvedV := resolveClosedLetAlias letCtx 8 v
      let entry := if !resolvedV.hasLooseBVars then some resolvedV else none
      exprHasTautologyAux letCtx ty || exprHasTautologyAux letCtx v ||
        exprHasTautologyAux (letCtx.push entry) b
    | .mdata _ e' => exprHasTautologyAux letCtx e'
    | .proj _ _ e' => exprHasTautologyAux letCtx e'
    | _ => false

  let exprHasTautology (e : Expr) : Bool :=
    (resolveClosedLetAlias #[] 8 e).isConstOf ``True || exprHasTautologyAux #[] e

  -- `[adv A2]`: do NOT use blanket `nm.isInternalDetail`, which returns `true` for ANY user-written
  -- `_`-prefixed public theorem (`theorem _sneaky (h : False) : True`), allowing `_`-prefixed
  -- conditional or tautological theorems to evade `conditionalTests` and `tautologicalWitnesses`!
  let rec nameHasCompilerAuxComponent : Name → Bool
    | .anonymous => false
    | .num _ _ => true
    | .str parent s =>
      s.startsWith "_proof_" || s.startsWith "_simp_" || s.startsWith "_aux" ||
      s.startsWith "_unary" || s.startsWith "_mutual" || s.startsWith "_sunfold" ||
      s.startsWith "_unfold" || s.startsWith "_eq_" || s.startsWith "_congr_" ||
      s.startsWith "_splitter" || s.startsWith "_redArg" || s.startsWith "_closed_" ||
      s.startsWith "_lambda_" || s.startsWith "_sizeOf_" || s.startsWith "_sparseCasesOn_" ||
      s.startsWith "match_" || s.startsWith "proof_" ||
      nameHasCompilerAuxComponent parent

  let isCompilerGeneratedAuxThm (nm : Name) : Bool :=
    if nm.hasMacroScopes || nameHasCompilerAuxComponent nm then true
    else
      match nm with
      | .str parent s =>
        s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "ofNat_ctorIdx" ||
        s == "eq_def" ||
        s.startsWith "eq_" || s.startsWith "congr_" || s.startsWith "brecOn" ||
        s.startsWith "induct" || s.startsWith "casesOn" || s.startsWith "recOn" ||
        s.startsWith "below" || s.startsWith "ibelow" || s.startsWith "noConfusion" ||
        (s == "eq" && match parent with | .str _ ps => ps.startsWith "brecOn" | _ => false)
      | _ => false

  let env ← getEnv
  let some protoModIdx := env.header.moduleNames.idxOf? `Anneal.ExtTreeMapAllocAndNoWritableProto
    | throwError "module Anneal.ExtTreeMapAllocAndNoWritableProto not found in imports"

  -- Collect all declarations in Anneal.ExtTreeMapAllocAndNoWritableProto
  let protoModData := env.header.moduleData[protoModIdx]!
  let mut protoAllDecls : Array Name := #[]
  let mut protoPublicThms : Array Name := #[]
  let mut protoPublicThmSet : NameSet := {}
  for nm in protoModData.constNames do
    protoAllDecls := protoAllDecls.push nm
    if let some (.thmInfo _) := env.find? nm then
      if !isPrivateName nm && !isCompilerGeneratedAuxThm nm then
        protoPublicThms := protoPublicThms.push nm
        protoPublicThmSet := protoPublicThmSet.insert nm

  -- Collect all declarations in the current test file (`[adv A1]`: scan `ci.value?` across ALL
  -- declarations in `map₂` — including `def`, `private`, and `_`-prefixed helpers where
  -- `Name.isInternalDetail` is `true` — so placeholder laundering via `private def` cannot evade
  -- `placeholderUses`).
  let mut testAllDecls : Array Name := #[]
  let mut closedTestWitnesses : Array Name := #[]
  let mut conditionalTests : Array Name := #[]
  let mut placeholderUses : Array Name := #[]
  let mut tautologicalWitnesses : Array Name := #[]
  for (nm, ci) in env.constants.map₂.toList do
    testAllDecls := testAllDecls.push nm
    if let some val := ci.value? (allowOpaque := true) then
      if exprHasUnusedPlaceholderTo protoPublicThmSet val then
        placeholderUses := placeholderUses.push nm
    if let .thmInfo tv := ci then
      if !isPrivateName nm && !isCompilerGeneratedAuxThm nm then
        if tv.type.isForall then
          conditionalTests := conditionalTests.push nm
        else
          closedTestWitnesses := closedTestWitnesses.push nm
          if exprHasTautology tv.type then
            tautologicalWitnesses := tautologicalWitnesses.push nm

  let allAuditRoots := protoAllDecls ++ testAllDecls
  let (auditVisited, unsafeDecls, choiceAx, sorryAxFound, reduceAx) :=
    collectTransitiveClosure env allAuditRoots
  -- `[adv B1]`: A0 only looked for three *named* axioms, so a user-declared `axiom` anywhere in the
  -- closure would have passed. Flag every axiom outside `{propext, Quot.sound}`.
  let foreignAxiomsIn (env : Environment) (visited : NameSet) : Array Name := Id.run do
    let mut out : Array Name := #[]
    for nm in visited do
      if let some (.axiomInfo _) := env.find? nm then
        if nm != ``propext && nm != ``Quot.sound then
          out := out.push nm
    return out
  if !unsafeDecls.isEmpty then
    throwError "axiom audit FAILED: unsafe declarations found: {unsafeDecls}"
  if !choiceAx.isEmpty then
    throwError "axiom audit FAILED: Classical.choice dependency found!"
  if !sorryAxFound.isEmpty then
    throwError "axiom audit FAILED: sorryAx dependency found!"
  if !reduceAx.isEmpty then
    throwError "axiom audit FAILED: Lean.ofReduceBool / native_decide dependency found!"
  let foreignAx := foreignAxiomsIn env auditVisited
  if !foreignAx.isEmpty then
    throwError "axiom audit FAILED: axioms outside propext/Quot.sound found: {foreignAx}"
  if !conditionalTests.isEmpty then
    throwError "axiom audit FAILED: undischarged conditional test theorems found: {conditionalTests}"
  if !placeholderUses.isEmpty then
    throwError "axiom audit FAILED: `have _ := @thm` placeholder uses found: {placeholderUses}"
  if !tautologicalWitnesses.isEmpty then
    throwError "axiom audit FAILED: closed witnesses with tautological `a = a` / `a ↔ a` conjuncts: {tautologicalWitnesses}"

  -- Verify 100% public theorem reachability from closed test witnesses alone (`[adv A3]`: prune
  -- dead `.letE` / beta-redex / `letFun` bindings across ALL modules including `Proto.lean`)
  let closedReachable := collectPrunedReachableClosure env closedTestWitnesses
  let mut unreachedThms : Array Name := #[]
  for thmNm in protoPublicThms do
    if !closedReachable.contains thmNm then
      unreachedThms := unreachedThms.push thmNm
  if !unreachedThms.isEmpty then
    throwError "reachability audit FAILED: {unreachedThms.size} public theorems not exercised by closed test witnesses: {unreachedThms}"

  -- Self-test 1: rolled-back transitive Classical.choice probe
  withoutModifyingEnv do
    let Except.ok stx1a := Parser.runParserCategory (← getEnv) `command
      "noncomputable def _probeChoiceMid : Classical.inhabited_of_nonempty ⟨True.intro⟩ = Classical.inhabited_of_nonempty ⟨True.intro⟩ := rfl" "<probe1a>"
      | throwError "self-test 1a parse failed"
    elabCommand stx1a
    let Except.ok stx1b := Parser.runParserCategory (← getEnv) `command
      "noncomputable def _probeChoiceTop := _probeChoiceMid" "<probe1b>"
      | throwError "self-test 1b parse failed"
    elabCommand stx1b
    let (_, _, ch, _, _) := collectTransitiveClosure (← getEnv)
      #[`Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeChoiceTop]
    if ch.isEmpty then
      throwError "audit self-test 1 FAILED: missed transitive Classical.choice!"

  -- Self-test 2: direct sorryAx and Lean.ofReduceBool detection
  let (_, _, _, srCheck, _) := collectTransitiveClosure env #[``sorryAx]
  let (_, _, _, _, rbCheck) := collectTransitiveClosure env #[``Lean.ofReduceBool]
  if srCheck.isEmpty || rbCheck.isEmpty then
    throwError "audit self-test 2 FAILED: missed sorryAx or Lean.ofReduceBool!"

  -- Self-test 3: rolled-back `have _ := @thm` placeholder probe
  withoutModifyingEnv do
    let placeholderExpr : Expr :=
      .letE `_ (mkConst ``True)
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Option [0]) (mkConst ``MiriAllocId.ofUInt64_zero))
        (mkConst ``True.intro) false
    if !exprHasUnusedPlaceholderTo protoPublicThmSet placeholderExpr then
      throwError "audit self-test 3 FAILED: missed unused let placeholder!"

  -- Self-test 3b (`[adv B1]`): rolled-back *elaborated* `have _ := @thm` placeholder probe (A0's
  -- self-test 3 only checked a hand-built `.letE`, never what the elaborator actually emits).
  withoutModifyingEnv do
    let Except.ok stx3b := Parser.runParserCategory (← getEnv) `command
      "theorem _probePlaceholderReal : True := by\n  have _ := @Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext\n  exact True.intro" "<probe3b>"
      | throwError "self-test 3b parse failed"
    elabCommand stx3b
    let some (.thmInfo tv3b) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probePlaceholderReal
      | throwError "self-test 3b lookup failed"
    if !exprHasUnusedPlaceholderTo protoPublicThmSet tv3b.value then
      throwError "audit self-test 3b FAILED: missed an elaborated `have _ := @thm` placeholder!"

  -- Self-test 4 (`[adv A2]` strengthened): rolled-back `_`-prefixed conditional test theorem must
  -- be classified as a user theorem (`!isPrivateName && !isCompilerGeneratedAuxThm`) AND flagged!
  withoutModifyingEnv do
    let Except.ok stx4 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeCondTest (h : False) : True := True.intro" "<probe4>"
      | throwError "self-test 4 parse failed"
    elabCommand stx4
    let probeNm4 := `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeCondTest
    let some (.thmInfo tv) := (← getEnv).find? probeNm4
      | throwError "self-test 4 lookup failed"
    if isPrivateName probeNm4 || isCompilerGeneratedAuxThm probeNm4 || !tv.type.isForall then
      throwError "audit self-test 4 FAILED: missed `_`-prefixed conditional test theorem!"

  -- Self-test 5: clean constant false-positive guard
  let (visClean, uClean, cClean, sClean, rClean) :=
    collectTransitiveClosure env #[``Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext]
  if !uClean.isEmpty || !cClean.isEmpty || !sClean.isEmpty || !rClean.isEmpty ||
      !(foreignAxiomsIn env visClean).isEmpty then
    throwError "audit self-test 5 FAILED: false positive on clean theorem!"

  -- Self-test 6 (`[adv B1]`): a rolled-back user-declared axiom (added via `addDecl`, so no axiom
  -- command appears in this file) must be flagged by the foreign-axiom check.
  withoutModifyingEnv do
    let probeAx : AxiomVal :=
      { name := `probeForeignAxiomB1, levelParams := [], type := mkConst ``False, isUnsafe := false }
    liftCoreM <| addDecl (.axiomDecl probeAx)
    let (vis6, _, _, _, _) := collectTransitiveClosure (← getEnv) #[`probeForeignAxiomB1]
    if (foreignAxiomsIn (← getEnv) vis6).isEmpty then
      throwError "audit self-test 6 FAILED: missed a user-declared axiom!"

  -- Self-test 7 (`[adv A1]`): a rolled-back `private def` laundering an unused `let _ := @thm`
  -- placeholder (which B1's public-`.thmInfo`-only scan missed, and where `Name.isInternalDetail`
  -- is `true` because of `_private`) must be flagged via `map₂` + `ci.value?`.
  withoutModifyingEnv do
    let Except.ok stx7 := Parser.runParserCategory (← getEnv) `command
      "private def _probeDefLaunder : Bool := let _ := @Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext; true" "<probe7>"
      | throwError "self-test 7 parse failed"
    elabCommand stx7
    let mut caught7 := false
    for (nm, ci) in (← getEnv).constants.map₂.toList do
      if nm.toString.endsWith "_probeDefLaunder" then
        if let some val := ci.value? (allowOpaque := true) then
          if exprHasUnusedPlaceholderTo protoPublicThmSet val then
            caught7 := true
    if !caught7 then
      throwError "audit self-test 7 FAILED: missed `private def` placeholder laundering!"

  -- Self-test 8 (`[adv A1]`): a rolled-back term-mode `private theorem` using `have _ := @thm; ...`
  -- must also be flagged via `map₂` + `ci.value? (allowOpaque := true)`.
  withoutModifyingEnv do
    let Except.ok stx8 := Parser.runParserCategory (← getEnv) `command
      "private theorem _probePrivHaveLaunder : True := have _ := @Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext; True.intro" "<probe8>"
      | throwError "self-test 8 parse failed"
    elabCommand stx8
    let mut caught8 := false
    for (nm, ci) in (← getEnv).constants.map₂.toList do
      if nm.toString.endsWith "_probePrivHaveLaunder" then
        if let some val := ci.value? (allowOpaque := true) then
          if exprHasUnusedPlaceholderTo protoPublicThmSet val then
            caught8 := true
    if !caught8 then
      throwError "audit self-test 8 FAILED: missed `private theorem` term-mode `have` placeholder!"

  -- Self-test 10 (`[adv B2]`): a rolled-back closed witness with a tautological `a = a` conjunct must
  -- be flagged by the tautology detector, while a genuine canary statement must not be.
  withoutModifyingEnv do
    let Except.ok stx9 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeTautology : (2 : Nat) = 2 ∧ (1 : Nat) < 2 := ⟨rfl, by decide⟩" "<probe10>"
      | throwError "self-test 10 parse failed"
    elabCommand stx9
    let probeNm9 := `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeTautology
    let some (.thmInfo tv9) := (← getEnv).find? probeNm9
      | throwError "self-test 10 lookup failed"
    if isPrivateName probeNm9 || isCompilerGeneratedAuxThm probeNm9 || !exprHasTautology tv9.type then
      throwError "audit self-test 10 FAILED: missed a tautological `a = a` conjunct!"
  let some (.thmInfo tvClean) :=
      env.find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests.canary_part3B_allocWF_validation_lookup_soundness
    | throwError "self-test 10 clean lookup failed"
  if exprHasTautology tvClean.type then
    throwError "audit self-test 10 FAILED: false tautology positive on a genuine canary!"

  -- Self-test 11 (`[adv A2]`): rolled-back probes for `let`-aliased tautologies (`let x := 2; x = 2`),
  -- Boolean `BEq` tautologies (`(testId1 == testId1) = true`), and `True` conjuncts (`True ∧ 1 < 2`)!
  withoutModifyingEnv do
    let Except.ok stx11a := Parser.runParserCategory (← getEnv) `command
      "theorem _probeLetTaut : let x : Nat := 2; x = 2 := rfl" "<probe11a>"
      | throwError "self-test 11a parse failed"
    elabCommand stx11a
    let Except.ok stx11b := Parser.runParserCategory (← getEnv) `command
      "theorem _probeBeqTaut : (testId1 == testId1) = true := rfl" "<probe11b>"
      | throwError "self-test 11b parse failed"
    elabCommand stx11b
    let Except.ok stx11c := Parser.runParserCategory (← getEnv) `command
      "theorem _probeTrueConj : True ∧ (1 : Nat) < 2 := ⟨True.intro, by decide⟩" "<probe11c>"
      | throwError "self-test 11c parse failed"
    elabCommand stx11c
    let some (.thmInfo tvLet) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeLetTaut
      | throwError "self-test 11a lookup failed"
    let some (.thmInfo tvBeq) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeBeqTaut
      | throwError "self-test 11b lookup failed"
    let some (.thmInfo tvTr) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeTrueConj
      | throwError "self-test 11c lookup failed"
    if !exprHasTautology tvLet.type || !exprHasTautology tvBeq.type || !exprHasTautology tvTr.type then
      throwError "audit self-test 11 FAILED: missed let-aliased, BEq, or True-conjunct tautology!"

  -- Self-test 12 (`[adv A3]`):
  -- (a) parameterized `private def` placeholder laundering (`x : Nat => let _ := @thm; x` and
  --     `have _ := @thm; x`, missed by `!b.hasLooseBVars` in B1–B3 & A1–A2!) is flagged, while a
  --     genuine non-dependent term-mode `have h := thm; h` (falsely flagged by B1's motive check!)
  --     passes without false positive;
  -- (b) `collectPrunedReachableClosure` prunes dead `have _ := @target` bindings inside intermediate
  --     helper theorems so cross-module placeholder laundering inside `Proto.lean` cannot fake 100%
  --     reachability;
  -- (c) vacuous embedded implications (`(False → P) ∧ Q`), `P ∨ True`, and reflexive `a ≤ a` are
  --     flagged by `exprHasTautology`.
  withoutModifyingEnv do
    let Except.ok stx12a1 := Parser.runParserCategory (← getEnv) `command
      "private def _probeParamLetLaunder (x : Nat) : Nat := let _ := @Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext; x" "<probe12a1>"
      | throwError "self-test 12a1 parse failed"
    elabCommand stx12a1
    let Except.ok stx12a2 := Parser.runParserCategory (← getEnv) `command
      "private def _probeParamHaveLaunder (x : Nat) : Nat := have _ := @Anneal.ExtTreeMapAllocAndNoWritableProto.KeyedAllocWorld.ext; x" "<probe12a2>"
      | throwError "self-test 12a2 parse failed"
    elabCommand stx12a2
    let Except.ok stx12a3 := Parser.runParserCategory (← getEnv) `command
      "private theorem _probeLegitTermHave : MiriAllocId.ofUInt64 0 = none := have h := MiriAllocId.ofUInt64_zero; h" "<probe12a3>"
      | throwError "self-test 12a3 parse failed"
    elabCommand stx12a3
    let mut caughtLetParam := false
    let mut caughtHaveParam := false
    let mut falsePosLegitHave := false
    for (nm, ci) in (← getEnv).constants.map₂.toList do
      if let some val := ci.value? (allowOpaque := true) then
        if nm.toString.endsWith "_probeParamLetLaunder" && exprHasUnusedPlaceholderTo protoPublicThmSet val then
          caughtLetParam := true
        if nm.toString.endsWith "_probeParamHaveLaunder" && exprHasUnusedPlaceholderTo protoPublicThmSet val then
          caughtHaveParam := true
        if nm.toString.endsWith "_probeLegitTermHave" && exprHasUnusedPlaceholderTo protoPublicThmSet val then
          falsePosLegitHave := true
    if !caughtLetParam || !caughtHaveParam || falsePosLegitHave then
      throwError "audit self-test 12a FAILED: parameterized placeholder or legitimate term-mode `have` mishandled!"

    let Except.ok stx12b1 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeUnreachedTarget : (1 : Nat) = 1 := rfl" "<probe12b1>"
      | throwError "self-test 12b1 parse failed"
    elabCommand stx12b1
    let Except.ok stx12b2 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeMidLaunderHelper : (2 : Nat) = 2 := by\n  have _ := @_probeUnreachedTarget\n  exact rfl" "<probe12b2>"
      | throwError "self-test 12b2 parse failed"
    elabCommand stx12b2
    let Except.ok stx12b3 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeOuterWitness : (2 : Nat) = 2 := _probeMidLaunderHelper" "<probe12b3>"
      | throwError "self-test 12b3 parse failed"
    elabCommand stx12b3
    let prunedVis := collectPrunedReachableClosure (← getEnv)
      #[`Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeOuterWitness]
    if !prunedVis.contains `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeMidLaunderHelper ||
        prunedVis.contains `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeUnreachedTarget then
      throwError "audit self-test 12b FAILED: `collectPrunedReachableClosure` failed to prune dead cross-theorem placeholder!"

    let Except.ok stx12c1 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeFalseImpConj : (False → (1 : Nat) = 2) ∧ (1 : Nat) < 2 := ⟨False.elim, by decide⟩" "<probe12c1>"
      | throwError "self-test 12c1 parse failed"
    elabCommand stx12c1
    let Except.ok stx12c2 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeOrTrue : ((1 : Nat) = 2 ∨ True) ∧ (1 : Nat) < 2 := ⟨Or.inr True.intro, by decide⟩" "<probe12c2>"
      | throwError "self-test 12c2 parse failed"
    elabCommand stx12c2
    let Except.ok stx12c3 := Parser.runParserCategory (← getEnv) `command
      "theorem _probeReflLe : (2 : Nat) ≤ 2 ∧ (1 : Nat) < 2 := ⟨Nat.le_refl 2, by decide⟩" "<probe12c3>"
      | throwError "self-test 12c3 parse failed"
    elabCommand stx12c3
    let some (.thmInfo tvFI) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeFalseImpConj
      | throwError "self-test 12c1 lookup failed"
    let some (.thmInfo tvOT) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeOrTrue
      | throwError "self-test 12c2 lookup failed"
    let some (.thmInfo tvRL) := (← getEnv).find? `Anneal.ExtTreeMapAllocAndNoWritableProtoTests._probeReflLe
      | throwError "self-test 12c3 lookup failed"
    if !exprHasTautology tvFI.type || !exprHasTautology tvOT.type || !exprHasTautology tvRL.type then
      throwError "audit self-test 12c FAILED: missed False-implication, Or-True, or reflexive LE tautology!"

  logInfo s!"axiom audit passed: {allAuditRoots.size} declarations ({protoPublicThms.size} prototype public theorems, {closedTestWitnesses.size} closed test witnesses, 0 unsafe, 0 Classical.choice, 0 Lean.ofReduceBool, 0 sorryAx, 0 axioms outside propext/Quot.sound, 0 placeholder uses, 0 tautological conjuncts, 0 undischarged conditional test theorems, 100% theorem reachability from closed test witnesses; 12/12 rolled-back self-tests passed)"

end Anneal.ExtTreeMapAllocAndNoWritableProtoTests
